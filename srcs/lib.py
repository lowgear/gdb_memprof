from __future__ import annotations

import cProfile

import collections
from contextlib import contextmanager
import dataclasses
import gdb
import itertools
import re
import sys
import datetime
# import tabulate
import timeit
# from tqdm import tqdm
import typing

DBG = False


'''
Corner cases of current approach:
- If there is a union variable on the stack we don't know what to do with it

Valueable observations:
- `some_type arr[42];` calls some_type ctor therefore dctor will be called for each element later
  This means typed array are no threat for the approach at least for mildly sane programms
- Tail calls are not problematic. Calls which happened before them have deconstructed frames so can not hold pointers

Uncovered things:
- Global vars may have pointers to heap
- Thread locals may have pointers to heap
- Visiting lambda closures
- Unique identifiers which would cover anonymous types such as (the anon type is between typedef and MyEnum)
    typedef enum {
        First
    } MyEnum;

TODOs:
- Implement tracking of backtrace and value access chain for debug purposes
- Account strings
- Less dereferences = faster
'''


LONGLONG = gdb.lookup_type('long long')


def get_type_code_name(t: gdb.Type) -> str:
    if type(t) is int:
        code = t
    else:
        code = type.code
    if code == gdb.TYPE_CODE_PTR:
        return "TYPE_CODE_PTR"
    if code == gdb.TYPE_CODE_ARRAY:
        return "TYPE_CODE_ARRAY"
    if code == gdb.TYPE_CODE_STRUCT:
        return "TYPE_CODE_STRUCT"
    if code == gdb.TYPE_CODE_UNION:
        return "TYPE_CODE_UNION"
    if code == gdb.TYPE_CODE_ENUM:
        return "TYPE_CODE_ENUM"
    if code == gdb.TYPE_CODE_FLAGS:
        return "TYPE_CODE_FLAGS"
    if code == gdb.TYPE_CODE_FUNC:
        return "TYPE_CODE_FUNC"
    if code == gdb.TYPE_CODE_INT:
        return "TYPE_CODE_INT"
    if code == gdb.TYPE_CODE_FLT:
        return "TYPE_CODE_FLT"
    if code == gdb.TYPE_CODE_VOID:
        return "TYPE_CODE_VOID"
    if code == gdb.TYPE_CODE_SET:
        return "TYPE_CODE_SET"
    if code == gdb.TYPE_CODE_RANGE:
        return "TYPE_CODE_RANGE"
    if code == gdb.TYPE_CODE_STRING:
        return "TYPE_CODE_STRING"
    if code == gdb.TYPE_CODE_BITSTRING:
        return "TYPE_CODE_BITSTRING"
    if code == gdb.TYPE_CODE_ERROR:
        return "TYPE_CODE_ERROR"
    if code == gdb.TYPE_CODE_METHOD:
        return "TYPE_CODE_METHOD"
    if code == gdb.TYPE_CODE_METHODPTR:
        return "TYPE_CODE_METHODPTR"
    if code == gdb.TYPE_CODE_MEMBERPTR:
        return "TYPE_CODE_MEMBERPTR"
    if code == gdb.TYPE_CODE_REF:
        return "TYPE_CODE_REF"
    if code == gdb.TYPE_CODE_RVALUE_REF:
        return "TYPE_CODE_RVALUE_REF"
    if code == gdb.TYPE_CODE_CHAR:
        return "TYPE_CODE_CHAR"
    if code == gdb.TYPE_CODE_BOOL:
        return "TYPE_CODE_BOOL"
    if code == gdb.TYPE_CODE_COMPLEX:
        return "TYPE_CODE_COMPLEX"
    if code == gdb.TYPE_CODE_TYPEDEF:
        return "TYPE_CODE_TYPEDEF"
    if code == gdb.TYPE_CODE_NAMESPACE:
        return "TYPE_CODE_NAMESPACE"
    if code == gdb.TYPE_CODE_DECFLOAT:
        return "TYPE_CODE_DECFLOAT"
    if code == gdb.TYPE_CODE_INTERNAL_FUNCTION:
        return "TYPE_CODE_INTERNAL_FUNCTION"
    assert False, str(code)


NON_TRAVERSIBLE_CODES = {
    gdb.TYPE_CODE_INT,
    gdb.TYPE_CODE_PTR,
    gdb.TYPE_CODE_FUNC,
    gdb.TYPE_CODE_BOOL,
    gdb.TYPE_CODE_ENUM,
    gdb.TYPE_CODE_REF,
    gdb.TYPE_CODE_RVALUE_REF,
    gdb.TYPE_CODE_FLT,
    gdb.TYPE_CODE_METHODPTR,
    # TODO write warnings about them
    gdb.TYPE_CODE_UNION,
}


def not_implemented():
    raise NotImplementedError()


def get_frame_blocks(frame: gdb.Frame) -> typing.Iterable[gdb.Block]:
    try:
        block = frame.block()
    except RuntimeError:
        # TODO print warning about block with missing symbols
        return
    while block is not None:
        yield block
        if block.function is not None:
            return
        block = block.superblock


def get_frame_variables(frame: gdb.Frame) -> typing.Iterable[gdb.Symbol]:
    current_line = frame.find_sal().line
    for block in get_frame_blocks(frame):
        for variable in block:
            # Assume var declaration takes exactly one line
            # TODO properly detect if var have been initialized
            if variable.line < current_line:
                yield variable
            else:
                break


def get_stack_frames(thread: gdb.InferiorThread) -> typing.Iterable[gdb.Frame]:
    with defer_switch_thread_back():
        thread.switch()
        frame = gdb.newest_frame()
        while frame is not None:
            yield frame
            frame = frame.older()


class MemStats:
    @dataclasses.dataclass
    class TypeStat:
        cpp_type: gdb.Type
        instances_number: int = 0
        additional_size: int = 0

        @property
        def total_size(self):
            return self.instances_number * self.cpp_type.sizeof + self.additional_size


    def __init__(self):
        self._name_to_type_stat: typing.Dict[int, MemStats.TypeStat] = dict()

    def _get_type_stat(self, cpp_type: gdb.Type) -> MemStats.TypeStat:
        type_name = cpp_type.name
        if type_name not in self._name_to_type_stat:
            self._name_to_type_stat[type_name] = MemStats.TypeStat(cpp_type)
        return self._name_to_type_stat[type_name]

    def update_with_value(self, value: gdb.Value):
        cpp_type = value.dynamic_type.unqualified()
        actual_type = cpp_type.strip_typedefs()
        if actual_type.code == gdb.TYPE_CODE_ARRAY:
            cpp_type = actual_type
        instance_number = 1
        while cpp_type.code == gdb.TYPE_CODE_ARRAY:
            assert cpp_type.sizeof % cpp_type.target().sizeof == 0
            instance_number *= cpp_type.sizeof // cpp_type.target().sizeof
            cpp_type = cpp_type.target()

        stat = self._get_type_stat(cpp_type)
        stat.instances_number += instance_number

    def manualy_account(self, cpp_type: gdb.Type, size: int):
        self._get_type_stat(cpp_type.unqualified()).additional_size += size

    @property
    def type_stats(self):
        for _, stat in self._name_to_type_stat.items():
            yield stat

    def __str__(self):
        stats = list(self.type_stats)
        stats.sort(key=lambda x: x.total_size, reverse=True)

        total_instaces = sum(map(lambda x: x.instances_number, stats))
        total_size = sum(map(lambda x: x.total_size, stats))

        # return tabulate.tabulate(
        #     itertools.chain(
        #         (("Total", total_instaces, total_size), ),
        #         map(
        #             lambda s: (
        #                 s.cpp_type.tag or s.cpp_type.name,
        #                 s.instances_number,
        #                 s.total_size
        #             ),
        #             stats,
        #         )
        #     )
        # )
        builder = [f"Total: {total_instaces} {total_size}"]
        for st in stats[:10]:
            builder.append(f"{st.cpp_type.tag or st.cpp_type.name}, {st.instances_number}, {st.total_size}")
        return '\n'.join(builder)


def update_mem_stats(stats: MemStats, heap_value: gdb.Value):
    stats.update_with_value(heap_value)


TraverserType = typing.Callable[[gdb.Value], typing.Iterable[gdb.Value]]


_base_type_rx = re.compile('^([a-zA-Z0-9_:]+)<.*>$')


def find_matching_function(
        cpp_type: gdb.Type,
        match_cache: typing.Dict[str, typing.Callable],
        register: typing.Dict[str, typing.Callable]
) -> typing.Optional[typing.Callable]:
    key = get_type_key(cpp_type)
    if key in match_cache:
        return match_cache[key]

    def get(cpp_type: gdb.Type):
        code = cpp_type.strip_typedefs().code
        if code in NON_TRAVERSIBLE_CODES:
            return None

        if cpp_type.tag in register:
            return register[cpp_type.tag]
        base_type_name = cpp_type.unqualified().strip_typedefs().tag
        if not base_type_name:
            return None
        if base_type_name in register:
            return register[base_type_name]
        match = _base_type_rx.match(base_type_name)
        if not match:
            return None
        base_type_name = match.group(1)
        if base_type_name in register:
            return register[base_type_name]
        return None

    traverser = get(cpp_type)
    match_cache[key] = traverser
    return traverser


def add_function(name: str, fn, registry: typing.Dict[str, typing.Callable]):
    if not _base_type_rx.match(name + '<>'):
        raise ValueError(
            'libstdc++ programming error: \'%s\' does not match' % name)
    assert name not in registry
    registry[name] = fn


_custom_traverset_match_cache:typing.Dict[str, TraverserType] = dict()
_custom_type_visitors: typing.Dict[str, TraverserType] = dict()


def find_matching_custom_traverser(cpp_type: gdb.Type) -> typing.Optional[TraverserType]:
    return find_matching_function(
        cpp_type,
        _custom_traverset_match_cache,
        _custom_type_visitors,
    )


def add_custom_traverser(name: str, traverser: TraverserType):
    add_function(name, traverser, _custom_type_visitors)


_custom_memory_accounter_match_cache: typing.Dict[str, SizeGetter] = dict()
_custom_type_accounters: typing.Dict[str, SizeGetter] = dict()


def find_matching_custom_accounter(cpp_type: gdb.Type) -> typing.Optional[SizeGetter]:
    return find_matching_function(
        cpp_type,
        _custom_memory_accounter_match_cache,
        _custom_type_accounters,
    )


def add_custom_accounter(name: str, traverser: SizeGetter):
    add_function(name, traverser, _custom_type_accounters)


def simple_type_name(t: gdb.Type) -> str:
    def get(t):
        if t.tag:
            return t.tag
        t = t.unqualified().strip_typedefs()
        if t.tag:
            return t.tag
        if t.name:
            return t.name
        return str(t)
    s = get(t)
    bracket = s.find('<')
    if bracket != -1:
        s = s[:bracket]
    for p in ('class ', 'struct '):
        if s.startswith(p):
            s = s[len(p):].strip()
            break
    return s


SizeGetter = typing.Callable[[gdb.Value], int]

SizeVisitor = typing.Callable[[gdb.Value, SizeGetter], None]


class VertixBase:
    @property
    def value(self) -> gdb.Value:
        not_implemented()

    def child(self, value: gdb.Value, label: str) -> VertixBase:
        not_implemented()

    @property
    def path(self) -> typing.List[str]:
        not_implemented()



@dataclasses.dataclass
class PathVertix:
    value: gdb.Value
    label: str
    parent: typing.Optional[PathVertix] = None

    def child(self, value: gdb.Type, label: str):
        return PathVertix(value, label, self)

    @property
    def path(self) -> typing.List[str]:
        it = self
        result = []
        while it is not None:
            result.append(it.label)
            it = it.parent
        result.reverse()
        return result


@dataclasses.dataclass
class SimpleVertix:
    value: gdb.Value

    def child(self, value: gdb.Type, _: str):
        return SimpleVertix(value)

    @property
    def path(self) -> typing.List[str]:
        return tuple()


@dataclasses.dataclass
class DfsCbValue:
    out_values: typing.Iterable[VertixBase]
    neighbours: typing.Iterable[VertixBase]

EMPTY_DFS_VALUE = DfsCbValue(
    tuple(),
    tuple(),
)


stats = MemStats()
latest_print = datetime.datetime.now()


def dfs(root, cb: typing.Callable[[VertixBase], DfsCbValue], out_cb) -> typing.Iterable[VertixBase]:
    stack = []

    def push_neigbours(neigbours, parent):
        stack.append((iter(neigbours), parent))

    push_neigbours((root,), None)

    while stack:
        '''

        TODO find out why with so much work stats don't move an inch

        '''


        it, parent = stack[-1]
        try:
            vertix = next(it)
        except StopIteration:
            if parent is not None:
                out_cb(parent)
            stack.pop()
            continue

        cb_result = cb(vertix)
        push_neigbours(cb_result.neighbours, vertix)
        yield from cb_result.out_values


def list_fields(t: gdb.Type) -> typing.Iterable[gdb.Field]:
    return filter(
        lambda f: not f.artificial and f.type.strip_typedefs().code not in NON_TRAVERSIBLE_CODES,
        t.fields(),
    )


ValueWithPath = typing.Tuple[gdb.Value, typing.Tuple[str, ...]]


def list_member_value(v: VertixBase, t: gdb.Type) -> typing.Iterable[ValueWithPath]:
    for field in list_fields(t):
        try:
            # this will raise AttributeError for static members
            field.bitpos
            yield v.child(v.value[field], field.name)
        except gdb.error:
            pass
        except AttributeError:
            pass


_type_owns_memory = dict()


def get_type_key(t: gdb.Type):
    unqualified = t.unqualified()
    simplified = unqualified.strip_typedefs()
    name = str(simplified)
    if '{...}' not in name:
        return name

    name = str(unqualified)
    if '{...}' in name and '*' not in name:
        return None
    return name


def type_owns_memory(t: gdb.Type) -> typing.Optional[bool]:
    key = get_type_key(t)
    if key is None:
        return True

    r = None
    if key not in _type_owns_memory:
        r = None
    else:
        r = _type_owns_memory[key]

    return r


def mark_type_owns_memory(t: gdb.Type, owns: bool):
    if owns is None:
        return
    assert type(owns) is bool, str(t)
    key = get_type_key(t)
    if key is None:
        return
    if key in _type_owns_memory:
        assert owns == _type_owns_memory[key], key
    else:
        _type_owns_memory[key] = owns


def get_array_target_type(t: gdb.Type) -> gdb.Type:
    return t.strip_typedefs().target()


FastTypeTraverser = typing.Callable[[VertixBase, SizeVisitor], typing.Iterable[VertixBase]]
EMPTY_TRAVERSER: FastTypeTraverser = lambda _1, _2: tuple()


_cached_fast_type_traversers: typing.Dict[str, FastTypeTraverser] = dict()


def get_fast_type_traverser(cpp_type: gdb.Type) -> FastTypeTraverser:
    key = get_type_key(cpp_type)
    traverser = None
    if key not in _cached_fast_type_traversers:
        traverser = make_fast_type_traverser(cpp_type)
        if key is not None:
            # can not cache traverser for type with no unique key
            _cached_fast_type_traversers[key] = traverser
    else:
        traverser = _cached_fast_type_traversers[key]
    return traverser


def set_fast_type_traverser(cpp_type: gdb.Type, traverser: FastTypeTraverser) -> None:
    key = get_type_key(cpp_type)
    if key is None:
        return
    assert key not in _cached_fast_type_traversers
    _cached_fast_type_traversers[key] = traverser


def get_type_traverser_fast(cpp_type: gdb.Type) -> typing.Optional[FastTypeTraverser]:
    key = get_type_key(cpp_type)
    if key is not None and key in _cached_fast_type_traversers:
        return _cached_fast_type_traversers[key]
    return None


def get_array_type_size(t: gdb.Type) -> int:
    base_type = get_array_target_type(t)
    assert base_type != t
    assert str(t) != str(base_type)
    assert t.sizeof % base_type.sizeof == 0
    return t.sizeof // base_type.sizeof


def raises(cb, Ex):
    try:
        cb()
        return False
    except Ex:
        return True


@dataclasses.dataclass
class FieldInfo:
    field: typing.Optional[gdb.Field] = None
    traverser: typing.Optional[FastTypeTraverser] = None


@dataclasses.dataclass
class TypeTraverseVertix:
    cpp_type: gdb.Type
    parent_field_info: FieldInfo
    field_infos: typing.Optional[typing.Tuple[FieldInfo]] = None


slow_cnt = 0


def make_fast_type_traverser(root_type: gdb.Type) -> FastTypeTraverser:
    cached_traverser = get_type_traverser_fast(root_type)
    if cached_traverser is not None:
        return cached_traverser

    # global slow_cnt
    # slow_cnt += 1
    # print('SLOW', slow_cnt)


    def cb(vertix: TypeTraverseVertix) -> typing.Iterable[DfsCbValue]:
        cpp_type = vertix.cpp_type

        if get_type_traverser_fast(cpp_type) is not None:
            return EMPTY_DFS_VALUE

        code = cpp_type.strip_typedefs().code
        if code in NON_TRAVERSIBLE_CODES:
            return EMPTY_DFS_VALUE

        if code == gdb.TYPE_CODE_ARRAY:
            target_type = get_array_target_type(cpp_type)
            field_info = FieldInfo()
            vertix.field_infos = (field_info,)
            return DfsCbValue(
                tuple(),
                (TypeTraverseVertix(target_type, field_info),)
            )

        if find_matching_custom_traverser(cpp_type) is not None or \
           find_matching_custom_accounter(cpp_type) is not None:
            return EMPTY_DFS_VALUE

        if code == gdb.TYPE_CODE_STRUCT:
            # TODO there was smth else to filter ???
            fields = filter(lambda f: not raises(lambda: f.bitpos, AttributeError), list_fields(cpp_type))

            def tr(f: gdb.Field) -> typing.Tuple[TypeTraverseVertix, FieldInfo]:
                field_info = FieldInfo(field=f)
                v = TypeTraverseVertix(f.type, field_info)
                return v, field_info

            neigbours_and_field_infos = tuple(map(tr, fields))

            neighbours = tuple(map(lambda x: x[0], neigbours_and_field_infos))
            field_infos = tuple(map(lambda x: x[1], neigbours_and_field_infos))

            vertix.field_infos = field_infos

            return DfsCbValue(
                tuple(),
                neighbours,
            )

        assert False, f"{get_type_code_name(code)} {cpp_type}"


    def cb_out(vertix: TypeTraverseVertix):
        def get_traverser() -> FastTypeTraverser:
            cpp_type = vertix.cpp_type

            cached_traverser = get_type_traverser_fast(cpp_type)
            if cached_traverser is not None:
                return cached_traverser

            def make_traverser() -> FastTypeTraverser:
                code = cpp_type.strip_typedefs().code
                if code in NON_TRAVERSIBLE_CODES:
                    return EMPTY_TRAVERSER

                if code == gdb.TYPE_CODE_ARRAY:
                    sub_traverser = vertix.field_infos[0].traverser
                    assert sub_traverser is not None
                    if sub_traverser is EMPTY_TRAVERSER:
                        return EMPTY_TRAVERSER
                    size = get_array_type_size(cpp_type)

                    def traverser(v: VertixBase, cb: SizeVisitor) -> typing.Iterable[VertixBase]:
                        for i in range(size):
                            yield from sub_traverser(v.child(v.value[i], '[]'), cb)

                    return traverser

                custom_traverser = find_matching_custom_traverser(cpp_type)
                custom_accounter = find_matching_custom_accounter(cpp_type)
                assert custom_accounter is None or custom_traverser is None, str(cpp_type)

                if custom_traverser is not None:
                    def traverser(v: VertixBase, _) -> typing.Iterable[VertixBase]:
                        return map(lambda x: v.child(x, '[]'), custom_traverser(v.value))
                    return traverser

                if custom_accounter is not None:
                    def traverser(v: VertixBase, cb: SizeVisitor) -> typing.Iterable[VertixBase]:
                        cb(v, custom_accounter)
                        return tuple()
                    return traverser

                if code == gdb.TYPE_CODE_STRUCT:
                    def not_empty_traverser(i: FieldInfo) -> bool:
                        assert i.traverser is not None
                        return i.traverser is not EMPTY_TRAVERSER


                    field_infos = tuple(filter(not_empty_traverser, vertix.field_infos))
                    if not field_infos:
                        return EMPTY_TRAVERSER
                    def traverser(v: VertixBase, cb: SizeVisitor) -> typing.Iterable[VertixBase]:
                        for f in field_infos:
                            yield from f.traverser(v.child(v.value[f.field], f.field.name), cb)
                    return traverser

                assert False, f"{get_type_code_name(code)} {cpp_type}"


            traverser = make_traverser()
            set_fast_type_traverser(cpp_type, traverser)
            return traverser


        vertix.parent_field_info.traverser = get_traverser()

    info = FieldInfo()
    for _ in dfs(TypeTraverseVertix(root_type, info), cb, cb_out):
        pass

    assert info.traverser is not None
    return info.traverser


def get_heap_owning_pointers(root_vertix: VertixBase, size_visitor: SizeVisitor) -> typing.Iterable[VertixBase]:
    fast_traverser = get_fast_type_traverser(root_vertix.value.type)
    return fast_traverser(root_vertix, size_visitor)


    def cb(vertix: VertixBase):
        v = vertix.value
        cpp_type = v.type

        owns = type_owns_memory(cpp_type)
        if owns is not None and not owns:
            return EMPTY_DFS_VALUE

        type_code = cpp_type.strip_typedefs().code

        custom_traverser = find_matching_custom_traverser(cpp_type)
        if custom_traverser is not None:
            mark_type_owns_memory(cpp_type, True)
            return DfsCbValue(
                map(lambda x: vertix.child(x, '[]'), custom_traverser(v)),
                tuple(),
            )
        elif type_code == gdb.TYPE_CODE_ARRAY:
            base_type = get_array_target_type(cpp_type)
            assert base_type != cpp_type
            assert str(base_type) != str(cpp_type)
            assert cpp_type.sizeof % base_type.sizeof == 0
            size = cpp_type.sizeof // base_type.sizeof


            owns_mem = type_owns_memory(base_type)
            if base_type.strip_typedefs().code in NON_TRAVERSIBLE_CODES \
                or (owns_mem is not None and not owns_mem):
                return EMPTY_DFS_VALUE
            return DfsCbValue(
                tuple(),
                map(lambda i: vertix.child(v[i], '[]'), range(size)),
            )
        elif type_code == gdb.TYPE_CODE_UNION:
            # TODO check if union contains memory owning members and warn parent type (if exists) should be
            pass
        elif type_code == gdb.TYPE_CODE_STRUCT:
            return DfsCbValue(
                tuple(),
                list_member_value(vertix, cpp_type)
            )

        mark_type_owns_memory(cpp_type, False)
        return EMPTY_DFS_VALUE


    def out_cb(vertix: VertixBase):
        v = vertix.value
        cpp_type = v.type.unqualified()
        if type_owns_memory(cpp_type) is not None:
            return
        type_code = cpp_type.strip_typedefs().code

        if type_code == gdb.TYPE_CODE_ARRAY:
            mark_type_owns_memory(
                cpp_type,
                type_owns_memory(get_array_target_type(cpp_type))
            )
        elif type_code == gdb.TYPE_CODE_STRUCT:
            mark_type_owns_memory(
                cpp_type,
                any(map(lambda f: type_owns_memory(f.type), list_fields(cpp_type))),
            )
        else:
            mark_type_owns_memory(cpp_type, False)


    return dfs(root_vertix, cb, out_cb)


@contextmanager
def defer_switch_thread_back():
    selected_thread = gdb.selected_thread()
    try:
        yield
    finally:
        selected_thread.switch()


def symbol_location_str(s: gdb.Symbol) -> str:
    return f"{s.symtab.fullname()}:{s.line}"


def get_mem_stats() -> MemStats:
    visited_addresses: typing.Set[int] = set()
    def is_not_visited(v: VertixBase) -> bool:
        address = int(v.value.address)
        return address not in visited_addresses

    def mark_visited(v: VertixBase):
        address = int(v.value.address)
        visited_addresses.add(address)

    def visit_custom_accounted_value(v: VertixBase, size_getter: SizeGetter):
        size = size_getter(v.value)
        assert size >= 0
        if size != 0:
            stats.manualy_account(v.value.type, size)


    pending_number = 0
    handled_number = 0


    def visit_heap_value(v: VertixBase):
        def cb(v: VertixBase) -> DfsCbValue:
            nonlocal pending_number
            nonlocal handled_number
            pending_number -= 1
            handled_number += 1

            if not is_not_visited(v):
                return EMPTY_DFS_VALUE
            mark_visited(v)

            update_mem_stats(stats, v.value)

            now = datetime.datetime.now()
            global latest_print
            if now - latest_print > datetime.timedelta(seconds=5):
                latest_print = now
                # TODO print rate as dx/dt
                print(now, pending_number, handled_number)
                print(stats)
                print('===================================')
                sys.stderr.flush()

            def count(neighbours):
                nonlocal pending_number
                if hasattr(neighbours, '__len__'):
                    pending_number += len(neighbours)
                    return neighbours
                else:
                    def count_single(x):
                        nonlocal pending_number
                        pending_number += 1
                        return x
                    return map(count_single, neighbours)

            return DfsCbValue(
                tuple(),
                count(get_heap_owning_pointers(v, visit_custom_accounted_value)),
            )

        for _ in dfs(v, cb, lambda _: None):
            pass


    for thread in gdb.selected_inferior().threads():
        for frame in get_stack_frames(thread):
            for variable in get_frame_variables(frame):
                base_vertix = PathVertix(variable.value(frame), f"{symbol_location_str(variable)} {variable.name}")
                for heap_value_vertix in get_heap_owning_pointers(base_vertix, visit_custom_accounted_value):
                    pending_number += 1
                    visit_heap_value(heap_value_vertix)

    return stats


def deref_to_dynamic_type(v: gdb.Value):
    return v.cast(v.dynamic_type).dereference()


def name_without_templates(name):
    assert name
    builder = []
    i = 0
    base = 0
    balance = 0
    while i < len(name):
        was_zero = balance == 0
        if name[i] == '<':
            balance += 1
        elif name[i] == '>':
            balance -= 1
        is_zero = balance == 0
        if was_zero != is_zero:
            if balance != 0:
                builder.append(name[base:i])
            else:
                base = i + 1
        i += 1
    assert balance == 0
    if base < i:
        builder.append(name[base:i])

    return ''.join(builder)



class TraverseMemoryCmd(gdb.Command):
    """TODO"""

    def __init__(self):
        super(TraverseMemoryCmd, self).__init__(
            "traverse_mem_pointer", gdb.COMMAND_USER
        )

    def complete(self, text, word):
        # We expect the argument passed to be a symbol so fallback to the
        # internal tab-completion handler for symbols
        return gdb.COMPLETE_SYMBOL

    def invoke(self, args, from_tty):
        # print(sys.executable)
        # for i in tqdm(range(10)):
        #     sleep(3)


        # start = datetime.datetime.now()
        # stats = get_mem_stats()
        # for k, v in _cached_fast_type_traversers.items():
        #     assert v is not None
        #     print(v is EMPTY_TRAVERSER, k)

        # ts = list(set(map(name_without_templates, _type_owns_memory)))
        # ts.sort()
        # for i in ts:
        #     print(i)

        # print(f"{datetime.datetime.now() - start} elapsed")
        # print('--------------------')
        # if not DBG:
        #     print(stats)


        # print(get_mem_stats())
        cProfile.run('print(get_mem_stats())', sort='tottime')


TraverseMemoryCmd()
