# GDB Memprof

## Overview

Welcome to the GDB Memprof repository! This tool is designed to help you analyze memory usage in C++ programs. Unlike traditional memory profiling tools that use tracing to collect allocations and deallocations in runtime, this profiler is tailored for analyzing memory usage in correctly written C++ programs by inspecting memory snapshots. It has a meaningful purpose for programs that extensively use smart pointers for managing heap memory. The core of the tool is built around GDB Python API.

## Table of Contents

- [Overview](#overview)
- [Usage](#usage)
- [Features](#features)
- [What This Profiler Does Not Do](#what-gdb-memprof-does-not-do)
- [Technical Requirements](#technical-requirements)
- [Contributing](#contributing)

## Usage

Once you have installed the GDB Memprof, you can start using it to analyze memory usage in your C++ programs.

**TODO**

## Features

- **Memory Usage Analysis**: This profiler allows you to analyze memory usage patterns in C++ programs by inspecting memory snapshots.
- **Pause and Profile**: You can profile processes in a paused state without running them, making it suitable for analyzing memory usage without affecting program performance.
- **Core Dump Analysis**: It can also profile core dumps, enabling you to analyze memory usage even when a program has crashed.
- **Open Source**: The GDB Memprof is open-source, and contributions are welcome.

## What GDB Memprof Does Not Do

While the GDB Memprof is a valuable tool for analyzing memory usage, it's essential to understand its limitations:

- **(Kind of) No Memory Leak Detection**: This profiler is not intended for detecting memory leaks in your C++ programs. It can find memory that was not freed but is still held by smart pointers but lost raw pointers to allocated memory of lost cyclic shared pointers can not be detected.

- **Limited to Correctly Written Programs**: The profiler assumes that your C++ program is correctly written and does not have issues such as losing pointers or cyclic shared pointers. It may not provide meaningful results for programs with memory-related defects.

## Technical Requirements

Before using this GDB Memprof, please ensure that your program meets the following technical requirements:

1. **C++ Language**: Your program must be written in the C++ programming language.

2. **Debug Symbols**: Debug symbols are needed to be loaded in order to inspect memory.

3. **Program Correctness**: This profiler is designed for analyzing memory usage in correctly written C++ programs. Specifically, it is required that any allocated memory is reachable if traversed from pointers on thread stacks, and there are no issues such as losing pointers or cyclic shared pointers.

4. **Extensive Smart Pointer Usage**: The profiler is optimized for programs that use smart pointers (e.g., `std::shared_ptr`, `std::unique_ptr`) to manage heap memory. Its analysis may not be as effective for programs using other memory management techniques.

5. **Library Adaptors**: This tool requires adaptors for library types that are responsible for memory management. For example, `std::vector<int>` instances hold memory and are responsible for freeing it on destruction. GDB Memprof comes with partial coverage of types from STL (a certain version of it). If your program depends on other libraries like `boost` or `folly` they require writing adaptors too. The lack of such adaptors does not make use of GDB Memprof impossible but makes the results less meaningful because it limits how deep can the tool analyze data.

6. **GDB**: You need GDB (GNU Debugger) to run the profiler.

## Contributing

I WILL welcome contributions to the GDB Memprof project as soon as there is an MVP. Stay tuned.
