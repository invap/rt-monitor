# The Runtime Monitor
This project contains an implementation of the  Runtime Monitor (RM) of the RT-Constellation. The rationale behind this tool is that it enables runtime verification capabilities provided it is given:
1. an *analysis framework specification* (see Section [Specification language for describing the analysis framework](#specification-language-for-describing-the-analysis-framework) for a complete description of the specification language and the file format), and
2. a *stream of events* obtained through the RabbitMQ events exchange found in the RabbitMQ server configuration file. 

The reader is pointed to Section [Event language for monitoring](#event-language-for-monitoring) for a complete description of the event language and also consider reading:
 
- Section [Relevant information about the implementation](https://github.com/invap/rt-reporter/blob/main/README.md#relevant-information-about-the-implementation) of [The Runtime Reporter](https://github.com/invap/rt-reporter/) project (an example runtime reporter (RR) that produces event log files that can be processed by the RM), and 
- Section [Implementation of the C reporter API](https://github.com/invap/c-reporter-api/blob/main/README.md#implementation-of-the-reporter-api) of the [C reporter API](https://github.com/invap/c-reporter-api/) project (a library that can be used to produce an instrumented version of the source code of the SUT, which can later be processed by an event reporter). Alternatively, Section [Implementation of the Rust reporter API](https://github.com/clpombo/rust-reporter-api/blob/master/README.md#implementation-of-the-reporter-api) of the [Rust reporter API](https://github.com/clpombo/rust-reporter-api/)

The analysis process consists of checking if the stream of event obtained through the RabbitMQ events exchange[^reporters]
[^reporters]: Such a stream of events can  be produced by a specialized event reporter (for example, like the [Runtime Reporter](https://github.com/invap/rt-reporter "The Runtime Reporter") or the [DAP-supported Runtime Reporter](https://github.com/invap/dap-rt-reporter "The DAP-supported Runtime Reporter")).
, satisfies the desired properties formalized in the analysis framework specification. If it does, the verification is considered to be *SUCCESSFUL*, and if it does not, is considered to be *UNSUCCESSFUL* exposing an execution trace of the SUT that does not behave as prescribed by the specification.


## Structure the project
The RM project is organized as follows:
```graphql
rt-monitor/
├── rt_monitor                    # Package folder
│   ├── errors                    # Folder containing the implementation of the runtime exceptions
│   ├── framework
│   │   ├── components
│   │   │   ├── ...               # Folders hosting the python components used by the SUT
│   │   │   └── component.py      # Implements the interface of the python components used by the SUT
│   │   ├── process               # Contains the python files implementing structured sequential processes
│   │   ├── clock.py              # Implementation of the notion of clock used for checking timed properties
│   │   └── framework.py          # Implementation of the analysis framework
│   ├── property_evaluator        # Folder containing the implementation of the property evaluators
│   ├── reporting                 # Folder containing the implementation of event decoder and the event types
│   ├── logging_configuration.py  # Implementation of the structure for configuring the logger
│   ├── monitor.py                # Implementation of the analysis framework
│   ├── monitor_builder.py
│   ├── novalue.py
│   └── rt_monitor_sh.py          # Entry point of the command line interface of the RR
├── README_images                 # Images for the read me file
│   └── ...                       # ...
├── COPYING                       # Licence of the project 
├── Dockerfile                    # File containing the configuration for running the RM in a docker container 
├── pyproject.toml                # Configuration file (optional, recommended)
└── README.md                     # Read me file of the project
```


## Installation
In this section we will review relevant aspects of how to setup this project, both for developing new features for the RM, and for using it in the runtime verification of other software artifacts.

### Base Python installation

1. Python v.3.12+ (https://www.python.org/)
2. PIP v.24.3.1+ (https://pip.pypa.io/en/stable/installation/)
3. Setup tools v.75.3.0+ / Poetry v.2.1.1+ (https://python-poetry.org)


### Setting up the project
This section provide instructions for setting up the project using [Poetry](https://python-poetry.org)
1. **Install Poetry:** find instructions for your system [here](https://python-poetry.org) 
2. **Add [`pyproject.toml`](https://github.com/invap/rt-monitor/blob/main/pyproject.toml):** the content of the `pyproject.toml` file needed for setting up the project using poetry is shown below.
```toml
[project]
name = "rt-monitor"
version = "2.8.1"
description = "This project contains an implementation of the Runtime Monitor (RM) of the RT-Constellation. The rationale behind this tool is that it enables runtime verification capabilities provided it is given: 1. an *analysis framework specification* (see Section [Specification language for describing the analysis framework](#specification-language-for-describing-the-analysis-framework) for a complete description of the specification language and the file format), and 2. a *stream of events* obtained; through the RabbitMQ events exchange found in the RabbitMQ server configuration file. The reader is pointed to Section [Event language for monitoring](#event-language-for-monitoring) for a complete description of the event language and also consider reading: - Section [Relevant information about the implementation](https://github.com/invap/rt-reporter/blob/main/README.md#relevant-information-about-the-implementation) of [The Runtime Reporter](https://github.com/invap/rt-reporter/) project (an example runtime reporter (RR) that produces event log files that can be processed by the RM), and - Section [Implementation of the C reporter API](https://github.com/invap/c-reporter-api/blob/main/README.md#implementation-of-the-reporter-api) of the [C reporter API](https://github.com/invap/c-reporter-api/) project (a library that can be used to produce an instrumented version of the source code of the software under test (SUT), which can later be processed by the RR for producing an event log file). Alternatively, Section [Implementation of the Rust reporter API](https://github.com/clpombo/rust-reporter-api/blob/master/README.md#implementation-of-the-reporter-api) of the [Rust reporter API](https://github.com/clpombo/rust-reporter-api/). The analysis process consists of checking if the stream of event obtained through the RabbitMQ events exchange satisfies the desired properties formalized in the analysis framework specification. If it does, the verification is considered to be *SUCCESSFUL*, and if it does not, is considered to be *UNSUCCESSFUL* exposing an execution trace of the SUT that does not behave as prescribed by the specification."
authors = [
    {name = "Carlos Gustavo Lopez Pombo", email = "clpombo@gmail.com>"}
]
readme = "README.md"
license = "GNU AFFERO GENERAL PUBLIC LICENSE Version 3, 19 November 2007"
repository = "https://github.com/invap/rt-monitor"


requires-python = ">=3.12,<3.14"
packages = [
    { include = "rt_monitor" },
]
dependencies = [
    "numpy (~=2.1.2)",
    "pyformlang~=1.0.11",
    "pyobjc-core (>=10.3.1,<10.4.0); sys_platform == 'darwin'",
    "pyobjc-framework-applicationservices (>=10.3.1,<10.4.0); sys_platform == 'darwin'",
    "pyobjc-framework-cocoa (>=10.3.1,<10.4.0); sys_platform == 'darwin'",
    "pyobjc-framework-coretext (>=10.3.1,<10.4.0); sys_platform == 'darwin'",
    "pyobjc-framework-quartz (>=10.3.1,<10.4.0); sys_platform == 'darwin'",
    "pika (>=1.3.2)",
    "rt-rabbitmq-wrapper @ git+https://github.com/invap/rt-rabbitmq-wrapper.git@v2.0.1",
    "sympy (~=1.13.3)",
    "toml (~=0.10.2)",
    "wxpython (>=4.2.2,<4.3.0); sys_platform == 'darwin'",
    "wxpython @ https://extras.wxpython.org/wxPython4/extras/linux/gtk3/ubuntu-24.04/wxPython-4.2.2-cp312-cp312-linux_x86_64.whl ; sys_platform == 'linux'",
    "z3-solver (~=4.13.0.0)"
]

[build-system]
requires = ["poetry-core"]
build-backend = "poetry.core.masonry.api"

[dependency-groups]
dev = [
    "pytomlcleaner (>=1.0.0,<2.0.0)"
]
```
3. **Install the project:** To install the Python project using Poetry, navigate to the directory where the project is and run:
   ```bash	
   poetry install
   ```
3. **Activate the virtual environment**: To activate the virtual environment created by the previous command run:
   ```bash
   poetry env use [your_python_command]
   poetry env activate
   ```
this will ensure you are using the right Python virtual machine and then, activate the virtual environment.


### Using the project with docker
1. **Build the image:**
    ```bash
    docker build . -t rt-reporter-env
    ```
2. **Run the container:**
	```bash
	docker run -it -v$PWD:/home/workspace rt-reporter-env
	```
3. **Do something with RM...**


### Linting Python code (with Black)
A linter in Python is a tool that analyzes your code for potential errors, code quality issues, and stylistic inconsistencies. Linters help enforce a consistent code style and identify common programming mistakes, which can improve the readability and maintainability of your code. They’re especially useful in team environments to maintain coding standards.

Though primarily an auto-formatter, `Black` enforces a consistent code style and handles many linting issues by reformatting your code directly.

1. **Activate the virtual environment in your project directory:**
2. **Run linter (black):**
	- For correcting the code:
	```bash
	black .
	```
	- For checking but not correcting the code:
	```bash
	black . --check
	```

### Perform regression testing
Tu run the unit tests of the project use the command `python -m unittest discover -s . -t .`.

When executed, it performs Python unit tests with the `unittest` module, utilizing the `discover` feature to automatically find and execute test files.
- `python -m unittest`:
Runs the `unittest` module as a script. This is a built-in Python module used for testing. When called with `-m`, it allows you to execute tests directly from the command line.
- `discover`:
Tells `unittest` to search for test files automatically. This is useful when you have many test files, as it eliminates the need to specify each test file manually. By default, `unittest` discover will look for files that start with "test" (e.g., `test_example.py`).
- `-s .`:
The `-s` option specifies the start directory for test discovery.
Here, `.` means the current directory, so `unittest` will start looking for tests in the current directory and its subdirectories.
- `-t .`:
The `-t` option sets the top-level directory of the project.
Here, `.` also indicates the current directory. This is mainly useful when the start directory (`-s`) is different from the project's root. For simple projects, the start directory and top-level directory are often the same.

**In summary, this command tells Python’s `unittest` module to:**
Look in the current directory (`-s .`) for any test files that match the naming pattern `test*.py`.
Run all the tests it finds, starting from the current directory (`-t .`) and treating it as the top-level directory.

### Build the application as a library
To build a package from the Python project follow these steps:
Now that your configuration files are set, you can build the package using poetry running the build command in the root directory of the project:
```bash
poetry build
```
This will create two files in the [dist](https://github.com/invap/rt-monitor/tree/main/dist/) directory containing:
- A source distribution file named `rt_monitor-[version].tar.gz`
- A wheel distribution file named `rt_monitor-[version]-py3-none-any.whl`


### Distribution Options

#### Option A: PyPI (Public)

1. Configure PyPI repository (if not using TestPyPI):
```bash
poetry config pypi-token.pypi your-api-token
```
2. Publish to PyPI:
```bash
poetry publish
```

#### Option B: Test PyPI

```bash
# Configure TestPyPI
poetry config repositories.testpypi https://test.pypi.org/legacy/

# Publish to TestPyPI
poetry publish -r testpypi --build
```

#### Option C: Private/Internal Distribution

Configure private repository:
```bash
poetry config repositories.my-private https://your-private-pypi.com/simple/
poetry config http-basic.my-private username password
```
Publish to private repo:
```bash
poetry publish -r my-private --build
```

#### Option D: Direct Distribution

Share the wheel file directly:

```bash
# The wheel file is in dist/
ls dist/
# Share rt_monitor-[version]-py3-none-any.whl
```

### Version Management

Update version before building:

```bash
# Patch release (0.1.0 -> 0.1.1)
poetry version patch

# Minor release (0.1.0 -> 0.2.0)
poetry version minor

# Major release (0.1.0 -> 1.0.0)
poetry version major

# Specific version
poetry version 1.2.3
```

### Verification

Verify your package:

```bash
# Check the wheel contents
poetry run python -c "import rt_monitor; print(rt_monitor.__version__)"

# Or install and test
pip install dist/rt_monitor-*.whl
python -c "import rt_monitor"
```


## Relevant information about the implementation

### The Runtime Monitor architecture
[Figure 1](#rt-monitor-architecture) shows a high level view of the architecture of the RM. In it, we highlight the most relevant components and how they interact with each other and with the other agents of the RT-Constellation, through the RabbitMQ events and results-log exchanges found in the RabbitMQ server configuration file.

<figure id="rt-monitor-architecture" style="text-align: center;">
  <img src="./README_images/rt-monitor-architecture.pdf" width="600" alt="The Runtime Monitor architecture.">
  <figcaption style="font-style: italic;"><b>Figure 1</b>: The Runtime Monitor architecture.
  </figcaption>
</figure>

As we mentioned in the introduction, the RM requires two inputs: 
1. a *stream of events* obtained through the RabbitMQ events exchange found in the RabbitMQ server configuration file, obtained from a concrete execution of the SUT by an event reporter (for example, like the [Runtime Reporter](https://github.com/invap/rt-reporter "The Runtime Reporter") or the [DAP-supported Runtime Reporter](https://github.com/invap/dap-rt-reporter "The DAP-supported Runtime Reporter")), and 
2. an *analysis framework* consisting of: 
	1. a formalization of the Structured Sequential Process (SSP) (see Section [Syntax for writing SSPs](#syntax-for-writing-ssps) for details about the language for describing SPPs and the input file format), and
	2. a set of implementations of digital twins for the components used by the SUT (see Section [Implementation of digital twins for monitoring software components](#implementation-of-digital-twins-for-monitoring-software-components) for understanding the importance of digital twins in the verification of executions). 

Given that input, the `Analyzer` uses de `Event processor` to crawl the stream of events, decode them, and then execute them, producing: 

1. changes in the *execution state*, in the case of *state events*,
2. changes in the *process state*, expressing the traversing of the SSP, or
3. the execution of a function associated to a specific component through the `Components' command dispatcher` which, in turn, will produce the corresponding changes in the *Component state*.

Processing events associated with the traversing of the SSP triggers the analysis of properties associated to specific points in the SSP. In this way, an event of type `task_started` will result in checking that the preconditions of the task mentioned in the event are true in the current state, analogously, an event of type `task_finished` will result in checking that the postconditions of the task are true, finally, an event of type `checkpoint_reached` will result in checking that the properties associated to that point in the SSP are true.

Each property is declared to be of a certain type which requires a purpose specific `Specification builder` and `Evaluator`, built on top of specific solvers; for example, [The Z3 Theorem prover](https://www.microsoft.com/en-us/research/project/z3-3/) for SMT2 properties, [SymPy](https://www.sympy.org/en/index.html) for properties that require the use of a Computer Algebra System (CAS), or a Python program to solve simple arithmetic.


### Event language for monitoring
The SUT is assumed to be instrumented for ouputing a stream of predefined event types. Event types are defined as part of the reporting API; for example, in the case of the [C reporter API](https://github.com/invap/c-reporter-api/), the definition can be found in [Line 16](https://github.com/invap/c-reporter-api/blob/main/include/data_channel_defs.h#L16 "Event types") of file [`data_channel_defs.h`](https://github.com/invap/c-reporter-api/blob/main/include/data_channel_defs.h) as a C enumerated type:
```c
//classification of the different types of events
typedef enum {
	timed_event, 
	state_event, 
	process_event, 
	component_event, 
	end_of_report_event
} eventType;
```


Each event arrives packed through the RabbitMQ events exchange (see code fragment from [Line 147](https://github.com/invap/rt-monitor/blob/main/rt_monitor/monitor.py#L147) to [Line 152](https://github.com/invap/rt-monitor/blob/main/rt_monitor/monitor.py#L152) of file [`monitor.py`](https://github.com/invap/rt-monitor/blob/main/rt_monitor/monitor.py).
Whenever an event is received by the monitor (see code fragment from [Line 153](https://github.com/invap/rt-monitor/blob/main/rt_monitor/monitor.py#L153) to [Line 192](https://github.com/invap/rt-monitor/blob/main/rt_monitor/monitor.py#L192) of file [`monitor.py`](https://github.com/invap/rt-monitor/blob/main/rt_monitor/monitor.py), it is processed according to the event type:
- `timed_event`: the event is expected to have the format `[timestamp],timed_event,[event]` in the file corresponding to the main event report file. `[event]` provide details of the timed event reported and has the shape `[clock action],[clock variable]`, where `[clock action]` is in the set {`clock_start`, `clock_pause`, `clock_resume`, `clock_reset`} and `[clock variable]` is the name of a free clock variable occurring in any property of the SSP (see Section [Syntax for writing properties](#syntax-for-writing-properties "Syntax for writing properties") for details on the language for writing properties of structured sequential processes),
- `state_event`: the event is expected to have the format `[timestamp],state_event,[event]` in the file corresponding to the main event report file. `[event]` provide details of the state event reported and has the shape `variable_value_assigned,[variable name],[value]` where `[variable name]` is the name of a free state variable occurring in any property of the structured sequential process (see Section [Syntax for writing properties](#syntax-for-writing-properties "Syntax for writing properties") for details on the language for writing properties of structured sequential processes),
- `process_event`: the event is expected to have the format `[timestamp],process_event,[event]` in the file corresponding to the main event report file. `[event]` provide details of the process event reported and has the shape `task_started,[name]`, `task_finished,[name]` or `checkpoint_reached,[name]`, where `[name]` is a unique identifier corresponding to a task o checkpoint, respectively, in the structured sequential process (see Section [Specification language for describing the analysis framework](#specification-language-for-describing-the-analysis-framework "Specification language for describing the analysis framework") for details on the language for specifying the analysis framework),
- `component_event`: the event is expected to have the format `[timestamp],component_event,[event]` in the file corresponding to the main event report file. `[event]` provide details of the component event reported and has the shape `[component name],[function name],[parameter list]`, where `[component name]` is a unique identifier corresponding to a component declared in the specification of the analysis framework (see Section [Specification language for describing the analysis framework](#specification-language-for-describing-the-analysis-framework "Specification language for describing the analysis framework") for details on the language for specifying the analysis framework), `[function name]` is the name of a function implemented by the component, `[parameter list]` is the list of parameters required by the function `[function name]`, separated by commas.

### Specification language for describing the analysis framework
An *Analysis framework specification* is described in [TOML format](https://toml.io/) and, as we mentioned before, consists of: 
1. a formalization of the Structured Sequential Process (SSP) (see Section [Syntax for writing SSPs](#syntax-for-writing-ssps) for details about the language for describing SPPs and the input file format), and
2. a set of implementations of digital twins for the components used by the SUT (see Section [Implementation of digital twins for monitoring software components](#implementation-of-digital-twins-for-monitoring-software-components) for understanding the importance of digital twins in the verification of executions). 

This information is arranged in many files. The main file consists of two top-level tables, one for describing the SSP, under the keyword process, and the other for describing the digital twins for mimicking the SUT’s Components that will be monitored resorting to a black box strategy, under the keyword components.

#### Syntax for writing SSPs
The table `process` is mandatory and contains the following key/value pairs describing the SSP:

- [**mandatory**] `format`: whose associated value is a string, determining the format in which the process is presented (`regex` / `graph`), and
- [**mandatory**] `structure`: whose associated value is determined by the value associated to the key format:
	- if format is `regex`, the associated value is a string defining the process as a regular expression according to the following grammar:
		```regex
		regex ::= string | regex + regex | regex ; regex | regex*
		```
		, where the strings are the names of the tasks and checkpoints that are
part of the process
	- if format is `graph`, the associated value is a table with three key/value pairs defining a graph:
		- nodes: an array of string (i.e., the list of names of the tasks and the checkpoints that are part of the process),
		- edges: an array of 2-elements array of string (i.e., the arcs determining precedence between the tasks and the checkpoints that form the process), and
		- init: a string declaring the initial node (i.e., the first task to initiate or checkpoint to be checked).
- [**optional**] `tasks`: is an array of tables, one for each task that is part of the process.
- [**optional**] `checkpoints`: is an array of tables, one for each checkpoint that is part of the process, without distinction whether they are local or global.
- [**optional**] properties: is an array of tables, one for each property appearing in any task of checkpoint that is part of the process.

	A `task` is a table that contains the following key/value pairs:
	- [**mandatory**] `name`: whose associated value is a string used as a unique identifier across all the objects (i.e., tasks, checkpoints, and properties) appearing in the process,
	- [**optional**] `preconditions`: whose associated value is an array of string (i.e., the list of the names of the properties that have to be checked when the execution of the SUT reports an event task started, for this task name; when this key is not present or when it is present but with an empty array (i.e., "[]"), it is treated as the equivalent to the value true,
	- [**optional**] `postconditions`: whose associated value is an array of string (i.e., the list of the names of the properties that have to be checked when the execution of the SUT reports an event task finished, for this task name; when this key is not present or when it is present but with an empty array (i.e., "[]"), it is treated as the equivalent to the value true, and
	- [**optional**] `checkpoints`: whose associated value is an array of string (i.e., the list of the names of the checkpoints that are processed when the execution of the SUT reports an event checkpoint reached.

	A `checkpoint` is a table that contains the following key/value pairs:
	- [**mandatory**] `name`: whose associated value is a string used as a unique iden- tifier across all the objects (i.e., tasks, checkpoints, and properties) appearing in the process,
	- [**optional**] `properties`: whose associated value is an array of string (i.e., the list of names of the properties that have to be checked when an event checkpoint reached for this checkpoint name is reported by the execution of the SUT; when this key is not present or when it is present but with an empty array (i.e., "[]"), it is treated as the equivalent to the value true.

#### Syntax for writing properties
A `property` is a table that either be defined in-lined within the main file or in a separate file. 

When it is defined within the main file, it contains the following key/value pairs:
- [**mandatory**] `name`: whose associated value is a string used as a unique identifier across all the objects (i.e., tasks, checkpoints, and properties) appearing in the process,
- [**mandatory**] `format`: whose associated value is a string declaring the format in which the formula is written; the available formats are {`smt2`, `py`, `sympy`}. `py` and `sympy` formulae are Python boolean expressions that are assigned to the variable `result` and then executed using the instruction `exec`; after the execution, the projection of the value referenced by the variable location `result` is treated as the verdict of the analysis,
- [**mandatory**] `variables`: whose associated value is a string containing variable declarations separated by commas, that have to coincide with those variable symbols that appear free in the formula. Each declaration has the shape `([variable symbol]:[variable type] [stm2 type])`, where:
	- `[variable symbol]` is the string used as a term in the formula,
	- `[variable type]` is either `State`, `Component` or `Clock`, depending on whether the variable symbol refers to a value that comes from a `variable_value_assign` event reported by the execution of the SUT, or if it refers to values that are part of the internal state of one of the SUT’s Components, and
	- `[stm2 type]` is the variable sort in [SMT-Lib format](https://smt-lib.org);
- [**mandatory**] `formula`: whose associated value is a string containing the formula in the format declared in the value associated to the key format. If the format is `smt2` the string must be a well-formed formula written according to the syntax given in [[SMT-Lib format](https://smt-lib.org), Part 2]. If the format is `py` (resp. `sympy`) the string must be a legal expression executable in the Python virtual environment resulting from the [Runtime Monitor installation](#setting-up-the-project), and
- [**optional**] `declarations`: whose associated value is a string containing declarations required by the tool used for the analysis of the formula in order to evaluate the satisfiability of the formula. As in the previous case, if the format is `smt2` the string must formed by legal definitions written according to the syntax given in [[SMT-Lib format](https://smt-lib.org), Part 2], and if the format is `py` (resp. `sympy`) the string must formed by legal definitions executable in the Python virtual environment resulting from the Runtime Monitor installation

When it is defined in a separate file, it contains the following key/value pairs:
- [**mandatory**] `name`: whose associated value is a string used as a unique identifier across all the objects (i.e., tasks, checkpoints, and properties) appearing in the process, and
- [**mandatory**] `file`: whose associated value is a string declaring the file location that can be treated either as an absolute path if it starts with "\", or as a relative path if it starts with a ".".

The structure of the file defining the property is also given in [TOML format](https://toml.io/) and it contains the key/value pairs whose key are `format`, `variables` and `formula`, analogous to those used when the property is defined within the main file.

#### Syntax for declaring components
The top-level table `component` is optional because the analysis framework might not depend on any; this table contains one key/value pair whose key is location and whose value is a string describing the path to the files containing the [implementation of the digital twins](#implementation-of-digital-twins-for-monitoring-software-components) used by the Runtime Monitor for mimicking the behaviour of the SUT’s Components, and an array of table containing the details of each of the digital twins. Each digital twin appears under a keyword `components.list` containing the following key/value pairs:
- [**mandatory**] `name`: whose associated value is a string containing the name of the digital twin under which the events of type component event are reported,
- [**optional**] `component path`: whose associated value is a string describing the path to the file containing the implementation of this digital twin. This key/value pair, when present, overrides the key/value pair location mentioned above,
- [**mandatory**] `component file`: whose associated value is a string describing the name of the Python file implementing the digital twin, and
- [**mandatory**] `component name`: whose associated value is a string describing the name of the class implementing the digital twin.

#### Implementation of digital twins for monitoring software components
Digital twins play a fundamental role in the implementation of the RM as they provide the means to mimic the behaviour of Components that, while being an integral part of the SUT, are not monitored through time, process, state events, but through component events.

Digital twins are implementations of the abstract Python class [Component](https://github.com/invap/rt-monitor/blob/main/rt_monitor/framework/components/component.py) shown below.

```python
# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import inspect
from abc import ABC, abstractmethod
import logging
# Create a logger for the component component
logger = logging.getLogger(__name__)

from rt_monitor.errors.component_errors import FunctionNotImplementedError


class Component(ABC):
    exported_functions = {}

    def __init__(self):
        pass

    @abstractmethod
    def state(self):
        pass

    def get_status(self):
        raise NotImplementedError

    def process_high_level_call(self, string_call):
        ls = string_call.split(",")
        function_name = ls[0]

        if function_name not in self.exported_functions:
            logger.error(f"Function [ {function_name} ] not implemented by component [ {self.__class__.__name__} ].")
            raise FunctionNotImplementedError(function_name)

        function = self.exported_functions[function_name]
        args_str = ls[1:]
        self.run_with_args(function, args_str)
        return True

    def run_with_args(self, function, args):
        signature = inspect.signature(function)
        parameters = signature.parameters
        new_args = [self]
        for name, param in parameters.items():
            exp_type = param.annotation
            if exp_type is not inspect.Parameter.empty:
                if not args:
                    break  # No more args to process
                try:
                    value = args[0]
                    args = args[1:]
                    value = exp_type(value)
                    new_args.append(value)
                except (TypeError, ValueError) as e:
                    logger.error(f"Error converting arg '{name}' to {exp_type.__name__}: {e}")
                    raise
        return function(*new_args)
```
The implementation of the base class Component provide the basic means needed for a digital twin to execute its functionality within the Runtime Monitor whenever a component event is reveived. The class provides an implementation of a dynamic dispatcher for the functions whose invocation can be reported, the function process high level call.

Whenever a component event `timestamp,component_event,component_name,function_name,arg1,arg2, . . ., argn` is received by the Runtime Monitor through the Event exchange, it is processed by:
1. stripping the name of the component component name from the string (it has to coincide with the value associated to the key/value pair name of one of the digital twins declared as part of the analysis framework specification under the keyword `component.list`) and obtaining the component instance from the dictionary of digital twins,
2. calling the function `process_high_level_call` (see line 27 of the code shown above), passing the string `function_name,arg1,arg2, . . ., argn` as the argument,
3. splitting the function invocation in two strings, function name (`function_name`), and function arguments (`arg1,arg2, . . ., argn`),
4. extracting from the dictionary exported functions of the component class (see line 35 of the code shown above) the name of the function implementation associated to function name, and
5. calling the function `run_with_args` (see line 40 of the code shown above) passing the function (associated to the string `function_name`) as the first parameter and the string of arguments `arg1,arg2, ..., argn` as the second parameter. This function will interpret the comma-separated string (of arguments) and construct a list of values of the types corresponding to the function signature and finally it calls the function passing the list of values as parameter.

Implementing a digital twin requires the provision of a function `state` (see lines 20 to 22 of the code shown above). This function provide the means for projecting the observable attributes of the digital twin that can be used as variables of type `Component` in the specification of properties. A dictionary of `exported_functions` whose keys are the strings used to report function calls, and values are the function symbols used as reference for the implementation of the functionalities. Finally, the implementation might incorporate a function `status` (see lines 24 to 25 of the code shown above). This function provide the means to extract execution infor- mation of the digital twin that complements the result of the function state.

#### Summary
From a methodological point of view, once one have identified the need to predicate about certain attributes of interest of a component (i.e., variables declared as of type `Component` in properties of the analysis framework specification), implementing a digital twin requires:
1. selecting an internal structure for the digital twin, capable of representing the aspects of the component behaviour, that has impact on the attribute of interest,
2. implementing the function `state` that returns a dictionary that associates the names of these variables of type `Component` to values projected from the internal structure of the digital twin,
3. identifying functions of the component whose calls that have to be reported at runtime and selecting function names (strings) to report them; these strings will usually coincide with the components’ functions’ names,
4. implementing a function in the digital twin that have to be dispatched for each function name that can be reported, the execution of these functions have to modify the internal structure of the digital twin according to the expected behaviour such that observations through the function `state` coincide with the expected behaviour of the component,
5. build the `exported_functions` dictionary associating the function names (strings that can be reported through component events), with the functions implemented in the digital twin, and
6. identifying additional information of the execution of the digital twin that might be of use for other digital twins or visual components and implement the function status.


### The runtime monitoring process
The RM implements the analysis process. It starts by constructing:
1. a DFA of events corresponding to the SSP, and setting the current state to the initial state of the DFA,
2. a dictionary whose keys are the variable symbols occurring free in the properties declared in the SSP, and
3. a dictionary containing digital twins of the internal components of the SUT (the reader is referred to the section [implementation of the digital twins](#implementation-of-digital-twins-for-monitoring-software-components) for details of how these digital twins can be emplemented).

Thereafter, it proceeds to process the event stream by:
1. reading an event from the Event exchange,
2. decoding the event classifying it into one of the admisible types,
3. processing the event according to its type:
	- **State event**: updates the execution state by associating the value to the variable symbol, both reported in the event; naturally, this association will remain until a new value is reported for the same variable symbol,
	- **Process event**: determines whether the event is accepted by the DFA to check if the execution complies with the structural constraint formalized by the SSP. Once this condition is checked, and passed, the `Analyzer` collects the properties associated to that specific event (in the case of `task_start(a)`, it is the preconditions declared for a in the SSP, in the case of `task_finish(a)`, it is the postconditions declared for a, and in the case of `checkpoint reach(b)`, it is the properties declared for b) and checks them by successively invoking the `Property evaluator`, which: 
		1. using the corresponding Specification builder, builds a specification consisting of the property to be checked, the declarations for the variable symbols that appear free in the property and the axioms stating the values associated to those variable symbols, and 
		2. using the appropriate Evaluator, built on top of a specific purpose solver, analyzes the specification, and
	- **Component event**: dynamically dispatches the corresponding function of the digital twin of the Component whose name appears in the event; this forces the component’s internal state to update according to the behaviour of the real Component executing as within the SUT.


## Usage
The command line interface for the RM is very simple, see the help output below:

```bash
python -m rt_monitor.rt_monitor_sh --help
usage: The Runtime Monitor [-h] [--rabbitmq_config_file RABBITMQ_CONFIG_FILE]
                           [--log_level {debug,info,warnings,errors,critical}]
                           [--log_file LOG_FILE] [--timeout TIMEOUT]
                           [--stop {on_might_fail,on_fail,dont}]
                           spec_file

Performs runtime assertion checking of events got from a RabbitMQ server with
respect to a structured sequential process specification.

positional arguments:
  spec_file             Path to the TOML file containing the analysis
                        framework specification.

options:
  -h, --help            show this help message and exit
  --rabbitmq_config_file RABBITMQ_CONFIG_FILE
                        Path to the TOML file containing the RabbitMQ server
                        configuration.
  --log_level {debug,info,warnings,errors,critical}
                        Log verbose level.
  --log_file LOG_FILE   Path to log file.
  --timeout TIMEOUT     Timeout in seconds to wait for events after last
                        received, from the RabbitMQ server (0 = no timeout).
  --stop {on_might_fail,on_fail,dont}
                        Stop policy.

Example: python -m rt_monitor.rt_monitor_sh path/to/spec.toml
--rabbitmq_config_file=/path/to/rabbitmq_config.toml --log_file=output.log
--log_level=event --timeout=120 --stop=dont
```

### Errors
This section shows a list of errors that can be yielded by the command line interface:
- Error -1: "Input file error" indicates that there was an error while trying to open the SUT file
- Error -2: "RabbitMQ configuration error" indicates that there was an error during the configuration of the communication infrastructure
- Error -3: "Monitor error" indicates that there was an error during the monitoring process
- Error -4: "Unexpected error"

In Mac OS the execution of the RR migth output the message "This process is not trusted! Input event monitoring will not be possible until it is added to accessibility clients.". This happens when an application attempts to monitor keyboard or mouse input without having the necessary permissions because Mac OS restricts access to certain types of input monitoring for security and privacy reasons. To solve it you need to grant accessibility permissions to the application running the program (e.g., Terminal, iTerm2, or a Python IDE). Here’s how:
1. Open System Preferences:
	- Go to **Apple menu** --> **System Preferences** --> **Security & Privacy**.
2. Go to Accessibility Settings:
	- In the **Privacy** tab, select **Accessibility** from the list on the left.
3. Add Your Application:
	- If you are running the RR from **Terminal**, **iTerm2**, or a specific **IDE** (like PyCharm or VS Code), you will need to add that application to the list of allowed applications.
	- Click the **lock icon** at the bottom left and enter your password to make changes.
	- Then, click the `+` button, navigate to the application (e.g., Terminal or Python IDE), and add it to the list.
4. Restart the Application:
	- After adding it to the Accessibility list, restart the application to apply the new permissions.
Once you’ve done this, the message should go away, and pynput should be able to detect keyboard and mouse events properly.

In Mac OS the execution of the RR migth output the message "This process is not trusted! Input event monitoring will not be possible until it is added to accessibility clients.". This happens when an application attempts to monitor keyboard or mouse input without having the necessary permissions because Mac OS restricts access to certain types of input monitoring for security and privacy reasons. To solve it you need to grant accessibility permissions to the application running the program (e.g., Terminal, iTerm2, or a Python IDE). Here’s how:
1. Open System Preferences:
	- Go to **Apple menu** --> **System Preferences** --> **Security & Privacy**.
2. Go to Accessibility Settings:
	- In the **Privacy** tab, select **Accessibility** from the list on the left.
3. Add Your Application:
	- If you are running the RR from **Terminal**, **iTerm2**, or a specific **IDE** (like PyCharm or VS Code), you will need to add that application to the list of allowed applications.
	- Click the **lock icon** at the bottom left and enter your password to make changes.
	- Then, click the `+` button, navigate to the application (e.g., Terminal or Python IDE), and add it to the list.
4. Restart the Application:
	- After adding it to the Accessibility list, restart the application to apply the new permissions.
Once you’ve done this, the message should go away, and pynput should be able to detect keyboard and mouse events properly.


## License

Copyright (c) 2024 INVAP

Copyright (c) 2024 Fundacion Sadosky

This software is licensed under the Affero General Public License (AGPL) v3. If you use this software in a non-profit context, you can use the AGPL v3 license.

If you want to include this software in a paid product or service, you must negotiate a commercial license with us.

### Benefits of dual licensing:

It allows organizations to use the software for free for non-commercial purposes.

It provides a commercial option for organizations that want to include the software in a paid product or service.

It ensures that the software remains open source and available to everyone.

### Differences between the licenses:

The AGPL v3 license requires that any modifications or derivative works be released under the same license.

The commercial license does not require that modifications or derivative works be released under the same license, but it may include additional terms and conditions.

### How to access and use the licenses:

The AGPL v3 license is available for free on our website.

The commercial license can be obtained by contacting us at info@fundacionsadosky.org.ar

### How to contribute to the free open source version:

Contributions to the free version can be submitted through GitHub.
You shall sign a DCO (Developer Certificate of Origin) for each submission from all the members of your organization. The OCD will be an option during submission at GitHub.

*Contact email:* cglopezpombo@unrn.edu.ar (Carlos Gustavo Lopez Pombo)

### How to purchase the proprietary version:

The proprietary version can be purchased by contacting us at info@fundacionsadosky.org.ar

