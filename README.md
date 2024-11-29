# The Runtime Monitor
This project contains an implementation of a Runtime Monitor (RM). The rationale behind this tool is that it provides runtime verification capabilities provided it is given:
1. an analysis framework specification (see Section [Specification language for describing the analysis framework](#Specification-language-for-describing-the-analysis-framework) for a complete description of the specification language and the file format)
2. an [event logs map file](#event-logs-map-file) for a description of the file format) containing: 
	- a reference to the **main** event log file (see Section [Event language for monitoring](#event-language-for-monitoring) for a complete description of the event language and also consider reading: 
		- Section [Relevant information about the implementation](https://github.com/invap/rt-reporter/blob/main/README.md#relevant-information-about-the-implementation) of the [Runtime Reporte](https://github.com/invap/rt-reporter/) project (an example tool (RR) that produces event log files that can be processed by the RM), and 
		- Section [Implementation of the reporter API](https://github.com/invap/c-reporter-api/blob/main/README.md#implementation-of-the-reporter-api) of the [C reporter API](https://github.com/invap/c-reporter-api/) project (a library that can be used to produce an instrumented version of the source code of the software under test (SUT), which can later be processed by the RR for producing an event log file), and 
	- references to the event log files of all the self-loggable components declared in the analysis framework specification [ref. 1.] (see Section [Self-loggables software components](#self-loggables-software-components) for a discussion on how these event log files are processed)

The analysis process 





## Installation
In this section we will review relevant aspects of how to setup this project, both for developing new features for the RM, and for using it in the runtime verification of other software artifacts.

### Base Python installation

1. Python v.3.12+ (https://www.python.org/)
2. PIP v.24.3.1+ (https://pip.pypa.io/en/stable/installation/)

### Setting up a Python virtual environment
To create a Python virtual environment, follow these steps:

1. **Open a terminal or command prompt:**
Start by opening your terminal (on Mac OS or Linux) or Command Prompt/PowerShell (on Windows).

2. **Navigate to your project directory:**
If you have a specific directory for your project, navigate to it using the cd command:
```bash
cd path/to/your/project
```
3. **Create a Python virtual environment:**
Run one of the following commands, depending on your version of Python:
	- For Python 3.3 and newer:
	```bash
	python -m venv env
	```
	Replace `env` with whatever name you'd like for your environment folder (common names include venv, .venv, or env).
	- For Older Versions (Python 2):
		- You may need to install `virtualenv` first if you're using Python 2:
		```bash
		pip install virtualenv
		```
		- Then, create the virtual environment with:
		```bash
		virtualenv env
		```
4. **Activate the virtual environment:**
To activate the virtual environment, use one of the following commands based on your operating system:
	- On Mac OS and Linux:
	```bash
	source env/bin/activate
	```
	- On Windows:
	```bash
	.\env\Scripts\activate
	```
	Once activated, you’ll see the environment name in parentheses at the beginning of your command prompt.
5. **Install packages in the virtual environment:**
With the environment activated, you can now install packages using `pip`, and they’ll be isolated to this environment.
```bash
pip install package_name
```
Perform this command for each of the packages required (see Section [Required libraries](#required-libraries) above) replacing `package_name` with the name of each package.
6. **Deactivate the virtual environment:**
To exit the virtual environment, simply type:
```bash
deactivate
```
Your environment will remain in the project folder for you to reactivate as needed.

### Libraries and packages

- **Install Python dependencies for the application:**
```bash
pip install -r requirements.txt
```
- **Content of [`requirements.txt`](https://github.com/invap/rt-monitor/blob/main/requirements.txt):**



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

1. **Structure the project:**
The RR project is organized as follows:
```graphql
rt-reporter/
├── gui/                                  # Graphical user interface components
│   ├── main_window.py                         # Main window of the GUI
│   ├── reporter_communication_channel.py      # Main module for lauching the SUT and building the event logs
│   └── reporter_generation_status.py          # Status windows showing the event generation information
├── README_images/                        # Images for the read me file
│   ├── file_selector_window.png               # File selector window capture
│   └── main_window.png                        # Main window capture
├── requirements                          # Package requirements of the project
│   ├── development_requirements.txt           # Package requirements for development 
│   └── development_requirements.txt           # Package requirements for running
├── src/                                  # Common components graphical and command line interfaces 
│   └── communication_channel_conf.py          # Information for configuring the communication channel
├── COPYING                               # Licence of the project 
├── pyproject.toml                        # Configuration file (optional, recommended)
├── README.md                             # Read me file of the project
├── rt-reporter-gui                       # Entry point of the GUI of the RR
├── rt-reporter-sh                        # Entry point of the command line interface of the RR
└── setup.py                              # Metadata and build configuration
```

2. **The [`setup.py`](https://github.com/invap/rt-reporter/blob/main/setup.py) file:**
The [`setup.py`](https://github.com/invap/rt-reporter/blob/main/setup.py) file is the main configuration file for packaging in Python. Here’s a minimal example:
```python
from setuptools import setup, find_packages


def read_requirements(file):
    with open(file, 'r') as f:
        return f.read().splitlines()


setup(
    name="rt-reporter",
    version="0.1.0",
    author="Carlos Gustavo Lopez Pombo",
    author_email="clpombo@gmail.com",
    description="An implementation of an instrumentation-based runtime event reporter.",
    long_description=open("README.md").read(),
    long_description_content_type="text/markdown",
    url="https://github.com/invap/rt-reporter/",
    packages=find_packages(),
    install_requires=read_requirements("./requirements.txt"),
    classifiers=[
        "Development status :: 4 - Beta",
        "Intended Audience :: Developers",
        "Programming Language :: Python :: 3.12",
        "License :: OSI Approved :: GNU Affero General Public License v3 or later",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.12',
)
```

3. **Add [`pyproject.toml`](https://github.com/invap/rt-reporter/blob/main/pyproject.toml) (Optional but Recommended):**
The [`pyproject.toml`](https://github.com/invap/rt-reporter/blob/main/pyproject.toml) file specifies build requirements and configurations, especially when using tools like setuptools or poetry. Here’s a basic example:
```toml
[build-system]
requires = ["setuptools", "wheel"]
build-backend = "setuptools.build_meta"
```
This configuration tells Python to use `setuptools` and `wheel` for building the package.

4. **Build the package:**
Now that your configuration files are set, you can build the package using setuptools and wheel.
- Install the necessary tools (if not already installed):
```bash
pip install setuptools wheel
```
- Run the build command in the root directory (where setup.py is located):
```bash
python setup.py sdist bdist_wheel
```
This will create two files in a new dist/ directory:
- A source distribution (.tar.gz file)
- A wheel distribution (.whl file)

### Install the application as a library locally
Follow the steps below for installing the RR as a local library:
1. **Build the application as a library:**
Follow the steps in Section [Build the application as a library](#build-the-application-as-a-library)
2. **Install the package locally:** 
Use the command `pip install dist/my_package-0.1.0-py3-none-any.whl`, replacing `my_package-0.1.0-py3-none-any.whl` with the actual filename generated in the dist folder.

### Distribute the application as a library
Follow the steps below for distributing the RR as a library in PyPI:
1. **Build the application as a library:**
Follow the steps in Section [Build the application as a library](#build-the-application-as-a-library)
2. **Upload the package to PyPI:**
If you want to make your package publicly available, you can upload it to the Python Package Index (PyPI).
	- Install twine (a tool for uploading packages):
	```bash
	pip install twine
	```
	- Upload the package:
	```bash
	twine upload dist/*
	```
	This command will prompt you to enter your PyPI credentials. Once uploaded, others can install your package with `pip install your-package-name`.


## The Runtime Monitor architecture

---

Write.

---


## Event language for monitoring

---

Write.

---


## The monitoring process

---

Write.

---


## Monitoring components

---

Write.

---

### Self-logging software components

---

Remember to say that if the toml file providing the event logs list includes a certain component (for example, the adc in Example app) the event log file referenced in the toml file has to have the same component name as the component declared in the analysis framework specification

Write.

---

### Implementation of digital twins for monitoring software components

---

Write.

---


## Specification language for describing the analysis framework

---


By default, the files are expected to be found in the location designated by the attribute `working_directory`. If such attribute is not present, then the path of the analysis framework specification is used instead. Nonetheless, if the `file` attribute of a property is specifies by a string starting with `/` of `.`, the path section of the value of the attribute (i.e., the substring starting at position 0 and ending right before the last occurrence of `/`) overrides the default.

Components have a general path and specific paths for components. If the specific path is not preset, the general one is used. If both are missing the component is assumed to be in the directory from with the tool was launched ".".
Write.

---

### Syntax for writing properties

---

Write.

---


## Event logs map file

---

Write.

---


## Runtime verification with hardware in the loop

---

Write.

---


-------

## Relevant information ebout the implementation
The RR provides the basic functionality; once the SUT is chossen, the former runs the latter within a thread and captures its output pipe for pocessing the events and writing them in the corresponding event log files. The main log file is named `?_log.csv`, where `?` is the name of the SUT; for monitoring purposes this log file must be declared with the reference name "main" in the [event logs map file](https://github.com/invap/rt-monitor/blob/main/README.md#event-logs-map-file "Event logs map file") required by the [RM](https://github.com/invap/rt-monitor "Runtime Monitor") to execute the verification. The event log files produced by the self-loggable components receive their name from the name declared in the self-loggable component log initialization event, suffixed with `_log.csv`.

The SUT is assume to be instrumented for ouputing a stream of predefined event types packed in appropriate package types. Event types are defined in agreement between the RR and the reporter API; in our case, the definition can be seen in [Line 49](https://github.com/invap/c-reporter-api/blob/main/include/data_channel_defs.h#L49 "Event types") of file [`data_channel_defs.h`](https://github.com/invap/c-reporter-api/blob/main/include/data_channel_defs.h) as a C enumerated type:
```c
//classification of the different types of events
typedef enum {
	timed_event, 
	state_event, 
	process_event, 
	component_event, 
	self_loggable_component_log_init_event, 
	self_loggable_component_event
} eventType;
```
which are naturally recognized as integers by the code fragment from [Line 78](https://github.com/invap/rt-reporter/blob/main/reporter_communication_channel.py#L78) to [Line 107](https://github.com/invap/rt-reporter/blob/main/reporter_communication_channel.py#L107) where appropriate action is taken for each type of event, according to the association {(0, `timed_event`), (1, `state_event`), (2, `process_event`), (3, `component_event`), (4, `self_loggable_component_log_init_event`), (5, `self_loggable_component_event`)}. 
Each event type arrives packed in a package type corresponding to the event it contains, as they are defined in the code fragment from [Line 18](https://github.com/invap/rt-monitor-example-app/blob/main/buggy%20app/main.c#L18) to [Line 46](https://github.com/invap/rt-monitor-example-app/blob/main/buggy%20app/main.c#L46) of in the file [`data_channel_defs.c`](https://github.com/invap/c-reporter-api/blob/main/include/data_channel_defs.h).
All package types come inside a reporter package (see code fragment from [Line 51](https://github.com/invap/rt-monitor-example-app/blob/main/buggy%20app/main.c#L51) to [Line 62](https://github.com/invap/rt-monitor-example-app/blob/main/buggy%20app/main.c#L62) of file [`data_channel_defs.c`](https://github.com/invap/c-reporter-api/blob/main/include/data_channel_defs.h)) labeled with the event type they contain and time-stamped.
Whenever a reporter package is unpacked by the reporter (see code fragment from [Line 73](https://github.com/invap/rt-reporter/blob/main/src/reporter_communication_channel.py#L73) to [Line 77](https://github.com/invap/rt-reporter/blob/main/src/reporter_communication_channel.py#L77) of file [`reporter_communication_channel.py`](https://github.com/invap/rt-reporter/blob/main/src/reporter_communication_channel.py)) we obtain: 1) a `[timestamp]`, 2) an event type (interpreted as an integer), and 3) an `[event]`. According to the event type obtained after unpacking the reporter package, appropriate logging actions are taken:
- case 0: records the line "[timestamp],timed_event,[event]" in file corresponding to the main event log file. `[event]` provide details of the timed event reported and has the shape `[clock action],[clock variable]` where `[clock action]` is in the set {clock_start, clock_pause, clock_resume, clock_reset} and `[clock variable]` is the name of a free clock variable occurring in any property of the structured sequential process (see Section [Syntax for writing properties](https://github.com/invap/rt-monitor/blob/main/README.md#syntax-for-writing-properties "Syntax for writing properties") for details on the language for writing properties of structured sequential processes),
- case 1: records the line "[timestamp],state_event,[event]" in file corresponding to the main event log file. `[event]` provide details of the state event reported and has the shape `variable_value_assigned,[variable name],[value]` where `[variable name]` is the name of a free state variable occurring in any property of the structured sequential process (see Section [Syntax for writing properties](https://github.com/invap/rt-monitor/blob/main/README.md#syntax-for-writing-properties "Syntax for writing properties") for details on the language for writing properties of structured sequential processes),
- case 2: records the line "[timestamp],process_event,[event]" in file corresponding to the main event log file. `[event]` provide details of the process event reported and has the shape `task_started,[name]`, `task_finished,[name]` or `checkpoint_reached,[name]`, where `[name]` is a unique identifier corresponding to a task o checkpoint, respectively, in the structured sequential process (see Section [Structured Sequential Process](https://github.com/invap/rt-monitor/blob/main/README.md#structured-sequential-process "Structured Sequential Process") for details on the language for declaring structured sequential processes),
- case 3: records the line "[timestamp],component_event,[event]" in file corresponding to the main event log file. `[event]` provide details of the component event reported and has the shape `[component name],[function name],[parameter list],[result]`, where `[component name]` is a unique identifier corresponding to a component declared in the specification of the analysis framework (see Section [Specification language for describing the analysis framework](https://github.com/invap/rt-monitor/blob/main/README.md#specification-language-for-describing-the-analysis-framework "Specification language for describing the analysis framework") for details on the language for specifying the analysis framework), `[function name]` is the name of a function implemented by the component, `[parameter list]` is the list of parameters required by the function `[function name]`, separated by commas, and `[result]` is the value returned by the invocation, provided that the function returns a value, see for example the code fragment from [Line 70](https://github.com/invap/rt-monitor-example-app/blob/main/buggy%20app/main.c#L70) to [Line 76](https://github.com/invap/rt-monitor-example-app/blob/main/buggy%20app/main.c#L76) of the function [`main`](https://github.com/invap/rt-monitor-example-app/blob/main/buggy%20app/main.c#L17), in the file [`main.c`](https://github.com/invap/rt-monitor-example-app/blob/main/buggy%20app/main.c), where the invocation of function `sample` is followed by a code fragment reporting a component event:  
```c
value = sample ();
// [ INSTRUMENTACION: Component event. ]
pause(&reporting_clk);
sprintf(str, "adc,sample,%d",value);
report(component_event,str);
resume(&reporting_clk);
//
```
- case 4: in this case, no line is written to any event log because the event reported is the initialization of the event log file of a self-loggable component; thus, `[event]` only contains the name of the self-loggable component so the reporter can open a file named `[event]_log.csv` for writing,
- case 5: in this case `[event]` has the shape `[component name],[component event]', thus the reporter writes the line "[timestamp],[component event]" in the event log file corresponding to `[component name]`, and
- in any other case: records the line "[timestamp],invalid,[event]" in file corresponding to the main event log file.

## Usage
### GUI interface
The graphical user interface for the RR is very simple, it is launched by typing `python rt-reporter-gui` which will open de main window of the GUI of the RR, shown in [Figure 1](#main-window).

<figure id="main-window" style="text-align: center;">
  <img src="./README_images/main_window.png" width="600" alt="The main window of the GUI of the RR.">
  <figcaption style="font-style: italic;"><b>Figure 1</b>: The main window of the GUI of the RR.
  </figcaption>
</figure>

After clicking in the folder icon on the right of the text box, the file selection window will open (shown in [Figure 2](#file-selection-window)) and will allow to chose the executable file whose events will be recorded.

<figure id="file-selection-window" style="text-align: center;">
  <img src="./README_images/file_selector_window.png" width="600" alt="File selection window of the GUI of the RR.">
  <figcaption style="font-style: italic;"><b>Figure 2</b>: File selection window of the GUI of the RR.
  </figcaption>
</figure>

Then, clicking on the `Start` button at the bottom of [Figure 2](#file_selection_window) will run the SUT producing the corresponding event log files in the same location where the SUT is.

The `Stop` button at the bottom of [Figure 2](#file_selection_window) stops the execution of the SUT and closes the event log files.

Closing the window exits the GUI of the RR. 


### Command line interface
The command line interface for the RR is very simple, it is invoked by typing `python rt-reporter-sh [SUT full path]` and it will run the SUT producing the corresponding event log files in the same location where the SUT is, according to the indicated in `[SUT full path]`.

The interface keeps itself listening to the keyboard; pressing the letter `s` stops the execution of the SUT, closes the event log files and exits the command line interface of the RR.

An alternative implementation for Windows-based systems can be developed using `msvcrt`.

#### Errors
This section shows a list of errors that can be yielded by the command line interface:
- Error -1, "Erroneous number of arguments.": the command line interface expects exactly one parameter that is taken as the SUT to be reported; if it is passed zero or more than 1 parameter this error is yielded.
- Error -2: "File not found.": the command line interface expects the only parameter passed to be a file containing the SUT to be reported; if it is not present, this error is yielded.

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

### How to purchase the proprietary version:

The proprietary version can be purchased by contacting us at info@fundacionsadosky.org.ar


------


# Runtime Verification for Real Time DAQs


## Project Setup in Ubuntu


### Base Python installation

1. Python (https://www.python.org/)
2. PIP (https://pip.pypa.io/en/stable/installation/)


### IDE setup

Use `Python 3.10`


#### PyCharm

1. Go to `PyCharm -> Preferences -> Project -> Python Interpreter`
2. Add `WxPhython` and `z3-solver`


#### IntelliJ IDEA Ultimate

1. Go to `File -> Project Structure`
2. Go to `Platform Settings -> SDKs`
3. Select `Add new SDK -> Add Python SDK`
4. Create a **_new_** `Virtualenv Environment`
5. Go to `Platform Settings -> Project`
6. Choose the newly created SDK
7. Select `Apply` and `OK`

*Install all PIP packages inside the Python environment, using IDEA's console.


### Libraries and packages

Run the following terminal commands for each step.
1. Ubuntu package dependencies: `sudo make install-ubuntu-dependencies`
2. Python package dependencies: `install-python-dependencies-for-development` (make sure the terminal is using the Python environment, if you have previously set it up)

**Optional:** To install the prototype's dependencies, run `make install-prototype-python-dependencies`
*This will take some minutes. It should not be done unless you need to work inside the prototype's folder.


## Linting

To run the linter in autocorrect mode, just execute `make lint` in the root folder.
Make sure to run it inside the Python environment, if you use one. 


## Build and install as library

1. Build it by running `make build-package`
2. Install it by running `make install-package`


## Example usage

1. Choose a valid or invalid report from the available ones in the `example_usage/` directory.
2. Import it in the `usage.py` file, and pass it as an argument to the monitor's method.
3. Execute `make run-example-usage`.
4. The result of the verification will be printed in the console.


