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


## Simulator framework

- Simulator's description
- Architecture

