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

## Event language


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
