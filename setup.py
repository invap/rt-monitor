from setuptools import setup, find_packages


def read_requirements(file):
    with open(file, "r") as f:
        return f.read().splitlines()


setup(
    name="rt-reporter",
    version="0.1.0",
    author="Carlos Gustavo Lopez Pombo",
    author_email="clpombo@gmail.com",
    description="This project contains an implementation of a Runtime Monitoring tool (RM). The rationale behind this tool is that it provides runtime verification capabilities provided it is given: 1. an analysis framework specification, and 2. an event reports map file containing: a. a reference to the **main** event report file, and b. references to the event report files of the self-loggable components declared in the analysis framework specification.",
    long_description=open("README.md").read(),
    long_description_content_type="text/markdown",
    url="https://github.com/invap/rt-monitor/",
    packages=find_packages(),
    install_requires=read_requirements("./requirements.txt"),
    classifiers=[
        "Development status :: 4 - Beta",
        "Intended Audience :: Developers",
        "Programming Language :: Python :: 3.12",
        "License :: OSI Approved :: GNU Affero General Public License v3 or later",
        "Operating System :: OS Independent",
    ],
    python_requires=">=3.12",
)
