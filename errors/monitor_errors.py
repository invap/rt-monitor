# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


# Exceptions related to the construction of the analysis framework
class FrameworkError(Exception):
    def __init__(self):
        super().__init__()


class ReportListError(Exception):
    def __init__(self):
        super().__init__()


class UndeclaredComponentVariableError(Exception):
    def __init__(self):
        super().__init__()


class UnknownVariableClassError(Exception):
    def __init__(self):
        super().__init__()


class MonitorConstructionError(Exception):
    def __init__(self):
        super().__init__()


# Exceptions related to the analysis process
class AbortRun(Exception):
    def __init__(self):
        super().__init__()


# Variable exceptions
class UndeclaredVariableError(Exception):
    def __init__(self):
        super().__init__()


# Process exceptions
class TaskDoesNotExistError(Exception):
    def __init__(self):
        super().__init__()


class CheckpointDoesNotExistError(Exception):
    def __init__(self):
        super().__init__()


# Component exceptions
class ComponentDoesNotExistError(Exception):
    def __init__(self):
        super().__init__()


class ComponentError(Exception):
    def __init__(self):
        super().__init__()

