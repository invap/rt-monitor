# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


class BuildSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class EvaluationError(Exception):
    def __init__(self):
        super().__init__()


class NoValueAssignedToVariableError(Exception):
    def __init__(self):
        super().__init__()


class UnboundVariablesError(Exception):
    def __init__(self):
        super().__init__()


class UnsupportedVariableTypeError(Exception):
    def __init__(self):
        super().__init__()


class UnsupportedSMT2VariableTypeError(UnsupportedVariableTypeError):
    def __init__(self):
        super().__init__()


class UnsupportedSymPyVariableTypeError(UnsupportedVariableTypeError):
    def __init__(self):
        super().__init__()


class UnsupportedPyVariableTypeError(UnsupportedVariableTypeError):
    def __init__(self):
        super().__init__()
