# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


class NotImplementedPropertyType(Exception):
    def __init__(self, formula):
        super().__init__()
        self._formula = formula

    def get_formula(self):
        return self._formula


class PropertySourceError(Exception):
    def __init__(self):
        super().__init__()


class PropertyFormatError(Exception):
    def __init__(self, property_format):
        super().__init__()
        self._property_format = property_format

    def property_format(self):
        return self._property_format


class ProcessSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class TaskSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class LocalCheckpointSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class GlobalCheckpointSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class PropertySpecificationError(Exception):
    def __init__(self):
        super().__init__()


class VariablesSpecificationError(Exception):
    def __init__(self):
        super().__init__()
