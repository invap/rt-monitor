# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


class ProcessSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class TaskSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class CheckpointSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class PropertySpecificationError(Exception):
    def __init__(self):
        super().__init__()


class VariableSpecificationError(Exception):
    def __init__(self):
        super().__init__()
