# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


class FrameworkSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class ComponentsSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class ProcessSpecificationError(Exception):
    def __init__(self):
        super().__init__()


class UnsupportedNodeType(Exception):
    def __init__(self, node_name, node_type):
        super().__init__()
        self._node_name = node_name
        self._node_type = node_type

    def node_name(self):
        return self._node_name

    def node_type(self):
        return self._node_type


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


