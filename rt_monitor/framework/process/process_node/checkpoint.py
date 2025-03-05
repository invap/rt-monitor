# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from framework.process.process_node.element import Element


class Checkpoint(Element):
    def __init__(self, name, properties):
        super().__init__(name)
        self._properties = properties

    def properties(self):
        return self._properties

    def type(self):
        return "Checkpoint"