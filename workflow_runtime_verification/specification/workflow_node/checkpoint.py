# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from workflow_runtime_verification.specification.workflow_node.workflow_element import (
    WorkflowElement,
)


class Checkpoint(WorkflowElement):
    def __init__(self, name, properties):
        super().__init__(name)
        self._properties = properties

    def properties(self):
        return self._properties
