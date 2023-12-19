from workflow_runtime_verification.specification.workflow_node.workflow_element import (
    WorkflowElement,
)


class Checkpoint(WorkflowElement):
    def __init__(self, name, properties):
        super().__init__(name)
        self._properties = properties

    def properties(self):
        return self._properties
