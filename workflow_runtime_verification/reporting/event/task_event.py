from workflow_runtime_verification.reporting.event.workflow_event import WorkflowEvent


class TaskEvent(WorkflowEvent):
    def __init__(self, name, time) -> None:
        super().__init__(time)
        self._name = name

    def name(self):
        return self._name
