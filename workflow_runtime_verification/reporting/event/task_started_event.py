from workflow_runtime_verification.reporting.event.task_event import TaskEvent


class TaskStartedEvent(TaskEvent):
    def __init__(self, name, time) -> None:
        super().__init__(name, time)

    def process_with(self, monitor):
        return monitor.process_task_started(self)

    @classmethod
    def event_subtype(cls):
        return "task_started"

    @classmethod
    def decode_with(cls, decoder, encoded_event):
        return decoder.decode_task_started_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.name()}"
