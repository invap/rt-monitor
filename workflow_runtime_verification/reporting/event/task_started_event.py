from workflow_runtime_verification.reporting.event.task_event import TaskEvent
from workflow_runtime_verification.reporting.event_decoder import EventDecoder


class TaskStartedEvent(TaskEvent):
    def __init__(self, name, time) -> None:
        super().__init__(name, time)

    def process_with(self, monitor):
        return monitor.process_task_started(self)

    @staticmethod
    def event_subtype():
        return "task_started"

    @staticmethod
    def decode_with(encoded_event):
        return EventDecoder.decode_task_started_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.name()}"
