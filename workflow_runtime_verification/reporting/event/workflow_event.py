from workflow_runtime_verification.reporting.event.event import Event


class WorkflowEvent(Event):
    def __init__(self, time) -> None:
        super().__init__(time)

    @classmethod
    def event_type(cls):
        return "workflow_event"

    @classmethod
    def event_subtype(cls):
        raise NotImplementedError

    @classmethod
    def decode_with(cls, decoder, encoded_event):
        return decoder.decode_workflow_event(encoded_event)
