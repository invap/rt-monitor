# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from rt_monitor.reporting.event.task_event import TaskEvent


class TaskFinishedEvent(TaskEvent):
    def __init__(self, name, time) -> None:
        super().__init__(name, time)

    def process_with(self, monitor):
        return monitor.process_task_finished(self)

    @staticmethod
    def event_subtype():
        return "task_finished"

    @staticmethod
    def decode_with(decoder, encoded_event):
        return decoder.decode_task_finished_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.name()}"
