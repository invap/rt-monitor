# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from rt_monitor.framework.process.process_node.checkpoint import Checkpoint
from rt_monitor.framework.process.process_node.task import Task


class Process:
    def __init__(self, variables):
        super().__init__()
        self._variables = variables

    def task_exists(self, task_name):
        raise NotImplementedError

    def global_checkpoint_exists(self, checkpoint_name):
        raise NotImplementedError

    def local_checkpoint_exists(self, checkpoint_name):
        raise NotImplementedError

    def is_starting_element(self, element_name):
        raise NotImplementedError

    def task_specification_named(self, task_name):
        raise NotImplementedError

    def global_checkpoint_named(self, checkpoint_name):
        raise NotImplementedError

    def local_checkpoint_named(self, checkpoint_name):
        raise NotImplementedError

    def variables(self):
        return self._variables

    def _element_named(self, element_name):
        if self.task_exists(element_name):
            return self.task_specification_named(element_name)
        elif self.global_checkpoint_exists(element_name):
            return self.global_checkpoint_named(element_name)

    def _task_specifications(self):
        raise NotImplementedError

    def _global_checkpoints(self):
        raise NotImplementedError
