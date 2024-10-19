# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


class CheckpointDoesNotExist(Exception):
    def __init__(self, checkpoint_name):
        super().__init__()
        self._checkpoint_name = checkpoint_name

    def get_checkpoint_name(self):
        return self._checkpoint_name


class TaskDoesNotExist(Exception):
    def __init__(self, task_name):
        super().__init__()
        self._task_name = task_name

    def get_task_name(self):
        return self._task_name


class ComponentDoesNotExist(Exception):
    def __init__(self, component_name):
        super().__init__()
        self._component_name = component_name

    def get_component_name(self):
        return self._component_name
