# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from rt_monitor.framework.process.process_node.element import Element


class Task(Element):
    def __init__(self, name, preconditions, postconditions, checkpoints):
        super().__init__(name)
        self._preconditions = preconditions
        self._postconditions = postconditions
        self._checkpoints = checkpoints

    def preconditions(self):
        return self._preconditions

    def postconditions(self):
        return self._postconditions

    def checkpoints(self):
        return self._checkpoints

    @staticmethod
    def task_from_toml_dict(task_name, task_dict):
        return Task(
            task_name,
            task_dict["preconditions"] if "preconditions" in task_dict else set(),
            task_dict["postconditions"] if "postconditions" in task_dict else set(),
            task_dict["checkpoints"] if "checkpoints" in task_dict else set(),
        )
