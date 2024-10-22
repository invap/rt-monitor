# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from framework.process.process_node.element import Element


class Task(Element):
    def __init__(self, name, preconditions=None, postconditions=None, checkpoints=None):
        super().__init__(name)
        if preconditions is None:
            preconditions = set()
        if postconditions is None:
            postconditions = set()
        if checkpoints is None:
            checkpoints = set()
        self._preconditions = preconditions
        self._postconditions = postconditions
        self._checkpoints = checkpoints

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, self.__class__):
            return False
        it_has_the_same_name = self._name == other._name
        it_has_the_same_preconditions = self._preconditions == other._preconditions
        it_has_the_same_postconditions = self._postconditions == other._postconditions
        it_has_the_same_checkpoints = self._checkpoints == other._checkpoints
        return (
            it_has_the_same_name
            and it_has_the_same_preconditions
            and it_has_the_same_postconditions
            and it_has_the_same_checkpoints
        )

    def __hash__(self) -> int:
        return hash(
            (
                self.__class__.__name__,
                self._name,
                tuple(self._preconditions),
                tuple(self._postconditions),
                tuple(self._checkpoints),
            )
        )

    def has_checkpoint_named(self, checkpoint_name):
        return any(
            checkpoint.is_named(checkpoint_name) for checkpoint in self._checkpoints
        )

    def checkpoint_named(self, checkpoint_name):
        return next(
            checkpoint
            for checkpoint in self._checkpoints
            if checkpoint.is_named(checkpoint_name)
        )

    def preconditions(self):
        return self._preconditions

    def postconditions(self):
        return self._postconditions

    def checkpoints(self):
        return self._checkpoints

    def type(self):
        return "Task"