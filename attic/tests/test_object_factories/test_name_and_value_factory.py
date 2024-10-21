# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class TestNameAndValueFactory:
    def task_name(self):
        return "task name"

    def task_without_conditions_name(self):
        return "task without conditions"

    def task_with_unsatisfied_precondition_name(self):
        return "task with unsatisfied precondition"

    def task_with_satisfied_precondition_name(self):
        return "task with satisfied precondition"

    def task_with_unsatisfied_postcondition_name(self):
        return "task with unsatisfied postcondition"

    def task_with_satisfied_postcondition_name(self):
        return "task with satisfied postcondition"

    def starting_task_name(self):
        return "starting task"

    def middle_task_name(self):
        return "middle task"

    def middle_task_1_name(self):
        return "middle task 1"

    def middle_task_2_name(self):
        return "middle task 2"

    def middle_task_3_name(self):
        return "middle task 3"

    def final_task_name(self):
        return "final task"

    def non_existent_checkpoint_name(self):
        return "non-existent checkpoint"

    def checkpoint_name(self):
        return "checkpoint name"

    def non_existent_variable_name(self):
        return "non existent variable"

    def variable_name(self):
        return "variable"

    def another_variable_name(self):
        return "another_variable"

    def variable_value(self):
        return 1

    def another_variable_value(self):
        return 2

    def variable_type(self):
        return "uint16_t"
