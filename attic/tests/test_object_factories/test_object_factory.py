# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from monitor import Monitor
from framework.process.process_node.task import (
    Task,
)
from framework.process.process import (
    Process,
)
from attic.tests.test_object_factories.test_encoded_event_factory import (
    TestEncodedEventFactory,
)
from attic.tests.test_object_factories.test_logic_object_factory import (
    TestLogicObjectFactory,
)


class TestObjectFactory(TestLogicObjectFactory, TestEncodedEventFactory):
    def monitor_with_no_components_for(self, workflow_specification):
        return Monitor(
            workflow_specification,
            self.empty_component_dictionary(),
        )

    def monitor_for_workflow_with_one_task(self):
        return self.monitor_with_no_components_for(
            self.workflow_specification_with_one_task()
        )

    def monitor_for_workflow_with_many_tasks_and_parallel(self):
        return self.monitor_with_no_components_for(
            self.workflow_specification_with_many_tasks_and_parallel()
        )

    def monitor_for_workflow_with_many_tasks_and_choice(self):
        return self.monitor_with_no_components_for(
            self.workflow_specification_with_many_tasks_and_choice()
        )

    def workflow_specification_with_one_task(self):
        task_specification = self.task_specification()
        ordered_nodes = [task_specification]
        dependencies = set()

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_one_task_without_conditions(self):
        task_specification = self.task_specification_without_conditions()
        ordered_nodes = [task_specification]
        dependencies = set()

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_one_task_before_checkpoint(self, checkpoint):
        task_specification = self.task_specification()
        ordered_nodes = [task_specification, checkpoint]
        dependencies = {(0, 1)}

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_one_task_and_local_checkpoint(self, checkpoint):
        task_specification = Task(
            self.task_name(), checkpoints={checkpoint}
        )
        ordered_nodes = [task_specification]
        dependencies = set()

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_task_with_unsatisfied_precondition(self):
        task_specification = self.task_specification_with_unsatisfied_precondition()
        ordered_nodes = [task_specification]
        dependencies = set()

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_task_with_satisfied_precondition(self):
        task_specification = self.task_specification_with_satisfied_precondition()
        ordered_nodes = [task_specification]
        dependencies = set()

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_task_with_unsatisfied_postcondition(self):
        task_specification = self.task_specification_with_unsatisfied_postcondition()
        ordered_nodes = [task_specification]
        dependencies = set()

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_task_with_satisfied_postcondition(self):
        task_specification = self.task_specification_with_satisfied_postcondition()
        ordered_nodes = [task_specification]
        dependencies = set()

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_many_tasks(self):
        starting_task_specification = self.starting_task_specification()
        final_task_specification = Task(self.final_task_name())
        ordered_nodes = [starting_task_specification, final_task_specification]
        dependencies = {(0, 1)}

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_cycle(self):
        starting_task = self.starting_task_specification()
        middle_task_1 = Task(self.middle_task_1_name())
        middle_task_2 = Task(self.middle_task_2_name())
        middle_task_3 = Task(self.middle_task_3_name())
        final_task = Task(self.final_task_name())

        ordered_nodes = [
            starting_task,
            middle_task_1,
            middle_task_2,
            middle_task_3,
            final_task,
        ]
        dependencies = {(0, 1), (1, 2), (2, 3), (3, 4), (3, 1)}

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_nested_cycles(self):
        starting_task = self.starting_task_specification()
        middle_task_1 = Task(self.middle_task_1_name())
        middle_task_2 = Task(self.middle_task_2_name())
        middle_task_3 = Task(self.middle_task_3_name())
        final_task = Task(self.final_task_name())

        ordered_nodes = [
            starting_task,
            middle_task_1,
            middle_task_2,
            middle_task_3,
            final_task,
        ]
        dependencies = {(0, 1), (1, 2), (2, 3), (3, 4), (2, 2), (3, 1)}

        return Process(ordered_nodes, dependencies)

    def workflow_specification_ending_in_parallel(self):
        starting_node = self.starting_task_specification()
        middle_task_1 = Task(self.middle_task_1_name())
        middle_task_2 = Task(self.middle_task_2_name())
        middle_task_3 = Task(self.middle_task_3_name())

        ordered_nodes = [
            starting_node,
            middle_task_1,
            middle_task_2,
            middle_task_3,
        ]
        dependencies = {(0, 1), (0, 2), (2, 3)}

        return Process(ordered_nodes, dependencies)

    def workflow_specification_ending_in_choice(self):
        starting_node = self.starting_task_specification()
        middle_task_1 = Task(self.middle_task_1_name())
        middle_task_2 = Task(self.middle_task_2_name())
        middle_task_3 = Task(self.middle_task_3_name())

        ordered_nodes = [
            starting_node,
            middle_task_1,
            middle_task_2,
            middle_task_3,
        ]
        dependencies = {(0, 1), (0, 2), (2, 3)}

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_many_tasks_and_parallel(self):
        starting_node = self.starting_task_specification()
        middle_task_1 = Task(self.middle_task_1_name())
        middle_task_2 = Task(self.middle_task_2_name())
        middle_task_3 = Task(self.middle_task_3_name())
        final_node = Task(self.final_task_name())

        ordered_nodes = [
            starting_node,
            middle_task_1,
            middle_task_2,
            middle_task_3,
            final_node,
        ]
        dependencies = {(0, 1), (0, 2), (2, 3), (1, 4), (3, 4)}

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_many_tasks_and_choice(self):
        starting_node = self.starting_task_specification()
        middle_task_1 = Task(self.middle_task_1_name())
        middle_task_2 = Task(self.middle_task_2_name())
        middle_task_3 = Task(self.middle_task_3_name())
        final_node = Task(self.final_task_name())

        ordered_nodes = [
            starting_node,
            middle_task_1,
            middle_task_2,
            middle_task_3,
            final_node,
        ]
        dependencies = {(0, 1), (0, 2), (2, 3), (1, 4), (3, 4)}

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_cycle_inside_a_choice(self):
        starting_node = self.starting_task_specification()
        middle_task_1 = Task(self.middle_task_1_name())
        middle_task_2 = Task(self.middle_task_2_name())
        middle_task_3 = Task(self.middle_task_3_name())
        final_node = Task(self.final_task_name())

        ordered_nodes = [
            starting_node,
            middle_task_1,
            middle_task_2,
            middle_task_3,
            final_node,
        ]
        dependencies = {
            (0, 1),
            (0, 2),
            (2, 3),
            (3, 2),
            (1, 4),
            (3, 4),
        }

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_choice_nested_in_parallel(self):
        starting_node = self.starting_task_specification()
        middle_task_1 = Task(self.middle_task_1_name())
        middle_task_2 = Task(self.middle_task_2_name())
        middle_task_3 = Task(self.middle_task_3_name())
        final_node = Task(self.final_task_name())

        ordered_nodes = [
            starting_node,
            middle_task_1,
            middle_task_2,
            middle_task_3,
            final_node,
        ]
        dependencies = {
            (0, 1),
            (0, 2),
            (0, 3),
            (1, 4),
            (2, 4),
            (3, 4),
        }

        return Process(ordered_nodes, dependencies)

    def workflow_specification_with_parallel_nested_in_choice(self):
        starting_node = self.starting_task_specification()
        middle_task_1 = Task(self.middle_task_1_name())
        middle_task_2 = Task(self.middle_task_2_name())
        middle_task_3 = Task(self.middle_task_3_name())
        final_node = Task(self.final_task_name())

        ordered_nodes = [
            starting_node,
            middle_task_1,
            middle_task_2,
            middle_task_3,
            final_node,
        ]
        dependencies = {
            (0, 1),
            (0, 2),
            (0, 3),
            (1, 4),
            (2, 4),
            (3, 4),
        }

        return Process(ordered_nodes, dependencies)

    def task_specification(self):
        return Task.new_named(self.task_name())

    def task_specification_with_many_variables(self):
        preconditions = {
            self.condition_expecting_one_variable(),
            self.condition_expecting_another_variable(),
        }
        postconditions = {
            self.condition_expecting_one_variable(),
            self.condition_expecting_another_variable(),
        }

        return Task(
            self.task_name(), preconditions=preconditions, postconditions=postconditions
        )

    def task_specification_without_conditions(self):
        return Task.new_named(self.task_without_conditions_name())

    def task_specification_with_unsatisfied_precondition(self):
        name = self.task_with_unsatisfied_precondition_name()
        preconditions = {self.unsatisfied_property()}

        return Task(name, preconditions=preconditions)

    def task_specification_with_satisfied_precondition(self):
        name = self.task_with_satisfied_precondition_name()
        preconditions = {self.satisfied_property()}

        return Task(name, preconditions=preconditions)

    def task_specification_with_unsatisfied_postcondition(self):
        name = self.task_with_unsatisfied_postcondition_name()
        postconditions = {self.unsatisfied_property()}

        return Task(name, postconditions=postconditions)

    def task_specification_with_satisfied_postcondition(self):
        name = self.task_with_satisfied_postcondition_name()
        preconditions = {self.satisfied_property()}

        return Task(name, preconditions=preconditions)

    def starting_task_specification(self):
        return Task.new_named(self.starting_task_name())

    def empty_component_dictionary(self):
        return dict()
