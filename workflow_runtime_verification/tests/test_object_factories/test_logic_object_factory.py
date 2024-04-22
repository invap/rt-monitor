from workflow_runtime_verification.specification.logic_property import LogicProperty
from workflow_runtime_verification.tests.test_object_factories.test_name_and_value_factory import (
    TestNameAndValueFactory,
)


class TestLogicObjectFactory(TestNameAndValueFactory):
    def logic_property_from(self, variables, formula, property_name):
        return frozenset(variables), formula, property_name

    def condition_expecting_one_variable(self):
        def condition(state):
            return state[self.variable_name()] == self.variable_value()

        return LogicProperty.from_boolean_expression(condition)

    def condition_expecting_another_variable(self):
        def condition(state):
            return state[self.another_variable_name()] != state[self.variable_name()]

        return LogicProperty.from_boolean_expression(condition)

    def unsatisfied_property(self):
        return self.logic_property_from(set(), "(= 1 2)", "unsatisfied_property")

    def satisfied_property(self):
        return self.logic_property_from(set(), "(= 1 1)", "satisfied_property")

    def property_with_non_existent_variable(self):
        return self.logic_property_from(
            {"x", "y"}, "(= x y)", "property_with_non_existent_variable"
        )

    def empty_execution_state(self):
        return dict()

    def state_containing_one_expected_variable(self):
        return {self.variable_name(): self.variable_value()}

    def state_containing_all_expected_variables(self):
        return {
            self.variable_name(): self.variable_value(),
            self.another_variable_name(): self.another_variable_value(),
        }
