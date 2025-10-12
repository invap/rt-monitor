from z3 import Solver, String, sat, parse_smt2_string, Not


class LogicProperty:
    @classmethod
    def from_boolean_expression(cls, boolean_expression):
        return BooleanExpressionLogicProperty(boolean_expression)

    @classmethod
    def from_smt2_specification(cls, smt2_specification_file_path):
        return SMT2LogicProperty(smt2_specification_file_path)

    def evaluate(self, state):
        try:
            return self._evaluate(state)
        except self._variable_does_not_exist_error():
            return False

    def _variable_does_not_exist_error(self):
        return KeyError

    def _evaluate(self, state):
        raise NotImplementedError


class BooleanExpressionLogicProperty(LogicProperty):
    def __init__(self, boolean_expression):
        super().__init__()
        self._expression = boolean_expression

    def _evaluate(self, state):
        return self._expression(state)


class SMT2LogicProperty(LogicProperty):
    def __init__(self, specification_file_path):
        self._specification = self._specification_from_file(specification_file_path)

    def _evaluate(self, state):
        return not self._formula_has_a_counterexample(state)

    def _formula_has_a_counterexample(self, state):
        solver = Solver()
        self._add_negated_formula_to_solver(solver)
        self._replace_variables_in_formula(state, solver)

        return self._negated_formula_is_satisfiable(solver)

    def _add_negated_formula_to_solver(self, solver):
        for formula in self._specification:
            negated_formula = Not(formula)
            solver.add(negated_formula)

    def _replace_variables_in_formula(self, state, solver):
        # For now, I am assuming all variables are of type string.
        # I'm also assuming users will report the variables as named in the SMT2 file.
        for variable_name in state:
            variable_value = state[variable_name]
            variable = String(variable_name)
            solver.add(variable == variable_value)

    def _negated_formula_is_satisfiable(self, solver):
        return solver.check() == sat

    def _specification_from_file(self, smt2_specification_file_path):
        with open(smt2_specification_file_path, "r") as file:
            specification_as_text = file.read()
            file.close()

        return parse_smt2_string(specification_as_text)
