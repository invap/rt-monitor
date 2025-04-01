# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import logging
import graphviz
import copy

from pyformlang.finite_automaton import State, Symbol
from pyformlang.regular_expression import Regex

from rt_monitor.errors.process_errors import (
    ProcessSpecificationError,
    GlobalCheckpointSpecificationError,
    TaskSpecificationError, VariablesSpecificationError
)
from rt_monitor.framework.process.process import Process


class RegExProcess(Process):
    def __init__(self, dfa, tasks, checkpoints, variables):
        super().__init__(variables)
        self._dfa = dfa
        self._tasks = tasks
        self._checkpoints = checkpoints

    def dfa(self):
        return self._dfa

    @staticmethod
    def process_from_toml_dict(process_dict, files_path):
        # Create DFA from regex
        if "structure" not in process_dict:
            logging.error(f"Regular expression not found.")
            raise ProcessSpecificationError()
        dfa = Regex(process_dict["structure"].replace(";", ".")).to_epsilon_nfa().to_deterministic()
        dfa_copy = copy.deepcopy(dfa)
        # Build dictionaries containing tasks and checkpoints
        tasks = {}
        for task in process_dict["tasks"]:
            try:
                decoded_task = Process._decode_task(task["name"], process_dict["tasks"], files_path)
            except TaskSpecificationError:
                logging.error(f"Error decoding task from process [ {task["name"]} ].")
                raise ProcessSpecificationError()
            tasks[task["name"]] = decoded_task
        checkpoints = {}
        for checkpoint in process_dict["checkpoints"]:
            try:
                decoded_checkpoint = Process._decode_global_checkpoint(checkpoint["name"], process_dict["checkpoints"], files_path)
            except GlobalCheckpointSpecificationError:
                logging.error(f"Error decoding task from process [ {checkpoint["name"]} ].")
                raise ProcessSpecificationError()
            checkpoints[checkpoint["name"]] = decoded_checkpoint
        # Update the DFA to have the transitions corresponding to the events associated to each
        # element in the SSP.
        for source_state in dfa.states:
            for ssp_node_name in [symbol.value for symbol in dfa.symbols if dfa(source_state, symbol) != []]:
                destinations = dfa(source_state, ssp_node_name)
                # As we only iterate over the symbols labelling outgoing transitions and the automata is deterministic
                # destinations must be of lenght exactly 1.
                # assert(len(destinations) == 1)
                target_state = destinations[0]
                #
                # the label of the outgoing transition can only be a task name or a checkpoint name
                if ssp_node_name in tasks:
                    ################################################################################################
                    # Add:
                    #                                                   "checkpoint_reached_[local_checkpoint_name]"
                    #                                                 +---------------------------------------------+
                    #                                                 |                                             |
                    #                                                 |                                            \/
                    # source_state --"task_init_[ssp_node_name]"--> "task_{source_state}_{ssp_node_name}_{target_state}" --"task_finished_[ssp_node_name]"--> target_state
                    ################################################################################################
                    task_node = State(f"task_{source_state}_{ssp_node_name}_{target_state}")
                    dfa_copy.add_transition(source_state, Symbol(f"task_started_{ssp_node_name}"), task_node)
                    dfa_copy.add_transition(task_node, Symbol(f"task_finished_{ssp_node_name}"), target_state)
                    for local_checkpoint_name in [checkpoint.name() for checkpoint in tasks[ssp_node_name].checkpoints()]:
                        dfa_copy.add_transition(task_node, Symbol(f"checkpoint_reached_{local_checkpoint_name}"), task_node)
                else:  # ssp_node_name in checkpoint
                    ################################################################################################
                    # Add:
                    #      "checkpoint_reached_[global_checkpoint_name]"
                    #      +-------------------------------------------+
                    #      |                                           |
                    #      |                                          \/
                    # source_state --"global_checkpoint_name"--> target_state
                    ################################################################################################
                    dfa_copy.add_transition(source_state, Symbol(f"checkpoint_reached_{ssp_node_name}"), target_state)
        variables = _get_variables_from_dicts(tasks, checkpoints)
        return RegExProcess(dfa_copy, tasks, checkpoints, variables)

    def task_exists(self, task_name):
        return task_name in self._tasks

    def global_checkpoint_exists(self, checkpoint_name):
        return checkpoint_name in self._checkpoints

    def local_checkpoint_exists(self, checkpoint_name):
        found = False
        for task in self._tasks.values():
            if found:
                break
            found = any(checkpoint.name() for checkpoint in task.checkpoints())
        return found

    def task_specification_named(self, task_name):
        # This method assumes there is a task named that way.
        return self._tasks[task_name]

    def global_checkpoint_named(self, checkpoint_name):
        # This method assumes there is a global checkpoint named that way.
        return self._checkpoints[checkpoint_name]

    def local_checkpoint_named(self, checkpoint_name):
        # This method assumes there is a local checkpoint named that way.
        for task in self._tasks.values():
            for checkpoint in task.checkpoints():
                if checkpoint.name() == checkpoint_name:
                    return checkpoint

    def variables(self):
        return self._variables


# Raises: UnsupportedNodeType(), PropertySpecificationError()
def _get_variables_from_dicts(tasks, checkpoints):
    variables = {}
    for task_name in tasks:
        for formula in tasks[task_name].preconditions():
            for variable in formula.variables():
                if formula.variables()[variable][0] not in {"Component", "State", "Clock"}:
                    logging.error(
                        f"Variables class [ {formula.variables()[variable][0]} ] unsupported.")
                    raise VariablesSpecificationError()
                if variable in variables and not variables[variable] == formula.variables()[variable]:
                    logging.error(
                        f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                    raise VariablesSpecificationError()
                variables[variable] = formula.variables()[variable]
        for formula in tasks[task_name].postconditions():
            for variable in formula.variables():
                if formula.variables()[variable][0] not in {"Component", "State", "Clock"}:
                    logging.error(
                        f"Variables class [ {formula.variables()[variable][0]} ] unsupported.")
                    raise VariablesSpecificationError()
                if variable in variables and not variables[variable] == formula.variables()[variable]:
                    logging.error(
                        f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                    raise VariablesSpecificationError()
                variables[variable] = formula.variables()[variable]
        for checkpoint in tasks[task_name].checkpoints():
            for formula in checkpoint.properties():
                for variable in formula.variables():
                    if formula.variables()[variable][0] not in {"Component", "State", "Clock"}:
                        logging.error(
                            f"Variables class [ {formula.variables()[variable][0]} ] unsupported.")
                        raise VariablesSpecificationError()
                    if variable in variables and not variables[variable] == formula.variables()[variable]:
                        logging.error(
                            f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                        raise VariablesSpecificationError()
                    variables[variable] = formula.variables()[variable]
    for checkpoint_name in checkpoints:
        for formula in checkpoints[checkpoint_name].properties():
            for variable in formula.variables():
                if formula.variables()[variable][0] not in {"Component", "State", "Clock"}:
                    logging.error(
                        f"Variables class [ {formula.variables()[variable][0]} ] unsupported.")
                    raise VariablesSpecificationError()
                if variable in variables and not variables[variable] == formula.variables()[variable]:
                    logging.error(
                        f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                    raise VariablesSpecificationError()
                variables[variable] = formula.variables()[variable]
    return variables


def draw_dfa(dfa, dfa_name):
    # Initialize Graphviz
    dot = graphviz.Digraph(engine="dot")

    # Add states
    for state in dfa.states:
        if state in dfa.final_states:
            dot.node(str(state), shape="doublecircle")
        else:
            dot.node(str(state))

    # Add start state arrow
    dot.node("__start__", shape="none", width="0", height="0")
    dot.edge("__start__", str(dfa.start_state))

    # Add transitions
    for state in dfa.states:
        for symbol in dfa.symbols:
            next_state = dfa(state, Symbol(symbol))
            if next_state is not None:
                dot.edge(str(state), str(next_state), label=str(symbol))

    # Render the graph
    dot.render(dfa_name, format="png", view=True)
