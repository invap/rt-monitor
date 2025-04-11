# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import copy

from pyformlang.finite_automaton import State, Symbol
from pyformlang.regular_expression import Regex

from rt_monitor.errors.process_errors import ProcessSpecificationError
from rt_monitor.framework.process.process import Process


class RegExProcess(Process):
    def __init__(self, dfa, tasks, checkpoints, variables):
        super().__init__(dfa, tasks, checkpoints, variables)

    @staticmethod
    def process_from_toml_dict(process_dict, files_path):
        if "structure" not in process_dict:
            logging.error(f"Regular expression not found.")
            raise ProcessSpecificationError()
        # Create DFA from regex
        dfa_start = Regex(process_dict["structure"].replace(";", ".")).to_epsilon_nfa().to_deterministic()
        dfa = copy.deepcopy(dfa_start)
        # Build dictionaries containing tasks and checkpoints
        tasks, checkpoints = Process.dictionaries_from_toml_dict(process_dict, files_path)
        # Update the DFA to have the transitions corresponding to the events associated to each
        # element in the SSP.
        for source_state in dfa_start.states:
            for ssp_node_name in [symbol.value for symbol in dfa_start.symbols if dfa_start(source_state, symbol) != []]:
                destinations = dfa_start(source_state, ssp_node_name)
                # As we only iterate over the symbols labelling outgoing transitions and the automata is deterministic
                # destinations must be of lenght exactly 1.
                # assert(len(destinations) == 1)
                target_state = destinations[0]
                #
                # the label of the outgoing transition can only be a task name or a checkpoint name
                if ssp_node_name in tasks:
                    ################################################################################################
                    # Add:
                    #                                                      "checkpoint_reached_[local_checkpoint_name]"
                    #                                                    +---------------------------------------------+
                    #                                                    |                                             |
                    #                                                    |                                            \/
                    # source_state --"task_started_[ssp_node_name]"--> "task_{source_state}_{ssp_node_name}_{target_state}" --"task_finished_[ssp_node_name]"--> target_state
                    ################################################################################################
                    task_node = State(f"task_{source_state}_{ssp_node_name}_{target_state}")
                    dfa.add_transition(source_state, Symbol(f"task_started_{ssp_node_name}"), task_node)
                    dfa.add_transition(task_node, Symbol(f"task_finished_{ssp_node_name}"), target_state)
                    for local_checkpoint_name in [checkpoint for checkpoint in tasks[ssp_node_name].checkpoints()]:
                        dfa.add_transition(task_node, Symbol(f"checkpoint_reached_{local_checkpoint_name}"), task_node)
                else:  # ssp_node_name in checkpoint
                    ################################################################################################
                    # Add:
                    #      "checkpoint_reached_[global_checkpoint_name]"
                    #      +-------------------------------------------+
                    #      |                                           |
                    #      |                                          \/
                    # source_state --"global_checkpoint_name"--> target_state
                    ################################################################################################
                    dfa.add_transition(source_state, Symbol(f"checkpoint_reached_{ssp_node_name}"), target_state)
        variables = Process._get_variables_from_dicts(tasks, checkpoints)
        return RegExProcess(dfa, tasks, checkpoints, variables)

