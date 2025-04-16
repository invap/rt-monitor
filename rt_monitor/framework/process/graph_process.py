# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging

from pyformlang.finite_automaton import (
    State,
    Symbol,
    EpsilonNFA, Epsilon
)
from rt_monitor.errors.process_errors import (
    ProcessSpecificationError,
    VariableSpecificationError
)
from rt_monitor.framework.process.process import Process


class GraphProcess(Process):
    def __init__(self, dfa, tasks, checkpoints, properties, variables):
        super().__init__(dfa, tasks, checkpoints, properties, variables)

    @staticmethod
    def process_from_toml_dict(process_dict, files_path):
        if "structure" not in process_dict:
            logging.error(f"Regular expression not found.")
            raise ProcessSpecificationError()
        nfa = EpsilonNFA()
        # Build dictionaries containing tasks and checkpoints
        tasks, checkpoints, properties = Process.dictionaries_from_toml_dict(process_dict, files_path)
        # Build the NFA
        nodes = process_dict["structure"]["nodes"]
        # Add the start state
        start_node_name = process_dict["structure"]["start"]
        start_node_type = "task" if start_node_name in tasks else "checkpoint" if start_node_name in checkpoints else "invalid"
        if start_node_type == "invalid":  # This should never execute
            logging.error(f"Process atom [ {start_node_name} ] type error.")
            raise ProcessSpecificationError()
        nfa.add_start_state(State(f"{start_node_type}_{start_node_name}_source_state"))
        # Collect all final states (i.e., all the states)
        final_states_names = []
        for node_name in nodes:
            if node_name in tasks:
                ################################################################################################
                #
                # Add:
                #                                                                 checkpoint_reached_{local_checkpoint_name}
                #                                                                 +---------------------------------------+
                #                                                                 |                                       |
                #                                                                 |                                      \/
                #   task_{node_name}_source_state ---task_started_{node_name}--> task_source_state_{node_name}_target_state ---task_finished_{node_name}---> task_{node_name}_target_state
                #
                ################################################################################################
                st_0 = State(f"task_{node_name}_source_state")
                st = State(f"task_source_state_{node_name}_target_state")
                st_f = State(f"task_{node_name}_target_state")
                # Collect all final states (i.e., all the states)
                final_states_names += [f"task_{node_name}_source_state", f"task_source_state_{node_name}_target_state", f"task_{node_name}_target_state"]
                nfa.add_transition(st_0, Symbol(f"task_started_{node_name}"), st)
                for local_checkpoint_name in [checkpoint for checkpoint in tasks[node_name].checkpoints()]:
                    nfa.add_transition(st, Symbol(f"checkpoint_reached_{local_checkpoint_name}"), st)
                nfa.add_transition(st, Symbol(f"task_finished_{node_name}"), st_f)
            else: # node_name in checkpoint
                ################################################################################################
                #
                # Add:
                #
                #   task_{node_name}_source_state -- checkpoint_reached_{global_checkpoint_name} --> task_{node_name}_target_state
                #
                ################################################################################################
                st_0 = State(f"checkpoint_{node_name}_source_state")
                st_f = State(f"checkpoint_{node_name}_target_state")
                nfa.add_transition(st_0, Symbol(f"checkpoint_reached_{node_name}"), st_f)
                # Collect all final states (i.e., all the states)
                final_states_names += [f"checkpoint_{node_name}_source_state", f"checkpoint_{node_name}_target_state"]
        edges = process_dict["structure"]["edges"]
        for edge in edges:
            src_node_name, trg_node_name = edge[0], edge[1]
            src_node_type = "task" if src_node_name in tasks else "checkpoint" if src_node_name in checkpoints else "invalid"
            trg_node_type = "task" if trg_node_name in tasks else "checkpoint" if trg_node_name in checkpoints else "invalid"
            match src_node_type, trg_node_type:
                case "task", "task":
                    nfa.add_transition(State(f"task_{src_node_name}_target_state"), Epsilon(), State(f"task_{trg_node_name}_source_state"))
                case "task", "checkpoint":
                    nfa.add_transition(State(f"task_{src_node_name}_target_state"), Epsilon(), State(f"checkpoint_{trg_node_name}_source_state"))
                case "checkpoint", "task":
                    nfa.add_transition(State(f"checkpoint_{src_node_name}_target_state"), Epsilon(), State(f"task_{trg_node_name}_source_state"))
                case "checkpoint", "checkpoint":
                    nfa.add_transition(State(f"checkpoint_{src_node_name}_target_state"), Epsilon(), State(f"checkpoint_{trg_node_name}_source_state"))
                case _: # This should never execute
                    logging.error(f"Process atom type error.")
                    raise ProcessSpecificationError()
        # Add all final states
        for state_name in final_states_names:
            nfa.add_final_state(State(state_name))
        # Determinize the automaton
        dfa = nfa.to_deterministic()
        try:
            variables = Process._get_variables_from_properties(properties)
        except VariableSpecificationError:
            logging.error(f"Variables specification error.")
            raise ProcessSpecificationError()
        else:
            return GraphProcess(dfa, tasks, checkpoints, properties, variables)
