# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import argparse
import logging
import os
import sys
import threading
from enum import Enum, auto
from pathlib import Path
import wx

from pynput import keyboard

from rt_monitor.errors.monitor_errors import (
    FrameworkError,
    EventReportError
)
from rt_monitor.logging_configuration import (
    LoggingLevel,
    LoggingDestination,
    _set_up_logging,
    _configure_logging_destination,
    _configure_logging_level
)
from rt_monitor.monitor_builder import MonitorBuilder


class AnalysisStatus(Enum):
    NOT_RUNNING = auto()
    RUNNING = auto()
    PAUSING = auto()
    PAUSED = auto()
    STOPPING = auto()


# Events for managing the analysis process
pause_event = threading.Event()
has_paused_event = threading.Event()
stop_event = threading.Event()
has_stopped_event = threading.Event()
analysis_process_status = AnalysisStatus.NOT_RUNNING


def _run_verification(process_thread):
    # Start the listener in a separate thread
    listener = keyboard.Listener(on_press=on_press)
    listener.start()
    # Configure the monitor by setting up control events and callback function.
    process_thread.set_events(pause_event, has_paused_event, stop_event, has_stopped_event)
    # Starts the monitor thread
    process_thread.start()
    # Waiting for the verification process to finish, either naturally or manually.
    process_thread.join()
    listener.stop()
    # Signal the main loop to exit
    wx.CallAfter(wx.GetApp().ExitMainLoop)


def on_press(key):
    global pause_event
    global has_paused_event
    global stop_event
    global has_stopped_event
    global analysis_process_status
    try:
        # Check if the key has a `char` attribute (printable key)
        match key.char:
            case "s":
                if analysis_process_status == AnalysisStatus.RUNNING:
                    # Trigger stop event.
                    stop_event.clear()
                    analysis_process_status = AnalysisStatus.STOPPING
                    logging.warning(
                        "Verification is gracefully stopping in background. "
                        "It will STOP when it finishes processing the current event."
                    )
                    # Wait until the monitor thread notifies that the analysis haf been gracefully stopped
                    while has_stopped_event.is_set():
                        pass
                    logging.warning("Verification STOPPED.")
            case "p":
                if analysis_process_status == AnalysisStatus.RUNNING:
                    # Trigger pause event.
                    pause_event.clear()
                    analysis_process_status = AnalysisStatus.PAUSING
                    logging.warning(
                        "Verification is gracefully pausing in background. "
                        "It will PAUSE when it finishes processing the current event."
                    )
                    # Wait until the monitor thread notifies that the analysis haf been gracefully paused
                    while has_paused_event.is_set():
                        pass
                    analysis_process_status = AnalysisStatus.PAUSED
                    logging.warning("Verification PAUSED.")
                elif analysis_process_status == AnalysisStatus.PAUSED:
                    # Recover from pause.
                    pause_event.set()
                    analysis_process_status = AnalysisStatus.RUNNING
                    logging.warning("Verification RESUMED.")
                else:
                    pass
            case _:
                pass
    except AttributeError:
        # Handle special keys (like ctrl, alt, etc.) here if needed
        pass


def main():
    # Definition of global variables
    global pause_event
    global has_paused_event
    global stop_event
    global has_stopped_event
    global analysis_process_status

    # Argument processing
    parser = argparse.ArgumentParser(
        prog="The Runtime Monitor",
        description="Performs runtime assertion checking over an event report with respecto to a structured sequential process.",
        epilog="Example: python -m rt_monitor.rt_monitor_sh ssp_spec.toml main_log.csv --log-file output_log.txt --log-level all"
    )
    parser.add_argument("framework", type=str, help="Path to the framework specification file in toml format.")
    parser.add_argument("event_report", type=str, help="Path to the event report in cvs.")
    parser.add_argument("--log_file", type=str, required=False, help="Path to log file (optional argument)")
    parser.add_argument("--log_level", type=str, choices=["debug", "event", "analysis", "info", "warnings", "errors", "critical"], default="info", required=False, help="Log verbose level (optional argument)")

    # Declaration of useful functions
    def validate_input_path(path):
        try:
            path.resolve()  # Normalize and validate
        except (OSError, RuntimeError):
            return False, "Invalid path syntax or characters."
        # Check existence
        if not path.exists():
            return False, "Path does not exist."
        # Check if it's a file
        if not path.is_file():
            return False, "Path is not a file."
        # Check read permission
        if not os.access(path, os.R_OK):
            return False, "No read permission."
        return True, "Path is valid."

    # Start the execution of The Runtime Monitor
    # Parse arguments
    args = parser.parse_args()
    # Set up the logging infrastructure
    # Configure logging level.
    if args.log_level is None:
        logging_level = LoggingLevel.ANALYSIS
    else:
        match args.log_level:
            case "debug":
                logging_level = LoggingLevel.DEBUG
            case "event":
                logging_level = LoggingLevel.EVENT
            case "analysis":
                logging_level = LoggingLevel.ANALYSIS
            case "info":
                logging_level = LoggingLevel.INFO
            case "warnings":
                logging_level = LoggingLevel.WARNING
            case "errors":
                logging_level = LoggingLevel.ERROR
            case "critical":
                logging_level = LoggingLevel.CRITICAL
            case _:
                print(f"Logging level error: {args.log_level} is not a logging level.", file=sys.stderr)
                exit(-3)
    # Configure logging destination.
    if args.log_file is None:
        logging_destination = LoggingDestination.CONSOLE
    else:
        valid, message = validate_input_path(args.log_file)
        if not valid:
            print(f"Log file error. {message}", file=sys.stderr)
            exit(-3)
        else:
            logging_destination = LoggingDestination.FILE
    _set_up_logging()
    _configure_logging_destination(logging_destination, args.log_file)
    _configure_logging_level(logging_level)
    # Validate and normalise the framework path
    framework_path = Path(args.framework)
    valid, message = validate_input_path(framework_path)
    if not valid:
        print(f"Framework file error. {message}", file=sys.stderr)
        exit(-1)
    # Validate and normalise the event report path
    event_report_path = Path(args.event_report)
    valid, message = validate_input_path(event_report_path)
    if not valid:
        print(f"Event report file error. {message}", file=sys.stderr)
        exit(-2)
    # Create the Monitor
    monitor_builder = MonitorBuilder(args.framework, args.event_report)
    try:
        monitor = monitor_builder.build_monitor()
    except (FrameworkError, EventReportError):
        logging.critical(f"Runtime monitoring process ABORTED.")
    else:
        # Events setup for managing the running mode.
        pause_event.set()
        has_paused_event.set()
        stop_event.set()
        has_stopped_event.set()
        analysis_process_status = AnalysisStatus.RUNNING
        # Creates a thread for controlling the analysis process
        application_thread = threading.Thread(
            target=_run_verification, args=[monitor]
        )
        application_thread.start()


if __name__ == "__main__":
    app = wx.App()
    main()
    app.MainLoop()
