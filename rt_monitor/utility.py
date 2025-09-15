# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from pathlib import Path, PurePosixPath
import logging
# Create a logger for the monitor component
logger = logging.getLogger(__name__)


def is_valid_file_with_extension(path_str, extension):
    """
    Validates that a POSIX path string:
    1. Ends with a filename having the specified extension
    2. Has a parent directory that exists
    3. The file exists and is a regular file
    4. If extension is any, then it is ignored
    """
    # Normalize extension format
    normalized_extension = extension
    if extension and not extension.startswith('.'):
        normalized_extension = '.' + extension
    try:  # Normalize and convert to PurePosixPath for strict POSIX parsing
        path = PurePosixPath(path_str)
    except Exception:
        logger.error(f"Invalid POSIX path: {path_str}")
        return False
    # Validate filename exists and isn't empty
    if path.name == "" or path.name == "." or path.name == "..":
        logger.info(f"Invalid filename in path: {path_str}")
        return False
    # Validate extension
    if extension != "any" and path.suffix != normalized_extension:
        logger.info(f"File extension does not match for path: {path_str}")  
        return False
    # Convert to concrete Path for filesystem checks
    concrete_path = Path(path_str)
    try:
        # Check if the parent directory exists
        if not concrete_path.parent.is_dir():
            logger.info(f"Parent directory does not exist for path: {path_str}")
            return False
        # Check if the file exists and is a regular file
        return concrete_path.is_file()
    except PermissionError:  # Insufficient permissions to verify
        logger.error(f"Permission denied for path: {path_str}")
        return False
    except OSError:  # Other filesystem errors (e.g., broken symlink)
        logger.error(f"OS error when accessing path: {path_str}")
        return False

def is_valid_file_with_extension_nex(path_str, extension):
    """
    Validates that a POSIX path string:
    1. Ends with a filename having the specified extension
    2. Has a parent directory that exists
    3. If extension is any, then it is ignored
    """
    # Normalize extension format
    normalized_extension = extension
    if extension and not extension.startswith('.'):
        normalized_extension = '.' + extension
    try:  # Normalize and convert to PurePosixPath for strict POSIX parsing
        path = PurePosixPath(path_str)
    except Exception:
        logger.error(f"Invalid POSIX path: {path_str}")
        return False
    # Validate filename exists and isn't empty
    if path.name == "" or path.name == "." or path.name == "..":
        logger.info(f"Invalid filename in path: {path_str}")
        return False
    # Validate extension
    if extension != "any" and path.suffix != normalized_extension:
        logger.info(f"File extension does not match for path: {path_str}")
        return False
    # Convert to concrete Path for filesystem checks
    concrete_path = Path(path_str)
    try:
        # Check if the parent directory exists
        return concrete_path.parent.is_dir()
    except PermissionError:  # Insufficient permissions to verify
        logger.error(f"Permission denied for path: {path_str}")
        return False
    except OSError:  # Other filesystem errors (e.g., broken symlink)
        logger.error(f"OS error when accessing path: {path_str}")
        return False
