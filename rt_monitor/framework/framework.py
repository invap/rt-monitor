# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


class Framework:
    # Raises: FrameworkSpecificationError()
    def __init__(self, process, components):
        self._process = process
        self._components = components

    def components(self):
        return self._components

    def process(self):
        return self._process

    def stop_components(self):
        for component_name in self._components:
            self._components[component_name].stop()


