class TaskSpecification:
    @classmethod
    def new_named(cls, name):
        return cls(name)

    def __init__(
        self,
        name,
        preconditions=None,
        posconditions=None,
    ) -> None:
        super().__init__()

        if preconditions is None:
            preconditions = set()
        if posconditions is None:
            posconditions = set()

        self._name = name
        self._preconditions = preconditions
        self._posconditions = posconditions

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, self.__class__):
            return False

        it_has_the_same_name = self._name == other._name
        it_has_the_same_preconditions = self._preconditions == other._preconditions
        it_has_the_same_posconditions = self._posconditions == other._posconditions
        return (
            it_has_the_same_name
            and it_has_the_same_preconditions
            and it_has_the_same_posconditions
        )

    def __hash__(self) -> int:
        return hash(
            (
                self.__class__.__name__,
                self._name,
                tuple(self._preconditions),
                tuple(self._posconditions),
            )
        )

    def name(self):
        return self._name

    def preconditions(self):
        return self._preconditions

    def posconditions(self):
        return self._posconditions

    def is_named(self, task_name):
        return self._name == task_name
