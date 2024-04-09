class Clock:
    def __init__(self):
        super().__init__()
        self._pauseStart = 0
        self._dragTime = 0
        self._isPaused = False

    def start(self, startTime):
        self._pauseStart = 0
        self._dragTime = startTime
        self._isPaused = False

    def pause(self, pauseTime):
        if not self._isPaused:
            self._isPaused = True
            self._pauseStart = pauseTime

    def resume(self, resumeTime):
        if self._isPaused:
            self._dragTime += resumeTime() - self._pauseStart
            self._pauseStart = 0
            self._isPaused = False

    def reset(self, startTime):
        self._pauseStart = 0
        self._dragTime = startTime
        self._isPaused = False

    def getTime(self, now):
        return now - self._dragTime
