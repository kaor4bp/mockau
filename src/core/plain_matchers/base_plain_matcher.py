from abc import abstractmethod


class BasePlainMatcher:
    @abstractmethod
    def is_intersected(self, other):
        pass

    @abstractmethod
    def is_subset(self, other):
        pass
