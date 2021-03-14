from sys import stderr


DEBUG = False


def debug_print(*args, **kwargs):
    if DEBUG:
        print(*args, file=stderr, **kwargs)
