from sys import stderr


DEBUG = True


def debug_print(*args, **kwargs):
    if DEBUG:
        print(*args, file=stderr, **kwargs)
