import logging
import os


def init_logger(level="INFO"):
    logging.basicConfig(format='%(levelname)s: %(message)s', level=os.environ.get("LOGLEVEL", level))