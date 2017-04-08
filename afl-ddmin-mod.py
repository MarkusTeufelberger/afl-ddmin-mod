#!/usr/bin/env python3

# Based on the ddmin algorithm by Andreas Zeller
# published in https://www.st.cs.uni-saarland.de/papers/tse2002/tse2002.pdf
# and inspired by the implementation by Morten Brøns-Pedersen
# at https://github.com/br0ns/ddmin
#
# Further reading about the concept behind ddmin:
# https://en.wikipedia.org/wiki/Delta_Debugging

# stdlib imports
import argparse  # command line argument parsing
import hashlib  # sha256 hashing of maps
import math  # calculating stats
import multiprocessing  # CPU count
import os  # file size, removing temp files
import queue  # queue up work
import subprocess  # run external programs
import sys  # exit codes
import tempfile  # temporary input/output files
import threading  # multi threaded version
import time  # start/current time
from typing import List, Tuple, Union  # type hints

__version__ = "0.1"
__author__ = "Markus Teufelberger"

# globals
CACHE = {}
BEST_MAP_HASH = ""
TEST_CASES = {}
TEST_CASES_LOCK = threading.Lock()
DEPTH = 0
TIMESTAMP = 0
RUN_COUNT = 0
TOTAL_RUNS = 0
RESULTS = []


# From http://stackoverflow.com/questions/6517953/clear-all-items-from-the-queue:
class Queue(queue.Queue):
    """
    A custom queue subclass that provides a "clear" method.
    """

    def clear(self):
        """
        Clears all items from the queue.
        """
        with self.mutex:
            unfinished = self.unfinished_tasks - len(self.queue)
            if unfinished <= 0:
                if unfinished < 0:
                    raise ValueError('task_done() called too many times')
                self.all_tasks_done.notify_all()
            self.unfinished_tasks = unfinished
            self.queue.clear()
            self.not_full.notify_all()


def chunksize(chunks: Tuple[Tuple[int, int]]) -> int:
    """
    Calculate the total file size of a bunch of chunks.

    :param chunks: A tuple with (start, end,) offsets
    :return: the total length of the resulting file
    """
    return sum(end - start for start, end in chunks)


def write_file_from_chunks(chunks: Tuple[Tuple[int, int]], small_filename: str,
                           origin_filename: str):
    """
    Creates a new file from an existing file and chunks containing offsets.

    :param chunks: A tuple with (start, end,) offsets
    :param small_filename: Name/path of the new file
    :param origin_filename: Name/path of the original file
    """
    with open(small_filename, "wb") as small_file:
        with open(origin_filename, "rb") as origin_file:
            for chunk in chunks:
                length = chunksize((chunk, ))
                # seek to first relevant byte
                origin_file.seek(chunk[0])
                small_file.write(origin_file.read(length))


def normalize_chunks(chunks: Tuple[Tuple[int, int]]) -> Tuple[Tuple[int, int]]:
    """
    Minimize the amount of chunks needed to describe a smaller portion of a file.

    :param chunks: A tuple with (start, end,) offsets
    :return: A tuple containing as few as possible (start, end,) offsets
    """
    out = []
    start1, end1 = chunks[0]
    if len(chunks) > 1:
        for start2, end2 in chunks[1:]:
            if start2 == end1:
                end1 = end2
            else:
                out.append((start1, end1))
                start1, end1 = start2, end2
    out.append((start1, end1))
    return tuple(out)


def run_showmap(
        input_name: str, output_name: str,
        args) -> int:  # TODO: type annotation for argparse.ArgumentParser
    """
    Runs afl-showmap with the arguments specified.

    :param input_name: Name/path of the input file
    :param output_name: Name/path of the output file
    :param args: argparse.ArgumentParser that was created on startup
    :return: the return value of afl-showmap (0, 1, 2, or 3)
    """
    # always run in quiet mode
    commandline = ["afl-showmap", "-o", output_name, "-q"]
    if args.timeout is not "none":
        commandline.append("-t")
        commandline.append(str(args.timeout))
    if args.mem_limit is not 50:
        commandline.append("-m")
        commandline.append(str(args.mem_limit))
    if args.qemu_mode is True:
        commandline.append("-Q")
    if args.edge_only is True:
        commandline.append("-e")

    requires_stdin = True
    for subarg in args.command:
        if "@@" in subarg:
            commandline.append(subarg.replace("@@", input_name))
            requires_stdin = False
        else:
            commandline.append(subarg)
    # afl-showmap is very limited in regards to return codes:
    # 0: target ran fine
    # Should ask lcamtuf to change calculation for afl-showmap exit code to child_crashed * 3 + child_timed_out * 2
    # to allow to differentiate between hangs and incorrect args passed to afl-showmap
    # 1: target timed out or afl-showmap failed to run
    # 2: target crashed

    # This is by FAR the limiting factor execution time wise btw.!
    if requires_stdin:
        try:
            with open(input_name, "rb") as f:
                return subprocess.run(commandline,
                                      input=f.read(),
                                      stdout=subprocess.DEVNULL,
                                      stderr=subprocess.DEVNULL).returncode
        except IOError as ioe:
            print(ioe, file=sys.stderr)
            exit(1)
    else:
        return subprocess.run(commandline,
                              stdout=subprocess.DEVNULL,
                              stderr=subprocess.DEVNULL).returncode


def get_map_hash(
        chunks: Tuple[Tuple[int, int]],
        args) -> str:  # TODO: type annotation for argparse.ArgumentParser
    """
    Get the SHA256 hash of the map file generated by afl-showmap.

    Stores the hash in the global CACHE and retrieves it from there
     on subsequent runs instead of re-calculating, if available.
    Typically, chunks are normalized before, to ensure less space
      wasted and no duplication.

    :param chunks: A tuple with (start, end,) offsets
    :param args: argparse.ArgumentParser that was created on startup
    :return: The SHA256 hash of the map file
    """
    if chunks in CACHE:
        map_hash = CACHE[chunks]["map_hash"]
        # print("Cache hit!")
    else:
        global RUN_COUNT
        RUN_COUNT += 1
        global TOTAL_RUNS
        TOTAL_RUNS += 1
        # handle temporary files a bit more manually than simply using "with"
        tmpinput = tempfile.NamedTemporaryFile(delete=False)
        with open(args.input_file, "rb") as originfile:
            # assemble new input file with data from the original
            for chunk in chunks:
                length = chunksize((chunk, ))
                # seek to first relevant byte
                originfile.seek(chunk[0])
                tmpinput.write(originfile.read(length))
        tmpinput.close()
        tmpoutput = tempfile.NamedTemporaryFile(delete=False)
        tmpoutput.close()
        # both temp files are properly closed at this point
        ret_code = run_showmap(tmpinput.name, tmpoutput.name, args)
        with open(tmpoutput.name, "rb") as mapfile:
            map_hash = hashlib.sha256(mapfile.read()).hexdigest()

        # read the map:
        #
        # This might be interesting for the future,
        #  but maps can get quite large in memory and are costly to compare...
        #
        # with open(tmpoutput.name, "r") as mapfile:
        # afl_map = [(int(element.split(":")[0]), int(element.split(":")[1].strip()))
        # for element in mapfile.readlines()]

        # remove temp files
        os.unlink(tmpinput.name)
        os.unlink(tmpoutput.name)

        if map_hash in TEST_CASES:
            with TEST_CASES_LOCK:
                # This is not thread safe otherwise
                if chunksize(chunks) < TEST_CASES[map_hash]["chunk_size"]:
                    TEST_CASES[map_hash] = {
                        "chunks": chunks,
                        "chunk_size": chunksize(chunks),
                        "returncode": ret_code
                    }
                    # print("Smaller test found!")
        else:
            TEST_CASES[map_hash] = {
                "chunks": chunks,
                "chunk_size": chunksize(chunks),
                "returncode": ret_code
            }
            # print("New test found!")
            # cache the map_hash:
        CACHE[chunks] = {"map_hash": map_hash, "returncode": ret_code}
    return map_hash


def print_counters(chunks: Tuple[Tuple[int, int]]):
    """
    Helper function to print out some statistics and diagnostics.

    :param chunks: A tuple with (start, end,) offsets
    """
    print("Current depth: " + str(DEPTH) + "/" + str(math.ceil(math.log2(
        chunksize(chunks)))))
    print("Current chunk count: " + str(len(chunks)))
    print("Current size: " + str(chunksize(chunks)))
    print("# of unique maps: " + str(len(TEST_CASES)))
    global TIMESTAMP
    now = TIMESTAMP
    # reset timer
    TIMESTAMP = time.perf_counter()
    print("Seconds for this depth: " + str(TIMESTAMP - now))
    print("Runs at this depth: " + str(RUN_COUNT))
    print("Runs per second: " + str(RUN_COUNT / (TIMESTAMP - now)))
    print("Total runs: " + str(TOTAL_RUNS))
    print("")


def split_chunks(chunks: Tuple[Tuple[int, int]], jitter:
                 int) -> List[Tuple[Tuple[int, int]]]:
    """
    Given a tuple of chunks, creates all possible splits up to a certain offset.

    Chunks of length 1 are preserved, other splits that do not result in 2 chunks
    are discarded.
    
    TODO: Good place for doctests here.

    :param chunks: A tuple with (start, end,) offsets
    :param jitter: The maximum offset (+ and -) to consider
    :return: A deduplicated list of all resulting splits.
    """
    print_counters(chunks)
    # cache can be reset at this point
    # global CACHE
    # CACHE = {}
    # reset run count
    global RUN_COUNT
    RUN_COUNT = 0
    # depth increases
    global DEPTH
    DEPTH += 1

    chunk_list = []
    for variant in range(0, jitter + 1):
        newchunks_plus = []
        newchunks_minus = []
        for start, end in chunks:
            # preserve single byte chunks
            if (end - start) == 1:
                newchunks_plus.append((start, end))
                continue
            # ddmin originally only has 0 jitter and does strict binary search
            # ddmin-mod adds jitter to the mix
            delta_plus = (end - start) // 2 + variant
            delta_minus = (end - start) // 2 - variant
            mid_plus = start + delta_plus
            mid_minus = start + delta_minus
            # depending on jitter, start can be equal to or smaller than mid!
            if start < mid_plus < end:
                newchunks_plus.append((start, mid_plus))
            if start < mid_minus < end:
                newchunks_minus.append((start, mid_minus))
            # depending on jitter, mid can be equal to or larger than end!
            if start < mid_plus < end:
                newchunks_plus.append((mid_plus, end))
            if start < mid_minus < end:
                newchunks_minus.append((mid_minus, end))
        if newchunks_plus:
            chunk_list.append(tuple(newchunks_plus))
        if newchunks_minus:
            chunk_list.append(tuple(newchunks_minus))
    # deduplicate while preserving order
    # See: http://stackoverflow.com/q/480214
    # this ensures the canonical solution with jitter = 0 is always the first list element
    seen = set()
    return [x for x in chunk_list if x not in seen and not seen.add(x)]


def smaller_file(
        chunks: Tuple[Tuple[int, int]], fullmap_hash: str,
        args) -> bool:  # TODO: type annotation for argparse.ArgumentParser
    """
    Check if the file described by chunks is returning the same map as the original.

    :param chunks: A tuple with (start, end,) offsets
    :param fullmap_hash: The hash of the map of the original file
    :param args: argparse.ArgumentParser that was created on startup
    :return: True if "chunks" describes a file that results in the same map being created,
     False otherwise
    """
    # compresses the tuples
    # slightly expensive, but saves overhead
    norm_chunks = normalize_chunks(chunks)

    afl_map_hash = get_map_hash(norm_chunks, args)
    # either:
    # afl_map is identical to fullmap (afl_map == fullmap)
    # --> return True

    # if afl_map == fullmap:
    #    return True

    # or:
    # afl_map is a proper subset of fullmap (afl_map < fullmap)
    # --> return False, this is not an interesting test case

    # elif afl_map < fullmap:
    #     return False

    # or:
    # afl_map is a superset of fullmap (afl_map >= fullmap)
    # --> return False, but this might be an interesting new test case!

    # elif afl_map >= fullmap:
    #    return False

    # or:
    # afl_map differs from fullmap but does not hit all the same spots
    # --> return False, but this might be an interesting new test case!

    # else:
    #    return False

    # since all these cases are currently not checked or can only be checked with actual maps,
    # not with hashes, it is enough to return this:
    return afl_map_hash == fullmap_hash


def worker(work_queue,  # TODO: type annotation for Queue
           args):  # TODO: type annotation for argparse.ArgumentParser
    """
    Picks a task from a queue and clears it, if successful.

    :param work_queue: a custom queue.Queue that supports clear()
    :param args: argparse.ArgumentParser that was created on startup
    """
    while True:
        task = work_queue.get()
        if task is None:
            break
        if smaller_file(task, BEST_MAP_HASH, args):
            RESULTS.append(task)
            work_queue.task_done()
            work_queue.clear()
        else:
            work_queue.task_done()


def crunch_tests(args,  # TODO: type annotation for argparse.ArgumentParser
                 chunk_list: List[Tuple[Tuple[int, int]]]):
    """
    Distributes a list of candidate sub-files to worker threads.

    Exits after finding a result or after checking all subsets and complements.

    :param args: argparse.ArgumentParser that was created on startup
    :param chunk_list: a list of chunks describing various subsets of an input file
    """
    # set up threads
    num_threads = args.threads
    if num_threads == 0:
        num_threads = multiprocessing.cpu_count()
    # start threads
    work_queue = Queue()
    threads = []
    for _ in range(num_threads):
        thread = threading.Thread(target=worker, args=(work_queue, args, ))
        thread.start()
        threads.append(thread)

    # populate queue
    for chunks in chunk_list:
        # subsets:
        for chunk in chunks:
            chunk_ = (chunk, )
            work_queue.put(chunk_)
        # complements:
        for index, _ in enumerate(chunks):
            chunk_ = chunks[:index] + chunks[index + 1:]
            work_queue.put(chunk_)

    # block until the queue is done
    # queue is cleared early, as soon as a worker discovers a result
    work_queue.join()

    # stop the threads
    for _ in range(num_threads):
        work_queue.put(None)
    for thread in threads:
        thread.join()


def ddmin2_mod(chunk_list: List[Tuple[Tuple[int, int]]],
               depth: int,
               args,  # TODO: type annotation for argparse.ArgumentParser
               testfilesize: int) -> List[Tuple[Tuple[int, int]]]:
    print("chunklist length: " + str(len(chunk_list)))
    # maximum depth reached?
    if args.max_depth != "none":
        if depth > args.max_depth:
            return chunk_list

    # main work going on in here!
    crunch_tests(args, chunk_list)

    global RESULTS

    # ensure all results are smaller than the starting size
    RESULTS = [c for c in RESULTS if chunksize(c) < testfilesize]

    if RESULTS:
        # get the best result
        best_size = testfilesize
        best_result = None
        for result_ in RESULTS:
            new_size = chunksize(result_)
            if new_size < best_size:
                best_result = result_
                best_size = new_size
        # clear results
        RESULTS = []
        # new smallest test case
        norm_chunk_ = normalize_chunks(best_result)
        global BEST_MAP_HASH
        BEST_MAP_HASH = CACHE[norm_chunk_]["map_hash"]
        # subset or complement?
        global DEPTH
        if len(best_result) == 1:
            # reduce to subset
            # only use the successful split
            print("SUBSET FOUND, new best size: " + str(chunksize(
                best_result)))
            if args.restart_recursion:
                DEPTH = math.log2(len(best_result))
                return ddmin2_mod(
                    split_chunks(norm_chunk_, args.jitter), 1, args,
                    testfilesize)
            else:
                return ddmin2_mod(
                    split_chunks(best_result, args.jitter), depth + 1, args,
                    testfilesize)
        else:
            # reduce to complement
            # only use the successful split
            print("COMPLEMENT FOUND, new best size: " + str(chunksize(
                best_result)))
            if args.restart_recursion:
                DEPTH = math.log2(len(best_result))
                return ddmin2_mod([norm_chunk_], depth, args, testfilesize)
            else:
                return ddmin2_mod([best_result], depth, args, testfilesize)
    else:
        # can we still split the file further?
        max_chunksize = 0
        for chunk_ in chunk_list[0]:
            if chunksize((chunk_, )) > max_chunksize:
                max_chunksize = chunksize((chunk_, ))
        if max_chunksize == 1:
            print("DONE")
            print_counters(chunk_list[0])
            return chunk_list
        else:
            # neither subsets nor complements worked: increase the granularity and try again
            # !!!
            # Only use the canonical split, otherwise the search tree can get... difficult.
            # !!!
            # Wanna try it out?
            # Of course you want to! Here you go:
            # TODO: This is still buggy (a list of lists of chunks instead of a list of chunks)
            # smaller_chunks = [split_chunks(chunks, args.jitter) for chunks in chunk_list]
            smaller_chunks = split_chunks(chunk_list[0], args.jitter)
            print("SPLITTING CHUNKS, current best size: " + str(chunksize(
                chunk_list[0])))
            return ddmin2_mod(smaller_chunks, depth + 1, args, testfilesize)


def ddmin(args) -> List[Tuple[Tuple[
        int, int]]]:  # TODO: type annotation for argparse.ArgumentParser
    global TIMESTAMP
    TIMESTAMP = time.perf_counter()

    # TODO: better error handling
    try:
        testfilesize = os.path.getsize(args.input_file)
    except:
        print("Error while trying to get size of input file")
        raise
    chunks = ((0, testfilesize), )
    afl_map_hash = get_map_hash(chunks, args)

    # This must be the currently smallest known test case as it is the only one
    global BEST_MAP_HASH
    BEST_MAP_HASH = afl_map_hash

    return ddmin2_mod(split_chunks(chunks, args.jitter), 1, args, testfilesize)


def main() -> int:
    # TODO: Unit tests/Doctest etc.
    # TODO: Docstrings
    args = parse_argv()
    if vars(args)["command"][0] != "--":
        print("-- not found at the correct place! Please try again...")
        return -1

    # Run target once to check if everything works out
    with tempfile.NamedTemporaryFile() as tmpoutput:
        ret_code = run_showmap(args.input_file, tmpoutput.name, args)
        if os.path.getsize(tmpoutput.name) == 0:
            print("No map created by afl-showmap, aborting.")
            return -3
    if ret_code == 0:
        print("Target exits normally")
    elif ret_code == 1:
        print("Target crashes")
    elif ret_code == 2:
        print("Target times out")
    elif ret_code == 3:
        print("Target times out AND crashes")
    else:
        # afl-showmap shouldn't even be able to return this!
        print("Target does something weird/unknown")
        return -2

    # The main work happens here
    small_file_chunks_list = ddmin(args)

    # TODO: error handling
    # TODO: make sure nothing gets overwritten!
    # TODO: Collect/display statistics more regularly in time

    # write output file
    write_file_from_chunks(
        normalize_chunks(small_file_chunks_list[0]), args.output_file,
        args.input_file)

    if args.crash_dir:
        # write crashes
        os.makedirs(args.crash_dir, exist_ok=True)
        for testcase in TEST_CASES:
            if TEST_CASES[testcase]["returncode"] > 0:
                # filename: sha256 of the map that this file produces
                write_file_from_chunks(TEST_CASES[testcase]["chunks"],
                                       os.path.join(args.crash_dir, testcase),
                                       args.input_file)

    if args.all_tests_dir:
        # write test cases
        os.makedirs(args.all_tests_dir, exist_ok=True)
        for testcase in TEST_CASES:
            if TEST_CASES[testcase]["returncode"] == 0:
                # filename: sha256 of the map that this file produces
                write_file_from_chunks(
                    TEST_CASES[testcase]["chunks"],
                    os.path.join(args.all_tests_dir, testcase),
                    args.input_file)
    return 0


def int_or_none(string: str) -> Union[int, str]:
    """
    Only allows a positive integer or a string containing "none".

    :param string: The parameter to be checked
    :return: The positive integer (incl. 0) or the string "none"
    """
    if string == "none":
        return string
    try:
        value = int(string)
        if value <= 0:
            msg = "{number} is 0 or smaller".format(number=value)
            raise argparse.ArgumentTypeError(msg)
        return value
    except:
        msg = "{input} is not an integer".format(input=string)
        raise argparse.ArgumentTypeError(msg)


def positive_int(string: str) -> int:
    """
    Only allows an integer that is 0 or larger.

    :param string: The parameter to be checked
    :return: The positive integer
    """
    try:
        value = int(string)
        if value < 0:
            msg = "{number} is smaller than 0".format(number=value)
            raise argparse.ArgumentTypeError(msg)
        return value
    except:
        msg = "{input} is not an integer".format(input=string)
        raise argparse.ArgumentTypeError(msg)


def parse_argv():  # TODO: type annotation for argparse.ArgumentParser
    """
    Parses the commandline arguments using argparse.

    :return: The argparse.ArgumentParser containing the parsed arguments.
    """
    parser = argparse.ArgumentParser(
        usage="%(prog)s [ options ] -- /path/to/target_app [ ... ]",
        epilog="For additional tips, please consult the README.",
        add_help=False)  # Otherwise "--help" is the first item displayed

    # https://bugs.python.org/issue9694 - :-(
    # Custom groups give nicer headings though:
    required = parser.add_argument_group("Required parameters")
    exec_control = parser.add_argument_group("Execution control settings")
    algo_settings = parser.add_argument_group("Minimization settings")
    optional = parser.add_argument_group("Optional arguments and parameters")

    # YAPF messes up this section a bit, so it is disabled for now:
    # yapf: disable

    # Input file path/name
    required.add_argument(
        "-i",
        metavar="file",
        required=True,
        dest="input_file",
        help="input test case to be shrunk by the tool")

    # Output file path/name (smaller version of input)
    required.add_argument(
        "-o",
        metavar="file",
        required=True,
        dest="output_file",
        help="final output location for the minimized data")

    # Timeout
    exec_control.add_argument(
        "-t",
        help="timeout for each run (none)",
        type=int_or_none,
        metavar="msec",
        dest="timeout",
        default="none")

    # Memory limit
    exec_control.add_argument(
        "-m",
        help="memory limit for child process (50 MB)",
        type=int_or_none,
        metavar="megs",
        dest="mem_limit",
        default="50")

    # QEMU mode
    exec_control.add_argument(
        "-Q",
        action="store_true",
        help="use binary-only instrumentation (QEMU mode)",
        dest="qemu_mode",
        default=False)

    # Edge coverage only
    algo_settings.add_argument(
        "-e",
        action="store_true",
        help="solve for edge coverage only, ignore hit counts",
        dest="edge_only",
        default=False)

    # Limit recursion depth
    algo_settings.add_argument(
        "-d", "--max-depth",
        type=int_or_none,
        metavar="int",
        help="limit the maximum recursion depth (none)",
        default="none")

    # Jitter when splitting chunks
    algo_settings.add_argument(
        "-j", "--jitter",
        type=positive_int,
        metavar="int",
        help="test splitting at additional offsets (0)",
        default="0")

    # Restart recursion after finding a smaller input
    algo_settings.add_argument(
        "-r", "--restart-recursion",
        action="store_true",
        help="restart the recursion after finding a smaller input file",
        default=False)

    # Path for additional test cases
    optional.add_argument(
        "-a", "--all-tests-dir",
        metavar="dir",
        help="output directory for additional test cases that were discovered while minimizing")

    # Path for additional crashes
    optional.add_argument(
        "-c", "--crash-dir",
        metavar="dir",
        help="output directory for crashes that occurred while minimizing")

    # Number of threads
    algo_settings.add_argument(
        "--threads",
        # TODO: This needs to be at least 1, not 0
        type=positive_int,
        metavar="int",
        help="number of worker threads [0 = number of cores] (0)",
        default="0")

    # Help
    optional.add_argument(
        "-h", "--help",
        action="help",
        help="show this help message and exit")

    # Version
    optional.add_argument(
        "-V", "--version",
        action="version",
        version="%(prog)s-{version}".format(version=__version__))

    # Invoking the target app
    parser.add_argument(
        "command",
        nargs=argparse.REMAINDER,
        help=argparse.SUPPRESS)

    # yapf: enable

    return parser.parse_args()

# run main() if called standalone
if __name__ == "__main__":
    sys.exit(main())
