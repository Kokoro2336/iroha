#!/usr/bin/env python3
import argparse
import os
import subprocess
import sys
import shutil

def run_command(command, capture_output=True):
    """Runs a shell command."""
    result = subprocess.run(
        command,
        shell=True,
        stdout=subprocess.PIPE if capture_output else None,
        stderr=subprocess.PIPE if capture_output else None
    )
    return result

def find_files(directory, extension):
    """Recursively finds files with a specific extension."""
    matches = []
    for root, dirnames, filenames in os.walk(directory):
        for filename in filenames:
            if filename.endswith(extension):
                matches.append(os.path.join(root, filename))
    return matches

def clean_directory(directory):
    """Removes all files in a directory."""
    if os.path.exists(directory):
        for filename in os.listdir(directory):
            file_path = os.path.join(directory, filename)
            try:
                if os.path.isfile(file_path) or os.path.islink(file_path):
                    os.unlink(file_path)
                elif os.path.isdir(file_path):
                    shutil.rmtree(file_path)
            except Exception as e:
                print(f'Failed to delete {file_path}. Reason: {e}')
    else:
        os.makedirs(directory)

def main():
    parser = argparse.ArgumentParser(description='Compiler Test Runner')
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--test', type=str, help='Test file name (excluding .sy suffix) or test number')
    group.add_argument('--test-all', action='store_true', help='Test all .sy source files')
    parser.add_argument('--hidden', action='store_true', help='Include hidden functional tests')
    parser.add_argument('--clean', action='store_true', help='Clean test directories before running')
    parser.add_argument('--graph', action='store_true', help='Dump AST graph')
    parser.add_argument('--trace', action='store_true', help='Enable trace logging')
    args = parser.parse_args()

    if args.clean and not (args.test or args.test_all or args.hidden):
        clean_directory("./test")
        print("Cleaned test directory.")
        sys.exit(0)

    # Ensure cargo build is run
    print("Running cargo build...")
    build_result = run_command("RUSTFLAG='-A warnings' cargo build", capture_output=False)

    if build_result.returncode != 0:
        print("Build failed. Exiting.")
        sys.exit(1)

    compiler_binary = "./target/debug/compiler"
    if not os.path.exists(compiler_binary):
        print(f"Compiler binary not found at {compiler_binary}")
        sys.exit(1)

    test_files = []
    base_dir = "./functional_recover"
    functional_dir = os.path.join(base_dir, "functional")
    h_functional_dir = os.path.join(base_dir, "h_functional")

    if args.test_all and args.hidden:
        search_dirs = [functional_dir, h_functional_dir]
    elif args.hidden:
        search_dirs = [h_functional_dir]
    else:
        search_dirs = [functional_dir]

    if args.test:
        # Find specific test file
        found = False
        if args.test.startswith('h'):
            search_prefix = args.test[1:]
            current_search_dirs = [h_functional_dir]
        else:
            search_prefix = args.test
            current_search_dirs = [functional_dir]

        target_name = search_prefix + ".sy"
        all_sy = []
        for d in current_search_dirs:
            all_sy.extend(find_files(d, ".sy"))
        for f in all_sy:
            basename = os.path.basename(f)
            if basename == target_name or basename.startswith(search_prefix + "_"):
                test_files.append(f)
                found = True
                break
        if not found:
            print(f"Test file {args.test} not found.")
            sys.exit(1)
    elif args.test_all or args.hidden:
        # Find all test files
        for d in search_dirs:
            test_files.extend(find_files(d, ".sy"))
        # Sort for consistent order
        test_files.sort()
    else:
        parser.print_help()
        sys.exit(1)

    # Directories to manage
    logs_dir = "./logs"
    graphs_dir = "./graphs"
    dump_llvm_dir = "./dump_llvm"
    test_output_base = "./test"

    # clean test/ first
    if args.test_all or args.hidden or args.clean:
        clean_directory(test_output_base)
    passed = 0
    failed = 0

    try:
        for test_file in test_files:
            filename = os.path.basename(test_file)
            name_no_ext = os.path.splitext(filename)[0]
            print(f"Testing {name_no_ext}...")

            # Prepare directories
            clean_directory(logs_dir)
            clean_directory(graphs_dir)
            clean_directory(dump_llvm_dir)
            
            # Expected output file (if any)
            # We specify an output file in CWD, then move it.
            output_file_name = f"{name_no_ext}.out"
            
            # Run compiler
            # Command: ./target/debug/compiler <input> -o <output>
            cmd = [compiler_binary, test_file, "-o", output_file_name]
            if args.graph:
                cmd.append("--graph")
            
            try:
                if args.trace:
                    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env={**os.environ, "RUST_BACKTRACE": "1"})
                else:
                    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                
                # Determine output directory based on result
                status = "passed" if result.returncode == 0 else "failed"
                test_output_dir = os.path.join(test_output_base, status, name_no_ext)
                
                # Clean up the other possible location to avoid confusion
                other_status = "failed" if result.returncode == 0 else "passed"
                other_output_dir = os.path.join(test_output_base, other_status, name_no_ext)
                if os.path.exists(other_output_dir):
                    shutil.rmtree(other_output_dir)

                if os.path.exists(test_output_dir):
                    shutil.rmtree(test_output_dir)
                os.makedirs(test_output_dir)

                # Copy original source file
                shutil.copy2(test_file, test_output_dir)

                # Save stdout/stderr
                with open(os.path.join(test_output_dir, "stdout.txt"), "wb") as f:
                    f.write(result.stdout)
                with open(os.path.join(test_output_dir, "stderr.txt"), "wb") as f:
                    f.write(result.stderr)

                # Move logs
                if os.path.exists(logs_dir):
                    for f in os.listdir(logs_dir):
                        shutil.move(os.path.join(logs_dir, f), os.path.join(test_output_dir, f))
                
                # Move graphs
                if os.path.exists(graphs_dir):
                    for f in os.listdir(graphs_dir):
                        shutil.move(os.path.join(graphs_dir, f), os.path.join(test_output_dir, f))

                # Move dumped LLVM IR
                if os.path.exists(dump_llvm_dir):
                    for f in os.listdir(dump_llvm_dir):
                        shutil.move(os.path.join(dump_llvm_dir, f), os.path.join(test_output_dir, f))
                
                # Move output file
                if os.path.exists(output_file_name):
                    shutil.move(output_file_name, os.path.join(test_output_dir, output_file_name))

                if result.returncode != 0:
                    print(f"  [FAILED] {name_no_ext} (Exit Code: {result.returncode})")
                    failed += 1
                else:
                    print(f"  [PASSED] {name_no_ext}")
                    passed += 1

            except Exception as e:
                print(f"  [ERROR] Exception during test {name_no_ext}: {e}")

    except KeyboardInterrupt:
        print(f"Test interrupted by user. Passed: {passed}, Failed: {failed}")
        sys.exit(1)

    print(f"Testing complete. Passed: {passed}, Failed: {failed}")


if __name__ == "__main__":
    main()