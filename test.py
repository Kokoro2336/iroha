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

def normalize_output_bytes(data: bytes) -> bytes:
    normalized = data.replace(b"\r\n", b"\n")
    lines = normalized.split(b"\n")
    while lines and lines[0].strip() == b"":
        lines.pop(0)
    while lines and lines[-1].strip() == b"":
        lines.pop()
    return b"\n".join(lines)

def generate_cfg_graphs(ll_path: str, graph_dir: str, test_name: str):
    os.makedirs(graph_dir, exist_ok=True)
    abs_ll_path = os.path.abspath(ll_path)

    opt_commands = [
        ["opt", "-passes=dot-cfg", "-disable-output", "-disable-verify", abs_ll_path],
        ["opt", "-enable-new-pm=0", "-dot-cfg", "-disable-output", "-disable-verify", abs_ll_path],
        ["opt", "-enable-new-pm=0", "-dot-cfg-only", "-disable-output", "-disable-verify", abs_ll_path],
    ]

    opt_ok = False
    opt_stderr = b""
    for cmd in opt_commands:
        result = subprocess.run(cmd, cwd=graph_dir, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        opt_stderr += result.stderr
        if result.returncode == 0:
            opt_ok = True
            break

    if not opt_ok:
        return 1, b"", opt_stderr + b"\n[ERROR] Failed to generate CFG .dot via opt\n"

    dot_files = [f for f in os.listdir(graph_dir) if f.endswith(".dot")]
    if not dot_files:
        return 1, b"", b"[ERROR] opt succeeded but produced no .dot files\n"
    graphviz_stdout = b""
    graphviz_stderr = b""

    for dot_file in dot_files:
        dot_path = os.path.join(graph_dir, dot_file)
        svg_base = os.path.splitext(dot_file)[0]
        svg_path = os.path.join(graph_dir, f"{test_name}_{svg_base}.svg")
        dot_result = subprocess.run(
            ["dot", "-Tsvg", dot_path, "-o", svg_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        graphviz_stdout += dot_result.stdout
        graphviz_stderr += dot_result.stderr
        if dot_result.returncode != 0:
            return dot_result.returncode, graphviz_stdout, graphviz_stderr + b"\n[ERROR] Graphviz dot failed\n"

    return 0, graphviz_stdout, graphviz_stderr

def main():
    parser = argparse.ArgumentParser(description='Compiler Test Runner')
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--test', type=str, help='Test file name (excluding .sy suffix) or test number')
    group.add_argument('--test-all', action='store_true', help='Test all .sy source files')
    parser.add_argument('--hidden', action='store_true', help='Include hidden functional tests')
    parser.add_argument('--clean', action='store_true', help='Clean test directories before running')
    parser.add_argument('--graph', action='store_true', help='Generate CFG graphs (.dot/.svg) from linked LLVM IR using opt + graphviz')
    parser.add_argument('--trace', action='store_true', help='Enable trace logging')
    backend_group = parser.add_mutually_exclusive_group()
    backend_group.add_argument('--lli', action='store_true', help='Use lli to interpret linked .ll')
    backend_group.add_argument('--llc', action='store_true', help='Use llc to compile linked .ll into executable and run it')
    args = parser.parse_args()

    exec_mode = 'llc' if args.llc else 'lli'

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
    sylib_ll = "./sylib/sylib.ll"

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

            work_test_output_dir = os.path.join(test_output_base, "_work", name_no_ext)
            if os.path.exists(work_test_output_dir):
                shutil.rmtree(work_test_output_dir)
            os.makedirs(work_test_output_dir, exist_ok=True)

            # Prepare directories
            clean_directory(logs_dir)
            clean_directory(graphs_dir)
            clean_directory(dump_llvm_dir)
            
            # Expected output file (if any)
            # We specify an output file in CWD, then move it.
            output_file_name = f"{name_no_ext}.out"
            linked_ll_name = f"{name_no_ext}.linked.ll"
            target_dir = os.path.join(work_test_output_dir, "target")
            graph_output_dir = os.path.join(work_test_output_dir, "graph")
            os.makedirs(target_dir, exist_ok=True)
            os.makedirs(graph_output_dir, exist_ok=True)
            linked_ll_path = os.path.join(target_dir, linked_ll_name)
            if os.path.exists(linked_ll_path):
                os.unlink(linked_ll_path)
            
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

                final_returncode = result.returncode
                final_stdout = result.stdout
                final_stderr = result.stderr
                runtime_with_ret = None
                runtime_raw = None

                if final_returncode == 0:
                    generated_ll = os.path.join(dump_llvm_dir, f"{name_no_ext}.ll")
                    if not os.path.exists(generated_ll):
                        final_returncode = 1
                        final_stderr += (
                            f"\n[ERROR] Generated LLVM IR not found: {generated_ll}\n"
                        ).encode()
                    else:
                        if args.graph:
                            graph_code, graph_stdout, graph_stderr = generate_cfg_graphs(
                                generated_ll,
                                graph_output_dir,
                                name_no_ext,
                            )
                            final_stdout += graph_stdout
                            final_stderr += graph_stderr
                            if graph_code != 0:
                                final_returncode = graph_code

                        if final_returncode == 0 and not os.path.exists(sylib_ll):
                            final_returncode = 1
                            final_stderr += (
                                f"\n[ERROR] Runtime library LLVM IR not found: {sylib_ll}\n"
                            ).encode()

                        if final_returncode == 0:
                            link_cmd = ["llvm-link", generated_ll, sylib_ll, "-S", "-o", linked_ll_path]
                            link_result = subprocess.run(link_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                            final_stdout += link_result.stdout
                            final_stderr += link_result.stderr

                            if link_result.returncode != 0:
                                final_returncode = link_result.returncode
                        if final_returncode == 0:
                            input_file = os.path.splitext(test_file)[0] + ".in"
                            if exec_mode == 'lli':
                                lli_cmd = ["lli", linked_ll_path]
                                if os.path.exists(input_file):
                                    with open(input_file, "rb") as f_in:
                                        exec_result = subprocess.run(
                                            lli_cmd,
                                            stdin=f_in,
                                            stdout=subprocess.PIPE,
                                            stderr=subprocess.PIPE,
                                        )
                                else:
                                    exec_result = subprocess.run(
                                        lli_cmd,
                                        stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE,
                                    )
                            else:
                                obj_path = os.path.join(target_dir, f"{name_no_ext}.o")
                                asm_path = os.path.join(target_dir, f"{name_no_ext}.s")
                                exe_path = os.path.join(target_dir, f"{name_no_ext}.out")

                                llc_asm_cmd = ["llc", linked_ll_path, "-filetype=asm", "-o", asm_path]
                                llc_asm_result = subprocess.run(llc_asm_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                                final_stdout += llc_asm_result.stdout
                                final_stderr += llc_asm_result.stderr

                                if llc_asm_result.returncode != 0:
                                    final_returncode = llc_asm_result.returncode
                                    exec_result = None
                                else:
                                    llc_obj_cmd = ["llc", linked_ll_path, "-filetype=obj", "-o", obj_path]
                                    llc_obj_result = subprocess.run(llc_obj_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                                    final_stdout += llc_obj_result.stdout
                                    final_stderr += llc_obj_result.stderr

                                    if llc_obj_result.returncode != 0:
                                        final_returncode = llc_obj_result.returncode
                                        exec_result = None

                                    linker = shutil.which("clang") or shutil.which("cc") or shutil.which("gcc")
                                    if linker is None:
                                        final_returncode = 1
                                        final_stderr += b"\n[ERROR] No system linker found (clang/cc/gcc).\n"
                                        exec_result = None
                                    else:
                                        link_exe_cmd = [linker, obj_path, "-o", exe_path, "-no-pie"]
                                        link_exe_result = subprocess.run(
                                            link_exe_cmd,
                                            stdout=subprocess.PIPE,
                                            stderr=subprocess.PIPE,
                                        )
                                        final_stdout += link_exe_result.stdout
                                        final_stderr += link_exe_result.stderr

                                        if link_exe_result.returncode != 0:
                                            final_returncode = link_exe_result.returncode
                                            exec_result = None
                                        else:
                                            if os.path.exists(input_file):
                                                with open(input_file, "rb") as f_in:
                                                    exec_result = subprocess.run(
                                                        [exe_path],
                                                        stdin=f_in,
                                                        stdout=subprocess.PIPE,
                                                        stderr=subprocess.PIPE,
                                                    )
                                            else:
                                                exec_result = subprocess.run(
                                                    [exe_path],
                                                    stdout=subprocess.PIPE,
                                                    stderr=subprocess.PIPE,
                                                )

                            if exec_result is None:
                                runtime_raw = b""
                                runtime_with_ret = None
                            else:
                                runtime_raw = exec_result.stdout
                                runtime_with_ret = runtime_raw
                                if not runtime_with_ret.endswith(b"\n"):
                                    runtime_with_ret += b"\n"
                                runtime_with_ret += f"{exec_result.returncode}\n".encode()

                                final_stdout += runtime_with_ret
                                final_stderr += exec_result.stderr

                            if final_returncode == 0 and runtime_with_ret is None:
                                final_returncode = 1
                                final_stderr += b"\n[ERROR] Runtime execution did not produce output.\n"

                expected_output_file = os.path.splitext(test_file)[0] + ".out"
                if final_returncode == 0:
                    if runtime_with_ret is None:
                        final_returncode = 1
                        final_stderr += b"\n[ERROR] Runtime output missing for comparison.\n"
                    elif not os.path.exists(expected_output_file):
                        final_returncode = 1
                        final_stderr += (
                            f"\n[ERROR] Expected output not found: {expected_output_file}\n"
                        ).encode()
                    else:
                        with open(expected_output_file, "rb") as f_exp:
                            expected_bytes = f_exp.read()
                        expected_norm = normalize_output_bytes(expected_bytes)
                        actual_with_ret_norm = normalize_output_bytes(runtime_with_ret)
                        actual_raw_norm = normalize_output_bytes(runtime_raw or b"")
                        if expected_norm != actual_with_ret_norm and expected_norm != actual_raw_norm:
                            final_returncode = 1
                            final_stderr += b"\n[ERROR] Output mismatch with expected .out\n"

                        with open(os.path.join(work_test_output_dir, "actual.out"), "wb") as f_actual:
                            f_actual.write(runtime_with_ret)
                
                # Determine output directory based on result
                status = "passed" if final_returncode == 0 else "failed"
                test_output_dir = os.path.join(test_output_base, status, name_no_ext)
                
                # Clean up the other possible location to avoid confusion
                other_status = "failed" if final_returncode == 0 else "passed"
                other_output_dir = os.path.join(test_output_base, other_status, name_no_ext)
                if os.path.exists(other_output_dir):
                    shutil.rmtree(other_output_dir)

                if os.path.exists(test_output_dir):
                    shutil.rmtree(test_output_dir)
                os.makedirs(os.path.dirname(test_output_dir), exist_ok=True)

                # Copy original source file
                shutil.copy2(test_file, work_test_output_dir)

                if os.path.exists(expected_output_file):
                    shutil.copy2(
                        expected_output_file,
                        os.path.join(work_test_output_dir, "expected.out"),
                    )

                # Save stdout/stderr
                with open(os.path.join(work_test_output_dir, "stdout.txt"), "wb") as f:
                    f.write(final_stdout)
                with open(os.path.join(work_test_output_dir, "stderr.txt"), "wb") as f:
                    f.write(final_stderr)

                # Move logs
                if os.path.exists(logs_dir):
                    for f in os.listdir(logs_dir):
                        shutil.move(os.path.join(logs_dir, f), os.path.join(work_test_output_dir, f))
                
                # Move compiler-generated graphs (if any)
                if os.path.exists(graphs_dir):
                    for f in os.listdir(graphs_dir):
                        shutil.move(os.path.join(graphs_dir, f), os.path.join(work_test_output_dir, f))

                # Move dumped LLVM IR
                if os.path.exists(dump_llvm_dir):
                    for f in os.listdir(dump_llvm_dir):
                        src = os.path.join(dump_llvm_dir, f)
                        if f.endswith('.ll'):
                            dst = os.path.join(target_dir, f)
                        else:
                            dst = os.path.join(work_test_output_dir, f)
                        shutil.move(src, dst)
                
                # Move output file
                if os.path.exists(output_file_name):
                    shutil.move(output_file_name, os.path.join(work_test_output_dir, output_file_name))

                shutil.move(work_test_output_dir, test_output_dir)

                if final_returncode != 0:
                    print(f"  [FAILED] {name_no_ext} (Exit Code: {final_returncode})")
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