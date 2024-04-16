(* Testing framework for Imp.
 *
 * N. Danner
 *
 * Tests are defined by a combination of specifications and Imp source code
 * files.
 *
 * A test specification is a JSON object with the following attributes:
 *
 *   - "file":   name of an Imp source code file (string)
 *   - "input":  a string list of values to provide as input.
 *   - "output": a string list of expected output values.
 *
 * The test is conducted as follows.  The source code file is executed by the
 * interpreter.  Each `get_*` function is given the next item in the input
 * list.  Every `print_*` output is recorded into an output file.  The lines of
 * the output file are compared to the output list.  If they are the same, the
 * test passes; otherwise the test fails.  So, for example, consider
 *
 *   {
 *       "file":     "gcd.imp",
 *       "input":    [ "84", "60" ],
 *       "output":   [ "12" ]
 *   }
 *
 * This test will execute `gcd.imp`.  The first call to `get_*` will get "84"
 * and the second call will get "60".  The test passes if the program outputs a
 * single line that consists of "12", fails otherwise.
 *
 * A specification file is a sequence of specifications.  One test suite is
 * defined for each specification file, and is named for that file.  Individual
 * tests within a suite are named 0, 1, 2,... according to their index in the
 * specification file.
 *
 * Tests are grouped by teams.  Each team has a directory under
 * `interp_tests_dir`.  Each team directory has subdirectories `specs_dir`
 * (for test specifications) and `files_dir` (for the program files).
 *
 *)

open OUnit2

module YJ = Yojson.Basic
module YJU = YJ.Util

(* Directory in which to find test specifications.
 *)
let specs_dir = "specs"

(* Directory in which to find test code.
 *)
let files_dir = "files"

(* Directory in which to find team test directories.
 *)
let interp_tests_dir = "teams"

let iotest test_code input expected =
  fun tc ->
    (* Execute the test code, sending output to a file, then reading that
     * output back into `actual`.  This would be so much nicer if I could
     * just set the API output channel to a buffer!
     *)
    let (tmpfile, oc) = bracket_tmpfile tc in
    let () = 
      Imp.Interp.Api.in_channel := 
        Scanf.Scanning.from_string (String.concat " " input) in
    let () =
      Imp.Interp.Api.out_channel := oc in
    let () = Imp.Interp.Api.show_prompts := false in
    let () = Imp.Interp.exec test_code in
    let actual : string list =
      In_channel.with_open_text tmpfile In_channel.input_lines in

    assert_equal ~ctxt:tc ~printer:(String.concat " ") expected actual

(* extest test_code input expected = a test that succeeds when exxecuting
 * `test_code` with `input` raises an exception e such that
 * Printexc_to_string e = `expected`.
 *
 * We don't use assert_raise here, because that expects an exception value,
 * which requires us to know the arguments to the constructor when the
 * exception is raised, which is not something we can rely upon.  So instead
 * we compare to the string representation of the exception, which we expect
 * to be fixed by an appropriate call to Printexc.register_printer.
 *)
let extest test_code input expected =
  fun tc ->
    (* Execute the test code, sending output to a file, then reading that
     * output back into `actual`.  This would be so much nicer if I could
     * just set the API output channel to a buffer!
     *)
    let (_, oc) = bracket_tmpfile tc in
    let () = 
      Imp.Interp.Api.in_channel := 
        Scanf.Scanning.from_string (String.concat " " input) in
    let () =
      Imp.Interp.Api.out_channel := oc in
    let () = Imp.Interp.Api.show_prompts := false in

    let actual : string option =
      try
        let _ = Imp.Interp.exec test_code in
        None
      with
      | e -> Some (Printexc.to_string e)
    in

    assert_equal 
      ~ctxt:tc 
      ~printer:(function | Some s -> s | None -> "No exception raised") 
      (Some expected) actual


(* make_test_from_json_spec fd sp = (name, tf), where tf is a a test defined
 * by sp as described above and name is the name of the file used for the
 * test.  `fd` is the directory in which to find program files.
 *
 * Note that what I call a "test" has type `OUnit2.test_fun`.
 *)
let make_test_from_json_spec 
    (files_dir : string) (spec : YJ.t) : string*test_fun =
  (* Get the code to be tested.
   *)
  let test_file = 
    Filename.concat files_dir (spec |> YJU.member "file" |> YJU.to_string) in
  let test_code = In_channel.with_open_text test_file (
    fun ic ->
      let lexbuf = Lexing.from_channel ic in
      Imp.Parser.terminated_pgm Imp.Lexer.read_token lexbuf
  ) in

  (* Set the API input channel to read from the input in the test
   * specification.
   *)
  let input : string list = 
    spec |> YJU.member "input" |> YJU.to_list |> YJU.filter_string in

  (* Are we testing against expected output or an exception?
   *)
  let keys : string list = YJU.keys spec in

  if List.exists (fun k -> k = "output") keys then
    (* Get the expected output.
     *)
    let expected : string list =
      spec |> YJU.member "output" |> YJU.to_list |> YJU.filter_string in

    (test_file, iotest test_code input expected)
  else
    let ex : string =
      spec |> YJU.member "except" |> YJU.to_string in
    (test_file, extest test_code input ex)


(* make_suite_from_specs sd fd f = ts, where ts is a test suite with name
 * `f`, where the tests in ts are specified by the specs in `sd`/`f` and
 * program files are found in `fd`.
 *
 * Note that what I call a "test suite" has type OUnit2.test.
 *)
let make_suite_from_specs 
    (specs_dir : string) (files_dir : string) (f : string) : test =
  let specs = Filename.concat specs_dir f |> YJ.seq_from_file |> List.of_seq in

  f >::: 
    List.map 
      (
        fun s ->
          let (f, t) = make_test_from_json_spec files_dir s in
          f >:: t
      )
      specs

(*  is_dir f = true,  f is the name of a directory
 *             false, o/w.
 *)
let is_dir (f : string) : bool =
  match Unix.stat f with
  | {st_kind = S_DIR; _} -> true
  | _ -> false

let () =

  Printexc.register_printer (
    function
    | Imp.Interp.MultipleDeclaration _ -> Some "MultipleDeclaration"
    | Imp.Interp.UnboundVariable _ -> Some "UnboundVariable"
    | Imp.Interp.UndefinedFunction _ -> Some "UndefinedFunction"
    | Imp.Interp.TypeError _ -> Some "TypeError"
    | Imp.Interp.SecurityError -> Some "SecurityError"
    | _ -> None
  ) ;

  (* team_tests d = a test suite named `d` that consists of all tests under
   * the team directory `d`.  Only read tests from files with extension
   * .json.
   *)
  let team_tests d : test =
    let team_specs_dir = 
      Filename.concat d specs_dir in
    let team_files_dir =
      Filename.concat d files_dir in
    let spec_files = 
      List.filter (fun f -> Filename.check_suffix f "json")
        (Sys.readdir team_specs_dir |> Array.to_list) in
    let suites : test list = 
      List.map 
        (make_suite_from_specs team_specs_dir team_files_dir) spec_files in
    d >::: suites
  in

  (* team_dirs = all directories under the `interp_tests_dir` directory.
   *)
  let team_dirs : string list =
    Sys.readdir interp_tests_dir 
    |> Array.to_list 
    |> List.map (Filename.concat interp_tests_dir)
    |> List.filter is_dir in

  (*  all_suites = all test suites under all team directories combined into
   *  a single test suite named "all tests"
   *)
  let all_suites : test = "all tests" >::: List.map team_tests team_dirs in

  run_test_tt_main all_suites


