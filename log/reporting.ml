#load "str.cma";;

let split_line line = Str.split (Str.regexp ",") line

let iter_lines f file =
  let ch = open_in file in
  try while true do
      f (input_line ch)
    done with _ -> ();;

let print_ns ip = ignore (Sys.command ("dig -x " ^ ip ^ " +short"));;

iter_lines
  (fun line ->
    match split_line line with
      | dt::ip::_ -> print_string dt; print_string "  "; flush stdout; print_ns ip
      | _ -> print_endline "*** wrong format ***")
  "data/hitlog.txt";;
