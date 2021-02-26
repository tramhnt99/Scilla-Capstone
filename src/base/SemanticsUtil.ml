(* Utility function for creating strings for collecting semantics *)

(*Right now we only have variables, so just add \n *)
let output_seman log_l =
    (String.concat "\n" log_l) ^ "\n"
