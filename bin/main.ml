open Ila
let rec repl () : unit =
    print_string "λ> ";
    flush stdout;
    match read_line () with
    | exception End_of_file -> print_newline ()
    | line ->
        match get_command line with
        | Quit -> ()
        | Full t -> (Format.printf "%s@." t; repl ())
let () = repl ()