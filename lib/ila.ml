(*
    Ila : a minimal λ-term reducer with REPL. Uses a naive implementation of
    untyped λ-calculus (i.e. a substitution-based as opposed to
    an environment/closure-based approach) with user-facing de Bruijn indices.
    
    This de-Bruijn-based syntax has the advantage of being easy to implement
    (compared to allowing for named variables) as well as, in keeping with the
    tradition of esoteric languages, offering a mechanism by which the designer
    can punish the user. 
    
    Parses via comparably naive parser combinators.
*)
type tm = 
    | Ind of int
    | Lam of tm
    | App of tm * tm
(*
    Index-shifting function. Handles free variables.
*)
let rec shift (d : int) (c : int) (t : tm) : tm =
    match t with
    | Ind i -> if i >= c then Ind (i + d) else Ind i
    | Lam s -> Lam (shift d (c + 1) s)
    | App (m, n) -> App (shift d c m, shift d c n)
(*
    Substitution of a term for an index.
*)
let rec substitute (n : tm) (i : int) (m : tm) : tm =
    match m with
        | Ind j ->
            if i = j then n
            else if j > i then Ind (j - 1)
            else Ind j
        | Lam t -> Lam (substitute (shift 1 1 n) (i + 1) t)
        | App (f, x) -> App (substitute n i f, substitute n i x)
(*
    One-step reduction in normal order.
*)
let rec contract (t : tm) : tm option =
    match t with
    | App (Lam m, n) -> Some (substitute n 1 m)
    | App (f, x) ->
        (match contract f with
        | Some f' -> Some (App (f', x))
        | None ->
            (match contract x with
            | Some x' -> Some (App (f, x'))
            | None -> None))
    | Lam s ->
        (match contract s with
        | Some s' -> Some (Lam s')
        | None -> None)
    | Ind _  -> None
(*
    Multi-step reduction function with step maximum to hedge against terms without nfs.
*)
let normalize (t : tm) : tm =
    let rec f (t : tm) (n : int) : tm =
        if n <= 0 then t else
            (match contract t with
            | Some t' -> f t' (n - 1)
            | None -> t) in
    f t 1000000
(*
    Accommodates for abstractors being numbers.
*)
let rec nlam (n : int) (t : tm) : tm =
    match n <= 0 with
    | true -> t
    | false -> Lam (nlam (n - 1) t)
(*
    Accommodates for abstractors being numbers in the other direction.
*)
let rec unlam (t : tm) : int * tm =
    match t with
    | Lam t' -> let n, s = unlam t' in n + 1, s
    | t' -> 0, t'
(*
    Turns a term into a string.
*)
let rec stringify (t : tm) : string =
    match t with
    | Ind i -> string_of_int i
    | Lam t' -> let n, s = unlam t' in (string_of_int (n + 1)) ^ "." ^ stringify s
    | App (Ind i, Ind j) -> "(" ^ string_of_int i ^ " " ^ string_of_int j ^ ")" 
    | App (Lam t', s) -> "(" ^ stringify (Lam t') ^ ") " ^ stringify s
    | App (m, n) -> "(" ^ stringify m ^ " " ^ stringify n ^ ")"
(*
    Turns a term into a string.
*)
let fmt = Printf.sprintf
(*
    Conceptually, perhaps it should be "book with bookmark"
    or "marked book," but these are terribly unwieldy.
*)
type bookmark = string * int
(*
    Given a bookmark (string with index),
    returns the character at that index (if in bounds).
*)
let snapshot (s : bookmark) : char option =
    match snd s < String.length (fst s) with
    | false -> None
    | _ -> Some (fst s).[snd s]
let snapshot' (s : bookmark) : char =
    match snd s < String.length (fst s) with
    | false -> (fst s).[String.length (fst s) - 1]
    | _ -> (fst s).[snd s]
(*
    Increments the index of a bookmark, tantamount to
    "consuming a character."
*)
let advance (s : bookmark) : bookmark = (fst s, (snd s) + 1)
type 'a parser = bookmark -> (('a * bookmark), string) result
(*
    The most atomic of atomic parsers. Succeeds if the
    marked character satisfies a predicate.
*)
let satisfy (p : char -> bool) : char parser =
    fun s ->
        match snapshot s with
        | None -> Error (fmt "Index is out of bounds at %d." (snd s))
        | Some page ->
            match p page with
            | false -> Error (fmt "Failure at position %d." (snd s))
            | true -> Ok ((page, advance s))
(*
    "Wraps" a value in a parser.
*)
let pure (x : 'a) : 'a parser = fun s -> Ok (x, s)
(*
    Fails unconditionally.
*)
let fail : 'a parser = fun _ -> Error "Nonspecified failure."
(*
    Running (a <|> b) means "try a; if a succeeds, return its output;
    otherwise, try b."
*)
let ( <|> ) (p : 'a parser) (q : 'a parser) : 'a parser =
    fun s ->
        match p s with
        | Ok _ as result -> result
        | Error _ -> q s
(*
    Applies a parser-wrapped function to a parser.
*)
let ( <*> ) (f : ('a -> 'b) parser) (p : 'a parser) : 'b parser =
    fun s ->
        match f s with
        | Error msg -> Error msg
        | Ok (f', r) ->
            (match p r with
            | Error msg -> Error msg
            | Ok (p', r') -> Ok (f' p', r'))
(*
    Map. Applies a pure function to a parser.
*)
let ( <$> ) (f : 'a -> 'b) (p : 'a parser) : 'b parser = pure f <*> p 
(*
    Running (a << b) means "run a, then run b. If both succeed, return the
    output of a (having consumed the input of b)." Also commonly written "<*".
*)
let ( << ) (p : 'a parser) (q : 'b parser) : 'a parser =
    fun s -> 
        match p s with
        | Error msg -> Error msg
        | Ok (a, r) ->
            (match q r with
            | Error msg -> Error msg
            | Ok (_, r') -> Ok (a, r'))
(*
    Running (p >> b) means "run p, then run b. If both succeed, return the
    output of b." Also commonly written "*>".
*)
let ( >> ) (p : 'a parser) (q : 'b parser) : 'b parser =
    fun s ->
        match p s with
        | Error msg -> Error msg
        | Ok (_, t) -> q t
(*
    Running (star p) means "run p until p fails, storing successes in a list."
    Never fails; one can think of it as running p "0 or more times." Named after
    the Kleene star (as found in regex); this parser is commonly called "many."
*)                   
let star (p : 'a parser) : ('a list) parser =
    fun s ->
        let rec f (xs : 'a list) (s : bookmark) =
            match p s with
            | Error _ -> Ok (List.rev xs, s)
            | Ok (x, s') -> f (x :: xs) s'
        in f [] s
(*
    Running (plus p) means "run p, then if p succeeds, run until p fails,
    storing all successes in a list." Fails only if the initial p fails;
    one can think of it as running p "1 or more times." Named after the
    Kleene plus (as found in regex); this parser is commonly called "many1."
*)
let plus (p : 'a parser) : ('a list) parser =
    (List.cons <$> p) <*> star p
(*
    The eof parser succeeds if all input has been consumed.
    A more general parser library would use "unit parser" or similar
    instead of "char list parser."
*)
let eof : char list parser =
    fun s ->
        (match snd s < String.length (fst s) with
        | true -> Error ("Expected end of input.")
        | false -> Ok ([], s))
(*
    Succeeds if a char matches a specified char.
*)
let charms (c : char) : char parser = satisfy (Char.equal c)
(*
    Succeeds if a char matches any of a list of specified chars.
*)
let rec among (cs' : char list) : char parser =
    match cs' with
    | c :: cs -> charms c <|> among cs
    | [] -> fail
(*
    Succeeds if a char is a whitespace character.
*)
let whitespace : char parser = charms ' ' <|> charms '\n' <|> charms '\t'
(*
    Does what it says on the tin.
*)
let is_digit (c : char) : bool =
    match c with
    | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> true
    | _ -> false
(*
    Succeeds on a sequence of 1 or more digits.
*)
let index' : string parser =
    (fun cs -> String.of_seq (List.to_seq cs)) <$> plus (satisfy is_digit)
(*
    Succeeds on a sequence of 1 or more digits, consuming any whitespace
    which follows. Fails if said sequence is *not* followed
    by whitespace or eof.
*)
let index : string parser = index' << ((plus whitespace) <|> eof)
(*
    Succeeds on a parenthesized expression. 
*)
let parexp' : string parser =
    fun s ->
        let right_paren (s : bookmark) : int =
            let sign (s : bookmark) : int =
                match snapshot s with
                | Some '(' -> 1
                | Some ')' -> -1
                | _ -> 0 in
            let rec f (n : int) (s : bookmark) : int =
                let adv = advance s in
                match n with
                | 0 -> snd s
                | _ ->
                    match eof adv with
                    | Ok (_, _) -> -1
                    | Error _ -> f (n + (sign adv)) adv
            in f 1 s in
        match charms '(' s with
        | Error msg -> Error msg
        | Ok (_, _) ->
            let n = right_paren s in
            match n <= 0 with
            | true -> Error "Malformed parentheses."
            | false -> Ok (String.sub (fst s) (snd s) (n - (snd s) + 1), (fst s, n + 1))
(*
    Succeeds on a parenthesized expression, consuming any whitespace
    which follows. Fails if said expression is *not* followed by
    whitespace or eof.
*)
let parexp : string parser = parexp' << ((plus whitespace) <|> eof)
(*
    Succeeds if a char is part of the base alphabet of
    (this formulation of) lambda calculus. 
*)
let alphabet : char parser =
    (satisfy is_digit <|> whitespace <|> among ['('; ')'; '.'])
(*
    Collects characters which trigger the failure of
    a given char parser (while not collecting duplicates).
*)
let collect_failures (p : char parser) (s' : bookmark) : char list =
    let rec f (cs : char list) (s : bookmark) : char list =
        match eof s with
        | Ok (_, _) -> cs
        | Error _ ->
            (match plus (p <|> among cs) s with
            | Ok (xs, t) -> f cs t
            | Error _ -> f ((snapshot' s) :: cs) (advance s)) in
    f [] s'
(*
    Defines a collection of "syntactic sugar symbols" which
    extend the alphabet of the lambda calculus; outputs a
    string with said symbols expanded into lambda terms.
    Fails upon finding characters which are in neither
    the base nor the extended alphabet.
*)
let expand : string parser =
    fun t ->
    let g (s : string) (c : char) : string option =
        let f s' t : string = Str.global_replace (Str.regexp s') t s in
        match c with
        | '+' -> Some (f {|\+|}"(4.4 2 (3 2 1))")
        | '*' -> Some (f {|\*|}"(4.4 (3 2) 1)")
        | '&' -> Some (f {|&|} "(2.2 1 2)")
        | '|' -> Some (f {|\||} "(2.1 1 2)")
        | '~' -> Some (f {|~|} "(1.1 (2.2) (2.1))")
        | '?' -> Some (f {|?|} "(3.3 2 1)") (* If-then-else. *)
        | 'K' -> Some (f {|K|} "(2.2)")
        | 'Z' -> Some (f {|Z|} "(2.1)") (* "Z" is for "zero."*)
        | 'N' -> Some (f {|N|} "(3.2 (3 2 1))") (* Successor. "N" is for "next." *)
        | 'I' -> Some (f {|I|} "(1.1)")
        | 'S' -> Some (f {|S|} "(3.3 1 (2 1))")
        | 'M' -> Some (f {|M|} "(1.1 1)")
        | 'W' -> Some (f {|W|} "(2.2 1 1)")
        | 'B' -> Some (f {|B|} "(3.3 (2 1))")
        | 'C' -> Some (f {|C|} "(3.3 1 2)")
        | 'T' -> Some (f {|T|} "(2.1 2)")
        | 'Y' -> Some (f {|Y|} "(2.2 (1 1) (1.2 (1 1)))")
        | _ -> None in
    let rec f (cs' : char list) (s' : string) =
        match cs' with
        | c :: cs ->
            (match (g s' c) with
            | Some x -> f cs x
            | None -> None)
        | [] -> Some s' in
    match f (collect_failures alphabet t) (fst t) with
    | Some x -> Ok (x, t)
    | None -> Error "Syntax error."
(*
    "Peels" the outer layer of parentheses off a string
    if said string has such an outer layer of parentheses.
    If not, returns the string as is.
*)
let peel (s : string) : string =
    if String.starts_with ~prefix:"(" s && String.ends_with ~suffix:")" s
    then String.sub s 1 (String.length s - 2)
    else s
(*
    Parses a string directly to the lambda-term AST.
*)
let parse : tm parser = fun s ->
    let rec f (s : bookmark) : tm =
        match (index' << charms '.') s with
        | Ok (s', t) -> nlam (int_of_string s') (f t)
        | Error _ ->
            match (charms '\\' >> charms '.') s with
            | Ok (_, t) -> Lam (f t)
            | Error _ ->
                match (index' << eof) s with
                | Ok (i, _) -> Ind (int_of_string i)
                | Error _ ->
                    match plus (index <|> parexp) s with
                    | Error _ -> failwith "Syntax error."
                    | Ok (xs, _) ->
                        match List.map peel xs with
                        | x :: ys ->
                            List.fold_left (fun m n -> App (m, n)) (f (x, 0))
                            (List.map f (List.map (fun s -> (s, 0)) ys))
                        | [] -> failwith "Syntax error." in
    try Ok (f s, s) with Failure msg -> Error msg
let process_full (s : bookmark) : string =
    match expand s with
    | Ok (s', _) -> 
        (match parse (s', 0) with
        | Ok (t, _) -> stringify (normalize t)
        | Error msg -> msg)
    | Error msg -> msg
type command =
    | Full of string
    | Quit
let rec starts_among (xs : string list) (s : string) : bool =
    match xs with
    | y :: ys -> String.starts_with ~prefix: y s || starts_among ys s
    | [] -> false
let get_command (s : string) : command =
    match starts_among [":q"; ":quit"] s with
    | true -> Quit
    | false -> Full (process_full (s, 0))