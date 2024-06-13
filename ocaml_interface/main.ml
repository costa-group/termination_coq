let filename = "example_2.txt"    

let read_lines name : string list =
  let ic = open_in name in
  let try_read () =
    try Some (input_line ic) with End_of_file -> None in
  let rec loop acc = match try_read () with
    | Some s -> loop (s :: acc)
    | None -> close_in ic; List.rev acc in
  loop []
  
let explode s : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

  
let rec print_list = function 
[] -> ()
| e::l -> print_string e ; print_string "\n" ; print_list l
  
let () = 
try
    let lines = read_lines filename in
    let res = Parser.check_loop (List.map Parser.tokenize (List.map explode lines))   in
    (**print_list(entrada);**)
    print_string("Resultado: ");
    if res then print_string("Todo correcto\n") else print_string("Ha ocurrido un error\n");
    flush stdout
with e -> raise e
