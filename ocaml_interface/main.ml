
let filename = "example.txt"    

let read_lines name : string list =
  let ic = open_in name in
  let try_read () =
    try Some (input_line ic) with End_of_file -> None in
  let rec loop acc = match try_read () with
    | Some s -> loop (s :: acc)
    | None -> close_in ic; List.rev acc in
  loop []
  
let rec print_list = function 
[] -> ()
| e::l -> print_string e ; print_string "\n" ; print_list l
  
let () = 
try
    let lines = read_lines filename in
    print_list lines;
    flush stdout;
    let res = check_loop
with e -> raise e
