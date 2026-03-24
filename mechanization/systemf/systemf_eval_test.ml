open Systemf_eval

let rec print_term t =
  match t with
  | Tbool b -> string_of_bool b
  | Tvar i -> "var" ^ string_of_int i
  | Tabs (_, body) -> "λ." ^ print_term body
  | Tapp (f, a) -> "(" ^ print_term f ^ " " ^ print_term a ^ ")"
  | Ttabs body -> "Λ." ^ print_term body
  | Ttapp (f, _) -> print_term f ^ "[]"

let print_value v =
  match v with
  | Vbool b -> string_of_bool b
  | Vabs (env, body) -> "λ<" ^ string_of_int (List.length env) ^ ">." ^ print_term body
  | Vtabs (env, body) -> "Λ<" ^ string_of_int (List.length env) ^ ">." ^ print_term body

let print_result name result =
  match result with
  | None -> Printf.printf "%s -> timeout\n" name
  | Some None -> Printf.printf "%s -> stuck\n" name
  | Some (Some v) -> Printf.printf "%s -> %s\n" name (print_value v)

let () =
  Printf.printf "Testing System F eval function:\n\n";

  (* Test 1: Basic boolean *)
  let test1 = Tbool true in
  let result1 = eval 10 [] test1 in
  print_result "true" result1;

  (* Test 2: Identity function \x:Bool. x *)
  let test2 = Tabs (TBool, Tvar 0) in
  let result2 = eval 10 [] test2 in
  print_result "\\x:Bool. x" result2;

  (* Test 3: Application (\x:Bool. x) true *)
  let id_fun = Tabs (TBool, Tvar 0) in
  let test3 = Tapp (id_fun, Tbool true) in
  let result3 = eval 10 [] test3 in
  print_result "(\\x:Bool. x) true" result3;

  (* Test 4: Variable lookup failure *)
  let test4 = Tvar 0 in
  let result4 = eval 10 [] test4 in
  print_result "var0 (unbound variable)" result4;

  (* Test 5: Polymorphic identity /\X. \x:X. x *)
  let test5 = Ttabs (Tabs (TVar 0, Tvar 0)) in
  let result5 = eval 10 [] test5 in
  print_result "/\\X. \\x:X. x" result5;

  (* Test 6: Type application (/\X. \x:X. x)[Bool] *)
  let poly_id = Ttabs (Tabs (TVar 0, Tvar 0)) in
  let test6 = Ttapp (poly_id, TBool) in
  let result6 = eval 10 [] test6 in
  print_result "(/\\X. \\x:X. x)[Bool]" result6;

  (* Test 7: Full polymorphic application (/\X. \x:X. x)[Bool] true *)
  let test7 = Tapp (test6, Tbool true) in
  let result7 = eval 10 [] test7 in
  print_result "(/\\X. \\x:X. x)[Bool] true" result7;

  (* Test 8: Timeout case with insufficient fuel *)
  let test8 = Tapp (id_fun, Tbool true) in
  let result8 = eval 0 [] test8 in
  print_result "(\\x:Bool. x) true with 0 fuel" result8;

  Printf.printf "\nDone!\n"
