
(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun zero succ -> function 0 -> zero () | n -> succ (n-1))
    (fun _ -> match l with
              | [] -> None
              | x::_ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _::l' -> nth_error l' n0)
    n

type var = int

type ('t1, 't2) _bind = 't2

type ty =
| TVar of var
| TBool
| TFun of ty * ty
| TForall of (ty, ty) _bind

type term =
| Tbool of bool
| Tvar of int
| Tabs of ty * term
| Tapp of term * term
| Ttabs of term
| Ttapp of term * ty

type value =
| Vbool of bool
| Vabs of value list * term
| Vtabs of value list * term

type valueEnv = value list

(** val eval : int -> valueEnv -> term -> value option option **)

let rec eval fuel env t =
  (fun zero succ -> function 0 -> zero () | n -> succ (n-1))
    (fun _ -> None)
    (fun fuel0 ->
    match t with
    | Tbool b -> Some (Some (Vbool b))
    | Tvar i -> Some (nth_error env i)
    | Tabs (_, b) -> Some (Some (Vabs (env, b)))
    | Tapp (f, a) ->
      (match eval fuel0 env f with
       | Some o ->
         (match o with
          | Some v ->
            (match v with
             | Vabs (envf, b) ->
               (match eval fuel0 env a with
                | Some o0 ->
                  (match o0 with
                   | Some va -> eval fuel0 (va::envf) b
                   | None -> Some None)
                | None -> None)
             | _ -> Some None)
          | None -> Some None)
       | None -> None)
    | Ttabs b -> Some (Some (Vtabs (env, b)))
    | Ttapp (f, _) ->
      (match eval fuel0 env f with
       | Some o ->
         (match o with
          | Some v ->
            (match v with
             | Vtabs (envf, b) -> eval fuel0 envf b
             | _ -> Some None)
          | None -> Some None)
       | None -> None))
    fuel
