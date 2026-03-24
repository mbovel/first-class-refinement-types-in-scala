Require Import SystemF.systemf.
Require Import Extraction.

(* Set up extraction to OCaml *)
Extraction Language OCaml.

(* Configure standard type extractions to use OCaml built-ins *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].

(* Extract nat to int with simple pattern matching *)
Extract Inductive nat => "int" [ "0" "((+) 1)" ]
  "(fun zero succ -> function 0 -> zero () | n -> succ (n-1))".

Set Extraction AutoInline.

(* Extract the eval function *)
Extraction "systemf_eval.ml" eval.
