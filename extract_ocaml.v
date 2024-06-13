From Coq Require Import Strings.String.
Require Import List.
Import ListNotations.
Require Import parser.
Import Parser.
From Coq Require Import extraction.ExtrOcamlString.
Import ExtrOcamlString.

(** Type Extractions **)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "( , )" ].
Extract Inductive sumbool => "bool" ["true" "false"].

Extraction Parser.
Extraction "ocaml_interface/checker.ml" Parser. 
