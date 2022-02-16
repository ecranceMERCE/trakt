(*******************************************************************************)
(*                           *                     Trakt                       *)
(*  _______        _    _    *            Copyright (C) 2022 MERCE             *)
(* |__   __|      | |  | |   *     (Mitsubishi Electric R&D Centre Europe)     *)
(*    | |_ __ __ _| | _| |_  *        Enzo Crance <enzo.crance@inria.fr>       *)
(*    | | '__/ _` | |/ / __| ***************************************************)
(*    | | | | (_| |   <| |_  * This file is distributed under the terms of the *)
(*    |_|_|  \__,_|_|\_\\__| *   GNU Lesser General Public License Version 3   *)
(*                           *  (see LICENSE file for the text of the license) *)
(*******************************************************************************)

From elpi Require Import elpi.

From Trakt Require Import InternalProofs.

Elpi Command Trakt.

Elpi Accumulate File "elpi/types.elpi".
Elpi Typecheck.

From Trakt Require Export Database.
Elpi Accumulate Db embeddings.db.
Elpi Accumulate Db symbols.db.
Elpi Accumulate Db relations.db.
Elpi Accumulate Db conversion.db.

Elpi Accumulate File "elpi/common.elpi".
Elpi Typecheck.

Elpi Accumulate File "elpi/commands.elpi".
Elpi Typecheck.

Elpi Accumulate lp:{{
  pred elaborate-argument i:argument, o:argument.

  elaborate-argument (trm T) (trm ET) :-
    !, coq.elaborate-skeleton T _ ET ok.

  elaborate-argument A A.

  pred operation i:string, i:string, o:(list argument -> prop).

  operation "Add" "Embedding" add-embedding.
  operation "Add" "Symbol" add-symbol.
  operation "Add" "Relation" add-relation.
  operation "Add" "Conversion" add-conversion-allowed.

  main [str Command, str Element|RecordData] :-
    operation Command Element Op, !,
    std.assert! (std.map RecordData elaborate-argument ERecordData) "arguments are ill-typed",
    Op ERecordData.
  
  main _ :-
    coq.error {std.string.concat "\n" [
      "command syntax error",
      "usage: Trakt Add (Embedding|Symbol|Relation|Conversion) ...", "", ""
    ]}.
}}.
Elpi Typecheck.
Elpi Export Trakt.
