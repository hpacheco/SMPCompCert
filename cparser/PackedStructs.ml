(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Emulation of #pragma pack (experimental) *)

open Printf
open C
open Cutil
open Env
open Errors

type field_info = {
  fi_offset: int;                       (* byte offset within struct *)
  fi_swap: ikind option                 (* Some ik if byte-swapped *)
}

(* Mapping from (struct name, field name) to field_info.
   Only fields of packed structs are mentioned in this table. *)

let packed_fields : (ident * string, field_info) Hashtbl.t
                  = Hashtbl.create 57

(* The current packing parameters.  The first two are 0 if packing is
   turned off. *)

let max_field_align = ref 0
let min_struct_align = ref 0
let byte_swap_fields = ref false

(* Alignment *)

let is_pow2 n =
  n > 0 && n land (n - 1) == 0

let align x boundary =
  assert (is_pow2 boundary);
  (x + boundary - 1) land (lnot (boundary - 1))

(* Layout algorithm *)

let layout_struct mfa msa swapped loc env struct_id fields =
  let rec layout max_al pos = function
  | [] ->
      (max_al, pos)
  | f :: rem -> 
      if f.fld_bitfield <> None then
        error "%a: Error: bitfields in packed structs not allowed"
              formatloc loc;
      let swap =
        if swapped then begin
          match unroll env f.fld_typ with
          | TInt(ik, _) ->
              if sizeof_ikind ik = 1 then None else Some ik
          | _ ->
              error "%a: Error: byte-swapped fields must have integer type"
                    formatloc loc;
              None
        end else
          None in
      let (sz, al) =
        match sizeof env f.fld_typ, alignof env f.fld_typ with
        | Some s, Some a -> (s, a)
        | _, _ -> error "%a: struct field has incomplete type" formatloc loc;
                  (0, 1) in
      let al1 = min al mfa in
      let pos1 = align pos al1 in
      Hashtbl.add packed_fields
         (struct_id, f.fld_name)
         {fi_offset = pos1; fi_swap = swap};
      let pos2 = pos1 + sz in
      layout (max max_al al1) pos2 rem in
  let (al, sz) = layout 1 0 fields in
  if al >= msa then
    (0, sz)
  else
    (msa, align sz msa)

(* Rewriting of struct declarations *)

let transf_composite loc env su id attrs ml =
  match su with
  | Union -> (attrs, ml)
  | Struct ->
      let (mfa, msa, swapped) =
        if !max_field_align > 0 then
          (!max_field_align, !min_struct_align, !byte_swap_fields)
        else if find_custom_attributes ["packed";"__packed__"] attrs <> [] then
          (1, 0, false)
        else
          (0, 0, false) in
      if mfa = 0 then (attrs, ml) else begin
        let (al, sz) = layout_struct mfa msa swapped loc env id ml in
        let attrs =
          if al = 0 then attrs else
            add_attributes [Attr("__aligned__", [AInt(Int64.of_int al)])] attrs
        and field =
          {fld_name = "__payload";
           fld_typ = TArray(TInt(IChar, []), Some(Int64.of_int sz), []);
           fld_bitfield = None}
        in (attrs, [field])
      end

(* Accessor functions *)

let lookup_function loc env name =
  try
    match Env.lookup_ident env name with
    | (id, II_ident(sto, ty)) -> (id, ty)
    | (id, II_enum _) -> raise (Env.Error(Env.Unbound_identifier name))
  with Env.Error msg ->
    fatal_error "%a: Error: %s" formatloc loc (Env.error_message msg)

(*  (ty) e *)
let ecast ty e = {edesc = ECast(ty, e); etyp = ty}

(*  *e  *)
let ederef ty e = {edesc = EUnop(Oderef, e); etyp = ty}

(*  e + n *)
let eoffset e n =
  {edesc = EBinop(Oadd, e, intconst (Int64.of_int n) IInt, e.etyp);
   etyp = e.etyp}

(*  *((ty * ) (base.__payload + offset))  *)
let dot_packed_field base pf ty =
  let payload =
    {edesc = EUnop(Odot "__payload", base);
     etyp = TArray(TInt(IChar,[]),None,[]) } in
  ederef ty (ecast (TPtr(ty, [])) (eoffset payload pf.fi_offset))

(*  *((ty * ) (base->__payload + offset))  *)
let arrow_packed_field base pf ty =
  let payload =
    {edesc = EUnop(Oarrow "__payload", base);
     etyp = TArray(TInt(IChar,[]),None,[]) } in
  ederef ty (ecast (TPtr(ty, [])) (eoffset payload pf.fi_offset))

(*  (ty) __builtin_read_intNN_reversed(&lval)  *)
let bswap_read loc env lval ik =
  let uik = unsigned_ikind_of ik in
  let bsize = sizeof_ikind ik * 8 in
  let (id, fty) =
    lookup_function loc env (sprintf "__builtin_read_int%d_reversed" bsize) in
  let fn = {edesc = EVar id; etyp = fty} in
  let args =
    if uik = ik
    then [eaddrof lval]
    else [ecast (TPtr(TInt(uik,[]),[])) (eaddrof lval)] in
  let call = {edesc = ECall(fn, args); etyp = TInt(uik, [])} in
  if ik = uik then call else ecast (TInt(ik,[])) call

(*  __builtin_write_intNN_reversed(&lhs,rhs)  *)
let bswap_write loc env lhs rhs ik =
  let uik = unsigned_ikind_of ik in
  let bsize = sizeof_ikind ik * 8 in
  let (id, fty) =
    lookup_function loc env (sprintf "__builtin_write_int%d_reversed" bsize) in
  let fn = {edesc = EVar id; etyp = fty} in
  let args =
    if uik = ik
    then [eaddrof lhs; rhs]
    else [ecast (TPtr(TInt(uik,[]),[])) (eaddrof lhs);
          ecast (TInt(uik,[])) rhs] in
  {edesc = ECall(fn, args); etyp = TVoid[]}

(* Expressions *)

type context = Val | Effects

let transf_expr loc env ctx e =

  let is_packed_access ty fieldname =
    match unroll env ty with
    | TStruct(id, _) ->
        (try Some(Hashtbl.find packed_fields (id, fieldname))
         with Not_found -> None)
    | _ -> None in

  let is_packed_access_ptr ty fieldname =
    match unroll env ty with
    | TPtr(ty', _) -> is_packed_access ty' fieldname
    | _ -> None in 

  (* Transformation of l-values.  Return transformed expr plus
     [Some ik] if l-value is a byte-swapped field of kind [ik]
     or [None] otherwise. *)
  let rec lvalue e =
    match e.edesc with
    | EUnop(Odot fieldname, e1) ->
        let e1' = texp Val e1 in
        begin match is_packed_access e1.etyp fieldname with
        | None ->
            ({edesc = EUnop(Odot fieldname, e1'); etyp = e.etyp}, None)
        | Some pf ->
            (dot_packed_field e1' pf e.etyp, pf.fi_swap)
        end
    | EUnop(Oarrow fieldname, e1) ->
        let e1' = texp Val e1 in
        begin match is_packed_access_ptr e1.etyp fieldname with
        | None ->
            ({edesc = EUnop(Oarrow fieldname, e1'); etyp = e.etyp}, None)
        | Some pf ->
            (arrow_packed_field e1' pf e.etyp, pf.fi_swap)
        end
    | _ ->
        (texp Val e, None) 

  and texp ctx e =
    match e.edesc with
    | EConst _ -> e
    | ESizeof _ -> e
    | EVar _ -> e

    | EUnop(Odot _, _) | EUnop(Oarrow _, _) ->
        let (e', swap) = lvalue e in
        begin match swap with
        | None -> e'
        | Some ik -> bswap_read loc env e' ik
        end

    | EUnop((Oaddrof|Opreincr|Opredecr|Opostincr|Opostdecr as op), e1) ->
        let (e1', swap) = lvalue e1 in
        if swap <> None then
          error "%a: Error: &, ++ and -- over byte-swap field are not supported"
                formatloc loc;
        {edesc = EUnop(op, e1'); etyp = e.etyp}

    | EUnop(op, e1) ->
        {edesc = EUnop(op, texp Val e1); etyp = e.etyp}

    | EBinop(Oassign, e1, e2, ty) ->
        let (e1', swap) = lvalue e1 in
        let e2' = texp Val e2 in
        begin match swap with
        | None ->
            {edesc = EBinop(Oassign, e1', e2', ty); etyp = e.etyp}
        | Some ik ->
            if ctx <> Effects then
              error "%a: Error: assignment over byte-swapped field in value context is not supported"
                    formatloc loc;
            bswap_write loc env e1' e2' ik
        end

    | EBinop((Oadd_assign|Osub_assign|Omul_assign|Odiv_assign|Omod_assign|
              Oand_assign|Oor_assign|Oxor_assign|Oshl_assign|Oshr_assign as op),
              e1, e2, ty) ->
        let (e1', swap) = lvalue e1 in
        let e2' = texp Val e2 in
        if swap <> None then
          error "%a: Error: op-assignment over byte-swapped field in value context is not supported"
                formatloc loc;
        {edesc = EBinop(op, e1', e2', ty); etyp = e.etyp}

    | EBinop(Ocomma, e1, e2, ty) ->
        {edesc = EBinop(Ocomma, texp Effects e1, texp Val e2, ty);
         etyp = e.etyp}

    | EBinop(op, e1, e2, ty) ->
        {edesc = EBinop(op, texp Val e1, texp Val e2, ty); etyp = e.etyp}

    | EConditional(e1, e2, e3) ->
        {edesc = EConditional(texp Val e1, texp ctx e2, texp ctx e3);
         etyp = e.etyp}

    | ECast(ty, e1) ->
        {edesc = ECast(ty, texp Val e1); etyp = e.etyp}

    | ECall(e1, el) ->
        {edesc = ECall(texp Val e1, List.map (texp Val) el); etyp = e.etyp}

  in texp ctx e

(* Statements *)

let rec transf_stmt env s =
  match s.sdesc with
  | Sskip -> s
  | Sdo e ->
      {sdesc = Sdo(transf_expr s.sloc env Effects e); sloc = s.sloc}
  | Sseq(s1, s2) -> 
      {sdesc = Sseq(transf_stmt env s1, transf_stmt env s2); sloc = s.sloc }
  | Sif(e, s1, s2) ->
      {sdesc = Sif(transf_expr s.sloc env Val e,
                   transf_stmt env s1, transf_stmt env s2);
       sloc = s.sloc}
  | Swhile(e, s1) ->
      {sdesc = Swhile(transf_expr s.sloc env Val e, transf_stmt env s1);
       sloc = s.sloc}
  | Sdowhile(s1, e) ->
      {sdesc = Sdowhile(transf_stmt env s1, transf_expr s.sloc env Val e);
       sloc = s.sloc}
  | Sfor(s1, e, s2, s3) ->
      {sdesc = Sfor(transf_stmt env s1, transf_expr s.sloc env Val e,
                    transf_stmt env s2, transf_stmt env s3);
       sloc = s.sloc}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {sdesc = Sswitch(transf_expr s.sloc env Val e,
                       transf_stmt env s1); sloc = s.sloc}
  | Slabeled(lbl, s) ->
      {sdesc = Slabeled(lbl, transf_stmt env s); sloc = s.sloc}
  | Sgoto lbl -> s
  | Sreturn None -> s
  | Sreturn (Some e) ->
      {sdesc = Sreturn(Some(transf_expr s.sloc env Val e)); sloc = s.sloc}
  | Sblock _ | Sdecl _ ->
      assert false     (* should not occur in unblocked code *)

(* Functions *)

let transf_fundef env f =
  { f with fd_body = transf_stmt env f.fd_body }

(* Initializers *)

let rec check_init i =
  match i with
  | Init_single e -> true
  | Init_array il -> List.for_all check_init il
  | Init_struct(id, fld_init_list) ->
      List.for_all
        (fun (f, i) ->
          not (Hashtbl.mem packed_fields (id, f.fld_name)))
        fld_init_list
  | Init_union(id, fld, i) ->
      check_init i

(* Declarations *)

let transf_decl loc env (sto, id, ty, init_opt as decl) =
  begin match init_opt with
  | None -> () 
  | Some i ->
      if not (check_init i) then
        error "%a: Error: Initialization of packed structs is not supported"
              formatloc loc
  end;
  decl

(* Pragmas *)

let re_pack = Str.regexp "pack\\b"
let re_pack_1 = Str.regexp "pack[ \t]*(\\([ \t0-9,]*\\))[ \t]*$"
let re_comma = Str.regexp ",[ \t]*"

let process_pragma loc s =
  if Str.string_match re_pack s 0 then begin
    if Str.string_match re_pack_1 s 0 then begin
      let arg = Str.matched_group 1 s in
      let (mfa, msa, bs) =
        match List.map int_of_string (Str.split re_comma arg) with
        | [] -> (0, 0, false)
        | [x] -> (x, 0, false)
        | [x;y] -> (x, y, false)
        | x :: y :: z :: _ -> (x, y, z = 1) in
      if mfa = 0 || is_pow2 mfa then
        max_field_align := mfa
      else
        error "%a: Error: In #pragma pack, max field alignment must be a power of 2" formatloc loc;
      if msa = 0 || is_pow2 msa then
        min_struct_align := msa
      else
        error "%a: Error: In #pragma pack, min struct alignment must be a power of 2" formatloc loc;
      byte_swap_fields := bs;
      true
    end else begin
      warning "%a: Warning: Ill-formed #pragma pack, ignored" formatloc loc;
      false
    end
  end else
    false

(* Global declarations *)

let rec transf_globdecls env accu = function
  | [] -> List.rev accu
  | g :: gl ->
      match g.gdesc with
      | Gdecl((sto, id, ty, init) as d) ->
          transf_globdecls
            (Env.add_ident env id sto ty)
            ({g with gdesc = Gdecl(transf_decl g.gloc env d)} :: accu)
            gl
      | Gfundef f ->
          transf_globdecls
            (Env.add_ident env f.fd_name f.fd_storage (fundef_typ f))
            ({g with gdesc = Gfundef(transf_fundef env f)} :: accu)
            gl
      | Gcompositedecl(su, id, attr) ->
          transf_globdecls
            (Env.add_composite env id (composite_info_decl env su attr))
            (g :: accu)
            gl
      | Gcompositedef(su, id, attr, fl) ->
          let (attr', fl') = transf_composite g.gloc env su id attr fl in
          transf_globdecls
            (Env.add_composite env id (composite_info_def env su attr' fl'))
            ({g with gdesc = Gcompositedef(su, id, attr', fl')} :: accu)
            gl
      | Gtypedef(id, ty) ->
          transf_globdecls
            (Env.add_typedef env id ty)
            (g :: accu)
            gl
      | Genumdef _  ->
          transf_globdecls
            env
            (g :: accu)
            gl
      | Gpragma p ->
          if process_pragma g.gloc p
          then transf_globdecls env accu gl
          else transf_globdecls env (g :: accu) gl

(* Program *)

let program p =
  min_struct_align := 0;
  max_field_align := 0;
  byte_swap_fields := false;
  transf_globdecls (Builtins.environment()) [] p