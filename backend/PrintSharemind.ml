
(** Pretty-printers for Sharemind code *)

open Printf
open Camlcoq
open Datatypes
open AST
open Sharemind
open Maps

(* Printing of Sharemind code *)

let print_data pp (n,dta) =
  match dta with
  | Data_string str -> fprintf pp ":%s .data string \"%s\"\n" (extern_atom n) (camlstring_of_coqstring str)
  | Data_uint8 i    -> fprintf pp ":%s .data uint8 %ld\n" (extern_atom n) (camlint_of_coqint i)

let print_ast_ext pp ((efname,ef): (ident * AST.external_function)) =
  match ef with
  | EF_external (n,sg) -> fprintf pp ":%s .bind \"%s\"\n" (extern_atom efname) (camlstring_of_coqstring n)
  | EF_builtin (name,sg) -> fprintf pp "<unsupported builtin %s>\n" (camlstring_of_coqstring name)
  | EF_runtime (name,sg) -> fprintf pp "<unsupported runtime %s>\n" (camlstring_of_coqstring name)
  | EF_vload (chunk) -> fprintf pp "<unsupported vload>\n"
  | EF_vstore (chunk) -> fprintf pp "<unsupported vstore>\n"
  | EF_malloc -> fprintf pp "<unsupported malloc>\n"
  | EF_free -> fprintf pp "<unsupported free>"
  | EF_memcpy (sz,al) -> fprintf pp "<unsupported memcpy>\n"
  | EF_annot (kind,text,targs) -> fprintf pp "<unsupported annot>\n"
  | EF_annot_val (kind,text,targ) -> fprintf pp "<unsupported annot_val>\n"
  | EF_inline_asm (text,sg,clobbers) -> fprintf pp "<unsupported inline_asm>\n"
  | EF_debug (kind,text,targs) -> fprintf pp "<unsupported debug>\n"

let print_shm_ext pp ((efname,ef) : (ident * Sharemind.external_function)) = 
    fprintf pp ":%s .bind \"%s\"\n" (extern_atom efname) (camlstring_of_coqstring ef)

let print_idx pp (i:index) = fprintf pp "0x%Lx" (N.to_int64 i)

let print_lbl pp s = fprintf pp ":%s" (extern_atom s)

(* print as an imm value, in hexadecimal *)
let print_val pp v = 
    match v with
    | Init_int8 i -> fprintf pp "0x%lx" (camlint_of_coqint i)
    | Init_int16 i -> fprintf pp "0x%lx" (camlint_of_coqint i)
    | Init_int32 i -> fprintf pp "0x%lx" (camlint_of_coqint i)
    | Init_int64 i -> fprintf pp "0x%Lx" (camlint64_of_coqint i)
    | Init_float32 f -> fprintf pp "<unsupported float32>"
    | Init_float64 f -> fprintf pp "<unsupported float64>"
    | Init_space z -> fprintf pp "<unsupported space>"
    | Init_addrof (id,off) -> fprintf pp "<unsupported addrof>"

let print_loc_val pp (lv:location_val) = 
    match lv with
    | Imm (Coq_inl v) -> fprintf pp "imm %a" print_val v
    | Imm (Coq_inr lbl) -> fprintf pp "imm %a" print_lbl lbl
    | Reg idx -> fprintf pp "reg %a" print_idx idx
    | Stack idx -> fprintf pp "stack %a" print_idx idx 

let print_off pp off = print_loc_val pp off

let print_loc_ref pp (lr:location_ref) =
    match lr with
    | Ref (idx) -> fprintf pp "ref %a" print_idx idx 
    | Cref (idx) -> fprintf pp "cref %a" print_idx idx 
    | Mem (lv) -> fprintf pp "mem %a" print_loc_val lv 

let print_loc_mov pp (l:location_mov) = 
    match l with
    | MV lv -> print_loc_val pp lv
    | MR (lr,off) -> fprintf pp "%a %a" print_loc_ref lr print_off off
    
let print_loc pp (l:location) = 
    match l with
    | LV lv -> print_loc_val pp lv
    | LR lr -> print_loc_ref pp lr

let print_type pp (ty) = 
    match ty with
    | Uint8   -> fprintf pp "uint8"
    | Uint16  -> fprintf pp "uint16"
    | Uint32  -> fprintf pp "uint32"
    | Uint64  -> fprintf pp "uint64"
    | Int8    -> fprintf pp "int8"
    | Int16   -> fprintf pp "int16"
    | Int32   -> fprintf pp "int32"
    | Int64   -> fprintf pp "int64"
    | Float32 -> fprintf pp "float32"
    | Float64 -> fprintf pp "float64"
    | Bool    -> fprintf pp "bool"

let print_opt printv pp opt = match opt with
    | Some v -> printv pp v
    | None -> ()

let print_instr pp (i:instruction) = 
    match i with
    
    | Ipush a -> fprintf pp "push %a\n" print_loc_val a
    | Ipushref a -> fprintf pp "pushref %a\n" print_loc a
    | Ipushrefpart (a,off,bytes) -> fprintf pp "pushrefpart %a %a %a\n" print_loc a print_off off print_loc_val bytes
    | Ipushcref a -> fprintf pp "pushcref %a\n" print_loc a
    | Ipushcrefpart (a,off,bytes) -> fprintf pp "pushcrefpart %a %a %a\n" print_loc a print_off off print_loc_val bytes
    | Imov (fromv,tov,bytes) -> fprintf pp "mov %a %a %a\n" print_loc_mov fromv print_loc_mov tov (print_opt print_loc_val) bytes
    | Icall (fn,Some ret) -> fprintf pp "call %a %a\n" print_loc_val fn print_loc_val ret
    | Icall (fn,None) -> fprintf pp "call %a imm\n" print_loc_val fn
    | Isyscall (fn,Some ret) -> fprintf pp "syscall %a %a\n" print_loc_val fn print_loc_val ret
    | Isyscall (fn,None) -> fprintf pp "syscall %a imm\n" print_loc_val fn
    | Ialloc (a,bytes) -> fprintf pp "alloc %a %a\n" print_loc_val a print_loc_val bytes
    | Ifree a -> fprintf pp "free %a\n" print_loc_val a
    | Igetmemsize (a,b) -> fprintf pp "getmemsize %a %a\n" print_loc_val a print_loc_val b
    | Iresizestack n -> fprintf pp "resizestack %a\n" print_val n
    | Ilabel lbl -> fprintf pp "%a\n" print_lbl lbl
    | Ireturn ret -> fprintf pp "return %a\n" print_loc_val ret
    | Ihalt ret -> fprintf pp "halt %a\n" print_loc_val ret
    | Iuser_except -> fprintf pp "user_except\n"
    | Iconvert (ty1,v1,ty2,v2) -> fprintf pp "convert %a %a %a %a\n" print_type ty1 print_loc_val v1 print_type ty2 print_loc_val v2
    
    | Iudec (ty,v) -> fprintf pp "udec %a %a\n" print_type ty print_loc_val v
    | Iuinc (ty,v) -> fprintf pp "uinc %a %a\n" print_type ty print_loc_val v
    
    | Ibadd (ty,v1,v2) -> fprintf pp "badd %a %a %a\n" print_type ty print_loc_val v1 print_loc_val v2
    | Ibsub (ty,v1,v2) -> fprintf pp "bsub %a %a %a\n" print_type ty print_loc_val v1 print_loc_val v2
    
    | Itadd (ty,v1,v2,v3) -> fprintf pp "tadd %a %a %a %a\n" print_type ty print_loc_val v1 print_loc_val v2 print_loc_val v3
    | Itsub (ty,v1,v2,v3) -> fprintf pp "tsub %a %a %a %a\n" print_type ty print_loc_val v1 print_loc_val v2 print_loc_val v3
    | Itmul (ty,v1,v2,v3) -> fprintf pp "tmul %a %a %a %a\n" print_type ty print_loc_val v1 print_loc_val v2 print_loc_val v3
    
    | Ijmp dest -> fprintf pp "jmp %a\n" print_loc_val dest
    | Ijz    (d,t,v) -> fprintf pp "jz %a %a %a\n"     print_loc_val d print_type t print_loc_val v
    | Ijnz   (d,t,v) -> fprintf pp "jnz %a %a %a\n"    print_loc_val d print_type t print_loc_val v
    | Idnjz  (d,t,v) -> fprintf pp "jdnjz %a %a %a\n"  print_loc_val d print_type t print_loc_val v
    | Idnjnz (d,t,v) -> fprintf pp "jdnjnz %a %a %a\n" print_loc_val d print_type t print_loc_val v
    | Ijeq (d,t,v1,v2) -> fprintf pp "jeq %a %a %a %a\n" print_loc_val d print_type t print_loc_val v1 print_loc_val v2
    | Ijne (d,t,v1,v2) -> fprintf pp "jne %a %a %a %a\n" print_loc_val d print_type t print_loc_val v1 print_loc_val v2
    | Ijge (d,t,v1,v2) -> fprintf pp "jge %a %a %a %a\n" print_loc_val d print_type t print_loc_val v1 print_loc_val v2
    | Ijgt (d,t,v1,v2) -> fprintf pp "jgt %a %a %a %a\n" print_loc_val d print_type t print_loc_val v1 print_loc_val v2
    | Ijle (d,t,v1,v2) -> fprintf pp "jle %a %a %a %a\n" print_loc_val d print_type t print_loc_val v1 print_loc_val v2
    | Ijlt (d,t,v1,v2) -> fprintf pp "jlt %a %a %a %a\n" print_loc_val d print_type t print_loc_val v1 print_loc_val v2
    
    | Iteq (t,d,v1,v2) -> fprintf pp "teq %a %a %a %a\n" print_type t print_loc_val d print_loc_val v1 print_loc_val v2
    | Itne (t,d,v1,v2) -> fprintf pp "tne %a %a %a %a\n" print_type t print_loc_val d print_loc_val v1 print_loc_val v2
    | Itge (t,d,v1,v2) -> fprintf pp "tge %a %a %a %a\n" print_type t print_loc_val d print_loc_val v1 print_loc_val v2
    | Itgt (t,d,v1,v2) -> fprintf pp "tgt %a %a %a %a\n" print_type t print_loc_val d print_loc_val v1 print_loc_val v2
    | Itle (t,d,v1,v2) -> fprintf pp "tle %a %a %a %a\n" print_type t print_loc_val d print_loc_val v1 print_loc_val v2
    | Itlt (t,d,v1,v2) -> fprintf pp "tlt %a %a %a %a\n" print_type t print_loc_val d print_loc_val v1 print_loc_val v2
    
    | Ibtand (t,d,v1,v2) -> fprintf pp "btand %a %a %a %a\n" print_type t print_loc_val d print_loc_val v1 print_loc_val v2
    | Itshr0 (t,d,v1,v2) -> fprintf pp "tshr0 %a %a %a %a\n" print_type t print_loc_val d print_loc_val v1 print_loc_val v2

let print_pd pp (pdname,pd) = 
    fprintf pp ":%s .bind \"%s\"\n" (extern_atom pdname) (camlstring_of_coqstring pd)

let print_block pp (lbl,is) = 
    fprintf pp ":%s\n" (extern_atom lbl);
    List.iter (print_instr pp) is;
    fprintf pp "\n"

let sortedElements pt = List.sort
    (fun (pc1, _) (pc2, _) -> Pervasives.compare pc2 pc1)
    (PTree.elements pt)

let print_program pp (print_ef) (prog) =
    fprintf pp ".section PDBIND\n";
    List.iter (print_pd pp) (sortedElements prog.prog_pds);
    fprintf pp ".section BIND\n";
    List.iter (print_ef pp) (sortedElements prog.prog_exts);
    fprintf pp ".section RODATA\n";
    List.iter (print_data pp) (PTree.elements prog.prog_rodata);
    fprintf pp ".section DATA\n";
    fprintf pp ".section TEXT\n\n";
    List.iter (print_instr pp) prog.prog_init;
    fprintf pp "\n";
    List.iter (print_block pp) (sortedElements prog.prog_code)

let destination : string option ref = ref None

let print_if (passno:int) print_ef prog =
  match !destination with
  | None -> ()
  | Some f ->
      let str = Printf.sprintf "%s.%d" f passno in
      let oc = open_out str in
      print_program oc print_ef prog;
      close_out oc

 