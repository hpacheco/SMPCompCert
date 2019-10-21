

Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Sharemind.
Require Import Values Globalenvs.

(**
    Translates RTL code to Sharemind VM code
    * Allocates C function stack and global variables as Sharemind dynamic memory
    * Converts C function calls to Sharemind stack machine calls
    * Simulates the C contiguous memory model in the Sharemind block-based memory model
**)

Definition mergeOption {A: Type} (ox oy: option A) : option A :=
    match ox with
    | Some x => Some x
    | None => oy
    end.
    
Definition mergePTree {A: Type} (p1 p2: PTree.t A) : PTree.t A :=
    PTree.combine mergeOption p1 p2.

Definition singlePTree {A: Type} (p: (ident * A)) : PTree.t A :=
    PTree.set (fst p) (snd p) (PTree.empty A).

Definition show_typ (t: typ) : string :=
  match t with
  | Tint    => "int" 
  | Tfloat  => "float" 
  | Tlong   => "long" 
  | Tsingle => "single" 
  | Tany32  => "any32" 
  | Tany64  => "any64"
  end.

Definition show_opt_typ (mbt: option typ) : string :=
  match mbt with
  | Some t => show_typ t
  | None => ""
  end.
  
Fixpoint show_typ_list (ts: list typ) : string :=
  match ts with
  | nil => ""
  | cons x xs => show_typ x ++ " " ++ show_typ_list xs
  end.
  
Definition show_bool (b: bool) : string :=
  match b with
  | false => "false"
  | true => "true"
  end.
  
Definition show_cc (cc: calling_convention) : string :=
    show_bool cc.(cc_vararg) ++ " " ++ show_bool cc.(cc_unproto) ++ " " ++ show_bool cc.(cc_structret).

Definition show_sig (s: signature) : string :=
    show_typ_list s.(sig_args) ++ " -> " ++ show_opt_typ s.(sig_res) ++ " " ++ show_cc s.(sig_cc).

Definition show_external_function (ef: AST.external_function) : string :=
    match ef with
    | EF_external n sg => "external " ++ n++" "++show_sig sg
    | EF_builtin n sg => "bultin " ++ n++" "++show_sig sg
    | EF_runtime n sg => "runtime " ++ n++" "++show_sig sg
    | EF_vload (chunk) => "vload"
    | EF_vstore (chunk) => "vstore"
    | EF_malloc => "malloc"
    | EF_free => "free"
    | EF_memcpy  sz al => "memcpy"
    | EF_annot kind text targs => "annot"
    | EF_annot_val kind text targ => "annot_val"
    | EF_inline_asm text sg clobbers => "inline_asm"
    | EF_debug kind text targs => "debug"
    end.
    
Fixpoint show_external_functions (efs : list AST.external_function) : string :=
  match efs with
  | nil => ""
  | cons x xs => show_external_function x ++ "\\n" ++ show_external_functions xs
  end.

(* State monad, copied from RTLgen *)

Record state: Type := mkstate {
  st_globvars : list (ident * index); (* mapping from global variable names to their register index *)
  st_nextglob : index; (* number of used global registers index of next global variable *)
  st_freeglobs : list index; (* already used but now free global registers *)
  st_initcode : Sharemind.code; (* global register initialization code *)
  st_deinitcode : Sharemind.code; (* global register free code *)
  st_exts : PTree.t AST.external_function;
  st_funs : PTree.t Sharemind.code (* code for function definitions *)
}.

Inductive res (A: Type) (s: state): Type :=
  | Error: Errors.errmsg -> res A s
  | OK: A -> state -> res A s.

Arguments OK [A s].
Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret {A: Type} (x: A) : mon A :=
  fun (s: state) => OK x s.

Definition error {A: Type} (msg: Errors.errmsg) : mon A := fun (s: state) => Error msg.

Definition error_string {A: Type} (str: string) : mon A := error (Errors.msg str).

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' =>
        match g a s' with
        | Error msg => Error msg
        | OK b s'' => OK b s'' 
        end
    end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).

Parameter intern_string : string -> ident.
Parameter intern_keyword : string -> ident.
Parameter intern_node : ident -> node -> ident.

Definition intern_RODATA : ident := intern_keyword "RODATA".

(* convenience stack variables *)
Definition stack0 : location_val := Stack 0%N.
Definition stack1 : location_val := Stack 1%N.
Definition stack2 : location_val := Stack 2%N.

(* The first three registers are reserved for memory operations *)
Definition reg0 : location_val := Reg 0%N.
Definition reg1 : location_val := Reg 1%N.
Definition reg2 : location_val := Reg 2%N.

Definition maxPTree {A: Type} (pt: PTree.t A) : positive :=
    List.fold_right Pos.max xH (List.map fst (PTree.elements pt)).

Definition positiveToNat (i: positive) : nat := Pos.to_nat i.
Definition positiveFromNat (n: nat) : positive := Pos.of_nat n.

Fixpoint decreasingPTreeElements' {A: Type} (pt: PTree.t A) (n: nat) : list (positive * A) :=
    let i := positiveFromNat n in
    match n with
    | O => nil
    | S n' =>
        match PTree.get i pt with
        | Some x => (i,x) :: decreasingPTreeElements' pt n'
        | None => decreasingPTreeElements' pt n'
        end
    end.

Definition decreasingPTreeElements {A: Type} (pt: PTree.t A) : list (positive * A) :=
    decreasingPTreeElements' pt (positiveToNat (maxPTree pt)).

Definition state_init : state :=
  mkstate nil (3%N) nil nil nil (PTree.empty AST.external_function) (PTree.empty Sharemind.code).
  
Definition get_numglobs : mon index :=
    fun s =>
        let nglobs := s.(st_nextglob) in
        OK nglobs s.
  
Definition inc_nextglob : mon index :=
    fun s =>
        let frees := s.(st_freeglobs) in
        match frees with
        | nil => 
            let n := s.(st_nextglob) in
            OK n (mkstate s.(st_globvars) (N.succ n) frees s.(st_initcode) s.(st_deinitcode) s.(st_exts) s.(st_funs) )
        | cons n frees' =>
            OK n (mkstate s.(st_globvars) s.(st_nextglob) frees' s.(st_initcode) s.(st_deinitcode) s.(st_exts) s.(st_funs) )
        end.

Definition add_freeglob (n: index) : mon unit :=
    fun s => 
        let frees := s.(st_freeglobs) in
        let frees' := n :: frees in
        OK tt (mkstate s.(st_globvars) s.(st_nextglob) frees' s.(st_initcode) s.(st_deinitcode) s.(st_exts) s.(st_funs) ).
  
(* Temporarily reserves a global register *)
Definition with_glob {A: Type} (go: index -> mon A) : mon A :=
    do n <- inc_nextglob;
    do a <- go n;
    do tt <- add_freeglob n;
    ret a.

(* Registers a new global variable *)  
Definition state_new_globvar (name: ident) : mon index :=
  fun s => 
    let gvs := s.(st_globvars) in
    let n := s.(st_nextglob) in
    OK n (mkstate ((name,n) :: gvs) (N.succ n) s.(st_freeglobs) s.(st_initcode) s.(st_deinitcode) s.(st_exts) s.(st_funs) ).

Fixpoint lookup_globvar (k: ident) (l: list (ident * index)) : option index :=
      match l with
        | nil => None
        | (a,b) :: tl => if Pos.eqb a k then Some b else lookup_globvar k tl
      end.

Definition state_find_globvar (name: ident) : mon index :=
  fun s =>
    let gvs := s.(st_globvars) in
    match (lookup_globvar name gvs) with
    | Some igv => OK igv s
    | None => Error (Errors.MSG "could not find global variable" :: Errors.CTX name :: nil)
    end.

Fixpoint lookup_ext (ef: AST.external_function) (l: list (ident * AST.external_function)) : option ident :=
      match l with
        | nil => None
        | (a,b) :: tl => if external_function_eq b ef then Some a else lookup_ext ef tl
      end.

Definition state_find_builtin (ef: AST.external_function) : mon (ident) :=
    fun s =>
        let exts := s.(st_exts) in
        let efs := List.map snd (PTree.elements exts) in
        match (lookup_ext ef (PTree.elements exts)) with
        | Some ext => OK ext s
        | None => Error (Errors.msg ("could not find builtin "++show_external_function ef ++ " in \\n" ++ show_external_functions efs))
        end.

Definition state_ins_code (ic ec: code) : mon unit :=
  fun s => 
    let init := s.(st_initcode) in
    let free := s.(st_deinitcode) in
    OK tt (mkstate (s.(st_globvars)) s.(st_nextglob) s.(st_freeglobs) (init ++ ic) (free ++ ec) s.(st_exts) s.(st_funs) ).

Definition state_ins_ext (lbl: ident) (ef: AST.external_function) : mon unit :=
  fun s => 
    let efs := s.(st_exts) in
    let efs' := PTree.set lbl ef efs in
    OK tt (mkstate s.(st_globvars) s.(st_nextglob) s.(st_freeglobs) s.(st_initcode) s.(st_deinitcode) efs' s.(st_funs) ).

Definition state_ins_block (n: ident) (f: Sharemind.code) : mon unit :=
  fun s => 
    let fs := s.(st_funs) in
    let fs' := PTree.set n f fs in
    OK tt (mkstate (s.(st_globvars)) s.(st_nextglob) s.(st_freeglobs) s.(st_initcode) s.(st_deinitcode) s.(st_exts) fs' ).

Definition get_state : mon state :=
  fun s => OK s s.

(* Number of regs used in a function declaration *)

Fixpoint list_max_reg (rs: list reg) : Z :=
    match rs with
    | nil => Z0
    | cons x xs =>
        let m1 := Zpos x in
        let m2 := list_max_reg xs in
        Z.max m1 m2
    end.

Fixpoint builtin_arg_max_reg (ba:builtin_arg reg) : Z :=
    match ba with
    | BA x => Zpos x
    | BA_int n => Z0
    | BA_long (n) => Z0
    | BA_float (f) => Z0
    | BA_single (f) => Z0
    | BA_loadstack chunk pofs => Z0
    | BA_addrstack ofs => Z0
    | BA_loadglobal chunk id ofs => Z0
    | BA_addrglobal id ofs => Z0
    | BA_splitlong hi lo => Z.max (builtin_arg_max_reg hi) (builtin_arg_max_reg lo)
    | BA_addptr a1 a2 => Z.max (builtin_arg_max_reg a1) (builtin_arg_max_reg a2)
    end.
    
Fixpoint builtin_args_max_reg (rs: list (builtin_arg reg)) : Z :=
    match rs with
    | nil => Z0
    | cons x xs =>
        let m1 := builtin_arg_max_reg x in
        let m2 := builtin_args_max_reg xs in
        Z.max m1 m2
    end.

Fixpoint builtin_res_max_reg (ba: builtin_res reg) : Z :=
    match ba with
    | BR x => Zpos x
    | BR_none => Z0
    | BR_splitlong hi lo => Z.max (builtin_res_max_reg hi) (builtin_res_max_reg lo)
    end.

Definition sum_max_reg (ex: reg + ident) : Z :=
    match ex with
    | inl r => Zpos r
    | inr _ => Z0
    end.

Definition option_max_reg (mbx: option reg) : Z :=
    match mbx with
    | None => Z0
    | Some x => Zpos x
    end.

Definition instruction_max_reg (i: RTL.instruction) : Z :=
    match i with
    | Inop _ => Z0
    | Iop _ args res _ => Z.max (Zpos res) (list_max_reg args)
    | Iload _ _ args res _ => Z.max (Zpos res) (list_max_reg args)
    | Istore _ _ args res node => Z.max (Zpos res) (list_max_reg args)
    | RTL.Icall _ regident args res _ => Z.max (sum_max_reg regident) (list_max_reg (res :: args))
    | Itailcall _ regident regs => Z.max (sum_max_reg regident) (list_max_reg regs)
    | Ibuiltin _ bargs bres _ => Z.max (builtin_args_max_reg bargs) (builtin_res_max_reg bres)
    | Icond _ args _ _ => list_max_reg args
    | Ijumptable reg _ => Zpos reg
    | RTL.Ireturn (mbreg) => option_max_reg mbreg
    end.

Fixpoint instructions_max_reg (is: list RTL.instruction) : Z :=
    match is with
    | nil => Z0
    | cons x xs => Z.max (instruction_max_reg x) (instructions_max_reg xs)
    end.

Definition function_max_reg (f: RTL.function) : Z :=
    let m1 := list_max_reg f.(fn_params) in
    let m2 := instructions_max_reg (List.map snd (PTree.elements f.(fn_code))) in
    Z.max m1 m2.

(* RTL to Sharemind translation *)

Definition rtlglobdef: Type := AST.globdef RTL.fundef unit.
Definition rtlglobvar: Type := AST.globvar unit.

(* RTL registers always go into the sharemind register stack *)
Definition transl_reg (r: reg) : location_val :=
    Stack (Npos r).

Definition transl_ident (id: ident) : location_val :=
    Imm (inr id).
    
Definition transl_string (str: string) : location_val :=
    Imm (inr (intern_string str)).
    
Definition transl_node (name: ident) (n: node) : location_val :=
    Imm (inr (intern_node name n)).
    
Definition transl_int (i: int) : location_val :=
    Imm (inl (Init_int32 i)).
Definition transl_int64 (i: int64) : location_val :=
    Imm (inl (Init_int64 i)).
    
Definition transl_float32 (i: float32) : location_val :=
    Imm (inl (Init_float32 i)).
Definition transl_float (i: float) : location_val :=
    Imm (inl (Init_float64 i)).
    
Definition imm_int (i: int) : location_val := transl_int i.
Definition imm_int64 (i: int64) : location_val := transl_int64 i.

Definition imm_float32 (i: float32) : location_val := transl_float32 i.
Definition imm_float (i: float) : location_val := transl_float i.

(* assumes 64-bit memory addresses *)
Definition transl_addressing32 (addr: addressing) (args: list reg) (dest: location_val) : mon Sharemind.code :=
    match (addr,args) with
    | (Aindexed off,r1::nil) =>
        ret (Itadd Int32 dest (transl_reg r1) (imm_int (Int.repr off)) :: nil)
    | (Aindexed2 off,r1::r2::nil) =>
        let code := Itadd Int32 dest (transl_reg r1) (imm_int (Int.repr off))
                 :: Ibadd Int32 dest (transl_reg r2)
                 :: nil in
        ret code
    | (Ascaled sc off,r1::nil) =>
        let code := Itmul Int32 dest (transl_reg r1) (imm_int (Int.repr sc))
                 :: Ibadd Int32 dest (imm_int (Int.repr off))
                 :: nil in
        ret code
    | (Aindexed2scaled sc off,r1::r2::nil) =>
        let code := Itmul Int32 dest (transl_reg r2) (imm_int (Int.repr sc))
                 :: Ibadd Int32 dest (imm_int (Int.repr off))
                 :: Ibadd Int32 dest (transl_reg r1)
                 :: nil in
        ret code
    | (Aglobal sym off,nil) => error_string "unsupported addressing32 Aglobal"
    | (Abased _ _,_) => error_string "unsupported addressing32 Abased"
    | (Abasedscaled _ _ _,_) => error_string "unsupported addressing32 Abasedscaled"
    | (Ainstack off,nil) => error_string "unsupported addressing32 Ainstack"
    | _ => error_string "unsupported addressing32"
    end.

(* assumes 64-bit memory addresses *)
Definition transl_addressing64 (addr: addressing) (args: list reg) (dest: location_val) : mon Sharemind.code :=
    match (addr,args) with
    | (Aindexed off,r1::nil) =>
        ret (Itadd Int64 dest (transl_reg r1) (imm_int64 (Int64.repr off)) :: nil)
    | (Aindexed2 off,r1::r2::nil) =>
        let code := Itadd Int64 dest (transl_reg r1) (imm_int64 (Int64.repr off))
                 :: Ibadd Int64 dest (transl_reg r2)
                 :: nil in
        ret code
    | (Ascaled sc off,r1::nil) =>
        let code := Itmul Int64 dest (transl_reg r1) (imm_int64 (Int64.repr sc))
                 :: Ibadd Int64 dest (imm_int64 (Int64.repr off))
                 :: nil in
        ret code
    | (Aindexed2scaled sc off,r1::r2::nil) =>
        let code := Itmul Int64 dest (transl_reg r2) (imm_int64 (Int64.repr sc))
                 :: Ibadd Int64 dest (imm_int64 (Int64.repr off))
                 :: Ibadd Int64 dest (transl_reg r1)
                 :: nil in
        ret code
    | (Aglobal sym off,nil) => 
        do isym <- state_find_globvar sym;
        let code := Itadd Int64 dest (Reg isym) (imm_int64 (Int64.repr (Ptrofs.intval off)))
                 :: nil in
        ret code
    | (Abased _ _,_) => error_string "unsupported addressing64 Abased"
    | (Abasedscaled _ _ _,_) => error_string "unsupported addressing64 Abasedscaled"
    | (Ainstack off,nil) =>
        let code := Itadd Int64 dest stack0 (imm_int64 (Int64.repr (Ptrofs.intval off)))
                 :: nil in
        ret code
    | _ => error_string "unsupported addressing64"
    end.

Definition transl_condition (jump : bool) (cond: Op.condition) (args: list reg) (fcmp: Integers.comparison -> type -> location_val -> location_val -> Sharemind.instruction) : mon Sharemind.code :=
    match (cond,args) with
    | (Ccomp c,v1::v2::nil) => ret (fcmp c Int32 (transl_reg v1) (transl_reg v2) :: nil)
    | (Ccompu c,v1::v2::nil) => ret (fcmp c Uint32 (transl_reg v1) (transl_reg v2) :: nil)
    | (Ccompimm c n,v::nil) => if jump
        then ret (fcmp (swap_comparison c) Int32 (transl_int n) (transl_reg v) :: nil)
        else ret (fcmp c Int32 (transl_reg v) (transl_int n) :: nil)
    | (Ccompuimm c n,v::nil) => if jump
        then ret (fcmp (swap_comparison c) Uint32 (transl_int n) (transl_reg v) :: nil)
        else ret (fcmp c Uint32 (transl_reg v) (transl_int n) :: nil)
    | (Ccompl c,v1::v2::nil) => ret (fcmp c Int64 (transl_reg v1) (transl_reg v2) :: nil)
    | (Ccomplu c,v1::v2::nil) => ret (fcmp c Uint64 (transl_reg v1) (transl_reg v2) :: nil)
    | (Ccomplimm c n,v::nil) => if jump
        then ret (fcmp (swap_comparison c) Int64 (transl_int64 n) (transl_reg v) :: nil)
        else ret (fcmp c Int64 (transl_reg v) (transl_int64 n) :: nil)
    | (Ccompluimm c n,v::nil) => if jump
        then ret (fcmp (swap_comparison c) Uint64 (transl_int64 n) (transl_reg v) :: nil)
        else ret (fcmp c Uint64 (transl_reg v) (transl_int64 n) :: nil)
    | (Ccompf c,v1::v2::nil) => ret (fcmp c Float64 (transl_reg v1) (transl_reg v2) :: nil)
    | (Cnotcompf c,v1::v2::nil) => ret (fcmp (negate_comparison c) Float64 (transl_reg v1) (transl_reg v2) :: nil)
    | (Ccompfs c,v1::v2::nil) => ret (fcmp c Float32 (transl_reg v1) (transl_reg v2) :: nil)
    | (Cnotcompfs c,v1::v2::nil) => ret (fcmp (negate_comparison c) Float32 (transl_reg v1) (transl_reg v2) :: nil)
    | (Cmaskzero n,v::nil) => with_glob (fun glob =>
        let cmask := Ibtand Uint32 (Reg glob) (transl_reg v) (imm_int n) in
        let ccmp := fcmp Ceq Int32 (Reg glob) (imm_int64 (Int64.repr 0)) in
        ret (cmask :: ccmp :: nil))
    | (Cmasknotzero n,v::nil) => with_glob (fun glob =>
        let cmask := Ibtand Uint32 (Reg glob) (transl_reg v) (imm_int n) in
        let ccmp := fcmp Cne Int32 (Reg glob) (imm_int64 (Int64.repr 0)) in
        ret (cmask :: ccmp :: nil))
    | _ => error_string "<unsupported condition>\n"
    end.

Definition transl_cmp_bool (cmp: Integers.comparison) : (Sharemind.comparison_bool) :=
    match cmp with
    | Ceq => Iteq
    | Cne => Itne
    | Clt => Itlt
    | Cle => Itle
    | Cgt => Itgt
    | Cge => Itge
    end.

Definition transl_op (name: ident) (op: operation) (args: list reg) (dest: reg) : mon (Sharemind.code) :=
    match (op,args) with
    | (Omove,v1::nil) => ret (Imov (MV (transl_reg v1)) (MV (transl_reg dest)) None :: nil)
    | (Ointconst i,nil) => ret (Imov (MV (imm_int i)) (MV (transl_reg dest)) None :: nil)
    | (Olongconst i,nil) => ret (Imov (MV (imm_int64 i)) (MV (transl_reg dest)) None :: nil)
    | (Ofloatconst f,nil) => ret (Imov (MV (imm_float f)) (MV (transl_reg dest)) None :: nil)
    | (Osingleconst f,nil) => ret (Imov (MV (imm_float32 f)) (MV (transl_reg dest)) None :: nil)
    | (Oindirectsymbol id,_) => error_string "<unsupported operation Oindirectsymbol>\n"
    | (Ocast8signed,r1::nil) => ret (Iconvert Int8 (transl_reg r1) Int32 (transl_reg dest) :: nil)
    | (Ocast8unsigned,r1::nil) => ret (Iconvert Uint8 (transl_reg r1) Uint32 (transl_reg dest) :: nil)
    | (Ocast16signed,r1::nil) => ret (Iconvert Int16 (transl_reg r1) Int32 (transl_reg dest) :: nil)
    | (Ocast16unsigned,r1::nil) => ret (Iconvert Uint16 (transl_reg r1) Uint32 (transl_reg dest) :: nil)
    | (Oneg,_) => error_string "<unsupported operation Oneg>\n"
    | (Osub,_) => error_string "<unsupported operation Osub>\n"
    | (Omul,_) => error_string "<unsupported operation Omul>\n"
    | (Omulimm n,_) => error_string "<unsupported operation Omulimm>\n"
    | (Omulhs,_) => error_string "<unsupported operation Omulhs>\n"
    | (Omulhu,_) => error_string "<unsupported operation Omulhu>\n"
    | (Odiv,_) => error_string "<unsupported operation Odiv>\n"
    | (Odivu,_) => error_string "<unsupported operation Odivu>\n"
    | (Omod,_) => error_string "<unsupported operation Omod>\n"
    | (Omodu,_) => error_string "<unsupported operation Omodu>\n"
    | (Oand,_) => error_string "<unsupported operation Oand>\n"
    | (Oandimm n,_) => error_string "<unsupported operation Oandimm>\n"
    | (Oor,_) => error_string "<unsupported operation Oor>\n"
    | (Oorimm n,_) => error_string "<unsupported operation Oorimm>\n"
    | (Oxor,_) => error_string "<unsupported operation Oxor>\n"
    | (Oxorimm n,_) => error_string "<unsupported operation Oxorimm>\n"
    | (Onot,_) => error_string "<unsupported operation Onot>\n"
    | (Oshl,_) => error_string "<unsupported operation Oshl>\n"
    | (Oshlimm n,_) => error_string "<unsupported operation Oshlimm>\n"
    | (Oshr,_) => error_string "<unsupported operation Oshr>\n"
    | (Oshrimm n,_) => error_string "<unsupported operation Oshrimm>\n"
    | (Oshrximm n,_) => error_string "<unsupported operation Oshrximm>\n"
    | (Oshru,_) => error_string "<unsupported operation Oshru>\n"
    | (Oshruimm n,_) => error_string "<unsupported operation Oshruimm>\n"
    | (Ororimm n,_) => error_string "<unsupported operation Ororimm>\n"
    | (Oshldimm n,_) => error_string "<unsupported operation Oshldimm>\n"
    | (Olea a,args) => transl_addressing32 a args (transl_reg dest)
    | (Omakelong,_) => error_string "<unsupported operation Omakelong>\n"
    | (Olowlong,r1::nil) => ret (Iconvert Uint64 (transl_reg r1) Uint32 (transl_reg dest) :: nil) 
    | (Ohighlong,r1::nil) => ret (Itshr0 Uint64 (transl_reg dest) (transl_reg r1) (imm_int64 (Int64.repr 32)) :: nil )
    | (Ocast32signed,r1::nil) => ret (Iconvert Int32 (transl_reg r1) Int64 (transl_reg dest) :: nil)
    | (Ocast32unsigned,r1::nil) => ret (Iconvert Uint32 (transl_reg r1) Uint64 (transl_reg dest) :: nil)
    | (Onegl,_) => error_string "<unsupported operation Onegl>\n"
    | (Oaddlimm n,_) => error_string "<unsupported operation Oaddlimm>\n"
    | (Osubl,_) => error_string "<unsupported operation Osubl>\n"
    | (Omull,_) => error_string "<unsupported operation Omull>\n"
    | (Omullimm n,_) => error_string "<unsupported operatio Omullimmn>\n"
    | (Omullhs,_) => error_string "<unsupported operation Omullhs>\n"
    | (Omullhu,_) => error_string "<unsupported operation Omullhu>\n"
    | (Odivl,_) => error_string "<unsupported operation Odivl>\n"
    | (Odivlu,_) => error_string "<unsupported operation Odivlu>\n"
    | (Omodl,_) => error_string "<unsupported operation Omodl>\n"
    | (Omodlu,_) => error_string "<unsupported operation Omodlu>\n"
    | (Oandl,_) => error_string "<unsupported operation Oandl>\n"
    | (Oandlimm n,_) => error_string "<unsupported operation Oandlimm>\n"
    | (Oorl,_) => error_string "<unsupported operation Oorl>\n"
    | (Oorlimm n,_) => error_string "<unsupported operation Oorlimm>\n"
    | (Oxorl,_) => error_string "<unsupported operation Oxorl>\n"
    | (Oxorlimm n,_) => error_string "<unsupported operation Oxorlimm>\n"
    | (Onotl,_) => error_string "<unsupported operation Onotl>\n"
    | (Oshll,_) => error_string "<unsupported operation Oshll>\n"
    | (Oshllimm n,_) => error_string "<unsupported operation Oshllimm>\n"
    | (Oshrl,_) => error_string "<unsupported operation Oshrl>\n"
    | (Oshrlimm n,_) => error_string "<unsupported operation Oshrlimm>\n"
    | (Oshrxlimm n,_) => error_string "<unsupported operation Oshrxlimm>\n"
    | (Oshrlu,_) => error_string "<unsupported operation Oshrlu>\n"
    | (Oshrluimm n,_) => error_string "<unsupported operation Oshrluimm>\n"
    | (Ororlimm n,_) => error_string "<unsupported operation Ororlimm>\n"
    | (Oleal a,args) => transl_addressing64 a args (transl_reg dest)
    | (Onegf,_)  => error_string "<unsupported operation Onegf  >\n"
    | (Oabsf,_)  => error_string "<unsupported operation Oabsf  >\n"
    | (Oaddf,_)  => error_string "<unsupported operation Oaddf  >\n"
    | (Osubf,_)  => error_string "<unsupported operation Osubf  >\n"
    | (Omulf,_)  => error_string "<unsupported operation Omulf  >\n"
    | (Odivf,_)  => error_string "<unsupported operation Odivf  >\n"
    | (Onegfs,_) => error_string "<unsupported operation Onegfs >\n"
    | (Oabsfs,_) => error_string "<unsupported operation Oabsfs >\n"
    | (Oaddfs,_) => error_string "<unsupported operation Oaddfs >\n"
    | (Osubfs,_) => error_string "<unsupported operation Osubfs >\n"
    | (Omulfs,_) => error_string "<unsupported operation Omulfs >\n"
    | (Odivfs,_) => error_string "<unsupported operation Odivfs >\n"
    | (Osingleoffloat,r1::nil) => ret (Iconvert Float32 (transl_reg r1) Float64 (transl_reg dest) :: nil)
    | (Ofloatofsingle,r1::nil) => ret (Iconvert Float64 (transl_reg r1) Float32 (transl_reg dest) :: nil)
    | (Ointoffloat,r1::nil) => ret (Iconvert Float64 (transl_reg r1) Int32 (transl_reg dest) :: nil)
    | (Ofloatofint,r1::nil) => ret (Iconvert Int32 (transl_reg r1) Float64 (transl_reg dest) :: nil)
    | (Ointofsingle,r1::nil) => ret (Iconvert Float32 (transl_reg r1) Int32 (transl_reg dest) :: nil)
    | (Osingleofint,r1::nil) => ret (Iconvert Int32 (transl_reg r1) Float32 (transl_reg dest) :: nil)
    | (Olongoffloat,r1::nil) => ret (Iconvert Float64 (transl_reg r1) Int64 (transl_reg dest) :: nil)
    | (Ofloatoflong,r1::nil) => ret (Iconvert Int64 (transl_reg r1) Float64 (transl_reg dest) :: nil)
    | (Olongofsingle,r1::nil) => ret (Iconvert Float32 (transl_reg r1) Int64 (transl_reg dest) :: nil)
    | (Osingleoflong,r1::nil) => ret (Iconvert Int64 (transl_reg r1) Float32 (transl_reg dest) :: nil)
    | (Ocmp c,args) => transl_condition false c args (fun c ty => transl_cmp_bool c ty (transl_reg dest))
    | (Osel _ _,_) => error_string "<unsupported operation Osel>\n"
    | _ => error_string "<unsupported operation>"
    end.

(* assumes 64-bit addressing *)
Definition transl_load (chunk: memory_chunk) (addr: addressing) (args: list reg) (dest: location_val) : mon Sharemind.code := 
    with_glob (fun glob =>
        do caddr <- transl_addressing64 addr args (Reg glob);
        let sz := imm_int64 (Int64.repr (AST.chunk_size chunk)) in
        let cload := Ipush (Reg glob)
                  :: Icall (transl_string "moffset") None
                  :: Imov (MR (Mem reg0) reg1) (MV dest) (Some sz)
                  :: nil in
        ret (caddr ++ cload)).

(* assumes 64-bit addressing *)
Definition transl_store (chunk: memory_chunk) (addr: addressing) (args: list reg) (src: location_val) : mon Sharemind.code := 
    with_glob (fun glob =>
        do caddr <- transl_addressing64 addr args (Reg glob);
        let sz := imm_int64 (Int64.repr (AST.chunk_size chunk)) in
        let cstore := Ipush (Reg glob)
                   :: Icall (transl_string "moffset") None
                   :: Imov (MV src) (MR (Mem reg0) reg1) (Some sz)
                   :: nil in
        ret (caddr ++ cstore)).

Fixpoint transl_call_args' (args: list reg) : mon Sharemind.code :=
    match args with
    | nil => ret nil
    | cons x xs =>
        let c1 := Ipush (transl_reg x) in
        do c2 <- transl_call_args' xs;
        ret (c1 :: c2)
    end.

(* Pushes arguments into the register stack. *)
(* Note that RTL function arguments are always translated to Sharemind registers, i.e., values by reference are only used for builtin Sharemind calls. *)
Definition transl_call_args (args: list reg) : mon Sharemind.code :=
    (* pushes dummy value to function stack position (will be overwritten by allocation on function execution) *)
    let c0 := Ipush (Imm (inl (Init_int64 (Int64.repr Z0)))) in
    (* push arguments in reverse order *)
    do cargs <- transl_call_args' (List.rev args);
    ret (c0 :: cargs).

(* Translates an internal function call *)
Definition transl_call (sg: signature) (fn: reg + ident) (args: list reg) (dest: location_val) : mon Sharemind.code :=
    do cargs <- transl_call_args args;
    let sfn := match fn with
        | inl r => transl_reg r
        | inr n => Imm (inr n)
        end in 
    let sret := Some dest in
    let ccall := Icall sfn sret in
    ret (cargs ++ ccall :: nil).

Fixpoint transl_builtin_arg_action (arg: builtin_arg reg) (action : location_val -> Sharemind.instruction) : mon Sharemind.code :=
    match arg with
    | BA r => ret (action (transl_reg r) :: nil)
    | BA_int i => ret (action (imm_int i) :: nil)
    | BA_long i => ret (action (imm_int64 i) :: nil)
    | BA_float f => ret (action (imm_float f) :: nil)
    | BA_single f => ret (action (imm_float32 f) :: nil)
    | BA_loadstack chunk ofs => with_glob (fun glob =>
        do cload <- transl_load chunk (Ainstack ofs) nil (Reg glob);
        let cpush := action (Reg glob) in
        ret (cload ++ cpush :: nil))
    | BA_addrstack ofs => with_glob (fun glob =>
        let cadd := Itadd Uint64 (Reg glob) stack0 (imm_int64 (Int64.repr (Ptrofs.intval ofs))) in
        let cpush := action (Reg glob) in
        ret (cadd :: cpush :: nil))
    | BA_loadglobal chunk id ofs => with_glob (fun glob =>
        do cload <- transl_load chunk (Aglobal id ofs) nil (Reg glob);
        let cpush := action (Reg glob) in
        ret (cload ++ cpush :: nil))
    | BA_addrglobal id ofs => with_glob (fun glob =>
        do iid <- state_find_globvar id;
        let cadd := Itadd Int64 (Reg glob) (Reg iid) (imm_int64 (Int64.repr (Ptrofs.intval ofs))) in
        let cpush := action (Reg glob) in
        ret (cadd :: cpush :: nil))
    | BA_splitlong hi lo => error_string "BA_splitlong builtin_arg unsupported"
    | BA_addptr a1 a2 => with_glob (fun glob =>
        let cinit := Imov (MV (imm_int64 (Int64.repr 0))) (MV (Reg glob)) None in
        do c1 <- transl_builtin_arg_action a1 (Ibadd Uint64 (Reg glob));
        do c2 <- transl_builtin_arg_action a2 (Ibadd Uint64 (Reg glob));
        ret (cinit :: c1 ++ c2 ++ action (Reg glob) :: nil))
    end.

Definition transl_builtin_arg (arg: builtin_arg reg) : mon Sharemind.code :=
    transl_builtin_arg_action arg Ipush.

Fixpoint transl_builtin_args (args: list (builtin_arg reg)) : mon Sharemind.code :=
    match args with
    | nil => ret nil
    | cons x xs =>
        do c1 <- transl_builtin_arg x;
        do c2 <- transl_builtin_args xs;
        ret (c1 ++ c2)
    end.

Definition transl_builtin_res (res : builtin_res reg) : mon (option location_val) :=
    match res with
    | BR r => ret (Some (transl_reg r))
    | BR_none => ret None
    | BR_splitlong hi lo => error_string "splitlong builtin not supported"
    end.

(* These will be later bound to actual Sharemind external functions *)
Definition transl_builtin (efname: ident) (ef: AST.external_function) (args: list (builtin_arg reg)) (dest: builtin_res reg) : mon Sharemind.code :=
    do cargs <- transl_builtin_args args; (*(List.rev args); *)
    do sret <- transl_builtin_res dest;
    let ccall := Icall (Imm (inr efname)) sret in
    ret (cargs ++ ccall :: nil).

Definition transl_cmp (c: Integers.comparison) : (Sharemind.comparison) :=
    match c with
    | Ceq => Ijeq
    | Cne => Ijne
    | Clt => Ijlt
    | Cle => Ijle
    | Cgt => Ijgt
    | Cge => Ijge
    end.

Definition transl_instr (name: ident) (n: node) (i: RTL.instruction) : mon (Sharemind.code) :=
    let clbl := Ilabel (intern_node name n) in
    let jmp to := if peq (Pos.succ to) n then nil else Ijmp (transl_node name to) :: nil in
    do cinstr <- match i with
    | Inop next => ret (jmp next)
    | Iop op args dest next =>
        do cop <- transl_op name op args dest;
        ret (cop ++ jmp next)
    | Iload chunk addr args dest next => 
        do cload <- transl_load chunk addr args (transl_reg dest);
        ret (cload ++ jmp next)
    | Istore chunk addr args dest next => 
        do cload <- transl_store chunk addr args (transl_reg dest);
        ret (cload ++ jmp next)
   | RTL.Icall sg fn args dest next =>
        do ccall <- transl_call sg fn args (transl_reg dest);
        ret (ccall ++ jmp next)
    | Itailcall sg fn args =>
        let cfreestack := Ifree stack0 in
        do ccall <- transl_call sg fn args stack0;
        let creturn := Ireturn stack0 in
        ret (cfreestack :: ccall ++ creturn :: nil)
    | Ibuiltin ef args dest next =>
        do bname <- state_find_builtin ef;
        do cbuiltin <- transl_builtin bname ef args dest;
        ret (cbuiltin ++ jmp next)
    | Icond cond args ifso ifnot =>
        do cifso <- transl_condition true cond args (fun c => transl_cmp c (transl_node name ifso));
        let cifnot := jmp ifnot in
        ret (cifso ++ cifnot)    
    | Ijumptable arg tbl => error (Errors.msg "Ijumptable not supported")
    | RTL.Ireturn mbdest =>
        let cfreestack := Ifree stack0 in
        let creturn :=
            match mbdest with
            | Some dest => Ireturn (transl_reg dest)
            | None => Ireturn (Imm (inl (Init_int64 (Int64.repr Z0))))
            end in
        ret (cfreestack :: creturn :: nil)
    end;
    ret (clbl :: cinstr).

Fixpoint transl_instrs (name: ident) (is: list (node * RTL.instruction)) : mon (Sharemind.code) :=
    match is with
    | nil => ret nil
    | cons (n,x) xs =>
        do c1 <- transl_instr name n x;
        do c2 <- transl_instrs name xs;
        ret (c1 ++ c2)
    end.

Definition transl_fun (name: ident) (f: RTL.function) : mon (Sharemind.code) :=
    
    (* reserve space for the function's stack (stack slot 0) plus function registers (stack slots 1..nregs) *)
    let nregs := function_max_reg f in
    let stacksize := Init_int64 (Int64.repr (Z.succ nregs)) in 
    let cresize := Iresizestack stacksize in
    
    (* allocate the function's stack *)
    let fnstacksize := Int64.repr (f.(fn_stacksize)) in
    let calloc1 := Ipush (Imm (inl (Init_int64 fnstacksize))) in
    (* the function's stack is allocated in stack slot 0 *)
    let calloc2 := Icall (Imm (inr (intern_string "malloc"))) (Some stack0) in
    
    let centry := Ijmp (transl_node name f.(fn_entrypoint)) in
    do code <- transl_instrs name (decreasingPTreeElements f.(fn_code));
    let code' := cresize :: calloc1 :: calloc2 :: centry :: code in
    
    ret code'.

Definition transl_globfun (name: ident) (gf : RTL.fundef) : mon unit :=
    match gf with
    | Internal f =>
        do f' <- transl_fun name f;
        state_ins_block name f'
    | External ef => state_ins_ext name ef
    end.

Definition transl_globvar_init (greg: location_val) (off: int64) (i: init_data) : mon (Sharemind.instruction * int64) :=
    let ibytes := Int64.repr (AST.init_data_size i) in
    let from := MV (Imm (inl i)) in
    let voff := Imm (inl (Init_int64 off)) in
    let to := MR (Mem greg) voff in
    let mov := Imov from to (Some (Imm (inl (Init_int64 ibytes)))) in
    ret (mov,Int64.add off ibytes).

Fixpoint transl_globvar_inits (greg: location_val) (off: int64) (is: list init_data) : mon (Sharemind.code * int64)  :=
  match is with
  | nil => ret (nil,off)
  | cons x xs =>
      do (movx,offx) <- transl_globvar_init greg off x;
      do (movxs,offxs) <- transl_globvar_inits greg offx xs;
      ret (movx :: movxs,offxs)
  end.
    
(* Allocates global variables using dynamic memory *)
Definition transl_globvar (name: ident) (gv : rtlglobvar) : mon unit :=
    do n <- state_new_globvar name;
    let gvreg := Stack n in
    do (movs,nbytes) <- transl_globvar_inits gvreg (Int64.repr 0) gv.(gvar_init);
    let alloc1 := Ipush (Imm (inl (Init_int64 nbytes))) in
    let alloc2 := Icall (Imm (inr (intern_string "malloc"))) (Some gvreg) in
    let initcode := alloc1 :: alloc2 :: movs in
    let freecode := Ifree gvreg :: nil in
    state_ins_code initcode freecode.

Definition transl_globdef (name: ident) (gd : rtlglobdef) : mon unit :=
    match gd with
    | Gfun f => transl_globfun name f
    | Gvar v => transl_globvar name v
    end.

Fixpoint transl_globdefs (gds : list (ident * rtlglobdef)) : mon unit :=
    match gds with
    | nil => ret tt
    | cons (n,x) xs =>
        do _ <- transl_globdef n x;
        transl_globdefs xs
    end.

(* Simulate contiguous memory in sharemind block-based memory model *)

(* allocate dummy empty blocks so that pointer arithmetic = block arithmetic *)
(* receives number of bytes to allocate (stack0) *)
(* returns memory address where bytes were allocated *)
Definition malloc : Sharemind.block :=
    (intern_string "malloc"
    ,  Iresizestack (Init_int64 (Int64.repr 3))
    :: Ialloc stack1 stack0
    :: Ilabel (intern_string "malloc_loop")
    :: Ijge (transl_string "malloc_end") Uint64 (imm_int64 (Int64.repr 1)) stack0
    :: Ialloc stack2 (imm_int64 (Int64.repr 0))
    :: Iudec Uint64 stack0
    :: Ijmp (transl_string "malloc_loop")
    :: Ilabel (intern_string "malloc_end")
    :: Ireturn stack1
    :: nil
    ).

Definition moffset_error : (ident * sharemind_data) :=
    (intern_string "MOFFSET_ERROR",Data_string "invalid offset").

Definition user_except (lbl: ident) : Sharemind.code :=
       Imov (MV (Imm (inr (intern_RODATA)))) (MV reg0) None
    :: Igetmemsize (Imm (inr (intern_RODATA))) reg1
    :: Ibsub Uint64 reg1 (Imm (inr lbl))
    :: Ipushcrefpart (LR (Mem reg0)) (Imm (inr lbl)) reg1
    :: Iuser_except
    :: nil.

(* receives a memory address in Compcert's contiguous memory model (stack0) *)
(* converts it into a block + offset in Sharemind's memory model *)
(* writes memory handle for basic block to reg0 *)
(* writes offset to reg1 *)
(* writes size of block - off to reg2 *)
(* returns nothing *)
(* backtracks memory address until it finds a non-empty dummy block *)
Definition moffset : Sharemind.block :=
    (intern_string "moffset"
    ,  Imov (MV stack0) (MV reg0) None
    :: Imov (MV (imm_int64 (Int64.repr 0))) (MV reg1) None
    :: Ilabel (intern_string "moffset_loop")
    :: Ijz (transl_string "moffset_err") Uint64 reg0
    :: Igetmemsize reg0 reg2
    :: Ijnz (transl_string "moffset_end") Uint64 reg2
    :: Iudec Uint64 reg0
    :: Iuinc Uint64 reg1
    :: Ijmp (transl_string "moffset_loop")
    :: Ilabel (intern_string "moffset_end")
    :: Ibsub Uint64 reg2 reg1
    :: Ireturn (imm_int64 (Int64.repr 0))
    :: Ilabel (intern_string "moffset_err")
    :: user_except (fst moffset_error)
    ).

Definition mfree : Sharemind.block :=
    (intern_string "mfree"
    ,  Ifree stack0
    :: Ireturn (imm_int64 (Int64.repr 0))
    :: nil
    ).

Definition ins_block (x: Sharemind.block) (xs: PTree.t Sharemind.code) : PTree.t Sharemind.code :=
    match x with
    | (n,c) => PTree.set n c xs
    end.
    
Definition nToZ (n: N) : Z :=
  match n with
  | N0 => Z0
  | Npos p => Zpos p
  end.

Definition sharemind_rodata : PTree.t sharemind_data :=
    (singlePTree moffset_error).

Definition transl_program (p: RTL.program) : Errors.res (Sharemind.program AST.external_function) :=
  let s0 := state_init in
  let go := transl_globdefs p.(prog_defs)
  in
  match go s0 with
  | Error msg => Errors.Error msg
  | OK tt s =>
      let nglobs := s.(st_nextglob) in
      let cresize := Iresizestack (Init_int64 (Int64.repr (nToZ nglobs))) in
      (* use auxiliary register to store return *)
      let cmain := Icall (Imm (inr p.(prog_main))) (Some stack0) in
      let chalt := Ihalt stack0 in
      let cinit := cresize :: s.(st_initcode) ++ cmain :: s.(st_deinitcode) ++ chalt :: nil in
      let cblocks := ins_block malloc (ins_block moffset (ins_block mfree s.(st_funs))) in
      let prog := mkprogram AST.external_function (PTree.empty private_domain) sharemind_rodata s.(st_exts) cinit cblocks in
      Errors.OK prog
  end.
  

  