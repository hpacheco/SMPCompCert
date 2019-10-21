Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Import Sharemind.
Require Import Sharemindgen.
Require Import String.
Require Import Ascii.
Require Import Values Globalenvs Errors.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Parameter intern_string : string -> ident.

(* Converts Compcert external functions to Sharemind external functions *)

Definition logString_ext : (ident * string) :=
    (intern_string "logString","Process_logString").

Definition toString_ext (ty: type) : (ident * string) :=
    let str := type_to_string ty++"_toString" in
    (intern_string str,str).

Definition op_vec_ext (n:string) (ty: type) : (ident * string) :=
    let str := n++"_"++type_to_string ty++"_vec" in
    (intern_string str,"shared3p::"++str).

Definition conv_vec_ext (ty1 ty2: type) : (ident * string) :=
    let str := "conv_"++type_to_string ty1++"_to_"++type_to_string ty2++"_vec" in
    (intern_string str,"shared3p::"++str).

Definition get_shares_vec_ext := op_vec_ext "get_shares".   
Definition load_vec_ext := op_vec_ext "load".   
Definition store_vec_ext := op_vec_ext "store".    
Definition classify_vec_ext := op_vec_ext "classify".    
Definition declassify_vec_ext := op_vec_ext "declassify".
Definition new_vec_ext := op_vec_ext "new".
Definition delete_vec_ext := op_vec_ext "delete".
Definition assign_vec_ext := op_vec_ext "assign".
Definition add_vec_ext := op_vec_ext "add".

Definition sharemind_pds : (PTree.t Sharemind.private_domain) :=
    PTree.set (intern_string "PD") "pd_shared3p"
    (PTree.empty Sharemind.private_domain).
    
Fixpoint forPTree {B A: Type} (bs: list B) (mk: B -> (ident * A)) : PTree.t A :=
    match bs with
    | nil => PTree.empty A
    | cons x xs =>
        match mk x with
        | (id,a) => PTree.set id a (forPTree xs mk)
        end
    end.
    
Definition transl_ext (x: ident * string) : location_val :=
    transl_ident (fst x).

Infix "+++" := mergePTree (at level 80, right associativity).

    
Definition sharemind_exts : (PTree.t Sharemind.external_function) 
    :=  singlePTree logString_ext
    +++ forPTree alltypes toString_ext
    +++ forPTree alltypes get_shares_vec_ext
    +++ forPTree alltypes load_vec_ext
    +++ forPTree alltypes store_vec_ext
    +++ forPTree alltypes classify_vec_ext
    +++ forPTree alltypes declassify_vec_ext
    +++ forPTree alltypes new_vec_ext
    +++ forPTree alltypes delete_vec_ext
    +++ forPTree alltypes assign_vec_ext
    +++ forPTree alltypes add_vec_ext.

Definition print : Sharemind.code
    := Ipush stack0
    :: Icall (transl_string "moffset") None
    :: Ipushcrefpart (LR (Mem reg0)) reg1 reg2
    :: Isyscall (transl_ext logString_ext) None
    :: Ireturn (imm_int64 (Int64.repr 0))
    :: nil.
    
Definition to_string (ty: type) : Sharemind.code
    := Iresizestack (Init_int64 (Int64.repr 2))
    :: Ipush stack0
    :: Isyscall (transl_ext (toString_ext ty)) (Some stack1)
    :: Ireturn stack1
    :: nil.

Definition new (ty: type) : Sharemind.code
    := Iresizestack (Init_int64 (Int64.repr 1))
    :: Ipush (transl_string "PD")
    :: Ipush (imm_int64 (Int64.repr 1))
    :: Isyscall (transl_ext (new_vec_ext ty)) (Some stack0)
    :: Ireturn stack0
    :: nil.

Definition new_array (ty: type) : Sharemind.code
    := Iresizestack (Init_int64 (Int64.repr 2))
    :: Ipush (transl_string "PD")
    :: Ipush stack0
    :: Isyscall (transl_ext (new_vec_ext ty)) (Some stack1)
    :: Ireturn stack1
    :: nil.

Definition size_array (ty: type) : Sharemind.code
    := Iresizestack (Init_int64 (Int64.repr 2))
    :: Ipush (transl_string "PD")
    :: Ipush stack0
    :: Isyscall (transl_ext (get_shares_vec_ext ty)) (Some stack1)
    :: Ireturn stack1
    :: nil.

Definition load_array (ty: type) : Sharemind.code
    := Iresizestack (Init_int64 (Int64.repr 3))
    :: Ipush (transl_string "PD")
    :: Ipush (imm_int64 (Int64.repr 1))
    :: Isyscall (transl_ext (new_vec_ext ty)) (Some stack2)
    :: Ipush (transl_string "PD")
    :: Ipush stack0
    :: Ipush stack1
    :: Ipush stack2
    :: Isyscall (transl_ext (load_vec_ext ty)) None
    :: Ireturn stack2
    :: nil.

Definition store_array (ty: type) : Sharemind.code
    := Ipush (transl_string "PD")
    :: Ipush stack2
    :: Ipush stack1
    :: Ipush stack0
    :: Isyscall (transl_ext (store_vec_ext ty)) None
    :: Ireturn (imm_int64 (Int64.repr 0)) 
    :: nil.

Definition copy_array (ty: type) : Sharemind.code
    := Ipush (transl_string "PD")
    :: Ipush stack0
    :: Ipush stack1
    :: Isyscall (transl_ext (assign_vec_ext ty)) None
    :: Ireturn (imm_int64 (Int64.repr 0)) 
    :: nil.

Definition delete_array (ty: type) : Sharemind.code
    := Ipush (transl_string "PD")
    :: Ipush stack0
    :: Isyscall (transl_ext (delete_vec_ext ty)) None
    :: Ireturn (imm_int64 (Int64.repr 0)) 
    :: nil.

Definition classify (ty: type) : Sharemind.code
    := Iresizestack (Init_int64 (Int64.repr 2))
    :: Ipush (transl_string "PD")
    :: Ipush (imm_int64 (Int64.repr 1))
    :: Isyscall (transl_ext (new_vec_ext ty)) (Some stack1)
    :: Ipush (transl_string "PD")
    :: Ipush stack1
    :: Ipushcrefpart (LV stack0) (imm_int64 (Int64.repr 0)) (imm_int64 (Int64.repr (type_size ty)))
    :: Isyscall (transl_ext (classify_vec_ext ty)) None
    :: Ireturn stack1
    :: nil.

Definition classify_array (ty: type) : Sharemind.code
    := Ipush stack0
    :: Icall (transl_string "moffset") None
    :: Ipush (transl_string "PD")
    :: Ipush stack1
    :: Ipushcrefpart (LR (Mem reg0)) reg1 reg2
    :: Isyscall (transl_ext (classify_vec_ext ty)) None
    :: Ireturn (imm_int64 (Int64.repr 0))
    :: nil.

Definition declassify (ty: type) : Sharemind.code
    := Iresizestack (Init_int64 (Int64.repr 2))
    :: Ipush (transl_string "PD")
    :: Ipush stack0
    :: Ipushrefpart (LV stack1) (imm_int64 (Int64.repr 0)) (imm_int64 (Int64.repr (type_size ty)))
    :: Isyscall (transl_ext (declassify_vec_ext ty)) None
    :: Ireturn stack1
    :: nil.

Definition declassify_array (ty: type) : Sharemind.code
    := Ipush stack1
    :: Icall (transl_string "moffset") None
    :: Ipush (transl_string "PD")
    :: Ipush stack0
    :: Ipushrefpart (LR (Mem reg0)) reg1 reg2
    :: Isyscall (transl_ext (declassify_vec_ext ty)) None
    :: Ireturn (imm_int64 (Int64.repr 0))
    :: nil.

Definition add (ty : type) : Sharemind.code 
    := Iresizestack (Init_int64 (Int64.repr 3))
    :: Ipush (transl_string "PD")
    :: Ipush (imm_int64 (Int64.repr 1))
    :: Isyscall (transl_ext (new_vec_ext ty)) (Some stack2)
    :: Ipush (transl_string "PD")
    :: Ipush stack0
    :: Ipush stack1
    :: Ipush stack2
    :: Isyscall (transl_ext (add_vec_ext ty)) None
    :: Ireturn stack2
    :: nil.

Definition convert (ty1 ty2: type) : Sharemind.code
    := Iresizestack (Init_int64 (Int64.repr 2))
    :: Ipush (transl_string "PD")
    :: Ipush (imm_int64 (Int64.repr 1))
    :: Isyscall (transl_ext (new_vec_ext ty2)) (Some stack1)
    :: Ipush (transl_string "PD")
    :: Ipush stack0
    :: Ipush stack1
    :: Isyscall (transl_ext (conv_vec_ext ty1 ty2)) None
    :: Ireturn stack1
    :: nil.

Definition transl_bind1 (b: Sharemind.block) : Sharemind.code
    := Iresizestack (Init_int64 (Int64.repr 2))
    :: Ipush stack0
    :: Icall (Imm (inr (fst b))) (Some stack1) 
    :: Ireturn stack1
    :: nil.

Fixpoint take_str (n: nat) (s: string) : string :=
    match (n,s) with
    | (S n',String c s') => String c (take_str n' s')
    | _ => ""
    end.

Fixpoint takeWhile_str (p: ascii -> bool) (s: string) : string :=
    match s with
    | String c s' => if p c
        then String c (takeWhile_str p s')
        else EmptyString
    | EmptyString => EmptyString
    end.

Fixpoint drop_str (n: nat) (s: string) : string :=
    match (n,s) with
    | (S n',String c s') => drop_str n' s'
    | _ => s
    end.

Fixpoint suffix (s1: string) (s2: string) : bool :=
    let n := minus (length s2) (length s1) in
    String.eqb s1 (drop_str n s2).

Definition transl_ext_print (s: string) : option Sharemind.code :=
    if (String.eqb "print" s)
        then Some print
        else None.

Definition transl_ext_op (oppre: string) (oppos: string) (op: type -> Sharemind.code) (s: string) : option Sharemind.code :=
    if (prefix oppre s && suffix oppos s)
        then
            let snopre := drop_str (length oppre) s in
            let snoprepos := take_str (minus (length snopre) (length oppos)) snopre in
            option_map op (string_to_type snoprepos)
        else None.

Definition transl_ext_convert (s: string) : option Sharemind.code :=
    let spre := takeWhile_str (fun c => Bool.eqb (Ascii.eqb c "_") false) s in
    if (prefix "_to_" spre)
        then
            let spos := drop_str (length "_to_") spre in
            match (string_to_type spre,string_to_type spos) with
            | (Some t1,Some t2) => Some (convert t1 t2)
            | _ => None
            end
        else None.

Definition transl_ext_to_string := transl_ext_op "" "_to_string" to_string.
Definition transl_ext_new_array := transl_ext_op "new_" "_array" new_array.
Definition transl_ext_size_array := transl_ext_op "size_" "_array" size_array.
Definition transl_ext_classify_array := transl_ext_op "classify_" "_array" classify_array.
Definition transl_ext_declassify_array := transl_ext_op "declassify_" "_array" declassify_array.
Definition transl_ext_load_array := transl_ext_op "load_" "_array" load_array.
Definition transl_ext_store_array := transl_ext_op "store_" "_array" store_array.
Definition transl_ext_copy_array := transl_ext_op "copy_" "_array" copy_array.
Definition transl_ext_delete_array := transl_ext_op "delete_" "_array" delete_array.
Definition transl_ext_classify := transl_ext_op "classify_" "" classify.
Definition transl_ext_declassify := transl_ext_op "declassify_" "" declassify.
Definition transl_ext_new := transl_ext_op "new_" "" new.
Definition transl_ext_delete := transl_ext_op "delete_" "" delete_array.
Definition transl_ext_copy := transl_ext_op "copy_" "" copy_array.
Definition transl_ext_add := transl_ext_op "add_" "" add.

Definition option_compose {A B:Type} (f : A -> option B) (g : A -> option B) : (A -> option B) :=
  fun a =>
      match f a with
      | Some b => Some b
      | None => g a
      end.

Infix "||||" := option_compose (at level 80, right associativity).

Definition transl_ext_externals 
    :=   transl_ext_print
    |||| transl_ext_to_string
    |||| transl_ext_new_array
    |||| transl_ext_size_array
    |||| transl_ext_classify_array
    |||| transl_ext_declassify_array
    |||| transl_ext_load_array
    |||| transl_ext_store_array
    |||| transl_ext_copy_array
    |||| transl_ext_delete_array
    |||| transl_ext_classify
    |||| transl_ext_declassify
    |||| transl_ext_new
    |||| transl_ext_delete
    |||| transl_ext_copy
    |||| transl_ext_convert
    |||| transl_ext_add.

Definition transl_ext_builtin (n: ident) (ef : AST.external_function) : res Sharemind.block :=
    match ef with
    | EF_external name sg =>
        match transl_ext_externals name with
        | Some c => OK (n,c)
        | None => Error (msg ("external not supported "++name))
        end
    | EF_builtin name sg => Error (msg ("builtin not supported " ++ name))
    | EF_runtime name sg => Error (msg ("runtime not supported " ++ name))
    | EF_vload c => Error (msg "vload not supported")
    | EF_vstore c => Error (msg "vstore not supported")
    | EF_malloc => OK (n,transl_bind1 malloc)
    | EF_free => OK (n,transl_bind1 mfree)
    | _ => Error (msg "builtin not supported")
    end. 

Fixpoint transl_ext_builtins (exts : list (ident * AST.external_function)) : res Sharemind.blocks :=
    match exts with
    | nil => OK (PTree.empty Sharemind.code)
    | cons (n,x) xs =>
        do b' <- transl_ext_builtin n x;
        do xs' <- transl_ext_builtins xs;
        OK (PTree.set (fst b') (snd b') xs')
    end.

(* Removes unused labels *)

Definition identset := PTree.t unit.

Definition identset_list (x: identset) : list ident := List.map fst (PTree.elements x).
Definition empty_identset := PTree.empty unit.
Definition identset_union (x y: identset) : identset := mergePTree x y.
Definition identset_add (x: ident) (xs: identset) : identset := PTree.set x tt xs.
Definition identset_single (x: ident) : identset := PTree.set x tt empty_identset.
Definition identset_in (x: ident) (xs: identset) : bool :=
    match PTree.get x xs with
    | Some tt => true
    | None => false
    end.
Definition identset_size (xs: identset) : nat := PTree.fold (fun n x y => S n) xs 0%nat.

Infix "\|/" := identset_union (at level 80, right associativity).

Definition val_labels (v: Sharemind.val) : identset := empty_identset.
Definition type_labels (t: Sharemind.type) : identset := empty_identset.

Definition opt_labels {A: Type} (f: A -> identset) (o: option A) : identset :=
    match o with
    | None => empty_identset
    | Some a => f a
    end.

Definition loc_val_labels (l: location_val) : identset :=
    match l with
    | Imm (inl v) => val_labels v
    | Imm (inr i) => identset_single i
    | Reg idx => empty_identset
    | Stack idx => empty_identset
    end.
    
Definition opt_loc_val_labels := opt_labels loc_val_labels.
    
Definition loc_ref_labels (l: location_ref) : identset := empty_identset.

Definition loc_labels (l: location) : identset :=
    match l with
    | LV lv => loc_val_labels lv
    | LR lr => loc_ref_labels lr
    end.

Definition loc_mov_labels (l: location_mov) : identset :=
    match l with
    | MV lv => loc_val_labels lv
    | MR lr off => loc_ref_labels lr \|/ loc_val_labels off
    end.

Definition instr_labels (i: Sharemind.instruction) : identset :=
    match i with
    | Ipush a             => loc_val_labels a
    | Ipushref a          => loc_labels a
    | Ipushrefpart a b c  => loc_labels a \|/ loc_val_labels b \|/ loc_val_labels c
    | Ipushcref a         => loc_labels a
    | Ipushcrefpart a b c => loc_labels a \|/ loc_val_labels b \|/ loc_val_labels c
    | Imov a b c          => loc_mov_labels a \|/ loc_mov_labels b \|/ opt_loc_val_labels c
    | Icall a b           => loc_val_labels a \|/ opt_loc_val_labels b
    | Isyscall a b        => loc_val_labels a \|/ opt_loc_val_labels b
    | Ialloc a b          => loc_val_labels a \|/ loc_val_labels b
    | Ifree a             => loc_val_labels a
    | Igetmemsize a b     => loc_val_labels a \|/ loc_val_labels b
    | Iresizestack a      => val_labels a
    | Ilabel a            => identset_single a
    | Ireturn a           => loc_val_labels a
    | Ihalt a             => loc_val_labels a 
    | Iuser_except        => empty_identset
    | Iconvert a b c d    => type_labels a \|/ loc_val_labels b \|/ type_labels c \|/ loc_val_labels d  
    | Iudec a b           => type_labels a \|/ loc_val_labels b 
    | Iuinc a b           => type_labels a \|/ loc_val_labels b 
    | Ibadd a b c         => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c
    | Ibsub a b c         => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c
    | Itadd a b c d       => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Itsub a b c d       => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Itmul a b c d       => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Ijmp a              => loc_val_labels a
    | Ijz a b c           => loc_val_labels a \|/ type_labels b \|/ loc_val_labels c
    | Ijnz a b c          => loc_val_labels a \|/ type_labels b \|/ loc_val_labels c
    | Idnjz a b c         => loc_val_labels a \|/ type_labels b \|/ loc_val_labels c
    | Idnjnz a b c        => loc_val_labels a \|/ type_labels b \|/ loc_val_labels c
    | Ijeq a b c d        => loc_val_labels a \|/ type_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Ijne a b c d        => loc_val_labels a \|/ type_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Ijge a b c d        => loc_val_labels a \|/ type_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Ijgt a b c d        => loc_val_labels a \|/ type_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Ijle a b c d        => loc_val_labels a \|/ type_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Ijlt a b c d        => loc_val_labels a \|/ type_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Iteq a b c d        => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Itne a b c d        => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Itge a b c d        => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Itgt a b c d        => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Itle a b c d        => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Itlt a b c d        => type_labels a \|/ loc_val_labels b \|/ loc_val_labels c \|/ loc_val_labels d
    | Ibtand t a b c      => type_labels t \|/ loc_val_labels a \|/ loc_val_labels b \|/ loc_val_labels c
    | Itshr0 t a b c      => type_labels t \|/ loc_val_labels a \|/ loc_val_labels b \|/ loc_val_labels c
    end.

Fixpoint code_labels (c: Sharemind.code) : identset :=
    match c with
    | nil => empty_identset
    | cons x xs => instr_labels x \|/ code_labels xs
    end.

Section Search.

Variable bs: Sharemind.blocks.

Program Fixpoint search_used_labels (lbls: list ident) (used: identset) {measure (identset_size used)} : identset :=
    match lbls with
    | nil => used
    | cons lbl xs =>
        if identset_in lbl used
            then search_used_labels xs used
            else
                let used' := identset_add lbl used in
                let more :=
                    match PTree.get lbl bs with
                    | Some code => identset_list (code_labels code)
                    | None => nil
                    end in
                search_used_labels (app xs more) used'
    end.
Admit Obligations.
End Search.

Definition code_used_labels (init: Sharemind.code) (bs: Sharemind.blocks) : identset :=
    let initlbls
        := identset_add (intern_string "malloc")
        (identset_add (intern_string "moffset")
        (identset_add (intern_string "mfree")
        (code_labels init))) in
    search_used_labels bs (identset_list initlbls) empty_identset.

(* Starting from the program's start, searches for used labels *)
Definition program_used_labels {E: Type} (p: Sharemind.program E) : identset :=
    code_used_labels p.(prog_init E) p.(prog_code E).

Fixpoint remove_unused_list {A: Type} (used: identset) (exts: list (ident * A)) : PTree.t A :=
    match exts with
    | nil => PTree.empty A
    | cons (x,y) xs =>
        let rec := remove_unused_list used xs in
        if identset_in x used
            then PTree.set x y rec
            else rec
    end.

(* Converts external functions to sharemind virtual machine syscalls *)
Definition transl_ext_program (p: Sharemind.program AST.external_function) : res (Sharemind.program Sharemind.external_function) :=
    let used := program_used_labels p in

    let exts := p.(prog_exts AST.external_function) in
    let init := p.(prog_init AST.external_function) in
    let code := p.(prog_code AST.external_function) in
    let rodata := p.(prog_rodata AST.external_function) in
    
    let exts0 := remove_unused_list used (PTree.elements exts) in
    let code0 := remove_unused_list used (PTree.elements code) in
    
    do extblocks <- transl_ext_builtins (PTree.elements exts0);
    let code' := mergePTree code0 extblocks in
    let sysused' := code_used_labels init code' in
    let sexts' := remove_unused_list sysused' (PTree.elements sharemind_exts) in
    let p' := mkprogram Sharemind.external_function sharemind_pds rodata sexts' init code' in
    OK p'.

