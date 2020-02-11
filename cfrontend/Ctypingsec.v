
Require Import String.
Require Import Coqlib Maps Integers Floats Errors.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events.
Require Import Ctypes Ctyping Cop Csyntax Csem.

Local Open Scope error_monad_scope.

(**
    Security typechecker
    Assumes that typechecking has already passed, and thus that all intermediate expressions are correctly typed (with security annotations).
    Performs implicit classification.
    Introduces security builtin operations.
    Replaces security types for machine integers (that represent handles/pointers to secret data as managed by an external secure store).
**)

Parameter show_expr : expr -> string.
(* Parameter new_tmp : unit -> ident. *)

Definition mergeOption {A: Type} (ox oy: option A) : option A :=
    match ox with
    | Some x => Some x
    | None => oy
    end.

Definition mergePTree {A: Type} (p1 p2: PTree.t A) : PTree.t A :=
    PTree.combine mergeOption p1 p2.

Fixpoint concatPTrees {A: Type} (xs: list (PTree.t A)) : PTree.t A :=
    match xs with
    | nil => PTree.empty A
    | cons y ys => mergePTree y (concatPTrees ys)
    end.

Definition singlePTree {A: Type} (p: (ident * A)) : PTree.t A :=
    PTree.set (fst p) (snd p) (PTree.empty A).

(* temporary variables *)
(* Definition tmps := PTree.t type. *)

(*Definition notmps : tmps := PTree.empty type.*)

Fixpoint is_ext_lval (e: expr) : bool :=
    match e with
    | Ecomma e1 e2 _ => is_ext_lval e2
    | Eassign l r _ => is_ext_lval l
    | Eloc _ _ _ | Evar _ _ | Ederef _ _ | Efield _ _ _ => true
    | _ => false
    end.

(** Utils **)

Definition ssequence (s1 s2 : statement) : statement :=
    match (s1,s2) with
    | (Sskip,_) => s2
    | (_,Sskip) => s1
    | _ => Ssequence s1 s2
    end.

Fixpoint append_to_statement (s safter: statement) : statement :=
    match s with
    | Sskip => Sskip
    | Sdo e => Sdo e
    | Ssequence s1 s2 => ssequence (append_to_statement s1 safter) (append_to_statement s2 safter)
    | Sifthenelse e s1 s2 => Sifthenelse e (append_to_statement s1 safter) (append_to_statement s2 safter)
    | Swhile e s1 => Swhile e (append_to_statement s1 safter)
    | Sdowhile e s1 => Sdowhile e (append_to_statement s1 safter)
    | Sfor s1 e s2 s3 => Sfor (append_to_statement s1 safter) e (append_to_statement s2 safter) (append_to_statement s3 safter)
    | Sbreak => Sbreak
    | Scontinue => Scontinue
    | Sreturn e => ssequence safter s
    | Sswitch e lbls => Sswitch e (append_to_labeled_statements lbls safter)
    | Slabel l s1 => Slabel l (append_to_statement s1 safter)
    | Sgoto l => Sgoto l
    end
with append_to_labeled_statements (lbls: labeled_statements) (safter: statement) : labeled_statements :=
    match lbls with
    | LSnil => LSnil
    | LScons z s1 xs => LScons z (append_to_statement s1 safter) (append_to_labeled_statements xs safter)
    end.

Definition is_base_type (t: type) : bool :=
  match t with
  | Tint _ _ _ => true
  | Tlong _ _ => true
  | Tfloat _ _ => true
  | _ => false
  end.

Fixpoint type_has_secret (ty: type) : bool :=
  match ty with
  | Tvoid => false
  | Tint _ _ a => a.(attr_secret)
  | Tlong _ a => a.(attr_secret)
  | Tfloat _ a => a.(attr_secret)
  | Tpointer t a => a.(attr_secret) || type_has_secret t
  | Tarray t _ a => a.(attr_secret) || type_has_secret t
  | Tfunction _ _ _ => false
  | Tstruct _ a => a.(attr_secret)
  | Tunion _ a => a.(attr_secret)
  end.
  
Definition set_attr_secret (sec:bool) (a : attr) : attr :=
  {| attr_volatile := a.(attr_volatile);
     attr_secret := sec;
     attr_alignas := a.(attr_alignas);
  |}.
  
Definition make_public_attr (a : attr) : attr :=
  set_attr_secret false a.

Definition make_secret_attr (a : attr) : attr :=
  set_attr_secret true a.
  
Definition type_is_public (ty: type) : bool :=
  negb (type_is_secret ty).
  
Definition make_public_type (ty: type) : type :=
  change_attributes make_public_attr ty.

Definition make_secret_type (ty: type) : type :=
  change_attributes make_secret_attr ty.

Definition check_public (t: type) (m: string) : res unit :=
  if type_is_public t then OK tt else Error (msg ("unsupported secure control flow in"++m)).
  
Definition check_secret (t: type) (m: string) : res unit :=
  if type_is_secret t then OK tt else Error (msg ("expected secret type in "++m)).

Definition show_signedness (s: signedness) : string :=
  match s with
  | Signed => ""
  | Unsigned => "u"
  end.

Definition show_attr (a: attr) : string := if a.(attr_secret) then "secret " else "".

Fixpoint show_type (t: type) : string :=
  match t with
  | Tvoid => "void"
  | Tint IBool _ a => show_attr a++"bool"
  | Tint I8 s a => show_attr a++show_signedness s++"int8"
  | Tint I16 s a => show_attr a++show_signedness s++"int16"
  | Tint I32 s a => show_attr a++show_signedness s++"int32"
  | Tlong s a => show_attr a++show_signedness s++"int64"
  | Tfloat F32 a => show_attr a++"float32"
  | Tfloat F64 a => show_attr a++"float64"
  | Tpointer bt a => show_type bt ++ "*"++show_attr a
  | Tarray bt sz a => show_type bt ++"["++show_attr a++"]"
  | _ => "error"
  end.

(** builtins **)

Definition external_new_array (t: type) : external_function :=
    EF_external ("new_"++show_type (make_public_type t)++"_array") (mksignature (cons AST.Tlong nil) (Some Tptr) cc_default).
Definition external_delete_array (t: type) : external_function :=
    EF_external ("delete_"++show_type (make_public_type t)++"_array") (mksignature (cons Tptr nil) None cc_default).
Definition external_load_array (t: type) : external_function :=
    EF_external ("load_"++show_type (make_public_type t)++"_array") (mksignature (cons Tptr (cons AST.Tlong nil)) (Some (typ_of_type t)) cc_default).
Definition external_store_array (t: type) : external_function :=
    EF_external ("store_"++show_type (make_public_type t)++"_array") (mksignature (cons Tptr (cons AST.Tlong (cons (typ_of_type t) nil))) None cc_default).
Definition external_copy_array (t: type) : external_function :=
    EF_external ("copy_"++show_type (make_public_type t)++"_array") (mksignature (cons Tptr (cons Tptr nil)) None cc_default).
    
Definition builtin_new_array (t: type) (e1: expr) : expr :=
    Ebuiltin (external_new_array t) (Tcons (typeof e1) Tnil) (Econs e1 Enil) (Tpointer t snoattr).
Definition builtin_delete_array (t: type) (e1: expr) : expr :=
    Ebuiltin (external_delete_array t) (Tcons (typeof e1) Tnil) (Econs e1 Enil) Tvoid.
Definition builtin_load_array (t: type) (e1 e2: expr) : expr :=
    Ebuiltin (external_load_array t) (Tcons (typeof e1) (Tcons (typeof e2) Tnil)) (Econs e1 (Econs e2 Enil)) (make_secret_type t).
Definition builtin_store_array (t: type) (e1 e2 e3: expr) : expr :=
    Ebuiltin (external_store_array t) (Tcons (typeof e1) (Tcons (typeof e2) (Tcons (typeof e3) Tnil))) (Econs e1 (Econs e2 (Econs e3 Enil))) Tvoid.
Definition builtin_copy_array (t: type) (e1 e2: expr) : expr :=
    Ebuiltin (external_copy_array t) (Tcons (typeof e1) (Tcons (typeof e2) Tnil)) (Econs e1 (Econs e2 Enil)) Tvoid.

(**    
Definition external_new (t: type) : external_function :=
    EF_external ("new_"++show_type (make_public_type t)) (mksignature nil (Some (typ_of_type t)) cc_default).
Definition external_delete (t: type) : external_function :=
    EF_external ("delete_"++show_type (make_public_type t)) (mksignature (cons (typ_of_type t) nil) None cc_default).
Definition external_classify (t: type) : external_function :=
    EF_external ("classify_"++show_type (make_public_type t)) (mksignature (cons (typ_of_type t) nil) (Some (typ_of_type t)) cc_default).
Definition external_declassify (t: type) : external_function :=
    EF_external ("declassify_"++show_type (make_public_type t)) (mksignature (cons (typ_of_type t) nil) (Some (typ_of_type t)) cc_default).
Definition external_copy (t: type) : external_function :=
    EF_external ("copy_"++show_type (make_public_type t)) (mksignature (cons (typ_of_type t) (cons (typ_of_type t) nil)) None cc_default).
Definition external_binop (n: string) (t t1 t2: type) : external_function :=
    EF_external (n++"_"++show_type (make_public_type t)) (mksignature (cons (typ_of_type t1) (cons (typ_of_type t2) nil)) (Some (typ_of_type t)) cc_default).
    
Definition external_convert (t1 t2: type) : external_function :=
    EF_external (show_type (make_public_type t1) ++ "_to_" ++ show_type (make_public_type t2)) (mksignature (cons (typ_of_type t1) nil) (Some (typ_of_type t2)) cc_default).
    
Definition builtin_new (t: type) : expr :=
    Ebuiltin (external_new t) Tnil Enil (make_secret_type t).
Definition builtin_delete (t: type) (e1: expr) : expr :=
    Ebuiltin (external_delete t) (Tcons (typeof e1) Tnil) (Econs e1 Enil) Tvoid.
Definition builtin_classify (t: type) (e1: expr) : expr :=
    Ebuiltin (external_classify t) (Tcons (typeof e1) Tnil) (Econs e1 Enil) (make_secret_type t).
Definition builtin_declassify (t: type) (e1: expr) : expr :=
    Ebuiltin (external_declassify t) (Tcons (typeof e1) Tnil) (Econs e1 Enil) (make_public_type t).
Definition builtin_copy (t: type) (e1 e2: expr) : expr :=
    Ebuiltin (external_copy t) (Tcons (typeof e1) (Tcons (typeof e2) Tnil)) (Econs e1 (Econs e2 Enil)) Tvoid.
Definition builtin_binop (n: string) (t: type) (e1 e2: expr) : expr :=
    let t1 := typeof e1 in
    let t2 := typeof e2 in
    Ebuiltin (external_binop n t t1 t2) (Tcons t1 (Tcons t2 Tnil)) (Econs e1 (Econs e2 Enil)) (typeof e1).

Definition builtin_convert (t1 t2: type) (e: expr) : expr :=
    Ebuiltin (external_convert t1 t2) (Tcons t1 Tnil) (Econs e Enil) t2.
**)

(** Introduce secure builtins **)

Definition public_cast (n: string) (rt: type) (e:expr) : res expr :=
    ecast rt e.

Definition is_malloc_expr (e: expr) : bool :=
    match e with
    | Ebuiltin EF_malloc _ _ _ => true
    | _ => false
    end.

Definition secure_cast (n: string) (rt: type) (e:expr) : res expr :=
    let et := typeof e in
    if negb (type_has_secret et) && negb (type_has_secret rt) then OK e
    else if type_eq et rt then OK e
    else match (et,rt) with
    ((Tint _ _ a1 | Tlong _ a1 | Tfloat _ a1),(Tint _ _ a2 | Tlong _ a2 | Tfloat _ a2)) => 
        match (attr_secret a1,attr_secret a2) with
        | (true,true) => OK (builtin_convert et rt e)
        | (false,true) => let e' := Ecast e (make_public_type rt) in OK (builtin_classify rt e')
        | _ => Error (msg (n++" unsupported cast from secure to non-secure type, try declassify"))
        end
    | (Tarray bt2 _ a2,Tpointer bt1 a1) =>
        if (eqb (attr_secret a1) (attr_secret a2)) && type_eq bt1 bt2 then OK e
        else Error (msg ("unsupported secure conversion from " ++ show_type et ++ " to " ++ show_type rt))
    | (Tpointer bt1 a1,Tpointer bt2 a2) => 
        if negb (attr_secret a1) && negb (attr_secret a2) && is_malloc_expr e then OK e
        else Error (msg ("unsupported secure conversion from " ++ show_type et ++ " to " ++ show_type rt))
    | _ => Error (msg ("unsupported secure conversion from " ++ show_type et ++ " to " ++ show_type rt))
    end.

Definition secure_unop_expr (op: unary_operation) (t: type) (e1 : expr) : res expr :=
  do _ <- check_secret t ("secure "++show_unop op);
  match (op,t) with
  | _ => Error (msg ("unsupported secure "++show_unop op))
  end.

Definition secure_unop (op : unary_operation) (t: type) (e1: expr): res (expr) :=
  match (type_is_secret (typeof e1)) with
  | false => (* assumes that regular casts preserve non-top-level security tags*)
      OK (Eunop op e1 t)
  | _ =>
      do e1' <- secure_cast "secure_unop" t e1;
      secure_unop_expr op t e1'
  end.

Definition secure_cast_binop (op : type -> expr -> expr -> res expr) (t: type) (e1 e2: expr) : res expr :=
    do e1' <- secure_cast "secure_cast_binop1" t e1;
    do e2' <- secure_cast "secure_cast_binop2" t e2;
    op t e1' e2'.

(* does not assume that both expressions have the same type *)
Definition secure_binop_expr (op: binary_operation) (t: type) (e1 e2 : expr) : res expr :=
    let t1 := typeof e1 in
    let t2 := typeof e2 in
    if is_base_type t
        then match op with
        | Oadd =>
            do e1' <- secure_cast "secure_cast_binop1" t e1;
            do e2' <- secure_cast "secure_cast_binop2" t e2;
            OK (builtin_binop "add" t e1' e2')
        | Osub =>
            do e1' <- secure_cast "secure_cast_binop1" t e1;
            do e2' <- secure_cast "secure_cast_binop2" t e2;
            OK (builtin_binop "sub" t e1' e2')
        | Omul => match (type_is_secret t1,type_is_secret t2) with
            | (true,true) => 
                do e1' <- secure_cast "secure_cast_binop1" t e1;
                do e2' <- secure_cast "secure_cast_binop2" t e2;
                OK (builtin_binop "mul" t e1' e2')
            | (true,false) =>
                do e1' <- secure_cast "secure_cast_binop1" t e1;
                do e2' <- public_cast "public_cast_binop2" (make_public_type t) e2;
                OK (builtin_binop "mulc" t e1' e2')
            | (false,true) =>
                do e1' <- public_cast "public_cast_binop1" (make_public_type t) e1;
                do e2' <- secure_cast "secure_cast_binop2" t e2;
                OK (builtin_binop "mulc" t e2' e1')
            | (false,false) => Error (msg ("unexpected public binop"))
            end
        | _ => Error (msg ("unsupported secure binop"))
        end
        else Error (msg ("unsupported secure binop")).

Definition secure_eseqand_expr (t: type) (e1 e2 : expr) : res expr :=
  do _ <- check_secret t "secure &&";
  match t with
  | Tint IBool _ _ => OK (builtin_binop "and" t e1 e2)
  | _ => Error (msg "unsupported secure &&")
  end.
  
Definition secure_eseqor_expr (t: type) (e1 e2 : expr) : res expr :=
  do _ <- check_secret t "secure logical ||";
  match t with
  | Tint IBool _ _ => OK (builtin_binop "or" t e1 e2)
  | _ => Error (msg "unsupported secure ||")
  end.

Definition retype_secure_binop (pop : expr -> expr -> type -> expr) (sop : type -> expr -> expr -> res expr) (t: type) (e1 e2: expr): res (expr) :=
  match (type_is_secret (typeof e1),type_is_secret (typeof e2)) with
  | (false,false) => (* assumes that regular casts preserve non-top-level security tags*)
      OK (pop e1 e2 t)
  | _ => sop t e1 e2
  end.

Definition secure_condition (t: type) (e1 e2 e3: expr) : res expr :=
    do _ <- check_public (typeof e1) "conditional";
    do e2' <- secure_cast "secure_condition2" t e2;
    do e3' <- secure_cast "secure_condition3" t e3;
    OK (Econdition e1 e2' e3' t).

Fixpoint retype_secure_arguments (el: exprlist) (tyl: typelist) : res exprlist :=
  match el, tyl with
  | Enil, _ => OK Enil
  | _, Tnil => OK el
  | Econs e1 el, Tcons ty1 tyl =>
      do e1' <- secure_cast "retype_secure_arguments" ty1 e1;
      do el' <- retype_secure_arguments el tyl;
      OK (Econs e1' el')
  end.

Definition secure_call (name : expr) (args : exprlist) : res expr :=
    match classify_fun (typeof name) with
    | fun_case_f tyargs tyres cconv =>
        do args' <- retype_secure_arguments args tyargs;
        OK (Ecall name args' tyres)
    | _ =>
        Error (msg "call: not a function")
    end.

Definition check_same_expr (e1 e2 : expr) : res unit :=
  match (e1,e2) with
  | (Evar x1 t1,Evar x2 t2) => if ident_eq x1 x2 then OK tt else Error (msg "variables are not the same")
  | _ => Error (msg "expressions are not the same")
  end.

(* tries to split an expression into base pointer + offset *)
Fixpoint split_array_proj (e: expr) : res (expr * expr) :=
  match e with
  | Evalof l t => split_array_proj l
  | Evar x t => OK (e,Eval (Vlong Int64.zero) type_pint64u)
  | Ebinop Oadd e1 e2 t => match classify_add (typeof e1) (typeof e2) with
      | add_case_pi _ _ | add_case_pl _ => if type_is_public (typeof e2)
          then do (x',i') <- split_array_proj e1; do i'' <- ebinop Oadd i' e2; OK (x',i'')
          else Error (msg "Oadd secure pointer index cannot be secret")
      | add_case_ip _ _ | add_case_lp _ => if type_is_public (typeof e1)
          then do (x',i') <- split_array_proj e2; do i'' <- ebinop Oadd i' e1; OK (x',i'')
          else Error (msg "Oadd secure pointer index cannot be secret")
      | _ => Error (msg "Oadd secure pointer dereferencing could not be converted into projection")
      end
  | Ebinop Osub e1 e2 t => match classify_sub (typeof e1) (typeof e2) with
      | sub_case_pi _ _ | sub_case_pl _ => if type_is_public (typeof e2)
          then do (x',i') <- split_array_proj e1; do i'' <- ebinop Osub i' e2; OK (x',i'')
          else Error (msg "Osub secure pointer index cannot be secret")
      | sub_case_pp _ =>
          do (x1',i1') <- split_array_proj e1;
          do (x2',i2') <- split_array_proj e2;
          do _ <- check_same_expr x1' x2';
          do i' <- ebinop Osub i1' i2';
          OK (x1',i')
      | _ => Error (msg "Osub secure pointer dereferencing could not be converted into projection")
      end
  | _ => Error (msg ("secure pointer dereferencing could not be converted into projection "++ show_expr e))
  end.

Definition secure_load_array (t: type) (x : expr) (i: expr) : res expr :=
  if is_base_type t
      then OK (builtin_load_array t x i)
      else Error (msg "unsupported secure array load").

(* assumes that dereference is well-typed *)
Definition retype_secure_deref (go: expr -> res (expr * tmps)) (e: expr) (t: type) : res (expr * tmps) :=
  if type_is_public (typeof e)
      then
          do (e',tmps) <- go e;
          OK (Ederef e' t,tmps)
      else 
          do (x,i) <- split_array_proj e;
          do e' <- secure_load_array t x i;
          OK (e',notmps).

Definition secure_store_array (t: type) (l i r: expr) : res expr :=
  if is_base_type t
    then OK (builtin_store_array t l i r)
    else Error (msg "unsupported secure array store").

Definition retype_secure_assign_by_type (l: expr) (r: expr) (t: type) : res expr :=
    match t with
    (Tint _ _ _ | Tlong _ _ | Tfloat _ _) => OK (builtin_copy t r l)
    | Tpointer _ _ => OK (Eassign l r t)
(*    | Tarray bt _ _ => OK (builtin_copy_array bt r l) *)
    | _ => Error (msg "secure assign to a variable")
    end.

(*TODO: free secure data on right-side expressions! *)
Definition retype_secure_assign (go: expr -> res (expr * tmps)) (l r: expr) (t: type) : res (expr * tmps) :=
  if type_is_public (typeof l)
      then
          do (l',tmps) <- go l;
          OK (Eassign l' r t,tmps)
      else
          match l with
          | Evar n nt => do a' <- retype_secure_assign_by_type (Evar n nt) r nt; OK (a',notmps)
          | Ederef lptr tptr => if type_is_public (typeof lptr)
              then 
                  do (lptr',tmps) <- go lptr;
                  do a' <- retype_secure_assign_by_type (Ederef lptr' tptr) r t;
                  OK (a',tmps)
              else
                  do (lx,li) <- split_array_proj lptr;
                  do a' <- secure_store_array tptr lx li r;
                  OK (a',notmps)
          | Efield _ _ _ => Error (msg "secure assign field")
          | Eloc _ _ _ => Error (msg "secure assign loc")
          | _ => Error (msg "secure assign not a l-value")
          end.

Definition ret_tmp_expr (a: expr) (ts: tmps) : res (expr * tmps) :=
    let t := typeof a in
    if type_is_secret t && is_base_type t && negb (is_ext_lval a)
        then 
            let tmp := new_tmp tt in
            let tmpv := Evar tmp t in
            let ts' := PTree.set tmp t ts in
            OK (Eassign tmpv a t,ts')
        else OK (a,ts).

(* returns a typechecked expression with security ops replaced by builtins *)
Fixpoint retype_secure_expr (ce: composite_env) (e: typenv) (a: expr) : res (expr * tmps) :=
  match a with
  | Eval v t => ret_tmp_expr a notmps
  | Evar x t => ret_tmp_expr a notmps
  | Efield r f t =>
      do (r',tmps) <- retype_secure_expr ce e r;
      ret_tmp_expr (Efield r' f t) tmps
  | Evalof r t =>
      do (r',tmps) <- retype_secure_expr ce e r;
      ret_tmp_expr (Evalof r' t) tmps
  | Ederef r t =>
      do (a',tmps) <- retype_secure_deref (retype_secure_expr ce e) r t;
      ret_tmp_expr a' tmps
  | Eaddrof l t =>
      do (l',tmps) <- retype_secure_expr ce e l;
      ret_tmp_expr (Eaddrof l' t) tmps
  | Eunop op r1 t =>
      do (r1',tmps) <- retype_secure_expr ce e r1;
      do a' <- secure_unop op t r1';
      ret_tmp_expr (a') tmps
  | Ebinop op r1 r2 t =>
      do (r1',tmps1) <- retype_secure_expr ce e r1;
      do (r2',tmps2) <- retype_secure_expr ce e r2;
      do a' <- retype_secure_binop (Ebinop op) (secure_binop_expr op) t r1' r2';
      ret_tmp_expr a' (mergePTree tmps1 tmps2)
  | Ecast r t =>
      do (r',tmps) <- retype_secure_expr ce e r;
      do a' <- secure_cast "Ecast" t r;
      ret_tmp_expr a' tmps
  | Eseqand r1 r2 t =>
      do (r1',tmps1) <- retype_secure_expr ce e r1;
      do (r2',tmps2) <- retype_secure_expr ce e r2;
      do a' <- retype_secure_binop Eseqand (secure_cast_binop secure_eseqand_expr) t r1' r2';
      ret_tmp_expr a' (mergePTree tmps1 tmps2)
  | Eseqor r1 r2 t =>
      do (r1',tmps1) <- retype_secure_expr ce e r1;
      do (r2',tmps2) <- retype_secure_expr ce e r2;
      do a' <- retype_secure_binop Eseqor (secure_cast_binop secure_eseqor_expr) t r1' r2';
      ret_tmp_expr a' (mergePTree tmps1 tmps2)
  | Econdition r1 r2 r3 t =>
      do (r1',tmps1) <- retype_secure_expr ce e r1;
      do (r2',tmps2) <- retype_secure_expr ce e r2;
      do (r3',tmps3) <- retype_secure_expr ce e r3;
      do a' <- secure_condition t r1' r2' r3';
      ret_tmp_expr a' (mergePTree tmps1 (mergePTree tmps2 tmps3))
  | Esizeof r t => ret_tmp_expr (Esizeof r t) notmps
  | Ealignof r t => ret_tmp_expr (Ealignof r t) notmps
  | Eassign l r t =>
      do (r',tmps) <- retype_secure_expr ce e r;
      do r'' <- secure_cast "Eassign" t r';
      do (a',tmps') <- retype_secure_assign (retype_secure_expr ce e) l r'' t;
      ret_tmp_expr a' (mergePTree tmps tmps')
  | Eassignop op l r tres t => 
      do (l',tmps1) <- retype_secure_expr ce e l;
      do (r',tmps2) <- retype_secure_expr ce e r;
      do lr <- retype_secure_binop (Ebinop op) (secure_binop_expr op) tres (Evalof l' (typeof l')) r';
      do lr' <- secure_cast "Eassignop" t lr;
      do (a',tmps3) <- retype_secure_assign (retype_secure_expr ce e) l lr' t;
      ret_tmp_expr a' (mergePTree tmps1 (mergePTree tmps2 tmps3))
  | Epostincr id r t =>
      do (r',tmps1) <- retype_secure_expr ce e r;
      let one := Eval (Vint Int.one) (type_pint32s) in
      do radd1' <- retype_secure_binop (Ebinop Oadd) (secure_binop_expr Oadd) t (Evalof r' (typeof r')) one;
      do rsub1' <- retype_secure_binop (Ebinop Osub) (secure_binop_expr Osub) t (Evalof r' (typeof r')) one;
      match id with
      | Incr =>
          do (ass',tmps2) <- retype_secure_assign (retype_secure_expr ce e) r radd1' t;
          ret_tmp_expr (Ecomma ass' rsub1' t) (mergePTree tmps1 tmps2)
      | Decr =>
          do (ass',tmps2) <- retype_secure_assign (retype_secure_expr ce e) r rsub1' t;
          ret_tmp_expr (Ecomma ass' radd1' t) (mergePTree tmps1 tmps2)
      end
  | Ecomma r1 r2 t =>
      do (r1',tmps1) <- retype_secure_expr ce e r1;
      do (r2',tmps2) <- retype_secure_expr ce e r2;
      ret_tmp_expr (Ecomma r1' r2' t) (mergePTree tmps1 tmps2)
  | Ecall rname rargs t =>
      do (rname',tmps1) <- retype_secure_expr ce e rname; 
      do (rargs',tmps2) <- retype_secure_exprlist ce e rargs;
      do a' <- secure_call rname' rargs';
      ret_tmp_expr a' (mergePTree tmps1 tmps2)
  | Ebuiltin ef tyargs rargs tyres =>
      do (rargs',tmps1) <- retype_secure_exprlist ce e rargs;
      do rargs'' <- retype_secure_arguments rargs' tyargs;
      ret_tmp_expr (Ebuiltin ef tyargs rargs'' tyres) tmps1
  | Eloc _ _ _ => Error (msg "Eloc in source")
  | Eparen _ _ _ => Error (msg "Eparen in source")
  end
with retype_secure_exprlist (ce: composite_env) (e: typenv) (rs: exprlist) : res (exprlist * tmps) :=
  match rs with
  | Enil => OK (Enil,notmps)
  | Econs x xs =>
      do (x',tmps1) <- retype_secure_expr ce e x;
      do (xs',tmps2) <- retype_secure_exprlist ce e xs;
      OK (Econs x' xs',mergePTree tmps1 tmps2)
  end.

Definition retype_secure_public_expr (ce: composite_env) (e: typenv) (a: expr) (m: string) : res (expr * tmps) :=
    do _ <- check_public (typeof a) m;
    retype_secure_expr ce e a.

Fixpoint free_tmps_expr (e: expr) (tms: list (ident * type)) : expr :=
    match tms with
    | nil => e
    | cons (n,t) xs => free_tmps_expr (Ecomma e (builtin_delete t (Evar n t)) Tvoid) xs
    end.

Definition retype_secure_expr_free (ce: composite_env) (e: typenv) (a: expr) : res (expr * tmps) :=
    do (a',xs) <- retype_secure_expr ce e a;
    let t' := typeof a' in
    if complete_type ce t'
        then 
            let x := new_tmp tt in
            let v := Evar x t' in
            let xs' := PTree.set x t' xs in
            let a'' := Ecomma (free_tmps_expr (Eassign v a' t') (PTree.elements xs)) v t' in
            OK (a'',xs')
        else
            let a'' := free_tmps_expr a' (PTree.elements xs) in
            OK (a'',xs).

Definition retype_secure_public_expr_free (ce: composite_env) (e: typenv) (a: expr) (m: string) : res (expr * tmps) :=
    do _ <- check_public (typeof a) m;
    retype_secure_expr_free ce e a.

Fixpoint retype_secure_stmt (ce: composite_env) (e: typenv) (rt: type) (s: statement) : res (statement * tmps) :=
  match s with
  | Sskip => OK (Sskip,notmps)
  | Sdo a =>
      do (a',tmps) <- retype_secure_expr_free ce e a;
      OK (Sdo a',tmps)
  | Ssequence s1 s2 =>
      do (s1',tmps1) <- retype_secure_stmt ce e rt s1;
      do (s2',tmps2) <- retype_secure_stmt ce e rt s2;
      OK (ssequence s1' s2',mergePTree tmps1 tmps2)
  | Sifthenelse a s1 s2 =>
      do (a',tmps1) <- retype_secure_public_expr_free ce e a "ifthenelse";
      do (s1',tmps2) <- retype_secure_stmt ce e rt s1;
      do (s2',tmps3) <- retype_secure_stmt ce e rt s2;
      OK (Sifthenelse a' s1' s2',concatPTrees (tmps1 :: tmps2 :: tmps3 :: nil))
  | Swhile a s =>
      do (a',tmps1) <- retype_secure_public_expr_free ce e a "while";
      do (s',tmps2) <- retype_secure_stmt ce e rt s;
      OK (Swhile a' s',mergePTree tmps1 tmps2)
  | Sdowhile a s =>
      do (a',tmps1) <- retype_secure_public_expr_free ce e a "dowhile";
      do (s',tmps2) <- retype_secure_stmt ce e rt s;
      OK (Sdowhile a' s',mergePTree tmps1 tmps2)
  | Sfor s1 a s2 s3 =>
      do (a',tmps1) <- retype_secure_public_expr_free ce e a "for";
      do (s1',tmps2) <- retype_secure_stmt ce e rt s1;
      do (s2',tmps3) <- retype_secure_stmt ce e rt s2;
      do (s3',tmps4) <- retype_secure_stmt ce e rt s3;
      OK (Sfor s1' a' s2' s3',concatPTrees (tmps1 :: tmps2 :: tmps3 :: tmps4 :: nil))
  | Sbreak => OK (Sbreak,notmps)
  | Scontinue => OK (Scontinue,notmps)
  | Sreturn None => OK (Sreturn None,notmps)
  | Sreturn (Some a) =>
      do (a',tmps) <- retype_secure_expr_free ce e a;
      do a'' <- secure_cast "Sreturn" rt a';
      OK (Sreturn (Some a''),tmps)
  | Sswitch a sl =>
      do (a',tmps1) <- retype_secure_public_expr_free ce e a "switch";
      do (sl',tmps2) <- retype_secure_lblstmts ce e rt sl;
      OK (Sswitch a' sl',mergePTree tmps1 tmps2)
  | Slabel lbl s =>
      do (s',tmps) <- retype_secure_stmt ce e rt s;
      OK (Slabel lbl s',tmps)
  | Sgoto lbl => OK (Sgoto lbl,notmps)
  end
with retype_secure_lblstmts (ce: composite_env) (e: typenv) (rt: type) (sl: labeled_statements) : res (labeled_statements * tmps) :=
  match sl with
  | LSnil => OK (LSnil,notmps)
  | LScons case s sl =>
      do (s',tmps1) <- retype_secure_stmt ce e rt s;
      do (sl',tmps2) <- retype_secure_lblstmts ce e rt sl;
      OK (LScons case s' sl',mergePTree tmps1 tmps2)
  end.

Definition init_data_to_expr (i: init_data) (sg: signedness) : res expr :=
    match i with
    | Init_int8 i => OK (econst_int i sg)
    | Init_int16 i => OK (econst_int i sg)
    | Init_int32 i => OK (econst_int i sg)
    | Init_int64 l => OK (econst_long l sg)
    | Init_float32 f => OK (econst_single f)
    | Init_float64 f => OK (econst_float f)
    | _ => Error (msg "cannot initialize data")
    end.

(* We will not run the typechecker on the generated code *)
Definition initialize_secure_var (n: ident) (t: type) (inits : list init_data) : res (type * list init_data * (statement * statement)) :=
    if type_is_public t then OK (t,inits,(Sskip,Sskip))
    else match t with  
    (Tint _ _ _ | Tlong _ _ | Tfloat _ _) =>
        let sfree := Sdo (builtin_delete t (Evar n t)) in
        match inits with
        | nil =>
            let blt := builtin_new t in
            let sinit := Sdo (Eassign (Evar n t) blt t) in
            OK (t,nil,(sinit,sfree))
        | cons i is =>
            do ei <- init_data_to_expr i (type_signedness t);
            do ei' <- secure_cast "initialize" t ei;
            let sinit := Sdo (Eassign (Evar n t) ei' t) in
            OK (t,nil,(sinit,sfree))
        end
    | Tpointer _ _ =>
        match inits with
        | nil => OK (t,nil,(Sskip,Sskip))
        | cons i is => 
            do ei <- init_data_to_expr i (type_signedness t);
            do ei' <- secure_cast "initialize" t ei;
            let sinit := Sdo (Eassign (Evar n t) ei' t) in
            OK (t,nil,(sinit,Sskip))
        end
    | Tarray bt sz a => match inits with
        | nil => 
            let t' := Tpointer bt a in
            let blt := builtin_new_array bt (Eval (Vlong (Int64.repr sz)) type_pint64u) in
            let sinit := Sdo (Eassign (Evar n t) blt t) in
            let send := Sdo (builtin_delete_array bt (Evar n t')) in
            OK (t',nil,(sinit,send))
        | _ => Error (msg "unsupported secret array variable initialization")
        end
    | Tfunction _ _ _ => Error (msg "unsupported secret variable function type")
    | Tstruct _ _ => Error (msg "unsupported secret variable struct type")
    | Tunion _ _ => Error (msg "unsupported secret variable union type")
    | Tvoid => Error (msg "unsupported secret variable void type")
    end.

Definition retype_secure_fn_var (n : ident) (t: type) : res ((ident * type) * (statement * statement)) :=
    do res <- initialize_secure_var n t nil;
    match res with
    | (t',_,s') => OK ((n,t'),s')
    end.

Fixpoint retype_secure_fn_vars (ps : list (ident * type)) : res (list (ident * type) * (statement * statement)) :=
  match ps with
  | nil => OK (nil,(Sskip,Sskip))
  | cons (n,t) xs =>
      do (x',sx') <- retype_secure_fn_var n t;
      do (xs',sxs') <- retype_secure_fn_vars xs;
      OK (cons x' xs',(ssequence (fst sx') (fst sxs'),ssequence (snd sx') (snd sxs')))
  end.

Definition extend_function_body (sbefore: statement) (safter: statement) (f: function) : function :=
 mkfunction
     (f.(fn_return))
     (f.(fn_callconv))
     (f.(fn_params))
     (f.(fn_vars))
     (ssequence sbefore (append_to_statement (f.(fn_body)) safter)).

Definition retype_secure_function (ce: composite_env) (e: typenv) (f: function) : res function :=
  let e := bind_vars (bind_vars e f.(fn_params)) f.(fn_vars) in
  do (vars',ss) <- retype_secure_fn_vars f.(fn_vars);
  do (s',tmps) <- retype_secure_stmt ce e f.(fn_return) f.(fn_body);
  let vars'' := vars' ++ PTree.elements tmps in
  let s'' := ssequence (fst ss) (append_to_statement (f.(fn_body)) (snd ss)) in
  OK (mkfunction f.(fn_return) f.(fn_callconv) f.(fn_params) vars'' s'').
  
Definition retype_secure_fundef (ce: composite_env) (e: typenv) (fd: fundef) : res fundef :=
  match fd with
  | Internal f => do f' <- retype_secure_function ce e f; OK (Internal f')
  | External id args res cc => OK (External id args res cc)
  end.

Definition retype_secure_globvar (n: ident) (gv: globvar type) : res (globvar type * (statement * statement)) :=
    do res <- initialize_secure_var n gv.(gvar_info) gv.(gvar_init);
    match res with
    | (t',inits',s') => OK (mkglobvar t' inits' gv.(gvar_readonly) gv.(gvar_volatile),s')
    end.

Definition retype_secure_globdef (n: ident) (gd: globdef fundef type) : res (globdef fundef type * (statement * statement)) :=
    match gd with
    | Gfun f => OK (Gfun f,(Sskip,Sskip))
    | Gvar gv => do (gv',ss') <- retype_secure_globvar n gv; OK (Gvar gv',ss')
    end.
    
Fixpoint retype_secure_globdefs (defs: list (ident * globdef fundef type)) : res (list (ident * globdef fundef type) * (statement * statement)) :=
    match defs with
    | nil => OK (nil,(Sskip,Sskip))
    | cons (id,x) xs => do (x',s') <- retype_secure_globdef id x; do (xs',ss') <- retype_secure_globdefs xs; OK (cons (id,x') xs',(ssequence (fst s') (fst ss'),ssequence (snd s') (snd ss')))
    end.

Fixpoint extend_main (main: ident) (defs : list (ident * globdef fundef type)) (sbefore: statement) (safter: statement) : res (list (ident * globdef fundef type)) :=
    match defs with
    | nil => Error (msg "could not find main")
    | cons (id,x) xs => if ident_eq id main
        then match x with
        | Gfun (Internal f) => OK (cons (id,Gfun (Internal (extend_function_body sbefore safter f))) xs)
        | _ => Error (msg "could not add statement to non-internal main")
        end
        else do xs' <- extend_main main xs sbefore safter; OK (cons (id,x) xs')
    end.

(* structs and unions with secret content must be tagged as secret *)
Definition retype_secure_composite_definition (c: composite_definition) : res composite_definition :=
  match c with
  | Composite id su m a => if eqb (attr_secret a) (existsb type_has_secret (map snd m))
      then OK c
      else Error (msg "composite type with security does not match members")
  end.

Fixpoint retype_secure_composite_definitions (ts: list composite_definition) : res (list composite_definition) :=
  match ts with
  | nil => OK nil
  | cons x xs =>
      do x' <- retype_secure_composite_definition x;
      do xs' <- retype_secure_composite_definitions xs;
      OK (cons x' xs')
  end.

Definition retype_secure_program (p: program) : res program :=
  do types' <- retype_secure_composite_definitions p.(prog_types);
  do (defs,ss) <- retype_secure_globdefs p.(prog_defs);
  do p' <- make_program types' defs p.(prog_public) p.(prog_main);
        
  let e := bind_globdef (PTree.empty _) defs in
  let ce := p'.(prog_comp_env) in
  do tp <- transform_partial_program (retype_secure_fundef ce e) p';
  
  do defs' <- extend_main p'.(prog_main) tp.(AST.prog_defs) (fst ss) (snd ss);
  
  make_program p'.(prog_types) defs' p'.(prog_public) p'.(prog_main).

(**
    Remove security qualifiers
**)

Fixpoint remsec_type (t : type) : res type := 
  let tsec := Tlong Unsigned (make_public_attr (attr_of_type t)) in
  match t with
  | Tvoid => OK Tvoid
  | Tint _ _ a => if a.(attr_secret) then OK tsec else OK t
  | Tlong _ a => if a.(attr_secret) then OK tsec else OK t
  | Tfloat _ a => if a.(attr_secret) then OK tsec else OK t
  | Tpointer bt a => if a.(attr_secret) then OK tsec else do bt' <- remsec_type bt; OK (Tpointer bt' a)
  | Tarray bt sz a => if a.(attr_secret) then OK tsec else do bt' <- remsec_type bt; OK (Tarray bt' sz a)
  | Tfunction targs tret cconv =>
      do targs' <- remsec_types targs;
      do tret' <- remsec_type tret;
      OK (Tfunction targs' tret' cconv)
  | Tstruct n a => if a.(attr_secret) then OK tsec else OK t
  | Tunion n a => if a.(attr_secret) then OK tsec else OK t
  end
with remsec_types (ts : typelist) : res typelist :=
  match ts with
  | Tnil => OK Tnil
  | Tcons x xs => do x' <- remsec_type x; do xs' <- remsec_types xs; OK (Tcons x' xs')
  end.


Definition remsec_typ_of_type (t: type) : res AST.typ :=
  let tsec := AST.Tlong
  match t with
  | Tvoid => OK AST.Tint
  | Tint _ _ a => if a.(attr_secret) then OK tsec else OK AST.Tint
  | Tlong _ a => if a.(attr_secret) then OK tsec else OK AST.Tlong
  | Tfloat F32 a => if a.(attr_secret) then OK tsec else OK AST.Tsingle
  | Tfloat F64 a => if a.(attr_secret) then OK tsec else OK AST.Tfloat
  | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tstruct _ _ | Tunion _ _ => OK AST.Tptr
  end.
  
Definition remsec_opttyp_of_type (t: type) : res (option AST.typ) :=
  if type_eq t Tvoid then OK None else do optty' <- remsec_typ_of_type t; OK (Some optty').

Fixpoint remsec_typlist_of_typelist (tl: typelist) : res (list AST.typ) :=
  match tl with
  | Tnil => OK nil
  | Tcons hd tl => do hd' <- remsec_typ_of_type hd; do tl' <- remsec_typlist_of_typelist tl; OK (hd' :: tl')
  end.

Definition remsec_signature (s: signature) (targs : typelist) (tres: type) : res signature := 
  do typs' <- remsec_typlist_of_typelist targs;
  do res' <- remsec_opttyp_of_type tres;
  OK (mksignature typs' res' s.(sig_cc)).

Definition remsec_external_function (ef: external_function) (targs : typelist) (tres : type) : res external_function :=
  match ef with
  | EF_external n sg => do sg' <- remsec_signature sg targs tres; OK (EF_external n sg')
  | ef => OK ef
  end.

Fixpoint remsec_expr (a: expr) : res (expr) :=
  match a with
  | Eval v t =>
      do t' <- remsec_type t;
      OK (Eval v t')
  | Evar x t =>
      do t' <- remsec_type t;
      OK (Evar x t')
  | Efield r f t =>
      do t' <- remsec_type t;
      do r' <- remsec_expr r;
      OK (Efield r' f t')
  | Evalof r t =>
      do t' <- remsec_type t;
      do r' <- remsec_expr r;
      OK (Evalof r' t')
  | Ederef r t =>
      do t' <- remsec_type t;
      do r' <- remsec_expr r;
      OK (Ederef r' t')
  | Eaddrof l t =>
      do t' <- remsec_type t;
      do l' <- remsec_expr l;
      OK (Eaddrof l' t')
  | Eunop op r1 t =>
      do t' <- remsec_type t;
      do r1' <- remsec_expr r1;
      OK (Eunop op r1' t')
  | Ebinop op r1 r2 t =>
      do t' <- remsec_type t;
      do r1' <- remsec_expr r1;
      do r2' <- remsec_expr r2;
      OK (Ebinop op r1' r2' t')
  | Ecast r t =>
      do t' <- remsec_type t;
      do r' <- remsec_expr r;
      OK (Ecast r' t')
  | Eseqand r1 r2 t =>
      do t' <- remsec_type t;
      do r1' <- remsec_expr r1;
      do r2' <- remsec_expr r2;
      OK (Eseqand r1' r2' t')
  | Eseqor r1 r2 t =>
      do t' <- remsec_type t;
      do r1' <- remsec_expr r1;
      do r2' <- remsec_expr r2;
      OK (Eseqor r1' r2' t')
  | Econdition r1 r2 r3 t =>
      do t' <- remsec_type t;
      do r1' <- remsec_expr r1;
      do r2' <- remsec_expr r2;
      do r3' <- remsec_expr r3;
      OK (Econdition r1' r2' r3' t')
  | Esizeof r t =>
      do t' <- remsec_type t;
      do r' <- remsec_type r;
      OK (Esizeof r' t')
  | Ealignof r t =>
      do t' <- remsec_type t;
      do r' <- remsec_type r;
      OK (Ealignof r' t')
  | Eassign l r t =>
      do t' <- remsec_type t;
      do l' <- remsec_expr l;
      do r' <- remsec_expr r;
      OK (Eassign l' r' t')
  | Eassignop op l r tres t => 
      do tres' <- remsec_type tres;
      do t' <- remsec_type t;
      do l' <- remsec_expr l;
      do r' <- remsec_expr r;
      OK (Eassignop op l' r' tres' t')
  | Epostincr id l t =>
      do t' <- remsec_type t;
      do l' <- remsec_expr l;
      OK (Epostincr id l' t')
  | Ecomma r1 r2 t =>
      do t' <- remsec_type t;
      do r1' <- remsec_expr r1;
      do r2' <- remsec_expr r2;
      OK (Ecomma r1' r2' t')
  | Ecall rname rargs t =>
      do t' <- remsec_type t;
      do rname' <- remsec_expr rname; 
      do rargs' <- remsec_exprlist rargs;
      OK (Ecall rname' rargs' t')
  | Ebuiltin ef tyargs rargs t =>
      do ef' <- remsec_external_function ef tyargs t;
      do tyargs' <- remsec_types tyargs;
      do rargs' <- remsec_exprlist rargs;
      do t' <- remsec_type t;
      OK (Ebuiltin ef' tyargs' rargs' t')
  | Eloc b of t =>
      do t' <- remsec_type t;
      OK (Eloc b of t')
  | Eparen r ty t =>
      do t' <- remsec_type t;
      do ty' <- remsec_type ty;
      do r' <- remsec_expr r;
      OK (Eparen r' ty' t')
  end
with remsec_exprlist (rs: exprlist) : res (exprlist) :=
  match rs with
  | Enil => OK Enil
  | Econs x xs => do x' <- remsec_expr x; do xs' <- remsec_exprlist xs; OK (Econs x' xs')
  end.

Fixpoint remsec_stmt (s: statement) : res statement :=
  match s with
  | Sskip => OK Sskip
  | Sdo a => do a' <- remsec_expr a; OK (Sdo a')
  | Ssequence s1 s2 =>
      do s1' <- remsec_stmt s1;
      do s2' <- remsec_stmt s2;
      OK (ssequence s1' s2')
  | Sifthenelse a s1 s2 =>
      do a' <- remsec_expr a;
      do s1' <- remsec_stmt s1; do s2' <- remsec_stmt s2;
      OK (Sifthenelse a' s1' s2')
  | Swhile a s =>
      do a' <- remsec_expr a;
      do s' <- remsec_stmt s;
      OK (Swhile a' s')
  | Sdowhile a s =>
      do a' <- remsec_expr a;
      do s' <- remsec_stmt s;
      OK (Sdowhile a' s')
  | Sfor s1 a s2 s3 =>
      do a' <- remsec_expr a;
      do s1' <- remsec_stmt s1;
      do s2' <- remsec_stmt s2;
      do s3' <- remsec_stmt s3;
      OK (Sfor s1' a' s2' s3')
  | Sbreak => OK Sbreak
  | Scontinue => OK Scontinue
  | Sreturn None => OK (Sreturn None)
  | Sreturn (Some a) =>
      do a' <- remsec_expr a;
      OK (Sreturn (Some a'))
  | Sswitch a sl =>
      do a' <- remsec_expr a;
      do sl' <- remsec_lblstmts sl;
      OK (Sswitch a' sl')
  | Slabel lbl s => do s' <- remsec_stmt s; OK (Slabel lbl s')
  | Sgoto lbl => OK (Sgoto lbl)
  end
with remsec_lblstmts (sl: labeled_statements) : res labeled_statements :=
  match sl with
  | LSnil => OK LSnil
  | LScons c s sl =>
      do s' <- remsec_stmt s; do sl' <- remsec_lblstmts sl;
      OK (LScons c s' sl')
  end.

Definition remsec_fn_var (var : ident * type) : res (ident * type) :=
    do ty' <- remsec_type (snd var);
    OK (fst var,ty').

Fixpoint remsec_fn_vars (vars : list (ident * type)) : res (list (ident * type)) :=
  match vars with
  | nil => OK nil
  | cons x xs => do x' <- remsec_fn_var x; do xs' <- remsec_fn_vars xs; OK (cons x' xs')
  end.

Definition remsec_function (f: function) : res function :=
    do ret' <- remsec_type f.(fn_return);
    do params' <- remsec_fn_vars f.(fn_params);
    do vars' <- remsec_fn_vars f.(fn_vars);
    do body' <- remsec_stmt f.(fn_body);
    OK (mkfunction ret' f.(fn_callconv) params' vars' body').

Definition remsec_fundef (n: ident) (fd: fundef) : res fundef :=
  match fd with
  | Internal f => do f' <- remsec_function f; OK (Internal f')
  | External ef targs tres cconv => 
      do targs' <- remsec_types targs;
      do tres' <- remsec_type tres;
      do ef' <- remsec_external_function ef targs' tres';
      OK (External ef' targs' tres' cconv)
  end.
    
Definition remsec_globdef (n: ident) (t: type) : res type :=
    remsec_type t.

Definition remsec_member (xy : ident * type) : res (ident * type) := 
    match xy with
    | (x,y) => do y' <- remsec_type y; OK (x,y')
    end.

Fixpoint remsec_members (xs : list (ident * type)) : res (list (ident * type)) := 
    match xs with
    | nil => OK nil
    | x :: xs => do x' <- remsec_member x; do xs' <- remsec_members xs; OK (x'::xs')
    end.

Definition remsec_composite_definition (c: composite_definition) : res composite_definition :=
    match c with
    | Composite id su ms a =>
        do ms' <- (remsec_members ms);
        OK (Composite id su ms' (make_public_attr a))
    end.

Fixpoint remsec_composite_definitions (xs : list composite_definition) : res (list composite_definition) := 
    match xs with
    | nil => OK nil
    | x :: xs => do x' <- remsec_composite_definition x; do xs' <- remsec_composite_definitions xs; OK (x'::xs')
    end.

Definition remsec_program (p: program) : res program :=
    do tp <- transform_partial_program2 remsec_fundef remsec_globdef p;
    do types' <- remsec_composite_definitions p.(prog_types);
    make_program types' tp.(AST.prog_defs) p.(prog_public) p.(prog_main).

(** Typechecker **)

(*TODO: consider function pointers *)
(* TODO: typecheck secret global variable definitions, currently not allowed *)
Definition typecheck_secure_program (p: program) : res program :=
    do p1 <- typecheck_program p;
    do p2 <- retype_secure_program p1;
    remsec_program p2.
