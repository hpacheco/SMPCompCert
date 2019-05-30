
Require Import String.
Require Import Coqlib Maps Integers Floats Errors.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events.
Require Import Ctypes Ctyping Cop Csyntax Csem.

Local Open Scope error_monad_scope.

(**
    Security typechecker
    Assumes that typechecking has already passed, and thus that all intermediate expressions are corretly typed (with security annotations).
    Performs implicit classification.
    Introduces security builtin operations.
    Replaces security types for void pointers.
**)

(** Utils **)

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

Definition make_public_attr (a : attr) : attr :=
  {| attr_volatile := a.(attr_volatile);
     attr_secret := false;
     attr_alignas := a.(attr_alignas);
  |}.
  
Definition set_attr_secret (sec:bool) (a : attr) : attr :=
  {| attr_volatile := a.(attr_volatile);
     attr_secret := sec;
     attr_alignas := a.(attr_alignas);
  |}.
  
Definition type_is_public (ty: type) : bool :=
  negb (type_is_secret ty).
  
Definition make_public_type (ty: type) : type :=
  change_attributes make_public_attr ty.

Definition check_public (t: type) : res unit :=
  if type_is_public t then OK tt else Error (msg "unsupported secure control flow").
  
Definition check_secret (t: type) : res unit :=
  if type_is_secret t then OK tt else Error (msg "expected secret type").

(** builtins **)

Definition external_new_int8_array : external_function :=
    EF_builtin "new_int8_array" (mksignature (cons AST.Tlong nil) (Some Tptr) cc_default).
Definition builtin_new_int8_array (sz: expr) (rty : type) : expr :=
    Ebuiltin external_new_int8_array (Tcons (typeof sz) Tnil) (Econs sz Enil) rty.

Definition external_add_int8 : external_function :=
    EF_builtin "add_int8" (mksignature (cons Tptr (cons Tptr nil)) (Some Tptr) cc_default).
Definition builtin_add_int8 (e1 e2: expr) : expr :=
    Ebuiltin external_add_int8 (Tcons (typeof e1) (Tcons (typeof e2) Tnil)) (Econs e1 (Econs e2 Enil)) (typeof e1).

(** Security typechecker **)

(*TODO undefined*)
Definition secure_classify (t: type) (e: expr) : res expr := OK e.

(*TODO undefined*)
Definition secure_convert (rt t: type) (e: expr) : res expr := OK e.

Definition is_public_cast (rt: type) (t: type) (e: expr) : bool :=
    negb (type_has_secret rt) && negb (type_has_secret t).

Definition public_cast (rt: type) (t: type) (e: expr) : res expr :=
   if is_public_cast rt t e then OK e else Error (msg "unsupported non-public cast").

(* Disallow any cast involving security types besides direct classifies or conversions *)
(* TODO: casts are still not safe! e.g. int => void => int secret, int secret* => int** *)
Definition secure_cast (rt: type) (t: type) (e:expr) : res expr :=
    match (type_is_secret rt,type_is_secret t) with
    | (false,false) => OK e
    | (true,false) => do e' <- public_cast (make_public_type rt) t e; secure_classify t e'
    | (false,true) => Error (msg "unsupported cast from secure to non-secure type, try declassify")
    | (true,true) => secure_convert rt t e
    end.

Definition secure_binarith_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_case_i sg => OK (Tint I32 sg (snoattr (type_is_secret ty1 || type_is_secret ty2)))
  | bin_case_l sg => OK (Tlong sg (snoattr (type_is_secret ty1 || type_is_secret ty2)))
  | bin_case_f => OK (Tfloat F64 (snoattr (type_is_secret ty1 || type_is_secret ty2)))
  | bin_case_s => OK (Tfloat F32 (snoattr (type_is_secret ty1 || type_is_secret ty2)))
  | bin_default   => Error (msg m)
  end.

Definition secure_binarith_int_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_case_i sg => OK (Tint I32 sg (snoattr (type_is_secret ty1 || type_is_secret ty2)))
  | bin_case_l sg => OK (Tlong sg (snoattr (type_is_secret ty1 || type_is_secret ty2)))
  | _ => Error (msg m)
  end.

Definition secure_shift_op_type (ty1 ty2: type) (m: string): res type :=
  match classify_shift ty1 ty2 with
  | shift_case_ii sg | shift_case_il sg => OK (Tint I32 sg (snoattr (type_is_secret ty1 || type_is_secret ty2)))
  | shift_case_li sg | shift_case_ll sg => OK (Tlong sg (snoattr (type_is_secret ty1 || type_is_secret ty2)))
  | shift_default => Error (msg m)
  end.

Definition secure_comparison_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_default => Error (msg m)
  | c => OK (Tint I32 Signed (snoattr (type_is_secret ty1 || type_is_secret ty2)))
  end.

Definition secure_type_binop (op: binary_operation) (ty1 ty2: type) : res type :=
  match op with
  | Oadd => secure_binarith_type ty1 ty2 "operator +"
  | Osub => secure_binarith_type ty1 ty2 "operator infix -"
  | Omul => secure_binarith_type ty1 ty2 "operator infix *"
  | Odiv => secure_binarith_type ty1 ty2 "operator /"
  | Omod => secure_binarith_int_type ty1 ty2 "operator %"
  | Oand => secure_binarith_int_type ty1 ty2 "operator &"
  | Oor  => secure_binarith_int_type ty1 ty2 "operator |"
  | Oxor => secure_binarith_int_type ty1 ty2 "operator ^"
  | Oshl => secure_shift_op_type ty1 ty2 "operator <<"
  | Oshr => secure_shift_op_type ty1 ty2 "operator >>"
  | Oeq  => secure_comparison_type ty1 ty2 "operator =="
  | One  => secure_comparison_type ty1 ty2 "operator !="
  | Olt  => secure_comparison_type ty1 ty2 "operator <"
  | Ogt  => secure_comparison_type ty1 ty2 "operator >"
  | Ole  => secure_comparison_type ty1 ty2 "operator <="
  | Oge  => secure_comparison_type ty1 ty2 "operator >="
  end.

(*TODO undefined *)
Definition retype_secure_type (t: type) : res type := OK t.

Fixpoint retype_secure_typelist (ts: typelist) : res typelist :=
    match ts with
    | Tnil => OK Tnil
    | Tcons x xs => do x' <- retype_secure_type x; do xs' <- retype_secure_typelist xs; OK (Tcons x' xs')
    end.

(*TODO undefined*)
Definition secure_binop_expr (op: binary_operation) (t: type) (e1 e2 : expr) : res expr :=
  do _ <- check_secret t;
  match t with
  | Tint I8 Signed _ => OK (builtin_add_int8 e1 e2)
  | _ => Error (msg "unsupported secure binop")
  end.

Definition secure_binop (op : binary_operation) (t1 t2 t: type) (e1 e2: expr): res (expr * type) :=
  match (type_is_secret t1,type_is_secret t2) with
  | (false,false) => (* assumes that casts preserve non-top-level security tags*)
      do t' <- retype_secure_type t;
      OK (Ebinop op e1 e2 t',t)
  | _ =>
      do t' <- secure_type_binop op t1 t2;
      do e1' <- secure_cast t' t1 e1;
      do e2' <- secure_cast t' t2 e2;
      do e' <- secure_binop_expr op t' e1' e2';
      OK (e',t')
  end.
    

(*TODO undefined *)
(* returns a typechecked expression with security annotations already removed, and the typechecked security type *)
Fixpoint retype_secure_expr (ce: composite_env) (e: typenv) (a: expr) : res (expr * type) :=
  match a with
  | Eval v t => OK (a,t)
  | Evar x t => OK (a,t)
  | Efield r f t =>
      do (r',tr') <- retype_secure_expr ce e r;
      do t' <- type_field ce tr' f;
      do t'' <- retype_secure_type t';
      OK (Efield r f t'',t')
  | Evalof r t =>
      do (r',tr') <- retype_secure_expr ce e r;
      OK (Evalof r' (typeof r'),tr')
  (*| Ederef r t => if type_is_public (typeof r)
      then
          do r' <- retype_secure_expr r;
          do t' <- type_deref (typeof r);
          do t'' <- retype_secure_type t';
          OK (Ederef r' t'')
      else
          do (x,eoff) <- match r with
          | Evar x xt => 
          | Ebinop Oadd (Evar x xt) e2 _ =>
          | _ => Error (msg "unsupported array projection")
          end;*)
  | Eaddrof l t =>
      do (l',lt') <- retype_secure_expr ce e l;
      OK (Eaddrof l' (Tpointer (typeof l) pnoattr),Tpointer lt' pnoattr)
(*  | Eunop op r1 t =>
      do (r1',tr1') <- retype_secure_expr ce e r1;*)    
  | Ebinop op r1 r2 t =>
      do (r1',tr1') <- retype_secure_expr ce e r1;
      do (r2',tr2') <- retype_secure_expr ce e r2;
      secure_binop op tr1' tr2' t r1' r2'
  | _ => Error (msg "undefined")
  end.

Definition retype_secure_public_expr (ce: composite_env) (e: typenv) (a: expr) : res expr :=
    do _ <- check_public (typeof a);
    do (e',_) <- retype_secure_expr ce e a;
    OK e'.

Fixpoint retype_secure_stmt (ce: composite_env) (e: typenv) (rt: type) (s: statement) : res statement :=
  match s with
  | Sskip => OK Sskip
  | Sdo a => do (a',_) <- retype_secure_expr ce e a; OK (Sdo a')
  | Ssequence s1 s2 =>
      do s1' <- retype_secure_stmt ce e rt s1;
      do s2' <- retype_secure_stmt ce e rt s2;
      OK (Ssequence s1' s2')
  | Sifthenelse a s1 s2 =>
      do a' <- retype_secure_public_expr ce e a;
      do s1' <- retype_secure_stmt ce e rt s1; do s2' <- retype_secure_stmt ce e rt s2;
      OK (Sifthenelse a' s1' s2')
  | Swhile a s =>
      do a' <- retype_secure_public_expr ce e a;
      do s' <- retype_secure_stmt ce e rt s;
      OK (Swhile a' s')
  | Sdowhile a s =>
      do a' <- retype_secure_public_expr ce e a;
      do s' <- retype_secure_stmt ce e rt s;
      do _ <- check_public (typeof a);
      OK (Sdowhile a' s')
  | Sfor s1 a s2 s3 =>
      do a' <- retype_secure_public_expr ce e a;
      do s1' <- retype_secure_stmt ce e rt s1;
      do s2' <- retype_secure_stmt ce e rt s2;
      do s3' <- retype_secure_stmt ce e rt s3;
      OK (Sfor s1' a' s2' s3')
  | Sbreak => OK Sbreak
  | Scontinue => OK Scontinue
  | Sreturn None => OK (Sreturn None)
  | Sreturn (Some a) =>
      do (a',t') <- retype_secure_expr ce e a;
      do a'' <- secure_cast rt t' a';
      OK (Sreturn (Some a''))
  | Sswitch a sl =>
      do a' <- retype_secure_public_expr ce e a;
      do sl' <- retype_secure_lblstmts ce e rt sl;
      OK (Sswitch a' sl')
  | Slabel lbl s => do s' <- retype_secure_stmt ce e rt s; OK (Slabel lbl s')
  | Sgoto lbl => OK (Sgoto lbl)
  end
with retype_secure_lblstmts (ce: composite_env) (e: typenv) (rt: type) (sl: labeled_statements) : res labeled_statements :=
  match sl with
  | LSnil => OK LSnil
  | LScons case s sl =>
      do s' <- retype_secure_stmt ce e rt s; do sl' <- retype_secure_lblstmts ce e rt sl;
      OK (LScons case s' sl')
  end.

(*TODO undefined *)
Definition retype_secure_fn_params (ps : list (ident * type)) : res (list (ident * type)) := OK ps.

(*TODO fill with more types *)
Definition initialize_secure_var (n: ident) (t t': type) : res statement :=
    match t with
    | Tint I8 Signed a => OK Sskip
    | Tarray bt sz a => if a.(attr_secret)
        then if type_has_secret bt then Error (msg "unsupported secret array") else
        do blt <- match bt with
        | Tint I8 Signed _ => OK (builtin_new_int8_array (Eval (Vlong (Int64.repr sz)) (Tlong Signed pnoattr)) t')
        | _ => Error (msg "unsupported secret array")
        end;
        OK (Sdo (Eassign (Evar n t') blt t'))
        else OK Sskip
    | _ => Error (msg "unsupported secure variable type")
    end.

Definition retype_secure_fn_var (n : ident) (t: type) : res ((ident * type) * statement) :=
    do t' <- retype_secure_type t;
    do s' <- initialize_secure_var n t t';
    OK (pair (pair n t') s').

(*TODO undefined *)
Definition retype_secure_fn_vars (ps : list (ident * type)) : res (list (ident * type) * statement) := OK (ps,Sskip).

Definition retype_secure_function (ce: composite_env) (e: typenv) (f: function) : res function :=
  let e := bind_vars (bind_vars e f.(fn_params)) f.(fn_vars) in
  do s' <- retype_secure_stmt ce e f.(fn_return) f.(fn_body);
  do ret' <- retype_secure_type f.(fn_return);
  do params' <- retype_secure_fn_params f.(fn_params);
  do (vars',s0) <- retype_secure_fn_vars f.(fn_vars);
  OK (mkfunction ret' f.(fn_callconv) params' vars' (Ssequence s0 s')).         

Definition retype_secure_fundef (ce: composite_env) (e: typenv) (fd: fundef) : res fundef :=
  match fd with
  | Internal f => do f' <- retype_secure_function ce e f; OK (Internal f')
  | External id args res cc =>
      do args' <- retype_secure_typelist args;
      do res' <- retype_secure_type res;
      OK (External id args' res' cc)
  end.

(* TODO: reject global secure variables *)
Definition typecheck_secure_program (p: program) : res program :=
  let e := bind_globdef (PTree.empty _) p.(prog_defs) in
  let ce := p.(prog_comp_env) in
  do tp <- transform_partial_program (retype_secure_fundef ce e) p;
  OK {| prog_defs := tp.(AST.prog_defs);
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_types := p.(prog_types);
        prog_comp_env := ce;
        prog_comp_env_eq := p.(prog_comp_env_eq) |}.

(** Remove security qualifiers **)

(*Definition remsec_type (t : type) : res type := OK t.

Definition remsec_fundef (n: ident) (f: fundef) : res fundef := OK f.
    
Definition remsec_globdef (n: ident) (t: type) : res type :=
    remsec_type t.

Definition remsec_member (xy : ident * type) : res (ident * type) := 
    match xy with
    | pair x y => do y' <- remsec_type y; OK (pair x y')
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
    OK {| prog_defs := tp.(AST.prog_defs);
          prog_public := p.(prog_public);
          prog_main := p.(prog_main);
          prog_types := p.(prog_types);
          prog_comp_env := p.(prog_comp_env);
          prog_comp_env_eq := p.(prog_comp_env_eq) |}.*)
