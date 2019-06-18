
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
    Replaces security types for void pointers.
**)

(** Utils **)

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

Definition show_type (t: type) : string :=
  match t with
  | Tvoid => "void"
  | Tint IBool _ a => show_attr a++" bool"
  | Tint I8 s a => show_attr a++show_signedness s++"int8"
  | Tint I16 s a => show_attr a++show_signedness s++"int16"
  | Tint I32 s a => show_attr a++show_signedness s++"int32"
  | Tlong s a => show_attr a++show_signedness s++"int64"
  | Tfloat F32 a => show_attr a++"float32"
  | Tfloat F64 a => show_attr a++"float64"
  | _ => "error"
  end.

(** builtins **)

Definition external_new_array (t: type) : external_function :=
    EF_external ("new_"++show_type (make_public_type t)++"_array") (mksignature (cons AST.Tlong nil) (Some Tptr) cc_default).
Definition external_load_array (t: type) : external_function :=
    EF_external ("load_"++show_type (make_public_type t)++"_array") (mksignature (cons Tptr (cons AST.Tlong nil)) (Some (typ_of_type t)) cc_default).
    
Definition builtin_new_array (t: type) (e1: expr) : expr :=
    Ebuiltin (external_new_array t) (Tcons (typeof e1) Tnil) (Econs e1 Enil) (Tpointer t snoattr).
Definition builtin_load_array (t: type) (e1 e2: expr) : expr :=
    Ebuiltin (external_load_array t) (Tcons (typeof e1) (Tcons (typeof e2) Tnil)) (Econs e1 (Econs e2 Enil)) (make_secret_type t).
    
Definition external_classify (t: type) : external_function :=
    EF_external ("classify_"++show_type (make_public_type t)) (mksignature (cons (typ_of_type t) nil) (Some (typ_of_type t)) cc_default).
Definition external_declassify (t: type) : external_function :=
    EF_external ("declassify_"++show_type (make_public_type t)) (mksignature (cons (typ_of_type t) nil) (Some (typ_of_type t)) cc_default).
Definition external_binop (n: string) (t: type) : external_function :=
    EF_external (n++"_"++show_type (make_public_type t)) (mksignature (cons Tptr (cons (typ_of_type t) nil)) (Some (typ_of_type t)) cc_default).
    
Definition builtin_classify (t: type) (e1: expr) : expr :=
    Ebuiltin (external_classify t) (Tcons (typeof e1) Tnil) (Econs e1 Enil) (make_secret_type t).
Definition builtin_declassify (t: type) (e1: expr) : expr :=
    Ebuiltin (external_declassify t) (Tcons (typeof e1) Tnil) (Econs e1 Enil) (make_public_type t).
Definition builtin_binop (n: string) (t: type) (e1 e2: expr) : expr :=
    Ebuiltin (external_binop n t) (Tcons (typeof e1) (Tcons (typeof e2) Tnil)) (Econs e1 (Econs e2 Enil)) (typeof e1).

(** Introduce secure builtins **)

Definition secure_classify (t: type) (e: expr) : res expr :=
  if is_base_type t
      then OK (builtin_classify t e)
      else Error (msg "unsupported secure classify").

Definition secure_convert (rt: type) (e: expr) : res expr :=
  let t := typeof e in
  if type_eq rt t then OK e
  else match (rt,typeof e) with
  | _ => Error (msg "unsupported secure conversion")  
  end.

Definition is_public_cast (rt: type) (e: expr) : bool :=
    negb (type_has_secret rt) && negb (type_has_secret (typeof e)).

Definition public_cast (rt: type) (e: expr) : res expr :=
   if is_public_cast rt e then OK e else Error (msg "unsupported non-public cast").

(* Disallow any cast involving security types besides direct classifies or conversions *)
(* TODO: casts are still not safe! e.g. int => void => int secret, int secret* => int** *)
Definition secure_cast (rt: type) (e:expr) : res expr :=
    let t := typeof e in
    match (type_is_secret rt,type_is_secret t) with
    | (false,false) => OK e
    | (true,false) => do e' <- public_cast (make_public_type rt) e; secure_classify t e'
    | (false,true) => Error (msg "unsupported cast from secure to non-secure type, try declassify")
    | (true,true) => secure_convert rt e
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
      do e1' <- secure_cast t e1;
      secure_unop_expr op t e1'
  end.

Definition secure_binop_expr (op: binary_operation) (t: type) (e1 e2 : expr) : res expr :=
  do _ <- check_secret t ("secure "++show_binop op);
  match op with
  | Oadd => if is_base_type t
      then OK (builtin_binop "add" t e1 e2)
      else Error (msg ("unsupported secure "++show_binop op))
  | _ => Error (msg ("unsupported secure "++show_binop op))
  end.

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

Definition secure_binop (pop : expr -> expr -> type -> expr) (sop : type -> expr -> expr -> res expr) (t: type) (e1 e2: expr): res (expr) :=
  match (type_is_secret (typeof e1),type_is_secret (typeof e2)) with
  | (false,false) => (* assumes that regular casts preserve non-top-level security tags*)
      OK (pop e1 e2 t)
  | _ =>
      do e1' <- secure_cast t e1;
      do e2' <- secure_cast t e2;
      sop t e1' e2'
  end.

Definition secure_condition (t: type) (e1 e2 e3: expr) : res expr :=
    do _ <- check_public (typeof e1) "conditional";
    do e2' <- secure_cast t e2;
    do e3' <- secure_cast t e3;
    OK (Econdition e1 e2' e3' t).

Fixpoint retype_secure_arguments (el: exprlist) (tyl: typelist) : res exprlist :=
  match el, tyl with
  | Enil, Tnil => OK Enil
  | Enil, _ => Error (msg "not enough arguments")
  | _, Tnil => if strict then Error (msg "too many arguments") else OK Enil
  | Econs e1 el, Tcons ty1 tyl =>
      do e1' <- secure_cast ty1 e1;
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
  | Evar x t => OK (e,Eval (Vlong Int64.zero) type_pint64u)
  | Ebinop Oadd e1 e2 t => match classify_add (typeof e1) (typeof e2) with
      | add_case_pi _ _ | add_case_pl _ => do (x',i') <- split_array_proj e1; do i'' <- ebinop Oadd i' e2; OK (x',i'')
      | add_case_ip _ _ | add_case_lp _ => do (x',i') <- split_array_proj e2; do i'' <- ebinop Oadd i' e1; OK (x',i'')
      | _ => Error (msg "+ secure pointer dereferencing could not be converted into projection")
      end
  | Ebinop Osub e1 e2 t => match classify_sub (typeof e1) (typeof e2) with
      | sub_case_pi _ _ | sub_case_pl _ => do (x',i') <- split_array_proj e1; do i'' <- ebinop Osub i' e2; OK (x',i'')
      | sub_case_pp _ =>
          do (x1',i1') <- split_array_proj e1;
          do (x2',i2') <- split_array_proj e2;
          do _ <- check_same_expr x1' x2';
          do i' <- ebinop Osub i1' i2';
          OK (x1',i')
      | _ => Error (msg "+ secure pointer dereferencing could not be converted into projection")
      end
  | _ => Error (msg "secure pointer dereferencing could not be converted into projection")
  end.

Definition secure_load_array (t: type) (x i : expr) : res expr :=
  if is_base_type t
      then OK (builtin_load_array t x i)
      else Error (msg "unsupported secure array projection").

Definition secure_deref (e: expr) (t: type) : res expr :=
  if type_is_public (typeof e)
      then OK (Ederef e t)
      else
          do (x,i) <- split_array_proj e;
          secure_load_array t x i.

(* returns a typechecked expression with security ops replaced by builtins *)
Fixpoint retype_secure_expr (ce: composite_env) (e: typenv) (a: expr) : res (expr) :=
  match a with
  | Eval v t => OK a
  | Evar x t => OK a
  | Efield r f t =>
      do r' <- retype_secure_expr ce e r;
      OK (Efield r' f t)
  | Evalof r t =>
      do r' <- retype_secure_expr ce e r;
      OK (Evalof r' t)
  | Ederef r t =>
      do r' <- retype_secure_expr ce e r;
      secure_deref r' t
  | Eaddrof l t =>
      do l' <- retype_secure_expr ce e l;
      OK (Eaddrof l' t)
  | Eunop op r1 t =>
      do r1' <- retype_secure_expr ce e r1;
      secure_unop op t r1'
  | Ebinop op r1 r2 t =>
      do r1' <- retype_secure_expr ce e r1;
      do r2' <- retype_secure_expr ce e r2;
      secure_binop (Ebinop op) (secure_binop_expr op) t r1' r2'
  | Ecast r t =>
      do r' <- retype_secure_expr ce e r;
      secure_cast t r
  | Eseqand r1 r2 t =>
      do r1' <- retype_secure_expr ce e r1;
      do r2' <- retype_secure_expr ce e r2;
      secure_binop Eseqand secure_eseqand_expr t r1' r2'
  | Eseqor r1 r2 t =>
      do r1' <- retype_secure_expr ce e r1;
      do r2' <- retype_secure_expr ce e r2;
      secure_binop Eseqor secure_eseqor_expr t r1' r2'
  | Econdition r1 r2 r3 t =>
      do r1' <- retype_secure_expr ce e r1;
      do r2' <- retype_secure_expr ce e r2;
      do r3' <- retype_secure_expr ce e r3;
      secure_condition t r1' r2' r3'
  | Esizeof r t => OK (Esizeof r t)
  | Ealignof r t => OK (Ealignof r t)
  | Eassign l r t =>
      do l' <- retype_secure_expr ce e l;
      do r' <- retype_secure_expr ce e r;
      do r'' <- secure_cast t r';
      OK (Eassign l' r'' t)
  | Eassignop op l r tres t => 
      do l' <- retype_secure_expr ce e l;
      do r' <- retype_secure_expr ce e r;
      do lr <- secure_binop (Ebinop op) (secure_binop_expr op) tres l' r';
      do lr' <- secure_cast t lr;
      OK (Eassign l' lr' t)
  | Epostincr id r t =>
      do r' <- retype_secure_expr ce e r;
      let one := Eval (Vint Int.one) (type_pint32s) in
      do radd1' <- secure_binop (Ebinop Oadd) (secure_binop_expr Oadd) t r' one;
      do rsub1' <- secure_binop (Ebinop Osub) (secure_binop_expr Osub) t r' one;
      match id with
      | Incr => OK (Ecomma (Eassign r' radd1' t) rsub1' t)
      | Decr => OK (Ecomma (Eassign r' rsub1' t) radd1' t)
      end
  | Ecomma r1 r2 t =>
      do r1' <- retype_secure_expr ce e r1;
      do r2' <- retype_secure_expr ce e r2;
      OK (Ecomma r1' r2' t)
  | Ecall rname rargs t =>
      do rname' <- retype_secure_expr ce e rname; 
      do rargs' <- retype_secure_exprlist ce e rargs;
      secure_call rname' rargs'
  | Ebuiltin ef tyargs rargs tyres =>
      do rargs' <- retype_secure_exprlist ce e rargs;
      do rargs'' <- retype_secure_arguments rargs' tyargs;
      OK (Ebuiltin ef tyargs rargs'' tyres)
  | Eloc _ _ _ => Error (msg "Eloc in source")
  | Eparen _ _ _ => Error (msg "Eparen in source")
  end
with retype_secure_exprlist (ce: composite_env) (e: typenv) (rs: exprlist) : res (exprlist) :=
  match rs with
  | Enil => OK Enil
  | Econs x xs => do x' <- retype_secure_expr ce e x; do xs' <- retype_secure_exprlist ce e xs; OK (Econs x' xs')
  end.

Definition retype_secure_public_expr (ce: composite_env) (e: typenv) (a: expr) (m: string) : res expr :=
    do _ <- check_public (typeof a) m;
    retype_secure_expr ce e a.

Fixpoint retype_secure_stmt (ce: composite_env) (e: typenv) (rt: type) (s: statement) : res statement :=
  match s with
  | Sskip => OK Sskip
  | Sdo a => do a' <- retype_secure_expr ce e a; OK (Sdo a')
  | Ssequence s1 s2 =>
      do s1' <- retype_secure_stmt ce e rt s1;
      do s2' <- retype_secure_stmt ce e rt s2;
      OK (Ssequence s1' s2')
  | Sifthenelse a s1 s2 =>
      do a' <- retype_secure_public_expr ce e a "ifthenelse";
      do s1' <- retype_secure_stmt ce e rt s1; do s2' <- retype_secure_stmt ce e rt s2;
      OK (Sifthenelse a' s1' s2')
  | Swhile a s =>
      do a' <- retype_secure_public_expr ce e a "while";
      do s' <- retype_secure_stmt ce e rt s;
      OK (Swhile a' s')
  | Sdowhile a s =>
      do a' <- retype_secure_public_expr ce e a "dowhile";
      do s' <- retype_secure_stmt ce e rt s;
      OK (Sdowhile a' s')
  | Sfor s1 a s2 s3 =>
      do a' <- retype_secure_public_expr ce e a "for";
      do s1' <- retype_secure_stmt ce e rt s1;
      do s2' <- retype_secure_stmt ce e rt s2;
      do s3' <- retype_secure_stmt ce e rt s3;
      OK (Sfor s1' a' s2' s3')
  | Sbreak => OK Sbreak
  | Scontinue => OK Scontinue
  | Sreturn None => OK (Sreturn None)
  | Sreturn (Some a) =>
      do a' <- retype_secure_expr ce e a;
      do a'' <- secure_cast rt a';
      OK (Sreturn (Some a''))
  | Sswitch a sl =>
      do a' <- retype_secure_public_expr ce e a "switch";
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

Definition initialize_secure_var (n: ident) (t: type) (inits : list init_data) : res (type * list init_data * statement) :=
    if type_is_public t then OK (t,inits,Sskip)
    else match t with
    (Tvoid | Tint _ _ _ | Tlong _ _ | Tfloat _ _ | Tpointer _ _) => match inits with
        | nil => OK (t,nil,Sskip)
        | cons i is => do ei <- init_data_to_expr i (type_signedness t); OK (t,nil,Sdo (Eassign (Evar n t) ei t))
        end
    | Tarray bt sz a => match inits with
        | nil => 
            let t' := Tpointer bt a in
            let blt := builtin_new_array t (Eval (Vlong (Int64.repr sz)) type_pint64u) in
            OK (t',nil,Sdo (Eassign (Evar n t') blt t'))
        | _ => Error (msg "unsupported secret array variable initialization")
        end
    | Tfunction _ _ _ => Error (msg "unsupported secret variable function type")
    | Tstruct _ _ => Error (msg "unsupported secret variable struct type")
    | Tunion _ _ => Error (msg "unsupported secret variable union type")
    end.

Definition retype_secure_fn_var (n : ident) (t: type) : res ((ident * type) * statement) :=
    do res <- initialize_secure_var n t nil;
    match res with
    | (t',_,s') => OK ((n,t'),s')
    end.

Fixpoint retype_secure_fn_vars (ps : list (ident * type)) : res (list (ident * type) * statement) :=
  match ps with
  | nil => OK (nil,Sskip)
  | cons (n,t) xs => do (x',sx') <- retype_secure_fn_var n t; do (xs',sxs') <- retype_secure_fn_vars xs; OK (cons x' xs',Ssequence sx' sxs')
  end.

Definition retype_secure_function (ce: composite_env) (e: typenv) (f: function) : res function :=
  let e := bind_vars (bind_vars e f.(fn_params)) f.(fn_vars) in
  do s' <- retype_secure_stmt ce e f.(fn_return) f.(fn_body);
  do (vars',s0) <- retype_secure_fn_vars f.(fn_vars);
  OK (mkfunction f.(fn_return) f.(fn_callconv) f.(fn_params) vars' (Ssequence s0 s')).         

Definition retype_secure_fundef (ce: composite_env) (e: typenv) (fd: fundef) : res fundef :=
  match fd with
  | Internal f => do f' <- retype_secure_function ce e f; OK (Internal f')
  | External id args res cc => OK (External id args res cc)
  end.

Definition retype_secure_globvar (n: ident) (gv: globvar type) : res (globvar type * statement) :=
    do res <- initialize_secure_var n gv.(gvar_info) gv.(gvar_init);
    match res with
    | (t',inits',s') => OK (mkglobvar t' inits' gv.(gvar_readonly) gv.(gvar_volatile),s')
    end.

Definition retype_secure_globdef (n: ident) (gd: globdef fundef type) : res (globdef fundef type * statement) :=
    match gd with
    | Gfun f => OK (Gfun f,Sskip)
    | Gvar gv => do (gv',s') <- retype_secure_globvar n gv; OK (Gvar gv',s')
    end.
    
Fixpoint retype_secure_globdefs (defs: list (ident * globdef fundef type)) : res (list (ident * globdef fundef type) * statement) :=
    match defs with
    | nil => OK (nil,Sskip)
    | cons (id,x) xs => do (x',s') <- retype_secure_globdef id x; do (xs',ss') <- retype_secure_globdefs xs; OK (cons (id,x') xs',Ssequence s' ss')
    end.

Fixpoint prepend_to_main (main: ident) (defs : list (ident * globdef fundef type)) (s: statement) : res (list (ident * globdef fundef type)) :=
    match defs with
    | nil => Error (msg "could not find main")
    | cons (id,x) xs => if ident_eq id main
        then match x with
        | Gfun (Internal f) => OK (cons (id,Gfun (Internal (prepend_function_body s f))) xs)
        | _ => Error (msg "could not add statement to non-internal main")
        end
        else do xs' <- prepend_to_main main xs s; OK (cons (id,x) xs')
    end.

Definition retype_secure_program (p: program) : res program :=
  do (defs,inits) <- retype_secure_globdefs p.(prog_defs);
  do defs' <- prepend_to_main p.(prog_main) defs inits;
  do p' <- make_program p.(prog_types) defs' p.(prog_public) p.(prog_main);
        
  let e := bind_globdef (PTree.empty _) p'.(prog_defs) in
  let ce := p'.(prog_comp_env) in
  do tp <- transform_partial_program (retype_secure_fundef ce e) p';
  make_program p'.(prog_types) tp.(AST.prog_defs) p'.(prog_public) p'.(prog_main).

(** Remove security qualifiers **)

Fixpoint remsec_type (t : type) : res type := 
  let tptr := Tpointer Tvoid (make_public_attr (attr_of_type t)) in
  match t with
  | Tvoid => OK Tvoid
  | Tint _ _ a => if a.(attr_secret) then OK tptr else OK t
  | Tlong _ a => if a.(attr_secret) then OK tptr else OK t
  | Tfloat _ a => if a.(attr_secret) then OK tptr else OK t
  | Tpointer bt a => if a.(attr_secret) then OK tptr else do bt' <- remsec_type bt; OK (Tpointer bt' a)
  | Tarray bt sz a => if a.(attr_secret) then OK tptr else do bt' <- remsec_type bt; OK (Tarray bt' sz a)
  | Tfunction targs tret cconv =>
      do targs' <- remsec_types targs;
      do tret' <- remsec_type tret;
      OK (Tfunction targs' tret' cconv)
  | Tstruct n a => if a.(attr_secret) then OK tptr else OK t
  | Tunion n a => if a.(attr_secret) then OK tptr else OK t
  end
with remsec_types (ts : typelist) : res typelist :=
  match ts with
  | Tnil => OK Tnil
  | Tcons x xs => do x' <- remsec_type x; do xs' <- remsec_types xs; OK (Tcons x' xs')
  end.


Definition remsec_typ_of_type (t: type) : res AST.typ :=
  match t with
  | Tvoid => OK AST.Tint
  | Tint _ _ a => if a.(attr_secret) then OK AST.Tptr else OK AST.Tint
  | Tlong _ a => if a.(attr_secret) then OK AST.Tptr else OK AST.Tlong
  | Tfloat F32 a => if a.(attr_secret) then OK AST.Tptr else OK AST.Tsingle
  | Tfloat F64 a => if a.(attr_secret) then OK AST.Tptr else OK AST.Tfloat
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
      OK (Ssequence s1' s2')
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

Definition typecheck_secure_program (p: program) : res program :=
    do p1 <- typecheck_program p;
    do p2 <- retype_secure_program p1;
    remsec_program p2.
