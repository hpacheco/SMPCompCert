
Require Import Coqlib Maps String.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.

Inductive type: Type :=
    | Uint8   : type
    | Uint16  : type
    | Uint32  : type
    | Uint64  : type
    | Int8    : type
    | Int16   : type
    | Int32   : type
    | Int64   : type
    | Float32 : type
    | Float64 : type
    | Bool    : type.

Definition alltypes : list type :=
    Uint8 :: Uint16 :: Uint32 :: Uint64 :: Int8 :: Int16 :: Int32 :: Int64 :: Float32 :: Float64 :: Bool :: nil.

Definition type_size (ty: type) : Z :=
    match ty with
    | Uint8   => 1
    | Uint16  => 2
    | Uint32  => 4
    | Uint64  => 8
    | Int8    => 1
    | Int16   => 2
    | Int32   => 4
    | Int64   => 8
    | Float32 => 4
    | Float64 => 8
    | Bool    => 1 (*Since compcert C treats bools as 8-bit ints *)
    end.

Definition type_to_string (t: type) : string :=
    match t with
    | Uint8   => "uint8"
    | Uint16  => "uint16"
    | Uint32  => "uint32"
    | Uint64  => "uint64"
    | Int8    => "int8"
    | Int16   => "int16"
    | Int32   => "int32"
    | Int64   => "int64"
    | Float32 => "float32"
    | Float64 => "float64"
    | Bool    => "bool"
    end.

Definition string_to_type (s: string) : option type :=
    match s with
    | "uint8"   => Some Uint8
    | "uint16"  => Some Uint16
    | "uint32"  => Some Uint32
    | "uint64"  => Some Uint64
    | "int8"    => Some Int8
    | "int16"   => Some Int16
    | "int32"   => Some Int32
    | "int64"   => Some Int64
    | "float32" => Some Float32
    | "float64" => Some Float64
    | "bool"    => Some Bool
    | _         => None
    end.

Definition index: Type := N.

Definition val: Type := init_data.

Inductive location_val: Type :=
  | Imm      : (val + ident) -> location_val
  | Reg      : index -> location_val
  | Stack    : index -> location_val.

Definition offset: Type := location_val.

Inductive location_ref: Type :=
  | Ref      : index -> location_ref
  | Cref     : index -> location_ref
  | Mem      : location_val -> location_ref.

Inductive location_mov : Type :=
  | MV : location_val -> location_mov
  | MR : location_ref -> offset -> location_mov.
  
Inductive location : Type :=
  | LV : location_val -> location
  | LR : location_ref -> location.

Definition nbytes: Type := location_val.

Inductive instruction: Type :=

  (* Common instructions *)
  | Ipush         : location_val -> instruction
  | Ipushref      : location -> instruction
  | Ipushrefpart  : location -> offset -> nbytes -> instruction
  | Ipushcref     : location -> instruction
  | Ipushcrefpart : location -> offset -> nbytes -> instruction
  | Imov          : location_mov -> location_mov -> option nbytes -> instruction
  | Icall         : location_val -> option location_val -> instruction
  | Isyscall      : location_val -> option location_val -> instruction
  | Ialloc        : location_val -> nbytes -> instruction
  | Ifree         : location_val -> instruction
  | Igetmemsize   : location_val -> location_val -> instruction
  | Iresizestack  : val -> instruction
  | Ilabel        : ident -> instruction
  | Ireturn       : location_val -> instruction
  | Ihalt         : location_val -> instruction
  | Iuser_except  : instruction
  | Iconvert      : type -> location_val -> type -> location_val -> instruction
  
  (* Unary arithmetic operations *)
  | Iudec         : type -> location_val -> instruction  (* d := d - 1 *)
  | Iuinc         : type -> location_val -> instruction  (* d := d + 1 *)
  
  (* Binary arithmetic operations *)
  | Ibadd         : type -> location_val -> location_val -> instruction  (* d := d + s *)
  | Ibsub         : type -> location_val -> location_val -> instruction  (* d := d - s *)
  
  (* Terniary arithmetic operations *)
  | Itadd         : type -> location_val -> location_val -> location_val -> instruction  (* d := s1 + s2 *)
  | Itsub         : type -> location_val -> location_val -> location_val -> instruction  (* d := s1 - s2 *)
  | Itmul         : type -> location_val -> location_val -> location_val -> instruction  (* d := s1 * s2 *)
  
  (* Jump operations *)
  | Ijmp          : location_val -> instruction
  | Ijz           : location_val -> type -> location_val -> instruction
  | Ijnz          : location_val -> type -> location_val -> instruction
  | Idnjz         : location_val -> type -> location_val -> instruction
  | Idnjnz        : location_val -> type -> location_val -> instruction
  | Ijeq          : location_val -> type -> location_val -> location_val -> instruction
  | Ijne          : location_val -> type -> location_val -> location_val -> instruction
  | Ijge          : location_val -> type -> location_val -> location_val -> instruction
  | Ijgt          : location_val -> type -> location_val -> location_val -> instruction
  | Ijle          : location_val -> type -> location_val -> location_val -> instruction
  | Ijlt          : location_val -> type -> location_val -> location_val -> instruction
  
  (* Logical operations *)
  | Iteq          : type -> location_val -> location_val -> location_val -> instruction
  | Itne          : type -> location_val -> location_val -> location_val -> instruction
  | Itge          : type -> location_val -> location_val -> location_val -> instruction
  | Itgt          : type -> location_val -> location_val -> location_val -> instruction
  | Itle          : type -> location_val -> location_val -> location_val -> instruction
  | Itlt          : type -> location_val -> location_val -> location_val -> instruction
  
  (* Ternary bitwise operations *)
  | Ibtand        : type -> location_val -> location_val -> location_val -> instruction
  | Itshr0        : type -> location_val -> location_val -> location_val -> instruction
  .
  
Definition comparison: Type := location_val -> type -> location_val -> location_val -> instruction.
Definition comparison_bool: Type := type -> location_val -> location_val -> location_val -> instruction.

Definition code: Type := list instruction.

Definition private_domain : Type := string.
Definition external_function : Type := string.

(* a block starts with a label and has only relative jumps or jumps to other blocks. It returns at the end *)
Definition block: Type := (ident * code).

Definition blocks: Type := PTree.t code.

Inductive sharemind_data: Type :=
    | Data_string : string -> sharemind_data
    | Data_uint8 : int -> sharemind_data
    .

Record program (E: Type) : Type := mkprogram {
  prog_pds: PTree.t private_domain;
  prog_rodata: PTree.t sharemind_data;
  prog_exts: PTree.t E;
  prog_init: code;
  prog_code: blocks
}.

Definition noprogram (E: Type) : (program E) := mkprogram E
    (PTree.empty private_domain)
    (PTree.empty sharemind_data)
    (PTree.empty E)
    nil
    (PTree.empty code).


