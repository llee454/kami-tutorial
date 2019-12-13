(**
  This module demonstrates how to define modules
  using Kami.
*)

Require Import Kami.AllNotations.
Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope list_scope.
Open Scope kami_scope.
Open Scope kami_action_scope.
Open Scope kami_expr_scope.

(**
  An example packet structure type.
*)
Example packet_type
  :  Kind
  := STRUCT {"field" :: Bit 4}.

(**
  An example packet structure.
*)
Open Scope kami_expr.
Example packet
  :  Expr type (SyntaxKind packet_type)
  := STRUCT {
       "field" ::= Const type (ConstBit WO~0~0~0~0)
     }.

(**
  An example reading a field value from a packet.

*)
Check (ReadStruct packet Fin.F1).
Check (packet @% "field").

(**
  Represents a 32-bit register with an initial
  state containing the value 4.
*)
Example register0 : RegInitT
  := ("register0",
       existT optConstFullT
         (SyntaxKind (Bit 32))
         (Some (SyntaxConst (ConstBit $4)))).

(**  Represents an uninitialized 16-bit register. *)
Example register1 : RegInitT
  := ("register1",
       existT optConstFullT
         (SyntaxKind (Bit 16))
         None).

(**
  Represents a method that accepts a 16 bit
  number, writes that number into register 1
  and returns the register's original value.
*)
Example method0 : DefMethT
  := ("method0",
       existT MethodT (Bit 16, Bit 16)
         (fun type (x : type (Bit 16))
           => Write "register1" : Bit 16 <- #x;
              Read result : Bit 16 <- "register";
              Ret #result)).

(** Represents the null method. *)
Example method1 : DefMethT
  := ("method1",
       existT MethodT (Void, Void)
         (fun type (_ : type (Void))
           => Retv)).

(**
  Represents a rule that does nothing -
  i.e. simply returns void.

  Note: all rules return void.
*)
Example rule0 : RuleT
  := ("rule0", fun type => Ret Const type WO).

(**
  Represents a rule that writes the value 5
  into register0.
*)
Example rule1 : RuleT
  := ("rule1",
      fun type
        => Write "register0" : Bit 32 <- Const type (natToWord 32 5);
           Ret Const type WO).

(**
  Represents a rule that calls a method named
  "method1" and returns void.
*)
Example rule2 : RuleT
  := ("rule2",
       fun type
         => Call _ : Void <- "method1" (Const type WO : Void);
            Ret Const type WO).

(** Represents the null base module. *)
Example null_base_module : BaseModule := BaseMod [] [] [].

(** Represents the null module. *)
Example null_module : Mod := Base null_base_module.

(**
  Represent a module that contains register0,
  rule1, and method0.

  This module repeatedly writes the value 5
  into register0.
*)
Example module0 : Mod
  := Base (BaseMod [register0] [rule1] [method0]).

(**
  Represents a module that contains register1,
  and rule0.

  This module repeatedly executes rule0 which
  does nothing.
*)
Example module1 : Mod
  := Base (BaseMod [register1] [rule0] []).
     
(**
  Represents a register file containing two 4 bit registers initialized to the value 8.
*)
Example register_file0
  := RegFile
       "register_file0"
       ["read0" ; "read1" ; "read2"]
       "write0" 2 (Some (ConstBit WO~1~0~0~0)).

(**
  An example base module illustrating Kami's
  module notation.
*)
Example module2 : BaseModule
  := MODULE {
    (* represents a 16 bit register *)
    Register "example_register" : Bit 16 <- getDefaultConst (Bit 16) 

    (* represents a rule *)
    with Rule "example_rule" := Retv

    (* represents a method *)
    with Method "example_method" (x : Bit 8) : Void := Retv
}.

(** Represents the return void action. *)
Example void_action : ActionT type Void := Ret Const type WO.


(** Represents the composition of two modules. *)
Example composite_module : Mod := ConcatMod module0 module1.

(** Proves that the return void action is well formed. *)
Definition void_action_wellformed
  :  forall module : BaseModule, WfActionT module void_action
  := fun module
       => WfReturn module (Const type (ConstBit WO)). 

Opaque void_action_wellformed.

(**
  Proves that the null base module is well formed.
*)
Definition null_base_module_wellformed : WfBaseModule null_base_module
  := conj
       (fun rule (H : In rule []) => False_ind _ H)
       (conj
         (fun method (H : In method []) => False_ind _ H)
         (conj (NoDup_nil string)
           (conj (NoDup_nil string)
                 (NoDup_nil string)))).

Opaque null_base_module_wellformed.

(** Proves that the null module is well formed. *)
Definition null_module_wellformed : WfMod null_module := BaseWf null_base_module_wellformed.

(**
  Represents the an action that a calls a void
  method and returns void.
*)
Example void_method_call : ActionT type Void
  := Call _ : Void <- "example_method" (Const type WO : Void);
     Ret Const type WO.

(**
  Proves that the void method call action is
  well formed within any module.
*)
Definition void_method_call_wellformed
  :  forall module : BaseModule, WfActionT module void_method_call
  := fun module : BaseModule
       => WfMCall "example_method" (Void, Void) (Const type WO)
            (fun _ : word 0 => Ret Const type WO)
            (fun _ : word 0 => WfReturn module (Const type WO)).

Opaque void_method_call_wellformed.

(** Represents the well formed null module. *)
Example well_formed_null_module : ModWf := Build_ModWf null_module_wellformed.

(** demonstrates the discharge_wf tactic. *)
Example discharge_wf_example : ModWf := @Build_ModWf null_module ltac:(discharge_wf).

(** demonstrates the discharge_wf tactic on a more complex module. *)
Example wellformed_module2 : ModWf := @Build_ModWf (Base module2) ltac:(discharge_wf).

(**
  Represents the values stored within a register
  - i.e. the state of a register.
*)
Example example_register_value : RegT
  := ("example_register_value",
      existT (fullType type) (SyntaxKind (Bit 2)) WO~0~1).

(**
  Represents the values stored within towo
  registers - i.e. the state of two registers.
*)
Example example_register_values : RegsT
  := [("register0", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 4));
      ("register1", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 8))].

(**
  Represents a pair of values satisfying a
  method signature.
*)
Example example_translated_signature : SignT (Bit 8, Bit 8) := (natToWord 8 16, natToWord 8 4).

(**
  Represents a method call/execution event.
*)
Example example_method_call_event : MethT
  := ("example_method", existT SignT (Bit 0, Bit 8) (WO, natToWord 8 4)).

(**
  Proves that a void return action returns the
  initial register state without any register
  updates or method calls/executions and returns
  a void value.
*)
Example void_return_effect
  :  forall initial_reg_state : RegsT,
       SemAction initial_reg_state Retv [] [] [] WO
  := fun initial_reg_state
       => SemReturn
            initial_reg_state (* the initial register state *)
            (Const type WO)   (* the action's return value *)
            (eq_refl WO)      
            (eq_refl [])      (* the return action does not read any registers *)
            (eq_refl [])      (* the return action does not update any registers *)
            (eq_refl []).     (* the return action does not call any registers *)

(**
  Demonstrates the mapping between a method
  call action and its register updates and
  return value.
*)
Example method_call_effect
  :  SemAction 
       []
       (Call _ : Void <- "method" (Const type WO : Void);
        Retv)
       [] []
       [("method", existT SignT (Void, Void) (WO, WO))]
       WO
  := SemMCall 
       (s := (Void, Void))      (* explicitly specifies the method signature *)
       (Const type WO)          (* the action's return value *)
       (fun _ : word 0 => Retv) (* the continuation after this call action. *)
       (eq_refl [("method", existT SignT (Void, Void) (WO, WO))]) (* the values passed to and returned by this method call. *)
       (void_return_effect []).                            (* proves that the continuation produces the needed effect. *)

(**
  Illustrates the effects of writing a value to
  a register.
*)
Example write_effect
  :  SemAction
       [("register", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 5))] (* the initial register state *)
       (Write "register" : Bit 8 <- $6; Retv)                                      (* the action performed *)
       []                                                                          (* the register reads *)
       [("register", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 6))] (* the register updates *)
       []                                                                          (* the method calls/executions *)
       WO                                                                          (* the return value *)
  := SemWriteReg
       (o := [("register", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 5))])
       (Const type (natToWord 8 6))

       (* prove that the correct type of value is stored. *)
       (or_introl
         (eq_refl ("register", SyntaxKind (Bit 8))))

       (* Prove that the register has only been written to once. *)
       (fun value (H : In ("register", value) nil) => H)

       (* Prove that the value written equals the value stored. *)
       (eq_refl [("register", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 6))])

       (* Prove that the return action has no further effect. *)
       (void_return_effect
         [("register", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 5))]).
       

(** Demonstrates the simplest possible substep. *)
Example null_substep
  :  Substeps null_base_module [] []
  := NilSubstep null_base_module [] (eq_refl []).

(**
  Represents an example substep in which a void
  return rule named "rule0" is executed.
*)
Example example_substep
  :  Substeps 
       (BaseMod [register0] [rule0] [])
       [("register0",
         existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5))] 
       [([], (Rle "rule0", []))]
  := AddRule
       (m := BaseMod [register0] [rule0] [])
       (o := [("register0", existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5))])
       (* prove that the register types in the initial register state agree with the module definitions. *)
       (eq_refl [("register0", SyntaxKind (Bit 32))])
       (* the rule body. *)
       (fun type => Ret Const type WO)
       (* prove that the rule is defined by the module. *)
       (or_introl
         (eq_refl ("rule0", fun type => Ret Const type WO)))
       (* proves that the rule body produces the given register reads, register writes, and method calls and returns void. *)
       (void_return_effect
         [("register0", existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5))])
       (* proves that the types given for register reads agree with the module definitions. *)
       (fun read (H : In read nil) => False_ind _ H)
       (* proves that the types given for register writes agree with the module definitions. *)
       (fun write (H : In write nil) => False_ind _ H)
       (* explicitly give the first label. *)
       (l := [([], (Rle "rule0", []))])
       (* explicitly give the remaining labels. *)
       (ls := [])
       (* prove that the first label contains an entry for this rule. *)
       (eq_refl [([], (Rle "rule0", []))])
       (* *)
       (fun label (H : In label nil) _ => False_ind _ H)
       (* prove that none of the remaining labels are rule executions. *)
       (fun label (H : In label nil) => False_ind _ H)
       (* prove that the remaining substeps are valid. *)
       (NilSubstep
         (BaseMod [register0] [rule0] [])
         [("register0", existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5))]
         (eq_refl [("register0", SyntaxKind (Bit 32))])).

(**
  Represents a substep in which a void return
  rule named "rule0" is executed.
*)
Example rule_substep 
  :  Substeps
       (BaseMod [] [rule0] [])
       []
       [([], (Rle "rule0", []))]
  := AddRule
       (m := BaseMod [] [rule0] [])
       (o := [])
       (* prove that the register types in the initial register state agree with the module definitions *)
       (ltac:(trivial))
       (* the rule body *)
       (fun type => Ret Const type WO)
       (* prove that the rule is defined by the module *)
       (ltac:(left; exact (eq_refl ("rule0", fun type => Ret Const type WO))))
       (* prove that the rule body produces the given register updates, method calls, and method executions *)
       (void_return_effect [])
       (* proves that the types given for the register reads agree with the module definitions. *)
       (fun read (H : In read nil) => ltac:(contradiction))
       (* proves that the types given for the register writes agree with the module definitions. *)
       (fun write (H : In write nil) => ltac:(contradiction))
       (* the first label *)
       (l := [([], (Rle "rule0", []))])
       (* the remaining labels *)
       (ls := [])
       (* prove that the first label contains an entry for this rule *)
       (ltac:(trivial))
       (* *)
       (fun label (H : In label nil) => ltac:(contradiction))
       (* prove that none of the remaining labels are rule executions. *)
       (fun label (H : In label nil) => ltac:(contradiction))
       (* prove that the remaining substeps are valid *)
       (NilSubstep
         (BaseMod [] [rule0] [])
         []
         (ltac:(trivial))).


(**
  Represents a singleton substep in which a void
  return method named "method1" is executed.
*)
Example method_substep
  :  Substeps
       (BaseMod [] [] [method1])
       [] (* no initial register states. *)
       [([], (Meth ("method1", existT SignT (Void, Void) (WO, WO)), []))]
  := AddMeth
       (m := BaseMod [] [] [method1])
       (o := [])
       (* prove that the register types in the initial register state agree with the module definitions. *)
       (eq_refl [])
       (* the method body *)
       (existT MethodT (Void, Void) (fun type (_ : type (Void)) => Retv))
       (* prove that the method is defined by the module. *)
       (or_introl
         (eq_refl ("method1", existT MethodT (Void, Void) (fun type (_ : type (Void)) => Retv))))
       (* prove that the method body produces the given effects. *)
       (void_return_effect [])
       (* proves that the types given for register reads agree with the module definitions. *)
       (fun read (H : In read nil) => False_ind _ H)
       (* proves that the types given for register writes agree with the module definitions. *)
       (fun write (H : In write nil) => False_ind _ H)
       (* explicitly give the first label. *)
       (l := [([], (Meth ("method1", existT SignT (Void, Void) (WO, WO)), []))])
       (* explicitly give the remaining labels. *)
       (ls := [])
       (* prove that the first label contains an entry for this rule. *)
       (eq_refl [([], (Meth ("method1", existT SignT (Void, Void) (WO, WO)), []))])
       (* prove that this method is called only once per substep. *)
       (fun label (H : In label nil) _ => False_ind _ H)
       (* prove that the remaining substeps are valid. *)
       (NilSubstep
         (BaseMod [] [] [method1])
         []
         (eq_refl [])).

(**
*)
Example rule2_substep
  :  Substeps
       (BaseMod [] [rule2] []) 
       []
       [([], (Rle "rule2", [("method1", existT SignT (Void, Void) (WO, WO))]))]
  := AddRule
       (m := BaseMod [] [rule2] [])
       (o := [])
       (* prove that the register types in the initial register state agree with the module definitions *)
       (ltac:(trivial))
       (* the rule body *)
       (fun type
         => Call _ : Void <- "method1" (Const type WO : Void);
            Ret Const type WO)
       (* prove that the rule is defined by the module *)
       (or_introl
         (eq_refl
           ("rule2",
             (fun type
               => Call _ : Void <- "method1" (Const type WO : Void);
                  Ret Const type WO))))
       (* prove that the rule body produces the given register updates, method calls, and method executions *)
       (SemMCall
         (s := (Void, Void))
         (Const type WO)
         (fun _ : word 0 => Retv)
         (eq_refl [("method1", existT SignT (Void, Void) (WO, WO))])
         (void_return_effect []))
       (* proves that the types given for register reads agree with the module definitions. *)
       (fun read (H : In read nil) => False_ind _ H)
       (* proves that the types given for register writes agree with the module definitions. *)
       (fun write (H : In write nil) => False_ind _ H)
       (* explicitly give the first label. *)
       (l := [([], (Rle "rule2", [("method1", existT SignT (Void, Void) (WO, WO))]))])
       (* explicitly give the remaining labels. *)
       (ls := [])
       (* prove that the first label contains an entry for this rule. *)
       (eq_refl [([], (Rle "rule2", [("method1", existT SignT (Void, Void) (WO, WO))]))])
       (* *)
       (fun label (H : In label nil) _ => False_ind _ H)
       (* prove that none of the remaining labels are rule executions. *)
       (fun label (H : In label nil) => False_ind _ H)
       (* prove that the remaining substeps are valid *)
       (NilSubstep
         (BaseMod [] [rule2] [])
         []
         (ltac:(trivial))).

(**
  An example step in which a single rule named
  "rule0" is executed.

  Note: this rule is simply a substep in which
  we've verified that the number of calls is less
  than the number of executions for each method.
*)
Example rule_step
  : Step
      (Base (BaseMod [] [rule0] []))
      []
      [([], (Rle "rule0", []))]
  := BaseStep
       rule_substep
       (fun method (H : In (fst method) nil)
         => ltac:(contradiction)).

(*
  An example step for a module that contains
  a method where the method was executed in
  response to an external call.
*)
Example method_step
  :  Step
       (Base (BaseMod [] [] [method1]))
       []
       [([], (Meth ("method1", existT SignT (Void, Void) (WO, WO)), []))]
  := BaseStep
       method_substep
       (fun method (H : In (fst method) ["method1"])
         => num_method_execs_positive method
              [([], (Meth ("method1", existT SignT (Void, Void) (WO, WO)), []))]).


