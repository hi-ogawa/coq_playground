(* ************** *)
(* Type Hierarchy *)
(* ************** *)

Check nat : Set.
Check Set : Type.
Check Prop : Type.
Check Type : Type.


(* ************** *)
(* Inductive Type *)
(* ************** *)

Inductive my_nat : Set :=
  | O' : my_nat
  | S' : my_nat -> my_nat.

(* three "thorems" are extracted from the definition *)
Check my_nat_ind
     : forall P : my_nat -> Prop,
       P O' -> (forall m : my_nat, P m -> P (S' m)) ->
       forall m : my_nat, P m.

Check my_nat_rec
     : forall P : my_nat -> Set,
       P O' -> (forall m : my_nat, P m -> P (S' m)) ->
       forall m : my_nat, P m.

Check my_nat_rect
     : forall P : my_nat -> Type,
       P O' -> (forall m : my_nat, P m -> P (S' m)) ->
       forall m : my_nat, P m.

(* function definition over inductive type *)
(* by using `Fixpoint` *)
Fixpoint my_add (x : my_nat) (y : my_nat) : my_nat :=
  match x with
    | O' => y
    | S' x' => S' (my_add x' y)
  end.

(* by using `my_nat_rec` *)
Definition my_add' := my_nat_rec (fun (_ : my_nat) => (my_nat -> my_nat))
                                  (fun (y : my_nat) => (y : my_nat))
                                  (fun (_ : my_nat) =>
                                     fun (prev : my_nat -> my_nat) =>
                                       fun c => S' (prev c)).

Compute my_add (S' (S' O')) (S' (S' (S' O'))).
Compute my_add' (S' (S' O')) (S' (S' (S' O'))).


(* ************************** *)
(* Polymorphic Inductive Type *)
(* ************************** *)

Inductive my_list (t : Set) : Set :=
  | Nil : my_list t
  | Cons : t -> my_list t -> my_list t.


(* ******************* *)
(* Inductive Predicate *)
(* ******************* *)

Inductive my_even : nat -> Prop :=
  | EvenO  : my_even O
  | EvenSS : forall (n : nat), my_even n -> my_even (S (S n)).

(* inductive principle is extracted *)
Check my_even_ind : forall P : nat -> Prop,
                    P O ->
                    (forall n : nat, my_even n -> P n -> P (S (S n))) ->
                    forall m : nat, my_even m -> P m.


(* ************** *)
(* Dependent Type *)
(* ************** *)

Section ilist.

Variable A :Set.

Inductive ilist : nat -> Set :=
  | INil : ilist O
  | ICons : forall (n : nat), A -> ilist n -> ilist (S n).

(*
  dependent pattern matching:
  Certified Programming with Dependent Types Section 8.2 is good resource
*)
Fixpoint app (n1 : nat) (ls1 : ilist n1) (n2 : nat) (ls2 : ilist n2) : ilist (n1 + n2) :=
  match ls1 in ilist n1 return ilist (n1 + n2) with  (* "in .. return .." can be omitted *)
    | INil => ls2
    | ICons n1' x ls1' => ICons (n1' + n2) x (app n1' ls1' n2 ls2)
  end.

Definition hd n (ls : ilist (S n)) : A :=
  match ls in ilist (S n) return A with  (* "in .. return .." can be omitted *)
    | ICons _ h _ => h
  end.

Definition hd' n (ls : ilist n) :=
  match ls in ilist n return (
          match n with
            | O => unit
            | S n' => A
          end
        ) with
    | INil => tt
    | ICons _ h _ => h
  end.

End ilist.
