/-
COMP2009-ACE

Exercise 01 (Propositional logic) (10 points)

Prove all the following propositions in Lean. 1 point per exercise.
That is replace "sorry" with your proof. 

You are only allowed to use the tactics introduced in the lecture
(i.e. assume, exact, apply, constructor, cases, left, right, have)

Please only use the tactics in the way indicated in the script,
otherwise you may lose upto 2 style points. 

-/

variables P Q R : Prop

theorem e01 : P → Q → P :=
begin
  assume p q,
  exact p,
end

theorem e02 : (P → Q → R) → (P → Q) → P → R :=
begin
  assume f q p,
  apply f,
  exact p,
  apply q,
  exact p,
end

theorem e03 : (P → Q) → P ∧ R → Q ∧ R :=
begin
  assume p2q p2r,
  constructor,
  cases p2r with p r,
  apply p2q,
  exact p,
  cases p2r with p r,
  exact r, 
end

theorem e04 : (P → Q) → P ∨ R → Q ∨ R :=
begin
  assume p2q pORr,
  cases pORr with p r,
  constructor,
  apply p2q,
  exact p, 
  right,
  exact r,
end

theorem e05 : P ∨ Q → R ↔ (P → R) ∧ (Q → R) :=
begin
  constructor,
  assume pqr,
  constructor,
  assume p,
  apply pqr,
  left,
  exact p,
  assume q,
  apply pqr,
  right,
  exact q,

  assume p2rANDq2r pORq,
  cases p2rANDq2r with l r,
  cases pORq with p q,
  apply l,
  exact p,
  apply r,
  exact q,
end

theorem e06 : P → ¬ ¬ P :=
begin
  assume p notp,
  apply notp,
  exact p,
end

theorem e07 : P ∧ true ↔ P :=
begin
  constructor,
  assume p2t,
  cases p2t with p t,
  exact p,

  assume p,
  constructor,
  exact p,
  constructor,
end

theorem e08 : P ∨ false ↔ P :=
begin
  constructor,
  assume p2f,
  cases p2f with p f,
  exact p,
  cases f,
  assume p,
  left,
  exact p,
end

theorem e09 : P ∧ false ↔ false :=
begin
  constructor,
  assume p2f,
  cases p2f with p f,
  exact f,

  assume f,
  cases f,
end

theorem e10 : P ∨ true ↔ true :=
begin
  constructor,
  assume pORt,
  cases pORt with p t,
  constructor,
  exact t,
  assume t,
  right,
  exact t,
end