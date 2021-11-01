/-
COMP2009-ACE

Exercise 02 (Propositional logic)

We play the game of logic poker :-)

    You have to classify the propositions into
    a) provable intuitionistically (i.e. in plain lean)
    b) provable classically (using em : P ∨ ¬ P or raa : ¬¬ P → P).
    c) not provable classically.
    and then you have to prove the propositions in a) and b) accordingly.

    Here is how you score:
    We start with 10 points :-)
    For any proposition which you didn't classify correctly (or not at all)
    you loose 1 point. :-(
    For any proposition which is provable but you didn't prove you loose
    1 point. :-(
    We stop subtracting points at 0. :-)

    Write the classification as a comment using -- after the proposition.

    You are only allowed to use the tactics introduced in the lecture
    (i.e. assume, exact, apply, constructor, cases, left, right, have, trivial)

    Please only use the tactics in the way indicated in the script,
    otherwise you may lose upto 2 style points. 

    For propositions classified into c) just keep "sorry," as the proof.
-/

variables P Q R : Prop

open classical

theorem raa : ¬ ¬ P → P := -- provable classically
begin
  assume nnp,
  cases em P with p np,
    exact p,
    have f : false,
      apply nnp,
      exact np,
    cases f,
end

theorem e01 : (P → Q) → (R → P) → (R → Q) := -- provable intuitionistically
begin
  assume p2q r2p r,
  apply p2q,
  apply r2p,
  exact r,
end

theorem e02 : (P → Q) → (P → R) → (Q → R) := -- not provable classically
begin
  sorry,
end

theorem e03 : (P → Q) → (Q → R) → (P → R) := -- provable intuitionistically
begin
  assume p2q q2r p,
  apply q2r,
  apply p2q,
  exact p,
end

theorem e04 : P → (P → Q) → P ∧ Q := -- provable intuitionistically
begin
  assume p p2q,
  constructor,
  exact p,
  apply p2q,
  exact p,
end

theorem e05 : P ∨ Q → (P → Q) → Q := -- provable intuitionistically
begin
  assume pORq p2q,
  cases pORq with p q,
  apply p2q,
  exact p,
  exact q,
end

theorem e06 : (P → Q) → ¬ P ∨ Q := -- provable classically
begin
  assume p2q,
  cases em P with p notp,
  right,
  apply p2q,
  exact p,
  left,
  exact notp,
end

theorem e07 : (¬ P ∨ Q) → P → Q := -- provable intuitionistically
begin
  assume notpORq p,
  cases notpORq with notp q,
  have f : false,
  apply notp,
  exact p,
  cases f,
  exact q,
end

theorem e08 : ¬ (P ↔ ¬ P) := -- provable classically
begin
  assume t,
  cases t with p2notp notp2p,
  cases em P with p notp,
  apply p2notp,
  exact p,
  exact p,
  apply notp,
  apply notp2p,
  exact notp,
end

theorem e09 : ¬ P ↔ ¬ ¬ ¬ P := -- provable classically
begin
  constructor,
  assume notp notnotp,
  cases em P with p notp,
  have f : false,
  apply notp,
  exact p,
  exact f,
  apply notnotp,
  exact notp,
  assume notnotnotp p,
  apply notnotnotp,
  assume notp,
  have f : false,
  apply notp,
  exact p,
  exact f,
end

theorem e10 : ((P → Q) → P) → P := -- provable classically
begin
  assume p2q,
  cases em P with p notp,
  exact p,
  apply p2q,
  assume p,
  have f : false,
  apply notp,
  exact p,
  cases f,
end