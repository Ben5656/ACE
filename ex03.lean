/-
COMP2009-ACE

Exercise 03 (Predicate logic)

    This exercise has 2 parts. In the 1st part you are supposed to
    formally define what certain relation bewteen humans are (like
    Father, brother-in-law etc). Here we use Lean only as a syntax  and type checker. 
    In the 2nd part we play logic poker again :-) but this time for
    predicate logic. 

    Each part counts for 50% of the mark.
-/

namespace family

-- Given the following type, predicates and relations:

constant People : Type
constants Male Female : People → Prop
-- Male x means x is male
-- Female x means x is fmeale
constant Parent : People → People → Prop
-- Parent x y means x is a parent of y
constant Married : People → People → Prop
-- Married x y means x is married to y

/-
Define the following relations (People → People → Prop) 
using the predicates and relations above:

- Father x y = x is the father of y
- Brother x y = x is the brother of y
- Grandmother x y = x is the grandmother of y
- FatherInLaw x y = x is the father-in-law of y
- SisterInLaw x y = x is the sister in law of y
- Uncle x y = x is the uncle of y

If you are not sure about the definition of these terms, check them 
in wikipedia. If there is more than one option choose one.
-/

/- As an example: here is the definition of Father: -/

def Father (x y : People) : Prop
  := Parent x y ∧ Male x

-- insert your definitions here
def Sibling(x y : People) : Prop := -- Defined to make brother, uncle and siblinginlaw more concise
  x ≠ y ∧ ∃ z: People, Parent z x ↔ Parent z y

def Brother(x y : People) : Prop :=
  Sibling x y ∧ Male x

def Grandmother(x y : People) : Prop :=
  (∃ z: People, Parent x z ∧ Parent z y) ∧ Female x

def FatherInLaw(x y : People) : Prop :=
  (∃ z: People, Parent x z ∧ Married z y) ∧ Male x

def SiblingInLaw(x y : People) : Prop := -- Defined to make uncle/sisterinlaw more concicse
  ∃ z: People, Married x z ∧ Sibling z y

def SisterInLaw(x y : People) : Prop :=
  SiblingInLaw x y ∧ Female x

def Uncle(x y : People) : Prop :=
  (∃ z: People, (Sibling x z ∧ SiblingInLaw x z) ∧ Parent z y) ∧ Male x 

end family

namespace poker
/-
   We play the game of logic poker - but this time with predicate logic :-)

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
    (i.e. assume, exact, apply, constructor, cases, left, right, have, 
    trivial, existsi, reflexivity, rewrite)

    Please only use the tactics in the way indicated in the script,
    otherwise you may lose upto 2 style points. 

    For propositions classified into c) just keep "sorry," as the proof.
-/

variable A : Type
variables PP QQ : A → Prop
variables RR : A → A → Prop
variables P Q R : Prop

open classical

theorem raa : ¬ ¬ P → P := 
begin
  assume nnp,
  cases (em P) with p np,
    exact p,
    have f : false,
      apply nnp,
      exact np,
    cases f,
end

theorem ex01 : (∀ x:A, ∃ y : A , RR x y) → (∃ y : A, ∀ x : A, RR x y) := -- not provable classically
begin
  sorry,
end

theorem ex02 :  (∃ y : A, ∀ x : A, RR x y) → (∀ x:A, ∃ y : A , RR x y) := -- provable intuitionistically
begin 
  assume x y,
  cases x with z d,
  constructor,
  apply d,
end

theorem ex03 : ∀ x y : A, x = y → RR x y → RR x x := -- provable intuitionistically
begin 
  assume x y z a,
  cases z with b c,
  exact a,
end

theorem ex04 : ∀ x y z : A, x ≠ y → x ≠ z → y ≠ z := -- not provable classically
begin 
  sorry,
end

theorem ex05 : ∀ x y z : A, x = y → x ≠ z → y ≠ z := -- provable intuitionistically
begin 
  assume a b c d e f,
  apply e,
  cases d with x y,
  exact f,
end

theorem ex06 : ∀ x y z : A, x ≠ y → (x ≠ z ∨ y ≠ z) := -- provable classically
begin 
  assume a b c ab,
  apply raa,
  assume not,
  apply not,
  constructor,
  assume ac,
  apply not,
  right,
  assume bc,
  apply ab,
  rewrite bc,
  exact ac,
end

theorem ex07 : ¬ ¬ (∀ x : A, PP x) → ∀ x : A, ¬ ¬ PP x := -- provable intuitionistically
begin 
  assume a b c,
  apply a,
  assume d,
  apply c,
  apply d,
end

theorem ex08 : (∀ x : A, ¬ ¬ PP x) → ¬ ¬ ∀ x : A, PP x := -- provable classically
begin 
  assume a b,
  apply b,
  assume c,
  apply raa,
  apply a,
end

theorem ex09 : (∃ x : A, true) → (∃ x:A, PP x) → ∀ x : A,PP x := -- not provable classically
begin 
  sorry,
end

theorem ex10 : (∃ x : A, true) → (∃ x:A, PP x → ∀ x : A,PP x) := -- provable classically
begin
  assume a,
  cases a with e t,
  apply raa,
  assume g,
  apply g,
  existsi e,
  assume ppe,
  assume a,
  apply raa,
  assume x,
  apply g,
  existsi a,
  assume y,
  contradiction,
end

end poker
