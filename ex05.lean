/-
COMP2009-ACE

Exercise 05 (Natural numbers)

    This exercise has 2 parts both count for 50%.

    In the first part the goal is to complete the proof that the
    natural numbers with addition and multiplication form a
    semiring. I insert the proof the addition forms a commutative
    monoid (which we have done in the lecture).

    In the 2nd part you should show that ≤ is anti-symmetric. I
    include the proofs (from the lecture) that it is reflexive and
    transitive.

-/

set_option pp.structure_projections false

namespace ex05

open nat

--we have defined +

def add : ℕ → ℕ → ℕ 
| n zero     := n
| n (succ m) := succ (add n m)

local notation m + n := add m n

-- and have shown that it is a commutative monoid

theorem add_rneutr : ∀ n : ℕ, n + 0 = n :=
begin
  assume n,
  refl,
end

theorem add_lneutr : ∀ n : ℕ, 0 + n  = n :=
begin
  assume n,
  induction n with n' ih,
  refl,
  dsimp [(+),add],
  rewrite ih,
end

theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) :=
begin
  assume l m n,
  induction n with n' ih,
  refl,
  dsimp [(+),add],
  rewrite ih,
end

lemma add_succ_lem : ∀ m n : ℕ, succ m + n = succ (m + n) :=
begin
  assume m n,
  induction n with n' ih,
  refl,
  apply congr_arg succ,
  exact ih,
end

theorem add_comm : ∀ m n : ℕ , m + n = n + m :=
begin
  assume m n,
  induction m with m' ih,
  apply add_lneutr,
  calc 
    succ m' + n = succ (m' + n) : by apply add_succ_lem
    ... = succ (n + m') : by apply congr_arg succ; exact ih
    ... = n + succ m' : by reflexivity,
end

-- now we define addition

def mul : ℕ → ℕ → ℕ
| m 0     := 0
| m (succ n) := (mul m n) + m

local notation m * n := mul m n

-- and your task is to show that it is a commutative semiring, i.e.

theorem mult_rneutr : ∀ n : ℕ, n * 1 = n :=
begin
  assume x,
  induction x with y z,
  reflexivity,
  dsimp[mul],
  apply congr_arg succ,
  exact z,
end

theorem mult_lneutr : ∀ n : ℕ, 1 * n  = n :=
begin
  assume x,
  induction x with y z,
  reflexivity,
  apply congr_arg succ,
  exact z,
end

theorem mult_zero_l : ∀ n : ℕ , 0 * n = 0 :=
begin
  assume x,
  induction x with y z,
  dsimp[mul],
  reflexivity,
  cases y,
  exact z,
  exact z,
end 

theorem mult_zero_r : ∀ n : ℕ , n * 0 = 0 :=
begin
  assume x,
  reflexivity,
end

theorem mult_distr_r :  ∀ l m n : ℕ , l * (m + n) = l * m + l * n :=
begin
  assume x y z,
  induction z with z' ih,
  rewrite add_rneutr,
  rewrite mult_zero_r,
  rewrite add_rneutr,

  dsimp[mul],
  dsimp[add],
  dsimp[mul],
  rewrite← add_assoc,
  rewrite ih,
end

theorem mult_distr_l :  ∀ l m n : ℕ , (m + n) * l = m * l + n * l :=
begin
  assume x y z,
  induction x with x' ih,
  rewrite mult_zero_r,
  reflexivity,
  dsimp[mul],
  rewrite ih,
  rewrite add_assoc,
  rewrite add_assoc,
  rewrite← add_assoc (z*x') y z,
  rewrite add_comm (z*x') y,
  rewrite add_assoc,
end

theorem mult_assoc : ∀ l m n : ℕ , (l * m) * n = l * (m * n) :=
begin
  assume x y z,
  induction z with z' ih,
  reflexivity,
  dsimp[mul],
  rewrite ih,
  rewrite mult_distr_r,
end

lemma mult_lemma : ∀ m n : ℕ , succ m * n = m * n + n :=
begin
  assume x y,
  induction y with y' ih,
  reflexivity,
  dsimp[mul],
  rewrite ih,
  rewrite add_assoc,
  apply congr_arg succ,
  rewrite add_comm,
  
  

  
end


theorem mult_comm :  ∀ m n : ℕ , m * n = n * m :=
begin
  assume x y,
  induction x with x' ih,
  dsimp[mul],
  rewrite mult_zero_l,
  dsimp[mul],
  rewrite← ih,
  apply mult_lemma,
end


-- part 2

def le(m n : ℕ) : Prop :=
  ∃ k : ℕ , k + m = n

local notation x ≤ y := le x y

theorem le_refl : ∀ x : ℕ , x ≤ x :=
begin
  assume x,
  existsi 0,
  apply add_lneutr,
end

theorem le_trans : ∀ x y z : ℕ , x ≤ y → y ≤ z → x ≤ z :=
begin
  assume x y z xy yz,
  cases xy with k p,
  cases yz with l q,
  existsi (k+l),
  rewrite← q,
  rewrite← p,
  calc 
    (k + l) + x = (l + k) + x : by rewrite (add_comm k l)
    ... = l + (k + x) : by rewrite add_assoc,
end


theorem anti_sym : ∀ x y : ℕ , x ≤ y → y ≤ x → x = y :=
begin
  
  
end

end ex05
