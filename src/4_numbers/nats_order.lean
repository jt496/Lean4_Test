import tactic.core
import data.nat.basic
import .nats_add_mul


/-  ℕ is just one example of an inductive type, Lean has many more. 

The definition of ≤ "less_than_or_equal" on ℕ is itself inductive:

inductive less_than_or_equal (a : ℕ) : ℕ → Prop
| refl : less_than_or_equal a
| step : Π {b}, less_than_or_equal b → less_than_or_equal (succ b)

We can interpret this as follows. Given `a : ℕ`
refl : a ≤ a (reflexivity)
step : ∀ b, a ≤ b → a ≤ b + 1  (whenever a ≤ b we have a ≤ b + 1)

Below we develop some of the basic results about ≤ for ℕ, again we use the 
same names as in mathlib but capitalised to avoid clashes.

-/
lemma Le_refl (n : ℕ) : n ≤ n :=
begin
  exact nat.less_than_or_equal.refl, -- refl 
end

lemma Le_succ (n : ℕ) : n ≤ n.succ :=
begin
  apply nat.less_than_or_equal.step, -- reduces the problem to showing n ≤ n
  exact Le_refl _,                   -- which is refl
end

/- The next proof uses a useful version of induction on ℕ starting from any m : ℕ -/
lemma Succ_le_succ (m n : ℕ) : m ≤ n → m.succ ≤ n.succ :=
begin 
  apply nat.le_induction,
  refl,
  intros n h,
  exact nat.less_than_or_equal.step,
end


-- An alternative proof of the previous result uses induction on the inductive definition of ≤
lemma Succ_le_succ' (m n : ℕ) : m ≤ n → m.succ ≤ n.succ :=
begin 
  -- We want to prove ∀ m n, m ≤ n → m.succ ≤ n.succ
  intro h, -- assume m ≤ n
  induction h with k h1 h,  -- this is doing induction on `m ≤ n`
  -- First need to prove m.succ ≤ m.succ (corresponding to the refl case of ≤ ) 
  refl,
  -- now have  m ≤ k and `m + 1 ≤ k + 1` and need to prove `m + 1 ≤ k + 2`, which is easy
  apply nat.less_than_or_equal.step h,
end

lemma Zero_le (n : ℕ) : 0 ≤ n :=
begin
  induction n with n hn, -- this is just standard induction
  {
    sorry,
  },
  {
    sorry,
  },
end

lemma Le_add_right (n k : ℕ) : n ≤ n + k:=
begin
  induction k with k hk,
  {
    sorry,
  },
  {
    sorry,
  },
end

lemma Le_add_left (n k : ℕ) : n ≤ k + n:=
begin
  sorry,
end

--The next proof again uses induction on the inductive definition of ≤ 
lemma Le.dest {n m : ℕ}:  n ≤ m → ∃ k, n + k = m:=
begin
  apply nat.le_induction,
  {
    sorry,
  },
  {
    sorry,
  },
end

lemma Le.intro {n m k : ℕ} (h :  n + k = m) : n ≤ m :=
begin
  sorry,
end

lemma Le_trans {a b c : ℕ} : a ≤ b → b ≤ c → a ≤ c:=
begin
  sorry,
end

lemma  Add_left_cancel {n m k : ℕ} (h : m + n = m + k) : n = k :=
begin -- Succ.inj may be useful here
  induction m with m hm,
  {
    sorry},
  {
    sorry},
end

lemma  Eq_zero_of_add_eq_zero_right {n m :ℕ} (h : n + m = 0) : n = 0:=
begin
  cases m, 
  {
    sorry},
  { 
    sorry},
end

lemma Le_antisymm {m n : ℕ} : m ≤ n → n ≤ m → m = n:=
begin
  sorry,
end

-- We have established quite a lot of the proof that ℕ is a partial order

--#print partial_order
--#print instances linear_order
-- To complete this we would need to consider the definition of < 
lemma Lt (m n : ℕ) : m < n ↔ m.succ ≤ n:=
begin
  refl,
end

