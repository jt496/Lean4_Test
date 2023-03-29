import tactic
import data.nat.gcd.basic


-- Rather than reinventing the wheel now we want to explore how to use mathlib

-- this gives us access to most results of the form `nat.blah` in their short form `blah`

open nat
variables {a b c d k m n : ℕ} -- these will now be available when needed in our examples below

/- TODO Ask Richard what he thinks we need to do on this topic -/
/- Integer dvd -/
example : d ∣ n ↔ ∃ k, n = d*k :=
begin
  refl,
end

example : a ∣ b →  b ∣ c →  a ∣ c:=
begin
  sorry,
end

example : a ∣ b → b ∣ a →  a = b:=
begin
  sorry,
end

example : 0 ∣ a → a = 0:=
begin
  sorry,
end

example : 1 ∣ a :=
begin
  sorry,
end

example : 2 ∣ a ↔ even a :=
begin
  sorry,
end

example : 2 ∣ a →  3 ∣ a →  6 ∣ a:=
begin
  sorry,
end

/-  k % m the remainder of k after division by m`
  while k/m is the quotient so: -/
example : m*(k/m) + (k%m) = k:=
begin
  sorry,
end

example : a % m = b % m → b % m = c % m → a % m = c % m:=
begin
  sorry,
end

#check nat.gcd

