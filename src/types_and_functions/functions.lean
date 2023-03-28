import Mathlib.Data.Real.Basic

variable {A B C D E F: Type} 
open Nat
/-
Everything in green or orange text is a `comment`. 

This means that Lean ignores it.

A single line comment starts with --

A multi-line comment starts with /- and s with -/

Comments are our way of explaining what our code does.

# What is Lean?   

Lean is at least three things: 

1) A programming language in which we can write proofs (and more);

2) A kernel that can verify the correctness of proofs written in this language;

3) A set of tools that help us to write proofs (automation).

We will gradually introduce the Lean language and we will rely on its kernel to check 
our code/proofs. The different tools for automation will also become apparent as we progress.

# Infoview

One of the most helpful tools that Lean has is the Infoview.

Open the `Infoview` panel by pressing `Ctrl + Shift + Enter`

You should now have a split-window with this Lean code file
on the left and the `Lean Infoview` on the right.

Before we start to introduce the Lean syntax and tactics,
lets first see what information this Lean Infoview provides.

As you move your cursor through the lines of text below, watch how
the Infoview updates. -/

-- 01
example  (x : A) : A :=  
by 
/-
If you place your cursor anywhere within this comment 
the Infoview should display:
1 goal
A : Type
x : A
⊢ A
-/
exact x
/-
  # Type theory vs Set theory

Lean is based on type theory.

While mathematicians usually talk about `sets` and `elements`, in Lean
we have `types` and `terms`. 

In our example above we told Lean that:

`x` is a term a of type A `(x : A)` we can think of this as saying `x ∈ A` 

The final line of the Infoview is our goal: `⊢ A` which tells us the type of the 
term that Lean is expecting us to produce. 

This is the `return type` of the function and is determined by the `: A` after the hypotheses in our example.

The `:=` tells Lean we are going to define the body of this function.

The function body bys with `by` and s with ``. This tells Lean
we are entering `tactic-mode`. 

(There are other `modes`, in particular `term-mode` but we will mainly focus on tactics.)

The only line of code inside the body is `exact x`. This is a tactic that says
`x` is `exactly` a term of the type required by the goal. (Because `x` is a term of type `A`.) 


Our next tactic is `sorry`. This is a magic tactic that will accomplish any goal. 

Unfortunately this is cheating (notice the example below has a yellow wavy-line under it to 
warn us that something is wrong and `sorry` is in bright red).

Throughout this course you will encounter Lean code containing `sorry` that you will need to 
edit, replacing the `sorry` with an actual proof of the required goal.

Can you replace the `sorry` with something that will actually accomplish the goal? -/

-- 02
example  (x : A) (y : B) (z : C) : B :=
by
/- 
1 goal
A B C : Type
x : A
y : B
z : C
⊢ B
-/
exact y

/-
If A and B are types,  then `A → B` is the type of functions from A to B. 

(Note that if you hover over any symbol Lean will tell you how to write it,
for example `→` is `\to`.)  

If `f : A → B` and `a : A` then `f a` is Lean for `f(a)`. 
This may look strange, but will actually make our proofs easier to read.
-/

-- 03
example  (f : A → B) (a : A) : B :=
by
/-
1 goal
A B : Type
f : A → B
a : A
⊢ B
-/
  exact f a -- Note that `exact f(a)` or `exact (f a)` or `exact (f(a))` will also work.


-- A different way to achieve the same goal is to use the `apply` tactic
-- 04
example (f : A → B) (a : A) : B :=
by
/-
1 goal
A B : Type
f : A → B
a : A
⊢ B
-/
apply f 
/-
Notice that our goal has changed from `⊢ B` to `⊢ A`. 
  
Think of this as saying if we have a function `f: A → B`
and our goal is `⊢ B` then we can `apply f` and this reduces our goal to supplying 
an input to the function `f`, namely a term of type A. 
-/ 
exact a  -- since our goal is now `⊢ A` we can close it with `a` since this is a term of type `A`.

-- 05
example  (f : A  → B) (g : B → C) (a : A) : C :=
by
-- goal `⊢ C`
  apply g -- goal changes from `⊢ C` to `⊢ B` 
  apply f -- goal changes from `⊢ B` to `⊢ A`
  exact a -- done!


/-
See how many different ways you can find to complete the next example 
using `exact` and/or `apply` -/

-- 06
example  (f : A  → B) (g : B → C) (h : C → D) (a : A): D := 
by
  apply h;  apply g;  apply f; exact a

-- 07
example (f :A → B) (g: B → C) (h: D → E) (i : C → E) (x : A) : E:=
by
  sorry


-- 08 Can you work out what `f: A → B → C` means and complete this example?
example (f : A → B → C)  (x : A) (y : B): C:=
by
  sorry


/- Mathematicians and Computer Scientists have slightly different ideas of how to 
   write functions of more than one variable. 

Math: `f : A × B → C`    Comp Sci: `g : A → B → C` 

Both of these can be defined in Lean, however the CS version (which is known as a
`curried` function) turns out to be extremely useful.

But what do we mean by `A → B → C` ? We need to know where the brackets should go.

We need to know whether  `A → B → C` is `A → (B → C)` or `(A → B) → C`

Lets see how we can use Lean's `#check`  command to work this out.  -/

--variable (f : A → (B → C))
--variable (g : (A → B) → C) 
--#check f  -- f : A → B → C    Lean has removed our unnecessary brackets from f.
--#check g  -- g : (A → B) → C  The brackets in g are required!

-- 09  What is f?
example (f : A → B → C → D) (g : A → B) (x : A)(z : C): D :=
by
  apply f; exact x; apply g;exact x;exact z


/- So far all our examples have involved applying functions to obtain new terms,
 but what if our goal is to construct a function itself?

  In order to define functions we need a new tactic: `intro`    -/

-- 10 
example : A → A :=
by
/-
1 goal
A : Type
⊢ A → A 
-/
  intro x -- Now we have a `x : A`, a term x of type A and our goal is now `⊢ A`
/-
1 goal
A : Type
x : A
⊢ A
-/
  exact x 


-- 11 
example (b : B) : A → B :=
by
  sorry


-- 12 [Tip: Rather than `intro a, intro b` you can just use `intros a b`]
example (c : C) : A → B → C → A → B →  C → A :=
by 
  sorry


-- 13 
example (f : (A → B) → (C → D) → E) (b : B) (d : D) : E :=
by
  sorry


-- 14   
example (f : (A → B → C) → D → (E → C) → B) (g : B → A → C) (h : (B → C) → D) (c : C): A → B:=
by
  sorry


-- 15 Can you find a two line proof of this? (Hint: first find a longer proof and then shorten it)
example : ((A → D) → ((B → E) → (C → F))) → (((A → D) → (B → E)) → ((A → D) → (C → F))) :=
by
  intro f g ad c; apply f ad (g ad) c;



