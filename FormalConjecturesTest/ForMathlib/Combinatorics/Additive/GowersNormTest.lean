/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesForMathlib.Combinatorics.Additive.GowersNorm

open Complex

variable {G : Type*} [AddCommGroup G]

/-- The multiplicative derivative with step 0 evaluates to the function multiplied by its conjugate. -/
lemma multiplicativeDerivative_zero (f : G → ℂ) (x : G) :
    multiplicativeDerivative 0 f x = f x * star (f x) := by
  simp [multiplicativeDerivative]

/-- The multiplicative derivative of a constant function is constant. -/
lemma multiplicativeDerivative_const (h : G) (c : ℂ) (x : G) :
    multiplicativeDerivative h (fun _ ↦ c) x = c * star c := by
  rfl

/-- The multiplicative derivative is invariant under translation of the input function. -/
lemma multiplicativeDerivative_add_right (h : G) (f : G → ℂ) (x y : G) :
    multiplicativeDerivative h (fun z ↦ f (z + y)) x = multiplicativeDerivative h f (x + y) := by
  simp [multiplicativeDerivative, add_right_comm]

/-- The multiplicative derivative distributes over the product of two functions. -/
lemma multiplicativeDerivative_mul (h : G) (f g : G → ℂ) :
    multiplicativeDerivative h (f * g) = multiplicativeDerivative h f * multiplicativeDerivative h g := by
  ext x
  simp only [multiplicativeDerivative, Pi.mul_apply, star_mul]
  ring

/-- The multiplicative derivative of a conjugated function. -/
lemma multiplicativeDerivative_star (h : G) (f : G → ℂ) (x : G) :
    multiplicativeDerivative h (star f) x = star (f x) * f (x + h) := by
  simp [multiplicativeDerivative]

/-- Taking the derivative with a negative step is equivalent to conjugating and shifting the positive derivative. -/
lemma multiplicativeDerivative_neg_add (h : G) (f : G → ℂ) (x : G) :
    multiplicativeDerivative (-h) f (x + h) = star (multiplicativeDerivative h f x) := by
  simp [multiplicativeDerivative, add_assoc, add_neg_cancel]
  ring

/-- Iterated multiplicative derivatives commute. -/
lemma multiplicativeDerivative_comm (h1 h2 : G) (f : G → ℂ) :
    multiplicativeDerivative h1 (multiplicativeDerivative h2 f) =
    multiplicativeDerivative h2 (multiplicativeDerivative h1 f) := by
  ext x
  simp [multiplicativeDerivative, add_right_comm]
  ring

/--
The multiplicative derivative of a linear phase (a unitary character) is a constant function.
This captures the property that taking the derivative of a phase annihilates the variable x.
-/
lemma multiplicativeDerivative_phase (h : G) (f : G → ℂ)
    (h_add : ∀ a b, f (a + b) = f a * f b)
    (h_unit : ∀ a, f a * star (f a) = 1) :
    multiplicativeDerivative h f = fun _ ↦ star (f h) := by
  ext x
  simp only [multiplicativeDerivative, h_add, star_mul]
  calc
    f x * (star (f h) * star (f x)) = (f x * star (f x)) * star (f h) := by ring
    _ = 1 * star (f h) := by rw [h_unit x]
    _ = star (f h) := by ring

open Fintype BigOperators

/-- The Gowers norm is always non-negative. -/
lemma gowersNormPow_nonneg [Fintype G] (d : ℕ) (f : G → ℂ) :
    0 ≤ gowersNormPow d f := by
  induction d generalizing f with
  | zero =>
    dsimp [gowersNormPow]
    positivity
  | succ d ih =>
    cases d with
    | zero =>
      dsimp [gowersNormPow]
      positivity
    | succ d =>
      dsimp [gowersNormPow]
      apply mul_nonneg
      · positivity
      · apply Finset.sum_nonneg
        intro h _
        apply ih

lemma multiplicativeDerivative_const_fn {G : Type*} [AddCommGroup G] (h : G) (c : ℂ) :
    multiplicativeDerivative h (fun _ ↦ c) = fun _ ↦ c * star c := by
  ext x
  rfl

/-- The Gowers norm of a constant function is the modulus of the constant to the 2^d power. -/
lemma gowersNormPow_const {G : Type*} [AddCommGroup G] [Fintype G] [Nonempty G] (c : ℂ) :
    ∀ (d : ℕ), gowersNormPow d (fun _ : G ↦ c) = ‖c‖ ^ (2 ^ d)
  | 0 => by
    have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [gowersNormPow, Finset.sum_const, nsmul_eq_mul]
  | 1 => by
    have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [gowersNormPow, Finset.sum_const, nsmul_eq_mul]
  | d + 2 => by
    have hG : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    dsimp [gowersNormPow]
    simp only [multiplicativeDerivative_const_fn]
    
    -- The recursive call automatically acts as the inductive hypothesis
    rw [gowersNormPow_const (c * star c) (d + 1)] 
    
    -- Collapse the real sum
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [inv_mul_cancel_left₀ hG]
    
    -- Clean up the norms and powers
    have h_norm : ‖c * star c‖ = ‖c‖ ^ 2 := by rw [norm_mul, star_def, norm_conj, sq]
    rw [h_norm, ← pow_mul]
    congr 1
    ring

lemma multiplicativeDerivative_add_right_fn {G : Type*} [AddCommGroup G] (h : G) (f : G → ℂ) (y : G) :
    multiplicativeDerivative h (fun z ↦ f (z + y)) = fun x ↦ multiplicativeDerivative h f (x + y) := by
  ext x
  simp [multiplicativeDerivative, add_right_comm]

/-- The Gowers norm is invariant under translation of the input function. -/
lemma gowersNormPow_translate {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) (y : G) :
    ∀ (d : ℕ), gowersNormPow d (fun z ↦ f (z + y)) = gowersNormPow d f
  | 0 => by
    dsimp [gowersNormPow]
    congr 2
    exact Fintype.sum_equiv (Equiv.addRight y) _ _ (by intro x; rfl)
  | 1 => by
    dsimp [gowersNormPow]
    congr 3
    exact Fintype.sum_equiv (Equiv.addRight y) _ _ (by intro x; rfl)
  | d + 2 => by
    dsimp [gowersNormPow]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    rw [multiplicativeDerivative_add_right_fn]
    exact gowersNormPow_translate (multiplicativeDerivative h f) y (d + 1)
