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

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open scoped BigOperators
open Complex

/-!
# Gowers Norms and Multiplicative Derivatives

This file provides common definitions for the multiplicative derivative and Gowers norms
over finite groups, which are frequently used in additive combinatorics.
-/

/--
The multiplicative derivative $\Delta_h f(x) = f(x) \overline{f(x+h)}$.
-/
noncomputable def multiplicativeDerivative {G : Type*} [AddGroup G] (h : G) (f : G → ℂ) : G → ℂ :=
  fun x ↦ f x * star (f (x + h))

/--
The $2^d$-th power of the $U^d$ Gowers norm of a function $f : G \to \mathbb{C}$ on a finite group $G$.
Defined inductively:
$\lVert f \rVert_{U^1}^2 = |\mathbb{E}_x f(x)|^2$
$\lVert f \rVert_{U^{d+1}}^{2^{d+1}} = \mathbb{E}_h \lVert \Delta_h f \rVert_{U^d}^{2^d}$
-/
noncomputable def gowersNormPow {G : Type*} [AddCommGroup G] [Fintype G] : ℕ → (G → ℂ) → ℝ
  | 0, f => ‖(Fintype.card G : ℂ)⁻¹ * ∑ x, f x‖
  | 1, f => ‖(Fintype.card G : ℂ)⁻¹ * ∑ x, f x‖^2
  | d + 2, f => (Fintype.card G : ℝ)⁻¹ * ∑ h, gowersNormPow (d + 1) (multiplicativeDerivative h f)
