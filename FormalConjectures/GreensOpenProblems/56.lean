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

import FormalConjectures.Util.ProblemImports
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Ben Green's Open Problem 56

*Reference:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.56)

Bounds for the inverse theorem for Gowers norms.
-/

namespace Green56

open scoped BigOperators
open Complex

/-- Shorthand notation for `𝔽 p n` over `p, n` as variables. -/
local macro "𝔽ₚⁿ" : term => `(𝔽 $(Lean.mkIdent `p) $(Lean.mkIdent `n))

/--
Polynomial Gowers Inverse Conjecture.

Fix an integer $s \ge 1$, and let $p > s$. Suppose that $f : \mathbb{F}_p^n \to \mathbb{C}$ is a function
with $|f(x)| \le 1$ for all $x$, and that $\lVert f \rVert_{U^{s+1}} \ge \delta$. Then there is a form
$\psi$ of degree $s$ such that $|\mathbb{E}_{x \in \mathbb{F}_p^n} f(x) e(-2 \pi i \psi(x)/p)| \gg \delta^{O_s(1)}$.
-/
@[category research open, AMS 5 11]
theorem green_56 :
    answer(sorry) ↔ ∀ (s : ℕ) (hs : 1 ≤ s) (p : ℕ) [Fact p.Prime] (hp : s < p),
      ∃ (C E : ℝ), 0 < C ∧ 0 < E ∧
      ∀ (δ : ℝ) (hδ : 0 < δ)

      -- Avoid vacuous truth if δ > 1, since the Gowers norm of a 1-bounded function is ≤ 1
      (hδ_le : δ ≤ 1)

      (n : ℕ)
      -- Avoid trivial 1-point domain if n = 0
      (hn : 1 ≤ n)

      (f : 𝔽ₚⁿ → ℂ)
      (hf : ∀ x, ‖f x‖ ≤ 1)
      (h_bound : gowersNormPow (s + 1) f ≥ δ ^ (2 ^ (s + 1))),
      ∃ (ψ : MvPolynomial (Fin n) (ZMod p)), ψ.totalDegree ≤ s ∧
        ‖(1 / (p^n : ℝ)) * ∑ x : 𝔽ₚⁿ,
          f x * Complex.exp (- 2 * Real.pi * Complex.I * (MvPolynomial.eval x ψ).val / p)‖ ≥ C * δ ^ E := by
  sorry

end Green56
