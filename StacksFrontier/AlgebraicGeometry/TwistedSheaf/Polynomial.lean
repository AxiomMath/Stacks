module

public import Mathlib.Topology.KrullDimension
public import StacksFrontier.Algebra.Polynomial.Numerical
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs

/-!
# The induction of Tag 0BEM

Tag 0BEM says that the Euler characteristic of the twists
`ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` of a coherent sheaf on a proper scheme over a field is a
numerical polynomial in `n_1, …, n_r` of total degree at most `dim Supp ℱ`. The source proves it
by induction on `dim Supp ℱ`: the zero-dimensional case is constant, and above it each first
difference of the Euler characteristic is a difference of Euler characteristics of two coherent
sheaves whose supports have strictly smaller dimension, so the first differences are polynomials
of strictly smaller total degree by the induction hypothesis, and "a simple arithmetic argument"
closes the proof.

That arithmetic argument is `MvPolynomial.exists_totalDegree_le_of_forall_fwdDiff`. This file
supplies the induction that consumes it, and nothing else: the descent is separated from the
geometry, so what Tag 0BEM still owes is exactly its two geometric inputs, stated as the
hypotheses of `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_dimension_descent`.

## Main results

* `MvPolynomial.exists_totalDegree_le_of_dimension_descent`: **the induction of Tag 0BEM, with
  the geometry abstracted away.** For a function `chi` on any type `S` carrying a natural-number
  "dimension" `dim`, if `chi F` is given by a polynomial of total degree `0` whenever
  `dim F = 0`, and if above that every first difference of `chi F` is a difference `chi G₁ - chi
  G₂` with `dim G₁, dim G₂ < dim F`, then `chi F` is given by a polynomial of total degree at
  most `dim F`.
* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_dimension_descent`: the same
  induction run on the Euler characteristics of the twists, concluding Tag 0BEM's statement in
  the shape in which the library states it.
* `MvPolynomial.coe_totalDegree_le_of_totalDegree_le`: the degree bound transported from `ℕ` to
  `WithBot ℕ∞`, where `topologicalKrullDim` takes its values.

## Implementation notes

**Why the induction is stated abstractly.** The descent is on a natural number, the first
differences are taken in `ℚ`, and the sheaves enter only through the values of the Euler
characteristic. Nothing in the argument is about sheaves, and stating it about sheaves would
force every intermediate polynomial to be carried alongside a coherence instance. `S` is
therefore an arbitrary type; the geometric corollary instantiates it at the coherent sheaves on
`X`, as a subtype, which is what supplies the coherence of `G₁` and `G₂` to the induction
hypothesis.

**The descent is on a bound, not on the dimension itself.** `dim` is an arbitrary
`ℕ`-valued function, so the geometric corollary may instantiate it by any bound for the
dimension of the support; the conclusion's degree bound is the value of that same function.
This is what lets the corollary state its conclusion against `topologicalKrullDim`, which takes
values in `WithBot ℕ∞` and so cannot be inducted on directly: the hypothesis `hdim` asks only
that the chosen natural number not exceed the dimension of the support, and
`MvPolynomial.coe_totalDegree_le_of_totalDegree_le` transports the bound.

**Induction on an upper bound.** The proof proves the stronger `∀ d, ∀ F, dim F ≤ d → …` by
induction on `d`, rather than strong induction on `dim F`, because the step needs the induction
hypothesis at every value below `dim F` at once and `dim G₁` is only known to be smaller, not
smaller by one.

**What is assumed, and what Tag 0BEM still owes.** Nothing here is conditional except the two
hypotheses of the geometric corollary, which are precisely the source's two geometric inputs:

* `hbase`, the zero-dimensional case, which is Tag 0AYT clauses (4) and (5) — `χ(X, ℱ) = dim_k
  H⁰(X, ℱ)` and `χ(X, ℱ ⊗ 𝓔) = n · χ(X, ℱ)` for `𝓔` locally free of rank `n`, the latter at
  `n = 1` making the function constant. Only clause (1) of Tag 0AYT is in the library, as
  `AlgebraicGeometry.nonempty_generatingSections_of_support_dim_le_zero`.
* `hstep`, the first-difference identity, which is the source's regular meromorphic section and
  its ideal of denominators (Tags 02OZ and 02P2) together with the two reductions that make them
  available (Tags 02OL and 02OM), the invariance of cohomology along a closed immersion (Tag
  089W) and additivity of the Euler characteristic (Tag 08AA). Of these only Tag 08AA is in the
  library, and conditionally:
  `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional_of_isZero`
  carries Tags 02O6 and 01XJ as hypotheses.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
-/

@[expose] public noncomputable section

namespace MvPolynomial

variable {r : ℕ}

/-- A bound on the total degree by a natural number transported to `WithBot ℕ∞`, where
`topologicalKrullDim` takes its values. -/
theorem coe_totalDegree_le_of_totalDegree_le {P : MvPolynomial (Fin r) ℚ} {d : ℕ}
    {D : WithBot ℕ∞} (hP : P.totalDegree ≤ d) (hd : (d : WithBot ℕ∞) ≤ D) :
    (P.totalDegree : WithBot ℕ∞) ≤ D :=
  le_trans (by exact_mod_cast hP) hd

/-- **The induction of Stacks Tag 0BEM, with the geometry abstracted away.** Let `chi` assign to
each element of `S` a function on `ℤ ^ r`, and let `dim : S → ℕ`. Suppose `chi F` is given by a
rational polynomial of total degree `0` whenever `dim F = 0`, and that for `dim F ≠ 0` each first
difference of `chi F` is a difference `chi G₁ - chi G₂` with `dim G₁` and `dim G₂` both smaller
than `dim F`. Then `chi F` is given by a rational polynomial of total degree at most `dim F`.

The step applies the induction hypothesis to `G₁` and `G₂` to express the `i`-th first difference
of `chi F` as a polynomial of total degree at most `dim F - 1`, and then
`MvPolynomial.exists_totalDegree_le_of_forall_fwdDiff` raises the degree by exactly one. -/
theorem exists_totalDegree_le_of_dimension_descent {S : Type*} (dim : S → ℕ)
    (chi : S → (Fin r → ℤ) → ℚ)
    (hbase : ∀ F : S, dim F = 0 →
      ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ 0 ∧
        ∀ n : Fin r → ℤ, eval (fun j => (n j : ℚ)) P = chi F n)
    (hstep : ∀ F : S, dim F ≠ 0 → ∀ i : Fin r,
      ∃ G₁ G₂ : S, dim G₁ < dim F ∧ dim G₂ < dim F ∧
        ∀ n : Fin r → ℤ,
          chi F (Function.update n i (n i + 1)) - chi F n = chi G₁ n - chi G₂ n)
    (F : S) :
    ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ dim F ∧
      ∀ n : Fin r → ℤ, eval (fun j => (n j : ℚ)) P = chi F n := by
  suffices key : ∀ d : ℕ, ∀ F : S, dim F ≤ d →
      ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ dim F ∧
        ∀ n : Fin r → ℤ, eval (fun j => (n j : ℚ)) P = chi F n from
    key (dim F) F le_rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro F hF
    by_cases h0 : dim F = 0
    · obtain ⟨P, hdeg, hP⟩ := hbase F h0
      exact ⟨P, by omega, hP⟩
    · choose G₁ G₂ hG₁ hG₂ hchi using hstep F h0
      have hdiff : ∀ i : Fin r, ∃ Q : MvPolynomial (Fin r) ℚ, Q.totalDegree ≤ dim F - 1 ∧
          ∀ n : Fin r → ℤ, eval (fun j => (n j : ℚ)) Q
            = chi F (Function.update n i (n i + 1)) - chi F n := fun i => by
        have h₁ := hG₁ i
        have h₂ := hG₂ i
        obtain ⟨P₁, hd₁, hP₁⟩ := ih (dim (G₁ i)) (by omega) (G₁ i) le_rfl
        obtain ⟨P₂, hd₂, hP₂⟩ := ih (dim (G₂ i)) (by omega) (G₂ i) le_rfl
        refine ⟨P₁ - P₂, ?_, fun n => ?_⟩
        · have := totalDegree_sub P₁ P₂
          omega
        · simp only [map_sub, hP₁ n, hP₂ n]
          exact (hchi i n).symm
      choose Q hQdeg hQ using hdiff
      obtain ⟨P, hdeg, hP⟩ :=
        exists_totalDegree_le_of_forall_fwdDiff (dim F - 1) (chi F) Q hQdeg hQ
      exact ⟨P, by omega, hP⟩

end MvPolynomial

namespace AlgebraicGeometry

open CategoryTheory
open Stacks.SheafOfModules.TensorSheafification

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ}
  (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- **Stacks Tag 0BEM from its two geometric inputs.** Let `dim` be any natural-number bound for
the dimension of the support of a coherent sheaf on `X`. Suppose

* `hbase`: whenever `dim G = 0`, the Euler characteristics of the twists of `G` are the values of
  a rational polynomial of total degree `0`, i.e. are constant — this is Tag 0AYT (4) and (5);
  and
* `hstep`: whenever `dim G ≠ 0`, each first difference of the Euler characteristics of the twists
  of `G` is the difference of those of two coherent sheaves of strictly smaller `dim` — this is
  the source's regular meromorphic section and ideal of denominators (Tags 02OZ, 02P2), with
  additivity of the Euler characteristic (Tag 08AA).

Then for every coherent `F` whose `dim` does not exceed the dimension of its support, the Euler
characteristics of the twists of `F` are the values of a rational polynomial which is zero or has
total degree at most that dimension. That is Tag 0BEM's conclusion in the shape in which the library
states it.

The hypothesis `hdim` is not a restriction on `F`: it fixes the meaning of `dim F` as a bound
realized by the support, which is what makes the conclusion's degree bound a statement about the
support rather than about the chosen `dim`. -/
theorem exists_eulerPolynomial_twistedSheaf_of_dimension_descent (dim : X.Modules → ℕ)
    (hbase : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), dim G = 0 →
      ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ 0 ∧
        ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
          = (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
              (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ))
    (hstep : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), dim G ≠ 0 → ∀ i : Fin r,
      ∃ (G₁ G₂ : X.Modules) (hG₁ : SheafOfModules.IsCoherent G₁)
        (hG₂ : SheafOfModules.IsCoherent G₂), dim G₁ < dim G ∧ dim G₂ < dim G ∧
        ∀ n : Fin r → ℤ,
          (@eulerCharacteristic k _ X f _ (twistedSheaf G L (Function.update n i (n i + 1)))
              (@twistedSheaf_isCoherent X r G L _ hG _) : ℚ)
            - (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
                (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ)
            = (@eulerCharacteristic k _ X f _ (twistedSheaf G₁ L n)
                (@twistedSheaf_isCoherent X r G₁ L _ hG₁ n) : ℚ)
              - (@eulerCharacteristic k _ X f _ (twistedSheaf G₂ L n)
                  (@twistedSheaf_isCoherent X r G₂ L _ hG₂ n) : ℚ))
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F)
    (hdim : ((dim F : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (SheafOfModules.supp F)) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) := by
  obtain ⟨P, hdeg, hP⟩ :=
    MvPolynomial.exists_totalDegree_le_of_dimension_descent
      (S := {G : X.Modules // SheafOfModules.IsCoherent G}) (fun G => dim G.1)
      (fun G n => (@eulerCharacteristic k _ X f _ (twistedSheaf G.1 L n)
        (@twistedSheaf_isCoherent X r G.1 L _ G.2 n) : ℚ))
      (fun G hG => hbase G.1 G.2 hG)
      (fun G hG i => by
        obtain ⟨G₁, G₂, hG₁, hG₂, h₁, h₂, h⟩ := hstep G.1 G.2 hG i
        exact ⟨⟨G₁, hG₁⟩, ⟨G₂, hG₂⟩, h₁, h₂, h⟩)
      ⟨F, hF⟩
  exact ⟨P, Or.inr (MvPolynomial.coe_totalDegree_le_of_totalDegree_le hdeg hdim), hP⟩

end AlgebraicGeometry

end
