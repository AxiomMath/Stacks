module

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Topology.Sheaves.Init

public import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# Smooth algebras over a quotient are locally base changes of standard smooth algebras

Let `R → R'` be a surjective ring map and let `R' → S'` be smooth. Then `S'` is, locally on
`Spec S'`, the base change of a standard smooth `R`-algebra: there are elements `g ∈ S'`
generating the unit ideal such that each `S'_g` is `R'`-isomorphic to `R' ⊗[R] S` for a standard
smooth `R`-algebra `S`.

## Main results

* `Algebra.Smooth.exists_span_eq_top_isStandardSmooth_algEquiv_tensorProduct`: a smooth algebra
  over a quotient of `R` is, locally on its spectrum, the base change of a standard smooth
  `R`-algebra.
* `Stacks.Smooth.LiftAlongSurjection.solution`: the same assertion.

## Implementation notes

The base is an arbitrary surjection `R → R'`; the case `R' = R ⧸ I` is given by
`Ideal.Quotient.mk_surjective`. The quotient `S ⧸ I S` is written as the base change `R' ⊗[R] S`,
which over `R' = R ⧸ I` agrees with it by `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`.
`Algebra.SubmersivePresentation.ofHasCoeffs` needs a base injecting into `R'`, so only the
pre-submersive `Algebra.PreSubmersivePresentation.ofHasCoeffs` is used, and its jacobian is
inverted by localizing. The parenthetical "(standard)" of the source is taken as part of the
assertion: `S` is standard smooth over `R`.

## References

* [Stacks Project, Tag 04B1](https://stacks.math.columbia.edu/tag/04B1)
-/

@[expose] public section

universe u v w

@[expose] public section

open TensorProduct

namespace Stacks.Smooth.LiftAlongSurjection

section Lift

variable {R R' T : Type*} [CommRing R] [CommRing R'] [CommRing T] [Algebra R R'] [Algebra R' T]
  [Algebra R T] [IsScalarTower R R' T] {ι σ : Type*} [Finite σ]
  (P : Algebra.SubmersivePresentation R' T ι σ) [P.HasCoeffs R]

/-- The jacobian of the pre-submersive presentation obtained by lifting the relations of `P` to
`R` is the class of `Algebra.SubmersivePresentation.jacobianOfHasCoeffs`. -/
private theorem ofHasCoeffs_jacobian :
    (P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian
      = Ideal.Quotient.mk _ (P.jacobianOfHasCoeffs R) := by
  classical
  have := Fintype.ofFinite σ
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Algebra.SubmersivePresentation.jacobianOfHasCoeffs]
  congr!

/-- Under the identification `R' ⊗[R] A ≃ₐ[R'] T` of
`Algebra.Presentation.tensorModelOfHasCoeffsEquiv`, the jacobian of the lifted presentation of
`A` over `R` goes to the jacobian of `P`. -/
private theorem tensorModelOfHasCoeffsEquiv_one_tmul_jacobian :
    P.toPresentation.tensorModelOfHasCoeffsEquiv R
        ((1 : R') ⊗ₜ (P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian) = P.jacobian := by
  rw [ofHasCoeffs_jacobian, ← Algebra.Presentation.tensorModelOfHasCoeffsEquiv_symm_tmul,
    AlgEquiv.apply_symm_apply, Algebra.SubmersivePresentation.aeval_jacobianOfHasCoeffs]

end Lift

/-- If `b : B` is a unit, then `B` is isomorphic as a `k`-algebra to `Localization.Away b`. -/
private theorem nonempty_algEquiv_localizationAway_of_isUnit {k B : Type*} [CommRing k]
    [CommRing B] [Algebra k B] {b : B} (hb : IsUnit b) :
    Nonempty (B ≃ₐ[k] Localization.Away b) :=
  have : IsLocalization.Away b B := IsLocalization.self fun _ ⟨n, hn⟩ ↦ hn ▸ hb.pow n
  ⟨(IsLocalization.algEquiv (Submonoid.powers b) B (Localization.Away b)).restrictScalars k⟩

/-- If `P` is a pre-submersive presentation of `A` over `R`, then a localization of `A` away from
the jacobian of `P` is standard smooth over `R`. -/
private theorem isStandardSmooth_localization_away_jacobian {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.PreSubmersivePresentation R A ι σ) (B : Type*) [CommRing B] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B] [IsLocalization.Away P.jacobian B] :
    Algebra.IsStandardSmooth R B :=
  Algebra.SubmersivePresentation.isStandardSmooth
    { __ := (Algebra.PreSubmersivePresentation.localizationAway B P.jacobian).comp P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit _).mul
          (IsLocalization.Away.algebraMap_isUnit _) }

/-- A standard smooth algebra `T` over `R'`, for a surjection `R → R'`, is `R'`-isomorphic to the
base change `R' ⊗[R] S` of a standard smooth `R`-algebra `S`. -/
private theorem exists_isStandardSmooth_nonempty_algEquiv_tensorProduct (R : Type u) [CommRing R]
    (R' : Type v) [CommRing R'] [Algebra R R'] (hsurj : Function.Surjective (algebraMap R R'))
    (T : Type w) [CommRing T] [Algebra R' T] [Algebra.IsStandardSmooth R' T] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.IsStandardSmooth R S),
      Nonempty (T ≃ₐ[R'] R' ⊗[R] S) := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹Algebra.IsStandardSmooth R' T›.out
  let : Algebra R T := ((algebraMap R' T).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' T := .of_algebraMap_eq fun _ ↦ rfl
  have : P.HasCoeffs R := ⟨by simp [hsurj.range_eq]⟩
  have hΔ : IsUnit ((1 : R') ⊗ₜ[R] (P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian) := by
    rw [← isUnit_map_iff (P.toPresentation.tensorModelOfHasCoeffsEquiv R),
      tensorModelOfHasCoeffsEquiv_one_tmul_jacobian]
    exact P.jacobian_isUnit
  obtain ⟨f⟩ := nonempty_algEquiv_localizationAway_of_isUnit (k := R') hΔ
  refine ⟨Localization.Away (P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian,
    inferInstance, inferInstance,
    isStandardSmooth_localization_away_jacobian (P.toPreSubmersivePresentation.ofHasCoeffs R) _,
    ?_⟩
  exact ⟨((P.toPresentation.tensorModelOfHasCoeffsEquiv R).symm.trans f).trans
    (IsLocalization.Away.tensorProductEquivTMulRight R R' _ _).symm⟩

/-- Let `R → R'` be a surjective ring map and let `R' → S'` be smooth. Then there are elements
`g ∈ S'` generating the unit ideal such that each `S'_g` is `R'`-isomorphic to `R' ⊗[R] S` for
some standard smooth `R`-algebra `S`. -/
public theorem solution (R : Type u) [CommRing R] (R' : Type v) [CommRing R'] [Algebra R R']
    (hsurj : Function.Surjective (algebraMap R R'))
    (S' : Type w) [CommRing S'] [Algebra R' S'] [Algebra.Smooth R' S'] :
    ∃ s : Set S', Ideal.span s = ⊤ ∧ ∀ g ∈ s,
      ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.IsStandardSmooth R S),
        Nonempty (Localization.Away g ≃ₐ[R'] R' ⊗[R] S) := by
  obtain ⟨s, hs, hs'⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R' S'
  refine ⟨s, hs, fun g hg ↦ ?_⟩
  have := hs' g hg
  exact exists_isStandardSmooth_nonempty_algEquiv_tensorProduct R R' hsurj (Localization.Away g)

end Stacks.Smooth.LiftAlongSurjection

end

@[expose] public section

open TensorProduct in
/-- Let `R → R'` be a surjective ring map (for instance `R' = R ⧸ I`) and let `R' → S'` be
smooth. Then there are elements `g ∈ S'` generating the unit ideal of `S'` such that each `S'_g` is
isomorphic as an `R'`-algebra to `R' ⊗[R] S` for some standard smooth `R`-algebra `S`; that is,
`S'` is, locally on `Spec S'`, a base change of a standard smooth `R`-algebra. -/
@[stacks 04B1 "The source's `R/I → S̄` is stated for an arbitrary surjection `R → R'`, which is
what the proof uses (it lifts the relations along `R[x] → R'[x]`); the source's form is the case
`R' = R ⧸ I`, by `Ideal.Quotient.mk_surjective`. The source's `S_i/I S_i` is the base change
`R' ⊗[R] S`, identified with that quotient over `R ⧸ I` by
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`. The parenthetical `(standard)` is taken as
the assertion. See the module docstring."]
public theorem Algebra.Smooth.exists_span_eq_top_isStandardSmooth_algEquiv_tensorProduct
    (R : Type u) [CommRing R] (R' : Type v) [CommRing R'] [Algebra R R']
    (hsurj : Function.Surjective (algebraMap R R'))
    (S' : Type w) [CommRing S'] [Algebra R' S'] [Algebra.Smooth R' S'] :
    ∃ s : Set S', Ideal.span s = ⊤ ∧ ∀ g ∈ s,
      ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.IsStandardSmooth R S),
        Nonempty (Localization.Away g ≃ₐ[R'] R' ⊗[R] S) :=
  Stacks.Smooth.LiftAlongSurjection.solution R R' hsurj S'

end
