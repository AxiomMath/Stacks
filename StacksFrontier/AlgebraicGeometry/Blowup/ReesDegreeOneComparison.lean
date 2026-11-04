module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesRestrictDegOne

/-!
# The degree-one generators of the two Rees gradings agree

Let `X` be a scheme and `I` a quasi-coherent ideal sheaf on it. A section `a ∈ I(U)` over an
affine open gives a degree-one element of the graded section ring of the Rees algebra *sheaf*,
`AlgebraicGeometry.reesDegreeOne` — this is the one the charts of
`AlgebraicGeometry.blowUp` are cut out by — and a degree-one element `a⁽¹⁾` of the *ordinary*
Rees algebra `Γ(X, U)[I(U)t]`, `Stacks.Blowup.reesDegOne`. This file proves that the comparison
`AlgebraicGeometry.reesSectionGradedHom` of the two graded rings carries the first to the second,
and draws the three consequences the comparison of `𝒪(1)` with the exceptional ideal sheaf needs.

## Main results

* `AlgebraicGeometry.coe_reesSectionGradedHom_reesDegreeOne`: **the comparison carries
  `reesDegreeOne` to `a⁽¹⁾`.** Both are the monomial `a·T`.
* `AlgebraicGeometry.gradedSectionRestriction_reesDegreeOne`: **the degree-one generator
  restricts to the degree-one generator of the restricted section.**
* `AlgebraicGeometry.projInclusionMap_preimage_basicOpen_reesDegreeOne`: the chart of the blowup
  cut out by `a` pulls back, along the Tag 01NO transition, to the chart cut out by the
  restriction of `a`.
* `AlgebraicGeometry.sectionRingBaseMap_mul_reesDegreeOne_comm`: **the cross identity**
  `a⁽⁰⁾·a'⁽¹⁾ = a'⁽⁰⁾·a⁽¹⁾` in the graded section ring. This is what makes the comparison of
  `𝒪(1)` with the exceptional ideal sheaf independent of the chart.

## Implementation notes

Every statement is proved by applying `AlgebraicGeometry.reesSectionGradedHom`, which is injective
because it is a ring *isomorphism* (`AlgebraicGeometry.reesSectionRingEquiv`), and computing in the
ordinary Rees algebra, where the elements are polynomials. Nothing can be computed on the sheaf
side: `AlgebraicGeometry.reesAlgebraData` is selected by `Classical.choice`, and
`AlgebraicGeometry.reesPieceEquiv` together with its five compatibility lemmas is all that is
available.

The degree of `AlgebraicGeometry.reesPieceEquiv` is pinned at the `ℕ` spelling while
`AlgebraicGeometry.reesDegreeOne` is written with `(reesAlgebraData I).pieceEquiv` at the `ℤ`
spelling `(1 : ℤ)`. The two agree definitionally — `((1 : ℕ) : ℤ)` and `(1 : ℤ)` are both
`Int.ofNat 1`, and the nonnegativity proofs are irrelevant — so the conversion is a single `rfl`
in `reesDegreeOne_eq_of`, stated once so that no later proof depends on it.

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial TopologicalSpace Opposite
open Stacks.Blowup (reesGrading reesDegOne sheafRestrict sheafRestrict_mem_ideal
  reesRestrict reesRestrict_reesDegOne coe_reesDegOne)
open Stacks.RelativeProj

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The degree-one generator attached to `a ∈ I(U)`, written with
`AlgebraicGeometry.reesPieceEquiv` rather than with the underlying field of
`AlgebraicGeometry.reesAlgebraData`. The two spellings of the degree, `(1 : ℤ)` and
`((1 : ℕ) : ℤ)`, are the same numeral and the nonnegativity proofs are irrelevant. -/
theorem reesDegreeOne_eq_of (U : X.affineOpens) (a : I.ideal U) :
    (reesDegreeOne I U a).1 =
      DirectSum.of ((reesSituation I).sectionPieces U.1) 1
        ((reesPieceEquiv I U 1).symm ⟨(a : Γ(X, U.1)), by simp⟩) :=
  rfl

/-- **The comparison of the two Rees gradings carries the degree-one generator of `a` to the
degree-one element `a⁽¹⁾` of the ordinary Rees algebra.** Both are the monomial `a·T`. -/
theorem coe_reesSectionGradedHom_reesDegreeOne (U : X.affineOpens) (a : I.ideal U) :
    ((reesSectionGradedHom I U (reesDegreeOne I U a).1 : ↥(reesAlgebra (I.ideal U))) :
        Polynomial Γ(X, U.1)) =
      monomial 1 (a : Γ(X, U.1)) := by
  rw [reesDegreeOne_eq_of, coe_reesSectionGradedHom_of]
  exact congrArg (monomial 1) (congrArg (fun z : ↥(I.ideal U ^ 1) => (z : Γ(X, U.1)))
    ((reesPieceEquiv I U 1).apply_symm_apply _))

/-- The comparison carries the degree-one generator of `a` to `Stacks.Blowup.reesDegOne`. -/
theorem reesSectionGradedHom_reesDegreeOne (U : X.affineOpens) (a : I.ideal U) :
    reesSectionGradedHom I U (reesDegreeOne I U a).1 = reesDegOne (I.ideal U) a.2 :=
  Subtype.ext ((coe_reesSectionGradedHom_reesDegreeOne I U a).trans
    (coe_reesDegOne (I.ideal U) a.2).symm)

/-- The comparison of the two Rees gradings over an affine open is injective: it is the underlying
map of the ring isomorphism `AlgebraicGeometry.reesSectionRingEquiv`. -/
theorem injective_reesSectionGradedHom (U : X.affineOpens) :
    Function.Injective (reesSectionGradedHom I U) :=
  fun _ _ h => (reesSectionRingEquiv I U).injective h

/-- **The degree-one generator restricts to the degree-one generator of the restricted
section.** -/
theorem gradedSectionRestriction_reesDegreeOne {U V : X.affineOpens} (h : U ≤ V)
    (a : I.ideal V) :
    Situation.gradedSectionRestriction (reesSituation I) U.1 V.1 h (reesDegreeOne I V a).1 =
      (reesDegreeOne I U ⟨(sheafRestrict h).hom (a : Γ(X, V.1)),
        sheafRestrict_mem_ideal I h a⟩).1 := by
  refine injective_reesSectionGradedHom I U ?_
  have hcomp : reesSectionGradedHom I U
        (Situation.gradedSectionRestriction (reesSituation I) U.1 V.1 h
          (reesDegreeOne I V a).1) =
      reesRestrict I h (reesSectionGradedHom I V (reesDegreeOne I V a).1) :=
    congrArg
      (fun k : (reesSituation I).sectionRingGrading V.1 →+*ᵍ reesGrading (I.ideal U) =>
        k (reesDegreeOne I V a).1)
      (reesSectionGradedHom_comp_gradedSectionRestriction I h)
  rw [hcomp, reesSectionGradedHom_reesDegreeOne, reesRestrict_reesDegOne,
    reesSectionGradedHom_reesDegreeOne]

/-- **The chart cut out by `a` pulls back to the chart cut out by the restriction of `a`.** The
preimage, under the Tag 01NO chart transition, of the standard open of the degree-one generator of
`a ∈ I(V)` is the standard open of the degree-one generator of its restriction to `U`. -/
theorem projInclusionMap_preimage_basicOpen_reesDegreeOne {U V : X.affineOpens} (h : U ≤ V)
    (a : I.ideal V) :
    Situation.projInclusionMap (reesSituation I) U.1 V.1 h U.2 V.2 ⁻¹ᵁ
        Proj.basicOpen ((reesSituation I).sectionRingGrading V.1) (reesDegreeOne I V a).1 =
      Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U ⟨(sheafRestrict h).hom (a : Γ(X, V.1)),
          sheafRestrict_mem_ideal I h a⟩).1 := by
  rw [show Situation.projInclusionMap (reesSituation I) U.1 V.1 h U.2 V.2 =
        Proj.map (Situation.gradedSectionRestriction (reesSituation I) U.1 V.1 h)
          (Situation.irrelevant_le_map_gradedSectionRestriction (reesSituation I) U.1 V.1 h
            U.2 V.2) from rfl,
    Proj.map_preimage_basicOpen, gradedSectionRestriction_reesDegreeOne]

/-- **The cross identity of two degree-one Rees generators**: `a⁽⁰⁾·a'⁽¹⁾` and `a'⁽⁰⁾·a⁽¹⁾` are
both the monomial `(a·a')·T` of the graded section ring. This is what makes the comparison of
`𝒪(1)` with the exceptional ideal sheaf independent of the chart.

The two degree-zero copies are passed as sections `r`, `r'` of the sheaf of rings together with
the equations identifying them with `a` and `a'`, rather than written as
`sectionRingBaseMap U.1 (a : Γ(X, U.1))`: the argument of
`Stacks.RelativeProj.Situation.sectionRingBaseMap` has the spelling
`X.ringCatSheaf.obj.obj (op U.1)`, which is definitionally but not *reducibly* `Γ(X, U.1)`, and
at the second spelling the rewriting step does not find its pattern. -/
theorem sectionRingBaseMap_mul_reesDegreeOne_comm (U : X.affineOpens)
    (r r' : X.ringCatSheaf.obj.obj (op U.1)) (a a' : I.ideal U)
    (hr : (show Γ(X, U.1) from r) = (a : Γ(X, U.1)))
    (hr' : (show Γ(X, U.1) from r') = (a' : Γ(X, U.1))) :
    (reesSituation I).sectionRingBaseMap U.1 r * (reesDegreeOne I U a').1 =
      (reesSituation I).sectionRingBaseMap U.1 r' * (reesDegreeOne I U a).1 := by
  refine injective_reesSectionGradedHom I U (Subtype.ext ?_)
  have key : ∀ (s : X.ringCatSheaf.obj.obj (op U.1)) (c : I.ideal U),
      ((reesSectionGradedHom I U ((reesSituation I).sectionRingBaseMap U.1 s *
            (reesDegreeOne I U c).1) : ↥(reesAlgebra (I.ideal U))) : Polynomial Γ(X, U.1)) =
        C (show Γ(X, U.1) from s) * (C (c : Γ(X, U.1)) * Polynomial.X) := by
    intro s c
    rw [map_mul, Subalgebra.coe_mul, coe_reesSectionGradedHom_baseMap,
      coe_reesSectionGradedHom_reesDegreeOne, ← C_mul_X_pow_eq_monomial, pow_one]
  rw [key r a', key r' a, hr, hr']
  ring

end AlgebraicGeometry

end
