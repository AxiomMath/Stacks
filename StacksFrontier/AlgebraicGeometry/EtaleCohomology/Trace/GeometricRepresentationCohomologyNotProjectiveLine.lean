module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationComparisonCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroProjectiveLine

/-!
# `H^i(X_{k̄}, ℱ_ρ) = H^i(π₁(X_{k̄}), M)` when `X_{k̄} ≇ 𝐏¹`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure of
`k`, and `Λ` a finite ring with `#Λ` invertible in `k`, and assume `X_{k̄} ≇ 𝐏¹_{k̄}`. Then the
functors `(M, ρ) ↦ H^i(X_{k̄}, ℱ_ρ)` on finite `Λ`-modules with a continuous action of
`π₁(X, η̄)` form a universal δ-functor, i.e. they are the right derived functors of
`(M, ρ) ↦ M^{π₁(X_{k̄}, η̄)}`, and the comparison morphism
`H^i(π₁(X_{k̄}, η̄), M) ⟶ H^i(X_{k̄}, ℱ_ρ)` is an isomorphism (the cohomological half of
[Stacks, Tag 03VM]).

The results follow from `AlgebraicGeometry.isIso_geometricComparison_of_smoothCurve`: the
topological instances on `X` and `X_{k̄}` are derived from `X` being a geometrically connected
curve, and the genus bound `X_{k̄}` proper `⇒ genus ≥ 1` is derived from `X_{k̄} ≇ 𝐏¹_{k̄}` through
`AlgebraicGeometry.one_le_genus_of_not_exists_iso_projectiveSpaceOver_one` (a smooth proper curve
of genus zero over an algebraically closed field is `𝐏¹`).

`𝐏¹_{k̄}` is `AlgebraicGeometry.projectiveSpaceOver 1 (Spec k̄)` ([Stacks, Tag 01NF]), and
`X_{k̄} ≇ 𝐏¹_{k̄}` is read as: there is no isomorphism `X_{k̄} ≅ 𝐏¹_{k̄}` over `k̄`. This is the
weakest reading of the hypothesis (an isomorphism over `k̄` is in particular an isomorphism of
schemes), so the statements below are the strongest ones.

## Main results

* `AlgebraicGeometry.one_le_genus_fieldBaseChange_of_not_iso`
* `AlgebraicGeometry.isIso_geometricComparison_of_not_iso_projectiveLine`
* `AlgebraicGeometry.isUniversal_geometricRepresentationCohomology_of_not_iso_projectiveLine`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] (Λ : Type) [Ring Λ] [Finite Λ]

/-- **`X_{k̄} ≇ 𝐏¹_{k̄}` forces genus `≥ 1` when `X_{k̄}` is proper.** -/
theorem one_le_genus_fieldBaseChange_of_not_iso
    (hP : ¬ ∃ e : Stacks.Frobenius.fieldBaseChange (Over.mk f) K ≅
        projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :
    IsProper (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) →
      1 ≤ genus (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) := by
  intro hprop
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := QuasiCompact.compactSpace_of_compactSpace f
  let := quasiSeparatedSpace_of_quasiSeparated f
  have := isCurve_fieldBaseChange_of_smooth B X f K
  have : Smooth (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))
      (‹Smooth f› : Smooth (Over.mk f).hom)
  exact one_le_genus_of_not_exists_iso_projectiveSpaceOver_one _ hP

/-- **`H^i(π₁(X_{k̄}, y), M) ⟶ H^i(X_{k̄}, ℱ_M)` is an isomorphism of δ-functors** for a
geometrically connected smooth curve `X` over `k` with `X_{k̄} ≇ 𝐏¹_{k̄}`, `k̄` an algebraic
closure of `k`, `Λ` a finite ring with `#Λ` invertible in `k`. -/
theorem isIso_geometricComparison_of_not_iso_projectiveLine
    (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : Stacks.Frobenius.fieldBaseChange (Over.mk f) K ≅
        projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    letI := QuasiCompact.compactSpace_of_compactSpace f
    letI := quasiSeparatedSpace_of_quasiSeparated f
    IsIso (geometricComparison B X Λ f K (contains_fieldBaseChange_of_isCurve B X f K) y) :=
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := QuasiCompact.compactSpace_of_compactSpace f
  let := quasiSeparatedSpace_of_quasiSeparated f
  isIso_geometricComparison_of_smoothCurve B X f K Λ
    (contains_fieldBaseChange_of_isCurve B X f K) y hΛ
    (one_le_genus_fieldBaseChange_of_not_iso B X f K hP)

/-- **`(M, ρ) ↦ H^i(X_{k̄}, ℱ_ρ)` is a universal δ-functor**, i.e. the right derived functors of
`(M, ρ) ↦ M^{π₁(X_{k̄}, η̄)}`, for a geometrically connected smooth curve `X` over `k` with
`X_{k̄} ≇ 𝐏¹_{k̄}`, `k̄` an algebraic closure of `k`, `Λ` a finite ring with `#Λ` invertible in
`k`. -/
theorem isUniversal_geometricRepresentationCohomology_of_not_iso_projectiveLine
    (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : Stacks.Frobenius.fieldBaseChange (Over.mk f) K ≅
        projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    (geometricRepresentationCohomology.{u, 0} B X
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
      Λ f K).IsUniversal :=
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := QuasiCompact.compactSpace_of_compactSpace f
  let := quasiSeparatedSpace_of_quasiSeparated f
  isUniversal_geometricRepresentationCohomology_of_smoothCurve B X f K Λ
    (contains_fieldBaseChange_of_isCurve B X f K) y hΛ
    (one_le_genus_fieldBaseChange_of_not_iso B X f K hP)

end AlgebraicGeometry

end
