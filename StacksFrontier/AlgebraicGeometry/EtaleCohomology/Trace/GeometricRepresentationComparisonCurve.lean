module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationComparisonIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeGeometry
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.AffineOrProjective
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.EtaleLocalStructure
public import StacksFrontier.AlgebraicGeometry.Picard.BaseChangeCurveTorsionFinite

/-!
# `H^i(π₁(X_{k̄}), M) ≅ H^i(X_{k̄}, ℱ_M)` for a smooth geometrically connected curve

Let `X` be a smooth geometrically connected curve over a field `k`, `K` an algebraic closure of
`k`, and `Λ` a finite ring with `#Λ` invertible in `k`. By Tag 0A27 the curve `X_K` is affine or
projective. If it is projective, assume it has genus at least one (the case `X_K ≅ 𝐏¹_K`, which
is the case of genus zero, is the exclusion in Tag 03VM). Then the comparison morphism
`H^i(π₁(X_K), M) ⟶ H^i(X_K, ℱ_M)` of δ-functors on finite `Λ`-modules with continuous
`π₁(X)`-action is an isomorphism, and `M ↦ H^i(X_K, ℱ_M)` is a universal δ-functor: the right
derived functors of `M ↦ M^{π₁(X_K)}`.

## Main results

* `AlgebraicGeometry.isIso_geometricComparison_of_smoothCurve`
* `AlgebraicGeometry.isUniversal_geometricRepresentationCohomology_of_smoothCurve`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] (Λ : Type) [Ring Λ] [Finite Λ]
  [ConnectedSpace X.1] [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
  [CompactSpace X.1] [QuasiSeparatedSpace X.1]
  (hK : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
  (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))

include f in
omit [IsAlgClosure k K] [ConnectedSpace X.1]
  [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)] [CompactSpace X.1]
  [QuasiSeparatedSpace X.1] in
/-- `X_K` is a curve over `K`: `X` is smooth and geometrically connected, hence geometrically
irreducible. -/
theorem isCurve_fieldBaseChange_of_smooth :
    IsCurve K (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) := by
  have : Smooth (Over.mk f).hom := ‹Smooth f›
  have : IsCurve k (Over.mk f).hom := ‹IsCurve k f›
  have : GeometricallyIrreducible (Over.mk f).hom :=
    geometricallyIrreducible_of_geometricallyConnected_of_smooth (Over.mk f).hom
      ‹GeometricallyConnected f›
  exact Stacks.Picard.isCurve_baseChange_of_geometricallyIrreducible (Over.mk f) K

/-- **`H^i(π₁(X_K), M) ⟶ H^i(X_K, ℱ_M)` is an isomorphism of δ-functors** for a smooth
geometrically connected curve `X` over `k` whose base change `X_K` to an algebraic closure is
either affine or of genus at least one, `#Λ` invertible in `k`. -/
theorem isIso_geometricComparison_of_smoothCurve (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hg : IsProper (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) →
      1 ≤ genus (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))) :
    IsIso (geometricComparison B X Λ f K hK y) := by
  have hΛK : IsUnit ((Nat.card Λ : ℕ) : K) := by
    simpa using hΛ.map (algebraMap k K)
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have hcurve : IsCurve k f := inferInstance
  have := isCurve_fieldBaseChange_of_smooth B X f K
  rcases isAffine_or_isProjectiveMorphism K
      (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) with h | h
  · have : IsAffine (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) := h
    rw [← geometricComparisonIsoOfIsAffine_hom B X Λ f K hK y hcurve]
    infer_instance
  · have : IsProper (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :=
      isProper_of_isProjectiveMorphism _ h
    have : Smooth (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :=
      MorphismProperty.of_isPullback (P := @Smooth)
        (IsPullback.of_hasPullback (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))
        (‹Smooth f› : Smooth (Over.mk f).hom)
    rw [← geometricComparisonIsoOfGenus_hom B X Λ f K hK y hcurve (hg inferInstance) hΛK]
    infer_instance

/-- **`M ↦ H^i(X_K, ℱ_M)` is a universal δ-functor**, i.e. the right derived functors of
`M ↦ M^{π₁(X_K)}`, under the hypotheses of
`AlgebraicGeometry.isIso_geometricComparison_of_smoothCurve`. -/
theorem isUniversal_geometricRepresentationCohomology_of_smoothCurve
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hg : IsProper (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) →
      1 ≤ genus (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))) :
    (geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
      Λ f K).IsUniversal := by
  have := isUniversal_geometricGroupCohomology B X Λ f K hK y
  have := isIso_geometricComparison_of_smoothCurve B X f K Λ hK y hΛ hg
  exact DeltaFunctor.IsUniversal.of_iso (asIso (geometricComparison B X Λ f K hK y))

end AlgebraicGeometry

end
