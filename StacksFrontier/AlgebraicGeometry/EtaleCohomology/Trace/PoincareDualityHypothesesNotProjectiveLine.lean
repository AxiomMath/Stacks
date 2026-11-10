module

public import
 StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGroupHomologyNotProjectiveLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationEffaceable

/-!
# The effacement inputs of the derived Poincaré duality of Tag 03VM, for `X_k̄ ≇ ℙ¹`

Under the hypotheses of Tag 03VM (`X` a smooth geometrically connected curve over `k`, `K` an
algebraic closure, `#Λ` invertible in `k`, `X_K ≇ ℙ¹_K`):

* `ρ ↦ Hⁱ(X_K, ℱ_ρ)` is elementwise effaceable
  (`elementwiseEffaceable_geometricRepresentationCohomology_of_not_iso_projectiveLine`):
  `X_K` is affine, or proper of genus `≥ 1`;
* `ρ ↦ H_c^{2-i}(X_K, ℱ_ρ)` is coeffaceable
  (`coeffaceable_compactSupportRepresentationHomology_of_not_iso_projectiveLine`).

These are the hypotheses `hEff` (over `Λᵐᵒᵖ`) and `hcoeff` of
`AlgebraicGeometry.galoisCompactSupportPoincareDualityNatIso`.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology
  Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] (Λ : Type) [Ring Λ] [Finite Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) K)) (j : CompactificationOf (Over.mk f))
  (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
  (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
    e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
      pullback.snd (Over.mk f).hom (specAlgebraMap k K))

include hΛ hP in
/-- **`ρ ↦ Hⁱ(X_K, ℱ_ρ)` is elementwise effaceable when `X_K ≇ ℙ¹_K`**: `X_K` is affine, or
proper, and then of genus `≥ 1`. -/
theorem elementwiseEffaceable_geometricRepresentationCohomology_of_not_iso_projectiveLine :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    (geometricRepresentationCohomology.{u, 0} B X
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
      Λ f K).ElementwiseEffaceable := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := QuasiCompact.compactSpace_of_compactSpace f
  let := quasiSeparatedSpace_of_quasiSeparated f
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have hcurve : IsCurve k f := inferInstance
  have := isCurve_fieldBaseChange_of_smooth B X f K
  rcases isAffine_or_isProjectiveMorphism K
      (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) with h | h
  · have : IsAffine (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) := h
    exact elementwiseEffaceable_geometricRepresentationCohomology_of_isAffine B X _ Λ f K hcurve
  · have : IsProper (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :=
      isProper_of_isProjectiveMorphism _ h
    have : Smooth (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :=
      MorphismProperty.of_isPullback (P := @Smooth)
        (IsPullback.of_hasPullback (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))
        (‹Smooth f› : Smooth (Over.mk f).hom)
    exact elementwiseEffaceable_geometricRepresentationCohomology_of_genus B X _ Λ f K hcurve
      (contains_fieldBaseChange_of_isCurve B X f K)
      (one_le_genus_fieldBaseChange_of_not_iso B X f K hP inferInstance)
      (by simpa using hΛ.map (algebraMap k K))

include hΛ hP in
/-- **`(M, ρ) ↦ H_c^{2-i}(X_K, ℱ_ρ)` is coeffaceable when `X_K ≇ ℙ¹_K`.** -/
theorem coeffaceable_compactSupportRepresentationHomology_of_not_iso_projectiveLine :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    (compactSupportRepresentationHomology B X
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
      Λ f j K).Coeffaceable := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := QuasiCompact.compactSpace_of_compactSpace f
  let := quasiSeparatedSpace_of_quasiSeparated f
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  let : Fintype Λ := Fintype.ofFinite Λ
  have hn := isUnit_card_fieldBaseChange K Λ hΛ
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  exact coeffaceable_compactSupportRepresentationHomology B X f K Λ y j hn hζ
    (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λ y hΛ hP)
    (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λᵐᵒᵖ y
      (isUnit_natCard_mulOpposite Λ hΛ) hP)

end AlgebraicGeometry

end
