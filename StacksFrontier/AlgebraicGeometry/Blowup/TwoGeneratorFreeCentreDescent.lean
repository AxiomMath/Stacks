module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorFreeNearCenter
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreeChartDescent

/-!
# The ordinary descent for the almost blowup square of Example 0EVH, free centre

A finite locally free module `𝒢` on the modification `X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))` of
[Stacks, Example 0EVH] whose restriction to the exceptional line is free of rank `r` comes from a
finite locally free module on the base `Spec A`, whose inverse image on the centre is free of
rank `r`.

This is the essential surjectivity half of [Stacks, Tag 0EXD] for that square in the case of a
free module on the centre, at the level of ordinary modules, not of
`AlgebraicGeometry.frobeniusColimitVectorBundles`.

All names are in the namespace `Stacks.AlmostBlowUp`.

## Main results

* `exists_opens_cover_center_isIso_restrict_hom_free`: an open `U` of the base containing the
  image of the centre, which together with the complement of the centre covers the base, and a
  map from the free module to `𝒢` that is an isomorphism on the exceptional line and over the
  preimage of `U`.
* `exists_modules_isFiniteLocallyFree_pullback_center_iso_free`: **the descent**, the statement
  above.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlmostBlowUp

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- **An open `U` containing the centre which, with the complement of the centre, covers the
base.** For `𝒢` finite locally free on the modification and free of rank `r` on the exceptional
line, there are such a `U` and a map `α` from the free module of rank `r` to `𝒢` which is an
isomorphism after pullback to the exceptional line and after restriction to the preimage of
`U`. -/
theorem exists_opens_cover_center_isIso_restrict_hom_free [IsNoetherianRing A] (r : ℕ)
    {G : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Modules}
    (hG : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (e : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).obj G ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r))) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ (U : (Spec (.of A)).Opens) (α : (_root_.SheafOfModules.free
        (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
        (ULift.{u} (Fin r))) ⟶ G),
      U ⊔ centerComplement A f₁ f₂ = ⊤ ∧
        Set.range (centerToBase A f₁ f₂).base ⊆ (U : Set _) ∧
          IsIso ((Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).map α) ∧
            IsIso ((Scheme.Modules.restrictFunctor
              (modificationToBase A f₁ f₂ ⁻¹ᵁ U).ι).map α) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have := isProper_modificationToBase A f₁ f₂
  obtain ⟨α, hαi, -, W, hWE, hαW⟩ := exists_hom_free_isIso_near_exceptional A f₁ f₂ r hG e
  obtain ⟨U, hUT, hUW⟩ := exists_opens_preimage_le_of_universallyClosed
    (modificationToBase A f₁ f₂) W
    (((centerIdealSheaf A f₁ f₂).support : Set (Spec (.of A))) ∪
      Set.range (centerToBase A f₁ f₂).base)
    (fun x' hx' => hWE (by
      rcases hx' with hx' | hx'
      · rwa [range_exceptionalToModification_eq_preimage_support A f₁ f₂]
      · rwa [range_eq_preimage_range_of_isPullback (twoGenerator_isPullback A f₁ f₂)]))
  refine ⟨U, α, ?_, fun x hx => hUT (Or.inr hx), hαi,
    isIso_restrictFunctor_map_of_le hUW α hαW⟩
  refine top_le_iff.mp fun x _ => ?_
  by_cases hx : x ∈ ((centerIdealSheaf A f₁ f₂).support : Set (Spec (.of A)))
  · exact Or.inl (hUT (Or.inl hx))
  · exact Or.inr hx

/-- **A finite locally free module on the modification of [Stacks, Example 0EVH] whose
restriction to the exceptional line is free of rank `r` comes from a finite locally free module
on the base, whose inverse image on the centre is free of rank `r`.**

This is the essential surjectivity half of [Stacks, Tag 0EXD] for that square with a free module
on the centre, at the level of ordinary modules.  The module on the base is also free of rank `r`
on an open `U` which, with the complement of the centre, covers the base. -/
theorem exists_modules_isFiniteLocallyFree_pullback_center_iso_free [IsNoetherianRing A] (r : ℕ)
    {G : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Modules}
    (hG : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (e : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).obj G ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r))) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ (N : (Spec (.of A)).Modules) (U : (Spec (.of A)).Opens),
      Scheme.Modules.IsFiniteLocallyFree N ∧
        U ⊔ centerComplement A f₁ f₂ = ⊤ ∧
          Nonempty (Scheme.Modules.restrict N U.ι ≅
            _root_.SheafOfModules.free (ULift.{u} (Fin r))) ∧
            Nonempty ((Scheme.Modules.pullback (centerToBase A f₁ f₂)).obj N ≅
              _root_.SheafOfModules.free (ULift.{u} (Fin r))) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  obtain ⟨U, α, hcov, hZU, -, hαU⟩ :=
    exists_opens_cover_center_isIso_restrict_hom_free A f₁ f₂ r hG e
  have := isIso_modificationToBase_restrict_centerComplement A f₁ f₂
  have hGflf : Scheme.Modules.IsFiniteLocallyFree G :=
    (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators G).mpr hG
  obtain ⟨N, hN, ⟨eU⟩, -⟩ :=
    exists_isFiniteLocallyFree_restrict_iso_of_isIso_restrict_free
      (modificationToBase A f₁ f₂) α hcov hGflf hαU
  exact ⟨N, U, hN, hcov, ⟨eU⟩,
    nonempty_pullback_iso_free_of_range_subset (centerToBase A f₁ f₂) U hZU eU⟩

end Stacks.AlmostBlowUp

end
