module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.EpiGlue
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts

/-!
# The projective bundle of an invertible module is the base

Let `X` be a scheme and `F` an invertible quasi-coherent `𝒪_X`-module. Then the projection
`π : 𝐏(F) ⟶ X` is an isomorphism. By the universal property over the base (Stacks 01O4,
`Stacks.RelativeProj.isUniversalOver_tautologicalDatum`), the identity `F ⟶ F` is an invertible
quotient of `F` and classifies a section `s` of `π`; and `π ≫ s = 𝟙` because any two invertible
quotients of the invertible module `π^*F` are equivalent, a surjection between invertible
modules being an isomorphism.

## Main results

* `Stacks.RelativeProj.isIso_projectiveBundleToBase_of_isInvertible`: **`𝐏(F) ⟶ X` is an
  isomorphism for `F` invertible.**

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

open Stacks.Divisors

/-- **Two invertible quotients of an invertible module are equivalent**: both quotient maps are
surjections between invertible modules, hence isomorphisms. -/
theorem invertibleQuotient_isEquivalent_of_isInvertible {T : Scheme.{u}} {M : T.Modules}
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 M)
    (Q R : InvertibleQuotient T M) : Q.IsEquivalent R := by
  have := Q.epi
  have := R.epi
  have := Stacks.Chow.GenuineChern.isIso_of_epi_of_isInvertible Q.q hM Q.invertible
  have := Stacks.Chow.GenuineChern.isIso_of_epi_of_isInvertible R.q hM R.invertible
  exact ⟨(asIso Q.q).symm ≪≫ asIso R.q, by simp⟩

/-- **The projective bundle of an invertible module is the base**: `𝐏(F) ⟶ X` is an
isomorphism, with inverse the section classified by the invertible quotient `𝟙 : F ⟶ F`. -/
theorem isIso_projectiveBundleToBase_of_isInvertible {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F) :
    IsIso (projectiveBundleToBase X F) := by
  obtain ⟨s, hs⟩ := (tautologicalDatum F).classifyingMorphismOver F
    ((Scheme.Modules.pullbackId X).app F).symm ⟨F, hF, 𝟙 F, inferInstance⟩
  have hπ : AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveBundle X F).presheaf
      (projectiveBundle X F).ringCatSheaf.2
      ((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj F) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (@Stacks.Modules.isInvertible_pullback _ _ (projectiveBundleToBase X F) F
        ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hF))
  exact ⟨s, (tautologicalDatum F).eq_of_overQuotient_isEquivalent
    ((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj F) (Iso.refl _)
    (projectiveBundleToBase X F ≫ s) (𝟙 _) (by rw [Category.assoc, hs, Category.comp_id])
    (Category.id_comp _) (invertibleQuotient_isEquivalent_of_isInvertible hπ _ _), hs⟩

end Stacks.RelativeProj

end
