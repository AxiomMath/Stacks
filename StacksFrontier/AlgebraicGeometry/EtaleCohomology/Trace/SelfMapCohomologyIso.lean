module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapDimensionZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistIsoTransferTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactTwistTrace

/-!
# The pullback action on `RΓ(S, Rf_*(f^{-1} C))` is invariant under isomorphisms of `C`

For an endomorphism `φ` of `Y` over `S` the action `φ^*` on `RΓ(S, Rf_*(f^{-1} C))`
(`Stacks.EtaleCohomology.selfMapCohomologyEndo`) is natural in the bounded below complex `C`; in
particular its trace, and the perfectness of the complex, only depend on `C` up to isomorphism.
The same holds for the trace of the identity of the complex of sections over `Spec Ω`. These
transfer Weil's formula (Step 9 of the proof of [Stacks, Tag 03UG]) between two models of the
constant sheaf.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_selfMapCohomologyEndo_eq_of_iso`,
  `Stacks.EtaleCohomology.isPerfect_selfMapCohomology_iff_of_iso`.
* `Stacks.EtaleCohomology.perfectDerivedTrace_id_baseSectionsComplex_eq_of_iso`,
  `Stacks.EtaleCohomology.isPerfect_baseSectionsComplex_iff_of_iso`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

section Generic

variable {A B : Type*} [Category* A] [Category* B] [HasZeroMorphisms A] [HasZeroMorphisms B]

/-- The twist of bounded below complexes induced by a natural transformation `F ⟶ F ⋙ P` is
natural. -/
lemma homMk_mapHomologicalComplex_app_naturality (F : A ⥤ B) (P : B ⥤ B)
    [F.PreservesZeroMorphisms] [P.PreservesZeroMorphisms] (θ : F ⟶ F ⋙ P)
    {K L : CochainComplex.Plus A} (e : K ⟶ L) :
    ObjectProperty.homMk (X := F.mapCochainComplexPlus.obj K)
        (Y := P.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj K))
        ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app K.obj) ≫
      P.mapCochainComplexPlus.map (F.mapCochainComplexPlus.map e) =
    F.mapCochainComplexPlus.map e ≫ ObjectProperty.homMk (X := F.mapCochainComplexPlus.obj L)
        (Y := P.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj L))
        ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app L.obj) := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ fun n => ?_)
  exact (θ.naturality (e.hom.f n)).symm

end Generic

section SelfMapIso

variable (Λ : Type) [CommRing Λ] {Y S : Scheme.{u}} (f : Y ⟶ S) (φ : Y ⟶ Y) (w : φ ≫ f = f)

/-- **The trace of `φ^*` on `RΓ(S, Rf_*(f^{-1} C))` is invariant under isomorphisms of `C`.** -/
theorem perfectDerivedTrace_selfMapCohomologyEndo_eq_of_iso
    {C₁ C₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ S)} (e : C₁ ≅ C₂)
    (h₁ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ f C₁)))
    (h₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ f C₂))) :
    perfectDerivedTrace Λ ⟨_, h₁⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} Λ f φ w C₁)) =
      perfectDerivedTrace Λ ⟨_, h₂⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} Λ f φ w C₂)) := by
  refine Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_iso.{0, u + 1, u + 2, u + 1}
    (etaleModuleDirectImage.{u, 0} Λ φ)
    (etaleModuleDirectImage.{u, 0} Λ f) (etaleModuleGlobalSections.{u, 0} Λ S)
    (selfMapDirectImageComp.{u, 0} Λ f φ w)
    ((etaleModuleInverseImage.{u, 0} Λ f).mapCochainComplexPlus.mapIso e)
    (selfMapComplexTwist.{u, 0} Λ f φ w C₁) (selfMapComplexTwist.{u, 0} Λ f φ w C₂)
    ?_ h₁ h₂
  exact homMk_mapHomologicalComplex_app_naturality _ _ (selfMapTwist.{u, 0} Λ f φ w) e.hom

/-- **Perfectness of `RΓ(S, Rf_*(f^{-1} C))` is invariant under isomorphisms of `C`.** -/
theorem isPerfect_selfMapCohomology_iff_of_iso
    {C₁ C₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ S)} (e : C₁ ≅ C₂) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
        (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ f C₁)) ↔
      StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
        (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ f C₂)) :=
  Functor.isPerfect_iff_of_iso (DerivedCategory.Plus.ι.mapIso
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ S).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ f).mapIso (DerivedCategory.Plus.Q.mapIso
        ((etaleModuleInverseImage.{u, 0} Λ f).mapCochainComplexPlus.mapIso e)))))

variable {Ω : Type u} [Field Ω]

/-- The complex of sections over `Spec Ω`, as a functor. -/
abbrev baseSectionsComplexFunctor :
    CochainComplex (EtaleModules.{u, 0} Λ (Spec (.of Ω))) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} Λ) ℤ :=
  (sheafToPresheaf _ (ModuleCat.{max (u + 1) 0} Λ) ⋙
    (CategoryTheory.evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{max (u + 1) 0} Λ)).obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The trace of the identity of the sections over `Spec Ω` is invariant under isomorphisms.** -/
theorem perfectDerivedTrace_id_baseSectionsComplex_eq_of_iso
    {C₁ C₂ : CochainComplex (EtaleModules.{u, 0} Λ (Spec (.of Ω))) ℤ} (e : C₁ ≅ C₂)
    (h₁ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex Λ C₁)))
    (h₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex Λ C₂))) :
    perfectDerivedTrace Λ ⟨_, h₁⟩ (𝟙 _) = perfectDerivedTrace Λ ⟨_, h₂⟩ (𝟙 _) :=
  perfectDerivedTrace_congr Λ ⟨_, h₁⟩ ⟨_, h₂⟩
    (DerivedCategory.Q.mapIso ((baseSectionsComplexFunctor Λ).mapIso e)) _ _ (by simp)

/-- **Perfectness of the sections over `Spec Ω` is invariant under isomorphisms.** -/
theorem isPerfect_baseSectionsComplex_iff_of_iso
    {C₁ C₂ : CochainComplex (EtaleModules.{u, 0} Λ (Spec (.of Ω))) ℤ} (e : C₁ ≅ C₂) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
        (DerivedCategory.Q.obj (baseSectionsComplex Λ C₁)) ↔
      StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
        (DerivedCategory.Q.obj (baseSectionsComplex Λ C₂)) :=
  Functor.isPerfect_iff_of_iso (DerivedCategory.Q.mapIso ((baseSectionsComplexFunctor Λ).mapIso e))

end SelfMapIso

end Stacks.EtaleCohomology
