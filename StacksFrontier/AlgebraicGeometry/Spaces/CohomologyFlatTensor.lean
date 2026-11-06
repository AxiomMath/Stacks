module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import StacksFrontier.Algebra.Category.ModuleCat.FlatTensorComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleCohomologyAbelianComparison
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Cohomology of an algebraic space commutes with flat tensor products

Let `X` be an algebraic space, `A` a ring acting on `𝒪_X` through a ring map
`φ : A ⟶ Γ(X, 𝒪_X)`, and `ℱ` an `𝒪_X`-module.  For an `A`-module `N` let `ℱ ⊗_A N` be the
abelian sheaf on the small étale site of `X` associated to `U ↦ ℱ(U) ⊗_A N`.  If `X` is
quasi-compact and quasi-separated and `N` is flat, then

`N ⊗_A H^p(X, ℱ) ≅ H^p(X, ℱ ⊗_A N)`.

This is the step of the proof of [Stacks, Tag 073K] in which `B` is written as a filtered
colimit of finite free `A`-modules: `N ↦ H^p(X, ℱ ⊗_A N)` is additive and commutes with
filtered colimits — the sheaf `ℱ ⊗_A N` does, and cohomology on a quasi-compact and
quasi-separated algebraic space does ([Stacks, Tag 073E]) — so
`CategoryTheory.Functor.bijective_tensorUnitComparison_of_flat` applies.

## Main definitions

* `AlgebraicGeometry.Space.moduleSectionsOverRing`: the sections of `ℱ` as a presheaf of
  `A`-modules.
* `AlgebraicGeometry.Space.sectionsTensorSheaf`: the functor `N ↦ ℱ ⊗_A N`, with sections raised
  to the universe `u + 1`.
* `AlgebraicGeometry.Space.sectionsTensorSheafUnitIso`: `ℱ ⊗_A A ≅ ℱ`.

## Main results

* `AlgebraicGeometry.Space.bijective_tensorUnitComparison_cohomologySectionsTensor`: the
  comparison `N ⊗_A H^p(X, ℱ ⊗_A A) ⟶ H^p(X, ℱ ⊗_A N)` is bijective for flat `N`.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {A : Type*} [Category A]
  [HasWeakSheafify J A]

/-- The sheafification of a morphism of presheaves into a sheaf, `α ↦ α^# ≫ ε`, is compatible
with endomorphisms: if `w ≫ α' = α ≫ g` on presheaves, then `w^# ≫ (α'^# ≫ ε) = (α^# ≫ ε) ≫ g`
on sheaves. -/
theorem presheafToSheaf_map_comp_counit_of_comp_eq {P P' : Cᵒᵖ ⥤ A} {G G' : Sheaf J A}
    (α : P ⟶ G.obj) (α' : P' ⟶ G'.obj) (w : P ⟶ P') (g : G ⟶ G') (h : w ≫ α' = α ≫ g.hom) :
    (presheafToSheaf J A).map w ≫ (presheafToSheaf J A).map α' ≫
        (sheafificationAdjunction J A).counit.app G' =
      ((presheafToSheaf J A).map α ≫ (sheafificationAdjunction J A).counit.app G) ≫ g := by
  have hn : (presheafToSheaf J A).map g.hom ≫ (sheafificationAdjunction J A).counit.app G' =
      (sheafificationAdjunction J A).counit.app G ≫ g :=
    (sheafificationAdjunction J A).counit.naturality g
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc, hn, Category.assoc]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {A : Type u} [CommRing A]
  (φ : A →+* RingCat.sectionsSubring
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)

include φ

/-- The ring map `A ⟶ 𝒪_X(U)` obtained by restricting the global functions `φ(a)` to an étale
chart `U`. -/
abbrev chartRingHomOfGlobal (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    A →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U :=
  (globalSectionEval _ U).comp φ

/-- The sections of an `𝒪_X`-module `ℱ`, as a presheaf of `A`-modules through `φ`. -/
def moduleSectionsOverRing (F : Modules.{u, u} B S hS X.1 X.2) :
    (SmallEtale B S hS X.1)ᵒᵖ ⥤ ModuleCat.{u} A where
  obj U := (ModuleCat.restrictScalars (chartRingHomOfGlobal B S hS X φ U)).obj (F.val.obj U)
  map {U V} f := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (chartRingHomOfGlobal B S hS X φ U)).obj (F.val.obj U))
    (Y := (ModuleCat.restrictScalars (chartRingHomOfGlobal B S hS X φ V)).obj (F.val.obj V))
    { toFun := fun x => (F.val.map f).hom x
      map_add' := fun x y => (F.val.map f).hom.map_add x y
      map_smul' := fun a x =>
        (F.val.map_smul f ((φ a).1 U) x).trans
          (congrArg (· • (F.val.map f).hom x) ((φ a).2 f)) }
  map_id U := ModuleCat.hom_ext (LinearMap.ext fun x =>
    congrArg (fun g => g.hom x) (F.val.map_id U))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun x =>
    congrArg (fun h => h.hom x) (F.val.map_comp f g))

/-- **The abelian sheaf `ℱ ⊗_A N`**, functorially in the `A`-module `N`: the sheafification of
`U ↦ ℱ(U) ⊗_A N`, with sections raised to the universe `u + 1`. -/
def sectionsTensorSheaf (F : Modules.{u, u} B S hS X.1 X.2) :
    ModuleCat.{u} A ⥤ Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  tensoringRight (ModuleCat.{u} A) ⋙
    (Functor.whiskeringLeft _ _ _).obj (moduleSectionsOverRing B S hS X φ F) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) ⋙
    presheafToSheaf _ _

/-- `ℱ ⊗_A N` commutes with colimits in `N` indexed by a category in the universe `u`. -/
theorem sectionsTensorSheaf_preservesColimitsOfShape (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Type u) [SmallCategory K] :
    PreservesColimitsOfShape K (sectionsTensorSheaf B S hS X φ F) := by
  have h1 : PreservesColimitsOfShape K (tensoringRight (ModuleCat.{u} A)) :=
    preservesColimitsOfShape_of_evaluation _ _ fun M =>
      preservesColimitsOfShape_of_natIso (Iso.refl (tensorLeft M))
  have h4 : PreservesColimitsOfShape K
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
    inferInstance
  unfold sectionsTensorSheaf
  infer_instance

/-- `ℱ ⊗_A N` is additive in `N`. -/
instance sectionsTensorSheaf_additive (F : Modules.{u, u} B S hS X.1 X.2) :
    (sectionsTensorSheaf B S hS X φ F).Additive := by
  have : (tensoringRight (ModuleCat.{u} A)).Additive :=
    ⟨fun {N N' f g} => by
      ext M : 2
      exact MonoidalPreadditive.whiskerLeft_add (C := ModuleCat.{u} A) (X := M) (f := f) (g := g)⟩
  unfold sectionsTensorSheaf
  infer_instance

/-- **`ℱ ⊗_A A ≅ ℱ`**: tensoring with `A` itself recovers the underlying abelian sheaf of `ℱ`,
with its sections raised to `u + 1`. -/
def sectionsTensorSheafUnitIso (F : Modules.{u, u} B S hS X.1 X.2) :
    (sectionsTensorSheaf B S hS X φ F).obj (ModuleCat.of A A) ≅
      (moduleToAbelianSheaf B S hS X).obj F :=
  (presheafToSheaf _ _).mapIso
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft (moduleSectionsOverRing B S hS X φ F)
      (rightUnitorNatIso (ModuleCat.{u} A)))
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) ≪≫
    NatIso.ofComponents (F := moduleSectionsOverRing B S hS X φ F ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})
      (G := ((moduleToAbelianSheaf B S hS X).obj F).obj) (fun _ => Iso.refl _)
      (fun _ => rfl)) ≪≫
    asIso ((sheafificationAdjunction (SmallEtale.topology B S hS X.1)
      AddCommGrpCat.{u + 1}).counit.app ((moduleToAbelianSheaf B S hS X).obj F))

set_option maxHeartbeats 1600000 in
/-- The functor `N ↦ H^p(X, ℱ ⊗_A N)` is additive. -/
instance cohomologySectionsTensor_additive (F : Modules.{u, u} B S hS X.1 X.2) (p : ℕ) :
    (sectionsTensorSheaf B S hS X φ F ⋙
      (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).rightDerived p).Additive :=
  have : (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).Additive :=
    smallEtaleGamma_additive B S hS X.1
  have : ((Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).rightDerived
      p).Additive :=
    (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
      (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})).additive p
  Functor.instAdditiveComp _ _

/-- The functor `N ↦ H^p(X, ℱ ⊗_A N)` from `A`-modules to abelian groups. -/
abbrev cohomologySectionsTensor (F : Modules.{u, u} B S hS X.1 X.2) (p : ℕ) :
    ModuleCat.{u} A ⥤ AddCommGrpCat.{u + 1} :=
  sectionsTensorSheaf B S hS X φ F ⋙
    (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).rightDerived p

/-- On a quasi-compact and quasi-separated algebraic space, `N ↦ H^p(X, ℱ ⊗_A N)` commutes with
filtered colimits: `ℱ ⊗_A N` does, and so does cohomology ([Stacks, Tag 073E]). -/
theorem preservesFilteredColimits_cohomologySectionsTensor (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (p : ℕ) :
    PreservesFilteredColimitsOfSize.{u, u} (cohomologySectionsTensor B S hS X φ F p) := by
  refine ⟨fun K _ _ => ?_⟩
  have := sectionsTensorSheaf_preservesColimitsOfShape B S hS X φ F K
  have : PreservesColimitsOfShape K
      ((Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).rightDerived p) :=
    ⟨fun {D} => by
      have := isIso_colimit_post_rightDerived_globalSections B S hS hZ X.1 X.2 hqc hqs p D
      exact preservesColimit_of_isIso_post _ _⟩
  exact comp_preservesColimitsOfShape _ _

/-- **Cohomology of a quasi-compact and quasi-separated algebraic space commutes with flat
tensor products**: for a flat `A`-module `N` the comparison
`N ⊗_A H^p(X, ℱ ⊗_A A) ⟶ H^p(X, ℱ ⊗_A N)` is bijective.  Here `A` acts on `H^p(X, ℱ ⊗_A A)` by
functoriality, and `ℱ ⊗_A A` is `ℱ` (`sectionsTensorSheafUnitIso`). -/
theorem bijective_tensorUnitComparison_cohomologySectionsTensor
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (p : ℕ) (N : ModuleCat.{u} A) [Module.Flat A N] :
    letI := Functor.unitObjModule.{u + 1, u} (cohomologySectionsTensor B S hS X φ F p)
    Function.Bijective (Functor.tensorUnitComparison.{u + 1, u}
      (cohomologySectionsTensor B S hS X φ F p)
      (fun a x => (Functor.unitObjModule_smul.{u + 1, u} _ a x).symm) N) := by
  have := preservesFilteredColimits_cohomologySectionsTensor B S hS X φ hZ hqc hqs F p
  let := Functor.unitObjModule.{u + 1, u} (cohomologySectionsTensor B S hS X φ F p)
  exact Functor.bijective_tensorUnitComparison_of_flat.{u + 1, u} _ _ N

end AlgebraicGeometry.Space
