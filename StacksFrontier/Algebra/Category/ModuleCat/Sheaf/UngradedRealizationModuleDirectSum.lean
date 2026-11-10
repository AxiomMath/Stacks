module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModule
public import StacksCore.Tactic.StacksAttribute

/-!
# The total module of a graded module is the sheafified direct sum of its pieces

Let `R` be a sheaf of rings on a site, `A` a graded algebra of presheaves of `R`-modules with
commutative homogeneous multiplication, and `M` a graded `A`-module. The total module
`Stacks.GradedModule.totalPresheafMod` has the objectwise direct sum `⨁ₙ Mₙ` as its sections,
and `SheafOfModules.GradedModule.ungradedSheaf` is its sheafification over the ungraded
realization of `A`. This file identifies the `R`-module underlying that sheafification with the
coproduct `∐ₙ Mₙ` of the homogeneous pieces, which is what makes the total module
quasi-coherent when the pieces are.

This is the module-side counterpart of
`Stacks.GradedAlgebra.directSumIsoUnderlyingModule` and
`Stacks.RelativeSpec.gradedCoprodIsoUnderlyingModule`, and it is the construction the base
change of [Stacks, Tag 0897] needs: with `X' = Spec_X(⨁ᵢ Aᵢ)` the relative spectrum of the
ungraded realization, [Stacks, Tag 01SB] turns a quasi-coherent module over `π_* 𝒪_{X'}` into a
quasi-coherent `𝒪_{X'}`-module, and the module over `π_* 𝒪_{X'}` that the graded module provides
is the total module.

## Main definitions

* `Stacks.GradedModule.directSumHom`: the comparison morphism from the objectwise direct sum of
  the homogeneous pieces to a sheaf of modules over a ring sheaf receiving the ungraded
  realization. It is the identity on sections; the content is that the two scalar actions agree,
  which is `Stacks.GradedModule.structureMap_smul`.
* `Stacks.GradedModule.directSumIsoRestrictScalars`: **the `R`-module underlying such a sheaf is
  the sheafification of the objectwise direct sum of the homogeneous pieces**, when the morphism
  out of the total module is locally bijective.

## Main results

* `Stacks.GradedModule.isLocallyInjective_toPresheaf_map_directSumHom` and
  `Stacks.GradedModule.isLocallySurjective_toPresheaf_map_directSumHom`: the comparison is
  locally bijective as soon as the morphism out of the total module is. Both are properties of
  the maps on sections alone, and the comparison has the same maps on sections.

## Implementation notes

The hypotheses are taken in the same shape as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum` for the algebra: local
injectivity and local surjectivity are explicit arguments rather than instances, because the
comparison morphism carries a compatibility proof and instance resolution does not solve the
resulting higher-order unification problem.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks

namespace GradedModule

section Comparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {ι : Type} [DecidableEq ι] [AddCommMonoid ι] {P : ι → PresheafOfModules.{w} R.obj}
  {A : GradedAlgebra P} [A.IsCommutative] {Q : ι → PresheafOfModules.{w} R.obj}
  (M : GradedModule A Q) {T : Sheaf J RingCat.{w}} (σ : R ⟶ T)
  (β : A.totalPresheaf ⟶ T.obj) (N : SheafOfModules.{w} T)
  (γ : M.totalPresheafMod ⟶
    (PresheafOfModules.restrictScalars β).obj ((SheafOfModules.forget T).obj N))

/-- The map on sections of a morphism out of the total module, with its target type written as
the sections of `N` rather than as a restriction of scalars. -/
noncomputable def totalSections (X : Cᵒᵖ) (m : M.Total X) : (N.val.obj X : Type w) :=
  (γ.app X).hom m

/-- The map on sections of a morphism out of the total module is additive. -/
lemma totalSections_add (X : Cᵒᵖ) (m m' : M.Total X) :
    M.totalSections β N γ X (m + m') =
      M.totalSections β N γ X m + M.totalSections β N γ X m' :=
  map_add (γ.app X).hom m m'

/-- A morphism out of the total module is semilinear over the base ring: the base ring acts on
the total module through the structure map of the ungraded realization. -/
lemma totalSections_smul (fac : A.structureHom ≫ β = σ.hom) (X : Cᵒᵖ) (r : R.obj.obj X)
    (m : M.Total X) :
    M.totalSections β N γ X (r • m) =
      (σ.hom.app X).hom r • M.totalSections β N γ X m := by
  have hr : (β.app X).hom (A.structureMap X r) = (σ.hom.app X).hom r :=
    congrArg (fun f : R.obj ⟶ T.obj => (f.app X).hom r) fac
  have hm : M.totalSections β N γ X (A.structureMap X r • m) =
      (β.app X).hom (A.structureMap X r) • M.totalSections β N γ X m :=
    (γ.app X).hom.map_smul (A.structureMap X r) m
  rw [← M.structureMap_smul r m, hm, hr]

/-- The map on sections of a morphism out of the total module commutes with restriction. -/
lemma totalSections_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.Total X) :
    M.totalSections β N γ Y (M.totalRestrict f m) =
      N.val.map f (M.totalSections β N γ X m) :=
  PresheafOfModules.naturality_apply γ f m

/-- **The comparison morphism from the objectwise direct sum of the homogeneous pieces of a
graded module to the module underlying a sheaf of modules over the ungraded realization.** It is
the identity on sections. -/
noncomputable def directSumHom (fac : A.structureHom ≫ β = σ.hom) :
    directSum Q ⟶ ((SheafOfModules.restrictScalars.{w} σ).obj N).val where
  app X := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (σ.hom.app X).hom).obj (N.val.obj X))
    { toFun := fun z => M.totalSections β N γ X z
      map_add' := fun z z' => M.totalSections_add β N γ X z z'
      map_smul' := fun r z => M.totalSections_smul σ β N γ fac X r z }
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    exact M.totalSections_naturality β N γ f z

/-- The comparison morphism is locally injective as soon as the morphism out of the total module
is. -/
lemma isLocallyInjective_toPresheaf_map_directSumHom (fac : A.structureHom ≫ β = σ.hom)
    (hγ : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf A.totalPresheaf).map γ)) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map (M.directSumHom σ β N γ fac)) :=
  have := hγ
  ⟨fun x y h =>
    Presheaf.equalizerSieve_mem J ((PresheafOfModules.toPresheaf A.totalPresheaf).map γ) x y h⟩

/-- The comparison morphism is locally surjective as soon as the morphism out of the total module
is. -/
lemma isLocallySurjective_toPresheaf_map_directSumHom (fac : A.structureHom ≫ β = σ.hom)
    (hγ : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf A.totalPresheaf).map γ)) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (M.directSumHom σ β N γ fac)) :=
  have := hγ
  ⟨fun s =>
    Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf A.totalPresheaf).map γ) s⟩

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The module underlying a sheaf of modules over the ungraded realization is the
sheafification of the objectwise direct sum of the homogeneous pieces**, as soon as the morphism
out of the total module is locally bijective. -/
noncomputable def directSumIsoRestrictScalars (fac : A.structureHom ≫ β = σ.hom)
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf A.totalPresheaf).map γ))
    (hsurj : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf A.totalPresheaf).map γ)) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj (directSum Q) ≅
      (SheafOfModules.restrictScalars.{w} σ).obj N :=
  sheafifyIsoOfLocallyBijective (M.directSumHom σ β N γ fac)
    (M.isLocallyInjective_toPresheaf_map_directSumHom σ β N γ fac hinj)
    (M.isLocallySurjective_toPresheaf_map_directSumHom σ β N γ fac hsurj)

end Comparison

end GradedModule

end Stacks

namespace SheafOfModules

open Stacks

section Ungraded

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A : GradedAlgebra.{w, w} R} [A.IsCommutative] (M : GradedModule.{w, w, w} A)

/-- The sheafification unit of the total module is locally injective: on presheaves of abelian
groups it *is* the sheafification unit. -/
lemma GradedModule.isLocallyInjective_toUngradedSheaf :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf A.toPresheafGradedAlgebra.totalPresheaf).map
        M.toUngradedSheaf) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J
    M.toPresheafGradedModule.totalPresheafMod.presheaf))

/-- The sheafification unit of the total module is locally surjective. -/
lemma GradedModule.isLocallySurjective_toUngradedSheaf :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf A.toPresheafGradedAlgebra.totalPresheaf).map
        M.toUngradedSheaf) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J
    M.toPresheafGradedModule.totalPresheafMod.presheaf))

omit [J.WEqualsLocallyBijective RingCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [A.IsCommutative] in
/-- The structure map of the ungraded realization factors the structure map of the ungraded
realization of the algebra through the sheafification unit. -/
theorem GradedModule.structureHom_comp_toTotalSheaf :
    A.toPresheafGradedAlgebra.structureHom ≫ A.toPresheafGradedAlgebra.toTotalSheaf J =
      A.ungradedStructureMap.hom :=
  rfl

/-- **The `R`-module underlying the total module `⨁ₙ Mₙ` of a graded module is the
sheafification of the objectwise direct sum of the homogeneous pieces.** -/
noncomputable def GradedModule.directSumIsoUngradedSheaf :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        (Stacks.directSum fun n : ℤ => (M.piece n).val) ≅
      (SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj M.ungradedSheaf :=
  M.toPresheafGradedModule.directSumIsoRestrictScalars A.ungradedStructureMap
    (A.toPresheafGradedAlgebra.toTotalSheaf J) M.ungradedSheaf M.toUngradedSheaf
    (GradedModule.structureHom_comp_toTotalSheaf (A := A) (J := J))
    (M.isLocallyInjective_toUngradedSheaf) (M.isLocallySurjective_toUngradedSheaf)

/-- The comparison morphism from the direct sum over the **nonnegative** degrees. -/
noncomputable def GradedModule.coprodDirectSumHom :
    (Stacks.directSum fun n : ℕ => (M.piece (n : ℤ)).val) ⟶
      ((SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj M.ungradedSheaf).val :=
  Stacks.directSumNatToInt (fun n : ℤ => (M.piece n).val) ≫
    M.toPresheafGradedModule.directSumHom A.ungradedStructureMap
      (A.toPresheafGradedAlgebra.toTotalSheaf J) M.ungradedSheaf M.toUngradedSheaf
      (GradedModule.structureHom_comp_toTotalSheaf (A := A) (J := J))

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through the sheafification and restriction-of-scalars API for sheaves of modules
/-- **The `R`-module underlying the total module of a graded module concentrated in nonnegative
degrees is the coproduct of its homogeneous pieces.** -/
noncomputable def GradedModule.coprodIsoUngradedSheaf
    (hzero : ∀ n : ℤ, n < 0 → Limits.IsZero (M.piece n)) :
    (∐ fun n : ℕ => M.piece (n : ℤ)) ≅
      (SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj M.ungradedSheaf :=
  (Stacks.sheafifyDirectSumIso (fun n : ℕ => M.piece (n : ℤ))).symm ≪≫
    Stacks.sheafifyIsoOfLocallyBijective (M.coprodDirectSumHom)
      (Stacks.isLocallyInjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallyInjective_directSumNatToInt _ _
          fun n hn U => Stacks.subsingleton_of_isZero (hzero n hn) U)
        (M.toPresheafGradedModule.isLocallyInjective_toPresheaf_map_directSumHom _ _ _ _ _
          (M.isLocallyInjective_toUngradedSheaf)))
      (Stacks.isLocallySurjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallySurjective_directSumNatToInt _ _
          fun n hn U => Stacks.subsingleton_of_isZero (hzero n hn) U)
        (M.toPresheafGradedModule.isLocallySurjective_toPresheaf_map_directSumHom _ _ _ _ _
          (M.isLocallySurjective_toUngradedSheaf)))

end Ungraded

end SheafOfModules

end
