module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RestrictScalarsConverse

/-!
# Restriction of scalars between the derived-complete subcategories

Let `𝒞` be a site, let `α : 𝒪 ⟶ 𝒪'` be a homomorphism of sheaves of commutative rings and let
`ℐ ⊂ 𝒪` be a sheaf of ideals. By [Stacks, Tag 099C] — in this library
`Stacks.SheafOfModules.DerivedRestrictScalars.isDerivedComplete_restrictScalars_iff` — a complex
of `𝒪'`-modules is derived complete along `ℐ𝒪'` exactly when its restriction of scalars is
derived complete along `ℐ`. In particular restriction of scalars carries
`D_comp(𝒪', ℐ𝒪')` into `D_comp(𝒪, ℐ)`, so the functor `D(𝒪') ⟶ D(𝒪)` lifts to the two full
subcategories. This file constructs that lift.

[Stacks, Tag 099I] asserts that the lift is an *equivalence* when `𝒪 ⟶ 𝒪'` is flat, `ℐ` is of
finite type and `𝒪/ℐ ≅ 𝒪'/ℐ𝒪'`. That is proved in `RestrictScalarsFlatEquivalence.lean`, as
`Stacks.SheafOfModules.DerivedRestrictScalars.isEquivalence_derivedCompleteRestrictScalars`;
this file only constructs the functor.

## Main definitions

* `Stacks.SheafOfModules.DerivedRestrictScalars.derivedCompleteRestrictScalars`: restriction of
  scalars as a functor `D_comp(𝒪', ℐ𝒪') ⥤ D_comp(𝒪, ℐ)`.

## Main results

* `Stacks.SheafOfModules.DerivedRestrictScalars.derivedCompleteRestrictScalars_comp_ι`: composing
  the lift with the inclusion of `D_comp(𝒪, ℐ)` recovers restriction of scalars on the derived
  categories.

## Implementation notes

The object part of the lift is the hypothesis-free direction of
`isDerivedComplete_restrictScalars_iff`; no finite-type assumption on `ℐ`, no flatness and no
agreement of the structure sheaves modulo `ℐ` is needed to form the functor. Those three enter
only in the assertion that it is an equivalence.

`AlgebraicGeometry.RingedSite.IsDerivedComplete X I` is already a predicate on
`DerivedCategory (SheafOfModules (ringSheaf X))`, hence an `ObjectProperty`, so the two full
subcategories are its `ObjectProperty.FullSubcategory` and the lift is `ObjectProperty.lift`.

As in `RestrictScalars.lean` and `RestrictScalarsConverse.lean`, the statements are for a site
`𝒞 : Type u` with `Category.{u} 𝒞` and sheaves of modules in universe `u`, that is for
`RingedSite.{u, u, u}`, because that is where `isDerivedComplete_restrictScalars_iff` lives.

## References

* [Stacks Project, Tag 099I](https://stacks.math.columbia.edu/tag/099I)
* [Stacks Project, Tag 099C](https://stacks.math.columbia.edu/tag/099C)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SheafOfModules.DerivedRestrictScalars

open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O O' : Sheaf J CommRingCat.{u}}

/-- **The functor of [Stacks, Tag 099I].** For a homomorphism `α : 𝒪 ⟶ 𝒪'` of sheaves of
commutative rings on a site and a sheaf of ideals `ℐ ⊂ 𝒪`, restriction of scalars
`D(𝒪') ⟶ D(𝒪)` carries the derived-complete complexes along `ℐ𝒪'` to the derived-complete
complexes along `ℐ`, by [Stacks, Tag 099C]
(`isDerivedComplete_restrictScalars_iff`), and so lifts to a functor
`D_comp(𝒪', ℐ𝒪') ⥤ D_comp(𝒪, ℐ)`.

Tag 099I asserts that this functor is an equivalence when `𝒪 ⟶ 𝒪'` is flat, `ℐ` is of finite
type and `𝒪/ℐ ≅ 𝒪'/ℐ𝒪'`; none of those hypotheses is needed to construct it. The equivalence is
`isEquivalence_derivedCompleteRestrictScalars` of `RestrictScalarsFlatEquivalence.lean`, which
carries the tag. -/
def derivedCompleteRestrictScalars (α : O ⟶ O')
    (I : _root_.SheafOfModules.Submodule
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O)))) :
    ObjectProperty.FullSubcategory
        (RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O')
          (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I)) ⥤
      ObjectProperty.FullSubcategory
        (RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O) I) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙
      (_root_.SheafOfModules.restrictScalars.{u}
        (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory)
    fun K ↦ (isDerivedComplete_restrictScalars_iff α I K.obj).mpr K.property

/-- The lift of [Stacks, Tag 099I] is restriction of scalars: composing it with the inclusion of
`D_comp(𝒪, ℐ)` into `D(𝒪)` gives the inclusion of `D_comp(𝒪', ℐ𝒪')` followed by restriction of
scalars on the derived categories. -/
theorem derivedCompleteRestrictScalars_comp_ι (α : O ⟶ O')
    (I : _root_.SheafOfModules.Submodule
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O)))) :
    derivedCompleteRestrictScalars α I ⋙
        ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O) I) =
      ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O')
          (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I)) ⋙
        (_root_.SheafOfModules.restrictScalars.{u}
          (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory :=
  rfl

/-- The underlying complex of the image of `K` under `derivedCompleteRestrictScalars α I` is the
restriction of scalars of the complex underlying `K`. -/
@[simp]
theorem derivedCompleteRestrictScalars_obj_obj (α : O ⟶ O')
    (I : _root_.SheafOfModules.Submodule
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))))
    (K : ObjectProperty.FullSubcategory
      (RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O')
        (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I))) :
    ((derivedCompleteRestrictScalars α I).obj K).obj =
      (_root_.SheafOfModules.restrictScalars.{u}
        (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj K.obj :=
  rfl

/-- The underlying morphism of the image of `g` under `derivedCompleteRestrictScalars α I` is the
restriction of scalars of the morphism underlying `g`. -/
@[simp]
theorem derivedCompleteRestrictScalars_map_hom (α : O ⟶ O')
    (I : _root_.SheafOfModules.Submodule
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))))
    {K L : ObjectProperty.FullSubcategory
      (RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O')
        (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I))} (g : K ⟶ L) :
    ((derivedCompleteRestrictScalars α I).map g).hom =
      (_root_.SheafOfModules.restrictScalars.{u}
        (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.map g.hom :=
  rfl

end Stacks.SheafOfModules.DerivedRestrictScalars

end
