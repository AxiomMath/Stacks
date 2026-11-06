module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # Right-derivedness on `D⁺` is absolute

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories with `𝒜` having enough
injectives, and let `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` be its right derived functor
`CategoryTheory.Functor.rightDerivedFunctorPlus`, with unit
`CategoryTheory.Functor.rightDerivedFunctorPlusUnith`. This file shows that for an arbitrary
functor `G : D⁺(ℬ) ⥤ ℋ` the composite `RF ⋙ G` is the right derived functor of
`K⁺(𝒜) ⥤ ℋ` along the localization `Qh : K⁺(𝒜) ⥤ D⁺(𝒜)` at the quasi-isomorphisms, with the
unit of `RF` whiskered by `G` as its unit.

## Main definitions

* `Stacks.DerivedIndexing.rightDerivedFunctorPlusCompUnit`: the unit of `RF ⋙ G`, namely the
  unit of `RF` whiskered on the right by `G`.

## Main results

* `Stacks.DerivedIndexing.isRightDerivedFunctor_rightDerivedFunctorPlus_comp`: for every functor
  `G : D⁺(ℬ) ⥤ ℋ`, the composite `RF ⋙ G` is the right derived functor of `F∗ ⋙ Qh ⋙ G` with
  respect to the quasi-isomorphisms of `K⁺(𝒜)`, with the whiskered unit.
* `Stacks.DerivedIndexing.rightDerivedFunctorPlusCompUnit_app`: the whiskered unit at an
  object `K` of `K⁺(𝒜)` is `G.map` of the unit of `RF` at `K`.
-/

@[expose] public section

universe w w' v v' v'' u u' u''

open CategoryTheory Limits

namespace Stacks.DerivedIndexing

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
  {H : Type u''} [Category.{v''} H]

/-- The unit of `RF ⋙ G`: the unit `CategoryTheory.Functor.rightDerivedFunctorPlusUnith` of
`RF = CategoryTheory.Functor.rightDerivedFunctorPlus`, whiskered on the right by `G`. -/
noncomputable def rightDerivedFunctorPlusCompUnit (G : DerivedCategory.Plus D ⥤ H) :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ G ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙ G :=
  Functor.whiskerRight F.rightDerivedFunctorPlusUnith G

/-- At `K : K⁺(𝒜)`, the unit of `RF ⋙ G` is `G.map` of the unit of `RF` at `K`. -/
theorem rightDerivedFunctorPlusCompUnit_app (G : DerivedCategory.Plus D ⥤ H)
    (K : HomotopyCategory.Plus C) :
    (rightDerivedFunctorPlusCompUnit F G).app K =
      G.map (F.rightDerivedFunctorPlusUnith.app K) :=
  rfl

/-- **Right-derivedness on the bounded below derived category is absolute.** For `F : 𝒜 ⥤ ℬ`
additive with `𝒜` having enough injectives, and for an arbitrary functor `G : D⁺(ℬ) ⥤ ℋ`, the
composite `RF ⋙ G` is a right derived functor of `F∗ ⋙ Qh ⋙ G` with respect to the
quasi-isomorphisms of `K⁺(𝒜)`, with unit
`Stacks.DerivedIndexing.rightDerivedFunctorPlusCompUnit`. -/
instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp (G : DerivedCategory.Plus D ⥤ H) :
    (F.rightDerivedFunctorPlus ⋙ G).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompUnit F G) (HomotopyCategory.Plus.quasiIso C) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ G)).isRightDerivedFunctor_of_isIso
    _ fun X ↦ by
      rw [rightDerivedFunctorPlusCompUnit_app]
      infer_instance

end Stacks.DerivedIndexing

end
