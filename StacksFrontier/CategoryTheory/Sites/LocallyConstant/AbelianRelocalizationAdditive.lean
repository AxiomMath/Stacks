module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianLocallyConstantInverseImage

/-!
# Additivity of the abelian inverse image and of the abelian relocalization along a section

The two functors between categories of sheaves of abelian groups built out of a morphism of
topoi `f : Sh(C) ⟶ Sh(D)` — the abelian inverse image
`CategoryTheory.Sites.abelianInverseImage` and the relocalization along a section
`MorphismOfTopoi.abelianSectionRelocalization` — are constructed by internalizing the group
operations, applying a finite-product-preserving functor between the two topoi of sheaves of
sets, and reading the operations back sectionwise. Nothing in that construction mentions the
additive structure of the hom groups, so additivity of the two functors is not part of their
definitions. This file supplies it.

Additivity is in both cases obtained from
`CategoryTheory.Functor.additive_of_preserves_binary_products`: a functor between preadditive
categories with binary products which preserves binary products and zero morphisms is additive.
For the abelian inverse image the preservation is already
available, since `CategoryTheory.Sites.abelianInverseImage_preservesFiniteLimits` records that
it is left exact. For the relocalization no such left exactness is available — the relocalization
is not a morphism of topoi and no adjoint of the base change along the section is constructed —
and the preservation is proved here, by transporting
`MorphismOfTopoi.preservesFiniteProducts_sectionRelocalization` through the comparison of
underlying sheaves of sets.

## Main results

* `MorphismOfTopoi.abelianSectionRelocalizationForgetIso` — forgetting the abelian group
  operations turns the abelian relocalization into the relocalization of sheaves of sets. As for
  the abelian inverse image this is the identity: the underlying sheaves of sets and their maps
  agree definitionally.
* `MorphismOfTopoi.preservesFiniteProducts_abelianSectionRelocalization` — the abelian
  relocalization preserves finite products.
* `CategoryTheory.Sites.abelianInverseImage_additive` and
  `MorphismOfTopoi.abelianSectionRelocalization_additive` — the two functors are additive.

## Implementation notes

The two additivity statements are exactly the hypotheses `Stacks.ModuleCatLift.moduleLift`
requires of an additive functor between categories of abelian sheaves in order to lift it to
sheaves of modules over a fixed ring; this file is the formal category theory which lets the
abelian case of Tag 093R be transported to sheaves of modules, and the Stacks tag is carried by
the statement that consumes it, not by anything here.

Finite products in `Sheaf _ AddCommGrpCat` are detected by the forgetful functor to sheaves of
sets: `CategoryTheory.sheafCompose _ (CategoryTheory.forget AddCommGrpCat)` preserves finite
limits, because after composing with `CategoryTheory.sheafToPresheaf` it is sectionwise the
forgetful functor of abelian groups, and it reflects isomorphisms, so it reflects finite limits
too. That is the same argument the left exactness of the abelian inverse image is proved by, and
it is isolated here as `CategoryTheory.Sites.preservesFiniteLimits_sheafCompose_forget` so that
the relocalization can reuse it.

The zero morphisms are preserved for the cheapest possible reason: a functor preserving the
terminal object between categories with a zero object preserves zero morphisms, and in a
preadditive category the terminal object is the zero object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.AbelianSheaf
open Stacks.Sites.AbelianPullback

universe v u v' u' w w'

namespace CategoryTheory.Sites

/-- **Forgetting the abelian group operations preserves finite limits of abelian sheaves.**
After composing with `CategoryTheory.sheafToPresheaf` the functor is sectionwise the forgetful
functor of abelian groups, which preserves all limits; and `CategoryTheory.sheafToPresheaf`
reflects finite limits, so the preservation descends to sheaves. -/
public theorem preservesFiniteLimits_sheafCompose_forget {E : Type u} [Category.{v} E]
    (J : GrothendieckTopology E) :
    PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w})) := by
  have : PreservesFiniteLimits
      (sheafCompose J (forget AddCommGrpCat.{w}) ⋙ sheafToPresheaf J (Type w)) := by
    show PreservesFiniteLimits
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type w))

section InverseImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- **The abelian inverse image of a morphism of topoi is additive.** It is left exact
(`CategoryTheory.Sites.abelianInverseImage_preservesFiniteLimits`), hence preserves binary
products and the terminal object, hence zero morphisms, hence is additive. -/
public instance abelianInverseImage_additive : (abelianInverseImage f).Additive := by
  have : HasZeroObject (Sheaf K AddCommGrpCat.{w'}) := hasZeroObject_of_hasTerminal_object
  have : HasZeroObject (Sheaf J AddCommGrpCat.{w}) := hasZeroObject_of_hasTerminal_object
  have : (abelianInverseImage f).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  exact Functor.additive_of_preserves_binary_products _

end InverseImage

end CategoryTheory.Sites

namespace MorphismOfTopoi

attribute [local instance] cartesianPresheafTypes braidedPresheafTypes cartesianSheafTypes
  braidedSheafTypes braidedSheafToPresheafTypes

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  {V : C} {Y : D}
  (σ : (presheafToSheaf J (Type w)).obj (yoneda.obj V) ⟶
    f.inverseImage.obj ((presheafToSheaf K (Type w)).obj (yoneda.obj Y)))

/-- **Forgetting the abelian group operations recovers the relocalization of sheaves of sets**,
naturally in the sheaf. The abelian relocalization internalizes the group operations, applies
`MorphismOfTopoi.sectionRelocalization`, and reads the result back sectionwise, so its underlying
sheaf of sets and its underlying maps are those of `MorphismOfTopoi.sectionRelocalization`
definitionally. -/
public def abelianSectionRelocalizationForgetIso :
    abelianSectionRelocalization J K f σ ⋙ sheafCompose (J.over V) (forget AddCommGrpCat.{w}) ≅
      sheafCompose (K.over Y) (forget AddCommGrpCat.{w}) ⋙ sectionRelocalization J K f σ :=
  Iso.refl _

/-- **The abelian relocalization along a section preserves finite products.** The relocalization
of sheaves of sets does (`MorphismOfTopoi.preservesFiniteProducts_sectionRelocalization`), and
`MorphismOfTopoi.abelianSectionRelocalizationForgetIso` transports that across the forgetful
functor, which reflects finite products. -/
public instance preservesFiniteProducts_abelianSectionRelocalization :
    PreservesFiniteProducts (abelianSectionRelocalization J K f σ) := by
  have : PreservesFiniteLimits (sheafCompose (J.over V) (forget AddCommGrpCat.{w})) :=
    preservesFiniteLimits_sheafCompose_forget _
  have : PreservesFiniteLimits (sheafCompose (K.over Y) (forget AddCommGrpCat.{w})) :=
    preservesFiniteLimits_sheafCompose_forget _
  have : PreservesFiniteProducts
      (abelianSectionRelocalization J K f σ ⋙
        sheafCompose (J.over V) (forget AddCommGrpCat.{w})) := by
    have : PreservesFiniteProducts
        (sheafCompose (K.over Y) (forget AddCommGrpCat.{w}) ⋙
          sectionRelocalization J K f σ) := inferInstance
    exact ⟨fun _ => preservesLimitsOfShape_of_natIso
      (abelianSectionRelocalizationForgetIso J K f σ).symm⟩
  exact preservesFiniteProducts_of_reflects_of_preserves _
    (sheafCompose (J.over V) (forget AddCommGrpCat.{w}))

/-- **The abelian relocalization along a section is additive.** It preserves finite products
(`MorphismOfTopoi.preservesFiniteProducts_abelianSectionRelocalization`), hence the terminal
object, hence zero morphisms, and a functor between preadditive categories preserving binary
products and zero morphisms is additive. -/
public instance abelianSectionRelocalization_additive :
    (abelianSectionRelocalization J K f σ).Additive := by
  have : HasZeroObject (Sheaf (K.over Y) AddCommGrpCat.{w}) :=
    hasZeroObject_of_hasTerminal_object
  have : HasZeroObject (Sheaf (J.over V) AddCommGrpCat.{w}) :=
    hasZeroObject_of_hasTerminal_object
  have : (abelianSectionRelocalization J K f σ).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  exact Functor.additive_of_preserves_binary_products _

end MorphismOfTopoi

end
