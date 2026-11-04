module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.Flat

/-!
# A full subsite of the site of a category fibred in groupoids, as a ringed topos

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids over the big fppf category of a scheme
`S` in `B`, carrying the site of **Stacks 06TP** for a topology `τ ≤ B.topology`, and let
`P` cut out a full subcategory of `𝒳` whose inclusion is continuous and cocontinuous for the
topology the subcategory inherits (**Stacks 07AK**).

Both sites are then ringed: `𝒳` by the structure sheaf of **Stacks 06TV**, and the subcategory by
its restriction along the inclusion. This file assembles the resulting morphism of ringed topoi
and proves it flat.

The content is the *ringed* half of **Stacks 0788**, stated once for an arbitrary such full
subcategory rather than twice; the two cases the source names, the lisse-étale site and the
flat-fppf site of an algebraic stack, are its two instantiations, in
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleInclusion.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfInclusion.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.subsiteTopology`: the topology the full subcategory inherits.
* `AlgebraicGeometry.Stack.subsiteStructureSheaf`: the restriction of the structure sheaf of
  Stacks 06TV to the full subcategory.
* `AlgebraicGeometry.Stack.associatedRingedTopos` and
  `AlgebraicGeometry.Stack.subsiteRingedTopos`: the two ringed topoi.
* `AlgebraicGeometry.Stack.subsiteToposMorphism`: the morphism of topoi `g`, at the universe of
  the structure sheaf's sections.
* `AlgebraicGeometry.Stack.subsiteRingedToposHom`: the morphism of ringed topoi
  `(g, g♯) : (Sh(𝒳'), O_{𝒳'}) ⟶ (Sh(𝒳), O_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.subsiteStructureSheafIso`: the inverse image of the structure sheaf is
  the restricted structure sheaf, and
  `AlgebraicGeometry.Stack.subsiteStructureSheafIso_hom_app`: that comparison is the identity on
  sections.
* `AlgebraicGeometry.Stack.isFlat_subsiteRingedToposHom`: the morphism of ringed topoi is flat
  (**Stacks 04JB**).

## Implementation notes

The structure sheaf of Stacks 06TV takes its sections in `Type u`, the universe of the schemes of
`B`, while the two sites live in a larger universe. Sheafification at that smaller coefficient
universe is available exactly because both sites are essentially small: for the total category
that is the hypothesis `EssentiallySmall.{u} X`, reduced to a statement about the base and the
fibres by `AlgebraicGeometry.Stack.essentiallySmall_obj`, and for the full subcategory it is then
automatic by `CategoryTheory.essentiallySmall_fullSubcategory`. The same smallness supplies the
pointwise right Kan extensions along which the cocontinuous direct image is computed.

Left exactness of the inverse image is automatic because the inverse image is restriction along
the inclusion on the nose, which is the shape the source's morphism of topoi has.

The identification of the inverse image of a sheaf of commutative rings with its restriction is
`Stacks.Sheaves.ToposPullback.restrictionCommRingNatIso`: transporting the ring operations along
restriction of sheaves of sets *is* restriction of sheaves of rings, with the identity as the
comparison on sections. That is why `subsiteStructureSheafIso_hom_app` is a `rfl`, and it is also
why the morphism of ringed topoi is flat: the inverse-image form of its structure map is that
comparison, an isomorphism, and an isomorphism of sheaves of commutative rings is a flat morphism
by `AlgebraicGeometry.SheafOfModules.isFlatMap_of_isIso`.

The explicit universe arguments on `restrictionCommRingNatIso`, on
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`, on
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat` and on
`AlgebraicGeometry.SheafOfModules.sheafULift` are needed: the universe of the sections and the
two universes of the site are independent here, and without them elaboration of those statements
leaves universe constraints of the form `u =?= max v w` unsolved.

## References

* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (P : ObjectProperty X)

/-- The topology a full subcategory of the total category of a category fibred in groupoids
inherits from the site of **Stacks 06TP**: a family of morphisms of the subcategory covers
exactly when its image covers upstairs. -/
abbrev subsiteTopology : GrothendieckTopology P.FullSubcategory :=
  P.ι.inheritedTopology (associatedTopology B S hS p τ)

section

variable [EssentiallySmall.{u} X]

/-- A full subcategory of an essentially small category is essentially small. -/
instance essentiallySmall_subsite : EssentiallySmall.{u} P.FullSubcategory :=
  essentiallySmall_fullSubcategory P

/-- Sheaves of sets on the essentially small site `associatedTopology` admit sheafification. -/
noncomputable instance hasSheafify_associatedTopology :
    HasSheafify (associatedTopology B S hS p τ) (Type u) :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _

/-- Sheaves of sets on the full subsite with `subsiteTopology` admit sheafification. -/
noncomputable instance hasSheafify_subsiteTopology :
    HasSheafify (subsiteTopology B S hS p τ P) (Type u) :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _

variable [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- The inverse image `g⁻¹` on sheaves of sets: restriction along the inclusion of the full
subcategory. -/
noncomputable abbrev subsiteInverseImage :
    Sheaf (associatedTopology B S hS p τ) (Type u) ⥤
      Sheaf (subsiteTopology B S hS p τ P) (Type u) :=
  P.ι.sheafPushforwardContinuous (Type u) _ _

/-- The structure sheaf of the full subsite: the restriction along the inclusion of the structure
sheaf of **Stacks 06TV**. Its ring of sections over an object of the subcategory is the ring of
sections of the ambient structure sheaf over that same object. -/
noncomputable def subsiteStructureSheaf :
    Sheaf (subsiteTopology B S hS p τ P) CommRingCat.{u} :=
  (P.ι.sheafPushforwardContinuous CommRingCat.{u} _ _).obj (structureSheaf B S hS p hp τ hτ)

/-- The site of **Stacks 06TP** with the structure sheaf of **Stacks 06TV**, as a ringed
topos. -/
noncomputable abbrev associatedRingedTopos : RingedTopos.{w, v, u} where
  C := X
  J := associatedTopology B S hS p τ
  O := structureSheaf B S hS p hp τ hτ

/-- The full subsite with the restricted structure sheaf, as a ringed topos. -/
noncomputable abbrev subsiteRingedTopos : RingedTopos.{w, v, u} where
  C := P.FullSubcategory
  J := subsiteTopology B S hS p τ P
  O := subsiteStructureSheaf B S hS p hp τ hτ P

variable [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- The morphism of topoi `g : Sh(𝒳') ⟶ Sh(𝒳)` of **Stacks 0788**, at the universe in which the
structure sheaf takes its sections: inverse image restriction along the inclusion, pushforward
its cocontinuous right adjoint, left exactness of restriction automatic.

This is the same geometric morphism as `AlgebraicGeometry.Stack.FlatFppf.toposMorphism` and
`AlgebraicGeometry.Stack.LisseEtale.toposMorphism`, at a smaller coefficient universe; it has to
be rebuilt there rather than transported, because a morphism of topoi names its two functors and
those are different functors at different coefficient universes. -/
noncomputable def subsiteToposMorphism :
    MorphismOfTopoi (Sheaf (subsiteTopology B S hS p τ P) (Type u))
      (Sheaf (associatedTopology B S hS p τ) (Type u)) := by
  have : ∀ F : P.FullSubcategoryᵒᵖ ⥤ Type u, P.ι.op.HasPointwiseRightKanExtension F :=
    fun F Y => by
      have := hasLimitsOfShape_of_essentiallySmall.{u} (StructuredArrow Y P.ι.op) (Type u)
      infer_instance
  exact
    { pushforward := P.ι.sheafPushforwardCocontinuous (Type u) _ _
      inverseImage := subsiteInverseImage B S hS p τ P
      adj := P.ι.sheafAdjunctionCocontinuous (Type u) _ _
      preservesFiniteLimits := by infer_instance }

/-- **The inverse image of the structure sheaf is the structure sheaf of the full subsite.**
The inverse image of sheaves of commutative rings along `g` transports the ring operations along
restriction of sheaves of sets, and that is restriction of sheaves of commutative rings. -/
noncomputable def subsiteStructureSheafIso :
    (inverseImageCommRingFunctor (subsiteToposMorphism B S hS p τ P)).obj
        (structureSheaf B S hS p hp τ hτ) ≅ subsiteStructureSheaf B S hS p hp τ hτ P :=
  (restrictionCommRingNatIso.{u, w, v, w, v} (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι).app _

/-- The comparison of `AlgebraicGeometry.Stack.subsiteStructureSheafIso` is the identity on
sections: a section of the inverse image of the structure sheaf over an object of the subsite is
literally a section of the structure sheaf over that object. -/
theorem subsiteStructureSheafIso_hom_app (U : P.FullSubcategoryᵒᵖ)
    (a : ((inverseImageCommRingFunctor (subsiteToposMorphism B S hS p τ P)).obj
      (structureSheaf B S hS p hp τ hτ)).obj.obj U) :
    (subsiteStructureSheafIso B S hS p hp τ hτ P).hom.hom.app U a = a := rfl

/-- **The morphism of ringed topoi of Stacks 0788**: the morphism of topoi `g` together with the
structure map `g♯ : O_𝒳 ⟶ g_* O_{𝒳'}`, the direct-image form of the identification of the inverse
image of the structure sheaf with the restricted one. -/
noncomputable def subsiteRingedToposHom :
    RingedToposHom (subsiteRingedTopos B S hS p hp τ hτ P)
      (associatedRingedTopos B S hS p hp τ hτ) where
  toToposHom := subsiteToposMorphism B S hS p τ P
  fSharp := ((commRingImageAdjunction (subsiteToposMorphism B S hS p τ P)).homEquiv _ _)
    (subsiteStructureSheafIso B S hS p hp τ hτ P).hom

/-- The inverse-image form of the structure map is the comparison isomorphism it was built
from. -/
theorem fSharpInverseImage_subsiteRingedToposHom :
    (subsiteRingedToposHom B S hS p hp τ hτ P).fSharpInverseImage =
      (subsiteStructureSheafIso B S hS p hp τ hτ P).hom :=
  Equiv.symm_apply_apply _ _

/-- **The morphism of ringed topoi of Stacks 0788 is flat (Stacks 04JB).** Its inverse-image
structure map is the comparison isomorphism
`AlgebraicGeometry.Stack.subsiteStructureSheafIso`, and an isomorphism of sheaves of commutative
rings is flat. -/
theorem isFlat_subsiteRingedToposHom :
    RingedToposHom.IsFlat
      (X := subsiteRingedTopos B S hS p hp τ hτ P)
      (Y := associatedRingedTopos B S hS p hp τ hτ)
      (subsiteRingedToposHom B S hS p hp τ hτ P) := by
  have : IsIso (subsiteRingedToposHom B S hS p hp τ hτ P).fSharpInverseImage := by
    rw [fSharpInverseImage_subsiteRingedToposHom]
    exact (subsiteStructureSheafIso B S hS p hp τ hτ P).isIso_hom
  have : HasSheafify (subsiteTopology B S hS p τ P) AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, w, v} _
  have : (subsiteTopology B S hS p τ P).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w, v, w} _
  unfold RingedToposHom.IsFlat SheafOfModules.IsFlatMapULift
  exact SheafOfModules.isFlatMap_of_isIso
    ((SheafOfModules.sheafULift.{u, v, w} (subsiteTopology B S hS p τ P)).map
      (subsiteRingedToposHom B S hS p hp τ hτ P).fSharpInverseImage)

end

end AlgebraicGeometry.Stack

end
