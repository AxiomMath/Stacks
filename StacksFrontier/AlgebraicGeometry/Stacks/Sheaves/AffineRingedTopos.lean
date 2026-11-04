module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEtaleSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# The ringed topos of the affine subsite (Stacks 0H0C)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `τ` be a topology on the
schemes of the ambient big fppf site. Stacks 0H0A equips the affine subcategory of `𝒳` with the
topology it inherits from the affine schemes over `S`, and Stacks 0H0B shows the inclusion is a
dense subsite, hence induces an equivalence of sheaf topoi. Stacks 0H0C upgrades that equivalence
to an equivalence of ringed topoi: the structure sheaf of `𝒳` restricts to a sheaf of commutative
rings on the affine subsite, and the inclusion becomes a morphism of ringed topoi whose inverse
image is restriction and whose structure morphism is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Stack.affineRestriction`: restriction of sheaves from the associated site to
  its affine subsite.
* `AlgebraicGeometry.Stack.liftedStructureSheaf`: the structure sheaf of Stacks 06TV, with its
  sections lifted to a universe containing the site.
* `AlgebraicGeometry.Stack.affineStructureSheaf`: its restriction to the affine subsite.
* `AlgebraicGeometry.Stack.fullRingedTopos` and `AlgebraicGeometry.Stack.affineRingedTopos`: the
  two ringed topoi.
* `AlgebraicGeometry.Stack.affineToFull`: the morphism of ringed topoi induced by the inclusion of
  the affine subsite.
* `AlgebraicGeometry.Stack.affineToFullFppf`: the same morphism for the fppf topology.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_affineToFull_inverseImage`: the inverse image of
  `affineToFull` is an equivalence.
* `AlgebraicGeometry.Stack.isIso_affineToFull_fSharpInverseImage`: the structure morphism of
  `affineToFull` is an isomorphism.
* `AlgebraicGeometry.Stack.forgetRing_map_affineToFull_fSharpInverseImage`: the structure
  morphism forgets to the identity on underlying sheaves of sets.

## Implementation notes

The statement is proved for an arbitrary topology `τ` on the schemes of the ambient site, coarser
than the fppf one, together with an arbitrary topology `J` on the affine schemes over `S` for which
the affine inclusion downstairs is a dense subsite; of the five standard topologies of the source,
only the fppf case is recorded here.

`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` needs the target category to have limits of
shape `StructuredArrow X G.op`, whose objects live in `max v w` for a site `𝒳 : Type v` with
`Category.{w} 𝒳`, so the topos is taken at the universe `max u v w` and the structure sheaf of
Stacks 06TV is lifted there by `AlgebraicGeometry.SheafOfModules.sheafULift`.

## References

* [Stacks Project, Tag 0H0A](https://stacks.math.columbia.edu/tag/0H0A)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (τ : GrothendieckTopology B.Schemes) (J : GrothendieckTopology (BigAffineFppf B S hS))

/-- The structure sheaf of Stacks 06TV with its sections, commutative rings in the scheme universe
`u`, replaced by their `ULift` to the universe `max u v w`. -/
noncomputable def liftedStructureSheaf (hp : p.IsFiberedInGroupoids) (hτ : τ ≤ B.topology) :
    Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w} :=
  (SheafOfModules.sheafULift.{u, v, w} (associatedTopology B S hS p τ)).obj
    (structureSheaf B S hS p hp τ hτ)

section Dense

variable [(AffineCategory.inclusion B S hS p).IsDenseSubsite
  (associatedAffineTopology B S hS p J) (associatedTopology B S hS p τ)]

/-- Restriction to the affine subsite: composition with the inclusion of the affine subcategory,
a functor of sites by Stacks 0H0B. -/
noncomputable abbrev affineRestriction (A : Type*) [Category A] :
    Sheaf (associatedTopology B S hS p τ) A ⥤
      Sheaf (associatedAffineTopology B S hS p J) A :=
  (AffineCategory.inclusion B S hS p).sheafPushforwardContinuous A
    (associatedAffineTopology B S hS p J) (associatedTopology B S hS p τ)

/-- The equivalence of sheaf topoi of Stacks 0H0B, for sheaves of sets in the universe
`max u v w`, whose inverse is restriction along the affine inclusion. -/
noncomputable def affineSheafEquiv :
    Sheaf (associatedAffineTopology B S hS p J) (Type (max u v w)) ≌
      Sheaf (associatedTopology B S hS p τ) (Type (max u v w)) :=
  Functor.IsDenseSubsite.sheafEquiv (associatedAffineTopology B S hS p J)
    (associatedTopology B S hS p τ) (AffineCategory.inclusion B S hS p) (Type (max u v w))

/-- The inverse of the equivalence of sheaf topoi is restriction. -/
@[simp] theorem affineSheafEquiv_inverse :
    (affineSheafEquiv B S hS p τ J).inverse =
      affineRestriction B S hS p τ J (Type (max u v w)) :=
  rfl

/-- The ringed topos of `𝒳`: the associated site of `𝒳` with a sheaf of commutative rings on it. -/
noncomputable abbrev fullRingedTopos
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    AlgebraicGeometry.RingedTopos.{w, v, max u v w} where
  C := 𝒳
  J := associatedTopology B S hS p τ
  O := O

/-- The ringed topos of the affine subsite: the affine subsite of Stacks 0H0A with the restriction
of a sheaf of commutative rings on the associated site. -/
noncomputable abbrev affineRingedTopos
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    AlgebraicGeometry.RingedTopos.{w, v, max u v w} where
  C := AffineCategory B S hS p
  J := associatedAffineTopology B S hS p J
  O := (affineRestriction B S hS p τ J CommRingCat.{max u v w}).obj O

/-- The structure sheaf of the affine subsite: the restriction of the structure sheaf of `𝒳`. -/
noncomputable abbrev affineStructureSheaf
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    Sheaf (associatedAffineTopology B S hS p J) CommRingCat.{max u v w} :=
  (affineRingedTopos B S hS p τ J O).O

/-- The morphism of topoi induced by the affine inclusion: its inverse image is restriction and its
direct image is the quasi-inverse supplied by the equivalence of Stacks 0H0B. -/
noncomputable def affineToposHom
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    MorphismOfTopoi (affineRingedTopos B S hS p τ J O).Topos
      (fullRingedTopos B S hS p τ O).Topos where
  pushforward := (affineSheafEquiv B S hS p τ J).functor
  inverseImage := (affineSheafEquiv B S hS p τ J).inverse
  adj := (affineSheafEquiv B S hS p τ J).symm.toAdjunction
  preservesFiniteLimits := by
    change PreservesFiniteLimits (affineRestriction B S hS p τ J (Type (max u v w)))
    infer_instance

/-- The inverse image of the induced morphism of topoi is restriction to the affine subsite. -/
@[simp] theorem affineToposHom_inverseImage
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    (affineToposHom B S hS p τ J O).inverseImage =
      affineRestriction B S hS p τ J (Type (max u v w)) :=
  rfl

/-- The isomorphism between the inverse image of the structure sheaf along the induced morphism of
topoi and its restriction, as sheaves of commutative rings. -/
noncomputable def affineStructureComparison
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    (inverseImageCommRingFunctor (affineToposHom B S hS p τ J O)).obj
        (fullRingedTopos B S hS p τ O).O ≅
      (affineRingedTopos B S hS p τ J O).O :=
  restrictionCommRingIso (associatedAffineTopology B S hS p J)
    (associatedTopology B S hS p τ) (AffineCategory.inclusion B S hS p) O

/-- The morphism of ringed topoi induced by the inclusion of the affine subsite: its underlying
morphism of topoi is the equivalence of Stacks 0H0B and its structure morphism is the adjunct of
the identification of the inverse image of the structure sheaf with its restriction. -/
@[stacks 0H0C "the morphism of ringed topoi"]
noncomputable def affineToFull
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    AlgebraicGeometry.RingedToposHom (affineRingedTopos B S hS p τ J O)
      (fullRingedTopos B S hS p τ O) where
  toToposHom := affineToposHom B S hS p τ J O
  fSharp := ((commRingImageAdjunction (affineToposHom B S hS p τ J O)).homEquiv _ _)
    (affineStructureComparison B S hS p τ J O).hom

/-- The inverse-image form of the structure morphism of `affineToFull` is the structure
comparison. -/
theorem affineToFull_fSharpInverseImage
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    (affineToFull B S hS p τ J O).fSharpInverseImage =
      (affineStructureComparison B S hS p τ J O).hom :=
  ((commRingImageAdjunction (affineToposHom B S hS p τ J O)).homEquiv _ _).symm_apply_apply _

/-- The structure morphism of `affineToFull` is an isomorphism. -/
@[stacks 0H0C "the structure morphism is an isomorphism"]
theorem isIso_affineToFull_fSharpInverseImage
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    IsIso (affineToFull B S hS p τ J O).fSharpInverseImage := by
  rw [affineToFull_fSharpInverseImage]
  exact (affineStructureComparison B S hS p τ J O).isIso_hom

/-- The inverse image of `affineToFull` is an equivalence. -/
@[stacks 0H0C "the inverse image is an equivalence"]
theorem isEquivalence_affineToFull_inverseImage
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    (affineToFull B S hS p τ J O).toToposHom.inverseImage.IsEquivalence :=
  (affineSheafEquiv B S hS p τ J).isEquivalence_inverse

/-- The structure morphism of `affineToFull` is the identity on underlying sheaves of sets. -/
theorem forgetRing_map_affineToFull_fSharpInverseImage
    (O : Sheaf (associatedTopology B S hS p τ) CommRingCat.{max u v w}) :
    (affineRingedTopos B S hS p τ J O).forgetRing.map
        (affineToFull B S hS p τ J O).fSharpInverseImage = 𝟙 _ :=
  (congrArg (affineRingedTopos B S hS p τ J O).forgetRing.map
      (affineToFull_fSharpInverseImage B S hS p τ J O)).trans
    (restrictionCommRingIso_hom_forget (associatedAffineTopology B S hS p J)
      (associatedTopology B S hS p τ) (AffineCategory.inclusion B S hS p) O)

end Dense

/-- Stacks 0H0B for the fppf topology: the affine inclusion of a category fibred in groupoids is a
dense subsite for the associated fppf topologies. -/
theorem isDenseSubsite_affineInclusion_fppf (hp : p.IsFiberedInGroupoids) :
    (AffineCategory.inclusion B S hS p).IsDenseSubsite
      (associatedAffineTopology B S hS p (BigAffineFppf.topology B S hS))
      (associatedTopology B S hS p B.topology) :=
  (AffineCategory.inclusion_isSpecialCocontinuous B S hS p hp
    (BigAffineFppf.topology B S hS) (BigFppfOver.topology B S hS)
    (bigAffineFppfInclusion_isDenseSubsite B S hS)).2

/-- The inclusion of the affine subsite of the associated fppf site of a category fibred in
groupoids, as a morphism of ringed topoi for the lifted structure sheaf of Stacks 06TV. -/
@[stacks 0H0C "the fppf topology"]
noncomputable def affineToFullFppf (hp : p.IsFiberedInGroupoids) :
    letI : (AffineCategory.inclusion B S hS p).IsDenseSubsite
        (associatedAffineTopology B S hS p (BigAffineFppf.topology B S hS))
        (associatedTopology B S hS p B.topology) :=
      isDenseSubsite_affineInclusion_fppf B S hS p hp
    AlgebraicGeometry.RingedToposHom
      (affineRingedTopos B S hS p B.topology (BigAffineFppf.topology B S hS)
        (liftedStructureSheaf B S hS p B.topology hp le_rfl))
      (fullRingedTopos B S hS p B.topology
        (liftedStructureSheaf B S hS p B.topology hp le_rfl)) :=
  letI := isDenseSubsite_affineInclusion_fppf B S hS p hp
  affineToFull B S hS p B.topology (BigAffineFppf.topology B S hS)
    (liftedStructureSheaf B S hS p B.topology hp le_rfl)

end AlgebraicGeometry.Stack

end
