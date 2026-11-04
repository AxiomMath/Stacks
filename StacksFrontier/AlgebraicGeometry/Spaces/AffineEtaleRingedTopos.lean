module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints

/-!
# The ringed topos of affine étale charts of an algebraic space

The affine étale site of an algebraic space `F` is a *ringed* topos, compared here with the
small étale ringed topos. Restriction of sheaves along the inclusion of the affine charts is an
equivalence of topoi, by `AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`,
and the structure sheaf of the affine étale site is by definition the restriction of the small
étale structure sheaf along it, so the comparison of the two ringed topoi is an isomorphism on
structure sheaves.

A `AlgebraicGeometry.RingedTopos` declares its underlying topos at the universe of its
structure rings, so both ringed topoi carry the structure sheaf at `u + 1`, the universe of the
étale charts themselves: `AlgebraicGeometry.Space.liftedStructurePresheaf`, which is a sheaf.

## Main definitions

* `AlgebraicGeometry.Space.liftedStructureSheaf` is the small étale structure sheaf with its
  rings of sections raised to the universe of the site.
* `AlgebraicGeometry.Space.affineEtaleRestriction` is restriction of sheaves along the inclusion
  of the affine étale charts, and
  `AlgebraicGeometry.Space.affineEtaleStructureSheaf` is the structure sheaf it restricts the
  lifted small étale structure sheaf to.
* `AlgebraicGeometry.Space.affineEtaleRingedTopos` and
  `AlgebraicGeometry.Space.liftedSmallEtaleRingedTopos` are the two ringed topoi.
* `AlgebraicGeometry.Space.affineEtaleToSmallEtale` is the induced morphism of ringed topoi.

## Main results

* `AlgebraicGeometry.Space.affineEtaleRestriction_isEquivalence`: restriction to affine charts is
  an equivalence of the topoi of sheaves of sets.
* `AlgebraicGeometry.Space.affineEtaleToSmallEtale` carries, as part of its statement, that its
  inverse image *is* that restriction, that the inverse image is an equivalence, and that its
  structure map is an isomorphism which after forgetting the ring operations is the identity of
  the restricted structure sheaf.

## Implementation notes

The structure sheaf of the affine étale site is *defined* as the restriction of the lifted small
étale structure sheaf, rather than as global regular functions on affine charts. The two agree,
because restriction along a fully faithful inclusion is evaluation.

The last clause of `affineEtaleToSmallEtale` is stated as an `HEq` because the identity it
asserts is an identity of morphisms of sheaves of sets whose source and target are given by two
different routes — the inverse image of the structure sheaf of the target, and the structure
sheaf of the source — which are equal but not syntactically so. Forgetting the ring operations
of `Stacks.Sheaves.ToposPullback.restrictionCommRingIso` is the identity, which is
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso_hom_forget`.

## References

* [Stacks Project, Tag 0H03](https://stacks.math.columbia.edu/tag/0H03)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)

/-! ### The structure sheaf at the universe of the site -/

/-- The small étale structure sheaf of `F` with its rings of sections raised to the universe of
the étale charts. -/
noncomputable def liftedStructureSheaf :
    { O : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u + 1} //
      O.obj = liftedStructurePresheaf B S hS F } := by
  have hP : Presheaf.IsSheaf (SmallEtale.topology B S hS F)
      (liftedStructurePresheaf B S hS F) := by
    rw [Presheaf.isSheaf_iff_isSheaf_comp (SmallEtale.topology B S hS F)
      (liftedStructurePresheaf B S hS F) (CategoryTheory.forget CommRingCat.{u + 1})]
    refine (isSheaf_iff_isSheaf_of_type _ _).2 ?_
    change Presieve.IsSheaf (SmallEtale.topology B S hS F)
      ((structurePresheaf B S hS F ⋙ CategoryTheory.forget CommRingCat.{u}) ⋙
        CategoryTheory.uliftFunctor.{u + 1, u})
    rw [Presieve.isSheaf_comp_uliftFunctor_iff]
    exact isSheaf_globalSections B S hS F
  exact ⟨⟨liftedStructurePresheaf B S hS F, hP⟩, rfl⟩

/-! ### Restriction to affine charts -/

/-- Restriction of sheaves along the inclusion of the affine étale charts of `F` into all its
étale charts. -/
noncomputable def affineEtaleRestriction (A : Type*) [Category A] :
    Sheaf (SmallEtale.topology B S hS F) A ⥤
      Sheaf (AffineEtale.topology B S hS F) A := by
  have : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F)
      (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  exact (AffineEtale.inclusion B S hS F).sheafPushforwardContinuous
    A (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)

/-- The structure sheaf of the affine étale site of `F`: the restriction to affine charts of the
lifted small étale structure sheaf. -/
noncomputable def affineEtaleStructureSheaf :
    Sheaf (AffineEtale.topology B S hS F) CommRingCat.{u + 1} :=
  (affineEtaleRestriction B S hS F hF CommRingCat.{u + 1}).obj
    (liftedStructureSheaf B S hS F).val

/-- The affine étale site of `F` with its structure sheaf, as a ringed topos. -/
noncomputable def affineEtaleRingedTopos : RingedTopos.{u, u + 1, u + 1} where
  C := AffineEtale B S hS F
  J := AffineEtale.topology B S hS F
  O := affineEtaleStructureSheaf B S hS F hF

/-- The small étale site of `F` with its lifted structure sheaf, as a ringed topos: the small
étale ringed topos `smallEtaleRingedTopos` with its structure rings in universe `u + 1` rather
than `u`. -/
noncomputable def liftedSmallEtaleRingedTopos : RingedTopos.{u, u + 1, u + 1} where
  C := SmallEtale B S hS F
  J := SmallEtale.topology B S hS F
  O := (liftedStructureSheaf B S hS F).val

/-- Restriction from the small étale site of an algebraic space to its affine étale charts is an
equivalence on sheaves of sets, at the universe of the objects of the site. -/
@[stacks 0H03 "equivalence of topoi"]
theorem affineEtaleRestriction_isEquivalence :
    (affineEtaleRestriction B S hS F hF (Type (u + 1))).IsEquivalence := by
  have : Functor.IsDenseSubsite (AffineEtale.topology B S hS F)
      (SmallEtale.topology B S hS F) (AffineEtale.inclusion B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  dsimp [affineEtaleRestriction]
  infer_instance

/-- The canonical morphism from the affine étale ringed topos of an algebraic space to its small
étale ringed topos.

Its inverse image is restriction to affine charts and is an equivalence, and its structure map
is an isomorphism which, after forgetting the ring operations, is the identity of the restricted
structure sheaf. -/
@[stacks 0H03 "canonical morphism of ringed topoi"]
noncomputable def affineEtaleToSmallEtale :
    { f : RingedToposHom
        (affineEtaleRingedTopos B S hS F hF)
        (liftedSmallEtaleRingedTopos B S hS F) //
      f.toToposHom.inverseImage =
        affineEtaleRestriction B S hS F hF (Type (u + 1)) ∧
      f.toToposHom.inverseImage.IsEquivalence ∧
      IsIso f.fSharpInverseImage ∧
      HEq ((affineEtaleRingedTopos B S hS F hF).forgetRing.map
        f.fSharpInverseImage)
        (𝟙 ((affineEtaleRingedTopos B S hS F hF).forgetRing.obj
          (affineEtaleRingedTopos B S hS F hF).O)) } := by
  let i := AffineEtale.inclusion B S hS F
  let J := AffineEtale.topology B S hS F
  let K := SmallEtale.topology B S hS F
  have : Functor.IsDenseSubsite J K i :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have : (affineEtaleRestriction B S hS F hF (Type (u + 1))).IsEquivalence :=
    affineEtaleRestriction_isEquivalence B S hS F hF
  let eTop : Sheaf K (Type (u + 1)) ≌ Sheaf J (Type (u + 1)) :=
    (affineEtaleRestriction B S hS F hF (Type (u + 1))).asEquivalence
  let g : MorphismOfTopoi (Sheaf J (Type (u + 1))) (Sheaf K (Type (u + 1))) := {
    pushforward := eTop.inverse
    inverseImage := affineEtaleRestriction B S hS F hF (Type (u + 1))
    adj := eTop.toAdjunction
    preservesFiniteLimits := by
      dsimp [affineEtaleRestriction]
      have hComp : PreservesFiniteLimits
          (i.sheafPushforwardContinuous (Type (u + 1)) J K ⋙
            sheafToPresheaf J (Type (u + 1))) :=
        preservesFiniteLimits_of_natIso
          (i.sheafPushforwardContinuousCompSheafToPresheafIso
            (Type (u + 1)) J K).symm
      exact preservesFiniteLimits_of_reflects_of_preserves
        (i.sheafPushforwardContinuous (Type (u + 1)) J K)
        (sheafToPresheaf J (Type (u + 1))) }
  let e : (inverseImageCommRingFunctor g).obj
        (liftedSmallEtaleRingedTopos B S hS F).O ≅
      (affineEtaleRingedTopos B S hS F hF).O :=
    restrictionCommRingIso J K i (liftedSmallEtaleRingedTopos B S hS F).O
  let f : RingedToposHom
      (affineEtaleRingedTopos B S hS F hF)
      (liftedSmallEtaleRingedTopos B S hS F) := {
    toToposHom := g
    fSharp := (commRingImageAdjunction g).unit.app
        (liftedSmallEtaleRingedTopos B S hS F).O ≫
      (pushforwardCommRingFunctor g).map e.hom }
  let U := (affineEtaleRingedTopos B S hS F hF).forgetRing
  have hInvEq : f.fSharpInverseImage = e.hom := by
    let E : ((inverseImageCommRingFunctor g).obj
          (liftedSmallEtaleRingedTopos B S hS F).O ⟶
        (affineEtaleRingedTopos B S hS F hF).O) ≃
        ((liftedSmallEtaleRingedTopos B S hS F).O ⟶
          (pushforwardCommRingFunctor g).obj
            (affineEtaleRingedTopos B S hS F hF).O) :=
      (commRingImageAdjunction g).homEquiv _ _
    exact E.symm_apply_apply e.hom
  have hInv : U.map f.fSharpInverseImage =
      𝟙 (U.obj (affineEtaleRingedTopos B S hS F hF).O) := by
    rw [hInvEq]
    exact restrictionCommRingIso_hom_forget J K i
      (liftedSmallEtaleRingedTopos B S hS F).O
  refine ⟨f, rfl, ?_, ?_, ?_⟩
  · exact affineEtaleRestriction_isEquivalence B S hS F hF
  · rw [hInvEq]
    exact Iso.isIso_hom e
  · exact heq_of_eq hInv

end AlgebraicGeometry.Space
