module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite

/-!
# Fibre products of algebraic spaces étale over an algebraic space

The spaces-étale site `AlgebraicGeometry.Space.SpacesEtale` of an algebraic space `X` over a scheme
`S` of a big fppf site (Stacks 03G0) has as objects the algebraic spaces over `S` equipped with an
étale morphism to `X`, as morphisms the commuting triangles over `X`, and as covering families
those whose members jointly cover the points of their target.

Being étale over `X` is an `ObjectProperty` of the slice above `X`, closed under isomorphisms and
fibre products. Hence the inclusion of the site into the slice creates fibre products, and the
algebraic space underlying a fibre product in the site is the fibre product of the underlying
algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isEtaleOver_isClosedUnderIsomorphisms`: being étale over `X` is
  invariant under isomorphism in the slice above `X`.
* `AlgebraicGeometry.Space.isEtaleOver_isClosedUnderLimitsOfShape_walkingCospan`: a fibre product
  in the slice above `X` of two objects étale over `X` is again étale over `X`.
* `AlgebraicGeometry.Space.SpacesEtale.instCreatesPullbacksInclusion`: the inclusion of the
  spaces-étale site of `X` into the slice above `X` creates fibre products.
* `AlgebraicGeometry.Space.SpacesEtale.instPreservesPullbacksToSpaces`: the algebraic space
  underlying a fibre product in the spaces-étale site of `X` is the fibre product of the underlying
  algebraic spaces.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- Being étale over `X` is invariant under isomorphism in the slice above `X`. -/
instance isEtaleOver_isClosedUnderIsomorphisms :
    (IsEtaleOver B S hS X).IsClosedUnderIsomorphisms where
  of_iso {U U'} e h := by
    have hinv : IsIso e.inv := inferInstanceAs (IsIso e.symm.hom)
    have hleft : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget X).map e.inv))
    have hhom : IsIso e.inv.left.hom :=
      inferInstanceAs (IsIso ((ObjectProperty.ι _).map e.inv.left))
    have hcomp : IsEtale B S hS (e.inv.left.hom ≫ U.hom.hom) :=
      isEtale_comp B S hS (isEtale_of_isIso B S hS e.inv.left.hom) h
    have hw : e.inv.left ≫ U.hom = U'.hom := Over.w e.inv
    have heq : e.inv.left.hom ≫ U.hom.hom = U'.hom.hom := by rw [← hw]; rfl
    change IsEtale B S hS U'.hom.hom
    exact heq ▸ hcomp

/-- A fibre product in the slice above `X` of two objects étale over `X` is again étale over
`X`. -/
instance isEtaleOver_isClosedUnderLimitsOfShape_walkingCospan :
    (IsEtaleOver B S hS X).IsClosedUnderLimitsOfShape WalkingCospan := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨D, hD⟩
  have hpb : IsPullback ((limit.π D WalkingCospan.left).left)
      ((limit.π D WalkingCospan.right).left) ((D.map WalkingCospan.Hom.inl).left)
      ((D.map WalkingCospan.Hom.inr).left) :=
    IsPullback.of_isLimit_cone (isLimitOfPreserves (Over.forget X) (limit.isLimit D))
  have hinl : IsEtale B S hS ((D.map WalkingCospan.Hom.inl).left).hom :=
    isEtale_of_isEtale_over B S hS (D.obj WalkingCospan.left).left.property
      (D.obj WalkingCospan.one).left.property X.property _ _ _
      (hD WalkingCospan.left) (hD WalkingCospan.one)
      (by simpa only [ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun k : _ ⟶ X => k.hom) (Over.w (D.map WalkingCospan.Hom.inl)))
  have hright : IsEtale B S hS ((limit.π D WalkingCospan.right).left).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ hpb hinl
  have hw : (limit.π D WalkingCospan.right).left ≫ (D.obj WalkingCospan.right).hom =
      (limit D).hom := Over.w (limit.π D WalkingCospan.right)
  have hcomp := isEtale_comp B S hS hright (hD WalkingCospan.right)
  have heq : ((limit.π D WalkingCospan.right).left).hom ≫
      (D.obj WalkingCospan.right).hom.hom = (limit D).hom.hom := by rw [← hw]; rfl
  change IsEtale B S hS (limit D).hom.hom
  exact heq ▸ hcomp

namespace SpacesEtale

/-- The inclusion of the algebraic spaces étale over `X` into the slice above `X` creates fibre
products. -/
noncomputable instance instCreatesPullbacksInclusion :
    CreatesLimitsOfShape WalkingCospan (inclusion B S hS X) :=
  inferInstanceAs (CreatesLimitsOfShape WalkingCospan (IsEtaleOver B S hS X).ι)

/-- The algebraic space underlying a fibre product in the spaces-étale site of `X` is the fibre
product of the underlying algebraic spaces. -/
instance instPreservesPullbacksToSpaces :
    PreservesLimitsOfShape WalkingCospan (toSpaces B S hS X) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    (inclusion B S hS X ⋙ Over.forget X))

end SpacesEtale

end AlgebraicGeometry.Space

end
