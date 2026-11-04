module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineRingedTopos
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall

/-!
# Stacks 04HR for sheaves of sets in the next universe

The inclusion of the small affine étale site of a scheme `S` into its small étale site exhibits
the former as a dense subsite of the latter (Stacks 04HR,
`AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous`). Restriction along it is
therefore an equivalence on sheaves, and this file records that equivalence for sheaves of sets
with values in `Type (u + 1)`, the universe in which sheaves on these sites are consumed by the
inverse-system machinery of Stacks 09YL/09YN.

## Main results

* `AlgebraicGeometry.SmallAffineEtale.sheafEquiv` — the equivalence
  `Sh(S_{affine,étale}, Type (u+1)) ≌ Sh(S_étale, Type (u+1))`.
* `AlgebraicGeometry.SmallAffineEtale.sheafEquiv_inverse_obj_obj` — its inverse is restriction
  along the inclusion, on the nose: the underlying presheaf of
  `(sheafEquiv B S hS).inverse.obj F` is `(inclusion B S hS).op ⋙ F.obj`.

The abelian analogue is `Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale`
together with `restrictToAffineEtale_isEquivalence`.

## References

* [Stacks 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallAffineEtale

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04HR, cocontinuity**, as an instance: the inclusion of the small affine étale site
into the small étale site is cocontinuous. The tree carries this only as the first component of
`AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous`; the dense-subsite component
is already a global instance (`inclusion_isDenseSubsite`), and the sheaf equivalence needs both. -/
public instance inclusion_isCocontinuous :
    (inclusion B S hS).IsCocontinuous (topology B S hS) (SmallEtale.topology B S hS) :=
  (inclusion_isSpecialCocontinuous B S hS).1

/-- Limits of the shape indexed by the affine objects over a given object of the small étale site
exist in `Type (u + 1)`, because the small affine étale site is essentially small. This is the
`Type (u + 1)` counterpart of `hasLimitsOfShape_structuredArrow`, which the tree has only for
`Type u`, and it is the one instance the sheaf equivalence below is missing. -/
public instance hasLimitsOfShape_structuredArrow_succ (X : (SmallEtale B S hS)ᵒᵖ) :
    Limits.HasLimitsOfShape (StructuredArrow X (inclusion B S hS).op) (Type (u + 1)) :=
  Limits.hasLimitsOfShape_of_essentiallySmall _ _

/-- **Stacks 04HR on sheaves of sets.** Restriction along the inclusion of the small affine étale
site of `S` into its small étale site is an equivalence of categories of sheaves of sets with
values in `Type (u + 1)`. No affineness of `S` is needed. -/
@[stacks 04HR "the induced equivalence of topoi `Sh(S_{affine,étale}) ≌ Sh(S_étale)`, for sheaves \
of sets with values in `Type (u + 1)`"]
public noncomputable def sheafEquiv :
    Sheaf (topology B S hS) (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B S hS) (Type (u + 1)) :=
  Functor.IsDenseSubsite.sheafEquiv (topology B S hS) (SmallEtale.topology B S hS)
    (inclusion B S hS) (Type (u + 1))

/-- The inverse of the equivalence of Stacks 04HR **is** restriction along the inclusion: it is
the functor `CategoryTheory.Functor.sheafPushforwardContinuous`, by definition. -/
theorem sheafEquiv_inverse :
    (sheafEquiv B S hS).inverse =
      (inclusion B S hS).sheafPushforwardContinuous (Type (u + 1)) (topology B S hS)
        (SmallEtale.topology B S hS) :=
  rfl

/-- The underlying presheaf of the restriction of a sheaf on the small étale site of `S` to the
small affine étale site is the composite `(inclusion).op ⋙ F.obj`, on the nose. This is the shape
in which the inverse-system machinery of Stacks 09YN consumes a sheaf, so the identification is
definitional and no transport is needed at the presheaf level. -/
theorem sheafEquiv_inverse_obj_obj
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))) :
    ((sheafEquiv B S hS).inverse.obj F).obj = (inclusion B S hS).op ⋙ F.obj :=
  rfl

/-- Sections of the restriction over an affine object are the sections of the original sheaf over
its image in the small étale site. -/
theorem sheafEquiv_inverse_obj_obj_obj
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (W : SmallAffineEtale B S hS) :
    ((sheafEquiv B S hS).inverse.obj F).obj.obj (op W) =
      F.obj.obj (op ((inclusion B S hS).obj W)) :=
  rfl

/-- The inverse of the equivalence of Stacks 04HR acts on a morphism of sheaves by restricting
its components, again on the nose. -/
theorem sheafEquiv_inverse_map_hom
    {F G : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))} (α : F ⟶ G) :
    ((sheafEquiv B S hS).inverse.map α).hom =
      Functor.whiskerLeft (inclusion B S hS).op α.hom :=
  rfl

end AlgebraicGeometry.SmallAffineEtale
