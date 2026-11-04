module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# The underlying object of a fibre product formed in an over category

The forgetful functor `CategoryTheory.Over.forget Y` preserves connected limits, so the object
underlying a fibre product formed in `Over Y` is canonically the fibre product of the
underlying objects. The comparison isomorphism and its two projections are recorded here; they
are what lets a statement about a fibre product in `Over Y` be read as a statement about the
ambient category.

## Main definitions

* `AlgebraicGeometry.overPullbackLeftIso` is the comparison isomorphism.

## Main results

* `AlgebraicGeometry.overPullbackLeftIso_hom_fst`,
  `AlgebraicGeometry.overPullbackLeftIso_hom_snd`,
  `AlgebraicGeometry.overPullbackLeftIso_inv_fst` and
  `AlgebraicGeometry.overPullbackLeftIso_inv_snd` compute it against the projections.
* `AlgebraicGeometry.overPullbackLeftIso_hom_fst_apply` and
  `AlgebraicGeometry.overPullbackLeftIso_hom_snd_apply` read the first two on points, for an
  over category of schemes.

## Implementation notes

The statement is general in the ambient category rather than being restricted to schemes: the
only inputs are fibre products in the ambient category, fibre products in the over category,
and preservation of connected limits by the forgetful functor, which Mathlib supplies as
`CategoryTheory.Over.preservesLimitsOfShape_forget_of_isConnected`. Consumers in the over
category of a presheaf category need exactly this generality.

The fibre product of the over category is taken as a hypothesis rather than derived from the
one in the ambient category, so that the isomorphism is about whichever fibre product the
caller's instance provides.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {Y : C} [HasPullbacks (Over Y)]
  {X X' Z : Over Y}

/-- The object underlying a fibre product formed in `Over Y` is the fibre product of the
underlying objects. -/
noncomputable def overPullbackLeftIso (f : X ⟶ Z) (g : X' ⟶ Z) :
    (pullback f g).left ≅ pullback f.left g.left :=
  (IsPullback.of_isLimit_cone
    (isLimitOfPreserves (Over.forget Y) (pullback.isLimit f g))).isoPullback

/-- The comparison isomorphism is compatible with the first projection. -/
theorem overPullbackLeftIso_hom_fst (f : X ⟶ Z) (g : X' ⟶ Z) :
    (overPullbackLeftIso f g).hom ≫ pullback.fst f.left g.left =
      (pullback.fst f g).left := by
  unfold overPullbackLeftIso
  exact IsPullback.isoPullback_hom_fst _

/-- The comparison isomorphism is compatible with the second projection. -/
theorem overPullbackLeftIso_hom_snd (f : X ⟶ Z) (g : X' ⟶ Z) :
    (overPullbackLeftIso f g).hom ≫ pullback.snd f.left g.left =
      (pullback.snd f g).left := by
  unfold overPullbackLeftIso
  exact IsPullback.isoPullback_hom_snd _

/-- The inverse comparison is compatible with the first projection. -/
theorem overPullbackLeftIso_inv_fst (f : X ⟶ Z) (g : X' ⟶ Z) :
    (overPullbackLeftIso f g).inv ≫
      (pullback.fst f g : pullback f g ⟶ X).left =
      pullback.fst f.left g.left := by
  simp [overPullbackLeftIso]

/-- The inverse comparison is compatible with the second projection. -/
theorem overPullbackLeftIso_inv_snd (f : X ⟶ Z) (g : X' ⟶ Z) :
    (overPullbackLeftIso f g).inv ≫
      (pullback.snd f g : pullback f g ⟶ X').left =
      pullback.snd f.left g.left := by
  simp [overPullbackLeftIso]

/-- The comparison isomorphism is compatible with the first projection, read on points. -/
theorem overPullbackLeftIso_hom_fst_apply {S : Scheme.{u}} {X X' Z : Over S}
    (f : X ⟶ Z) (g : X' ⟶ Z) (z : (pullback f g).left) :
    (pullback.fst f.left g.left).base ((overPullbackLeftIso f g).hom.base z) =
      (pullback.fst f g).left.base z := by
  rw [← overPullbackLeftIso_hom_fst f g]
  rfl

/-- The comparison isomorphism is compatible with the second projection, read on points. -/
theorem overPullbackLeftIso_hom_snd_apply {S : Scheme.{u}} {X X' Z : Over S}
    (f : X ⟶ Z) (g : X' ⟶ Z) (z : (pullback f g).left) :
    (pullback.snd f.left g.left).base ((overPullbackLeftIso f g).hom.base z) =
      (pullback.snd f g).left.base z := by
  rw [← overPullbackLeftIso_hom_snd f g]
  rfl

end AlgebraicGeometry

end
