module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Binary coproducts in a category of objects under a fixed object

If `C` has pushouts then `CategoryTheory.Under Y` has binary coproducts: the coproduct of two
objects under `Y` is the pushout of their structure morphisms, taken under `Y`.  For sheaves of
commutative algebras over the structure sheaf of a scheme this is the tensor product of two
algebras over the structure sheaf.

## Main definitions

* `Stacks.UnderCoproducts.cofan`: the cofan on two objects under `Y` with vertex
  the pushout of their structure morphisms.
* `Stacks.UnderCoproducts.isColimitCofan`: that cofan is colimiting.

## Main results

* `Stacks.UnderCoproducts.hasBinaryCoproducts`: `CategoryTheory.Under Y` has
  binary coproducts when `C` has pushouts.

## Implementation notes

Mathlib creates colimits in `CategoryTheory.Under Y` along
`CategoryTheory.StructuredArrow.proj` only for *connected* shapes
(`CategoryTheory.Limits.hasColimitsOfShape_of_isConnected`), and `Discrete WalkingPair` is not
connected: the coproduct under `Y` is a pushout in `C`, not a coproduct in `C`.  So the instance
below is not an instance of that one and has to be supplied by hand.

Both legs of the cofan are built with `CategoryTheory.Under.homMk`, whose commutativity
obligation for the left leg is `rfl` by the choice of vertex and for the right leg is
`CategoryTheory.Limits.pushout.condition`.  Morphisms under `Y` are compared with
`CategoryTheory.Under.hom_ext`, which reduces every equation to its component in `C`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.UnderCoproducts

variable {C : Type*} [Category C] [HasPushouts C] {Y : C}

/-- The vertex of the coproduct of two objects under `Y`: the pushout of their structure
morphisms, viewed as an object under `Y`. -/
noncomputable def coprodPt (A B : Under Y) : Under Y :=
  Under.mk (A.hom ≫ pushout.inl A.hom B.hom)

/-- The inclusion of the first summand into the coproduct of two objects under `Y`. -/
noncomputable def inl (A B : Under Y) : A ⟶ coprodPt A B :=
  Under.homMk (pushout.inl A.hom B.hom) rfl

/-- The inclusion of the second summand into the coproduct of two objects under `Y`. -/
noncomputable def inr (A B : Under Y) : B ⟶ coprodPt A B :=
  Under.homMk (pushout.inr A.hom B.hom) pushout.condition.symm

/-- The morphism out of the coproduct of two objects under `Y` induced by a pair of morphisms
to a common target. -/
noncomputable def desc {A B T : Under Y} (f : A ⟶ T) (g : B ⟶ T) : coprodPt A B ⟶ T :=
  Under.homMk (pushout.desc f.right g.right (by rw [Under.w f, Under.w g])) (by
    change (A.hom ≫ pushout.inl A.hom B.hom) ≫ _ = T.hom
    rw [Category.assoc, pushout.inl_desc, Under.w f])

/-- The underlying morphism of `inl A B` is `pushout.inl A.hom B.hom`. -/
@[simp]
theorem inl_right (A B : Under Y) : (inl A B).right = pushout.inl A.hom B.hom := rfl

/-- The underlying morphism of `inr A B` is `pushout.inr A.hom B.hom`. -/
@[simp]
theorem inr_right (A B : Under Y) : (inr A B).right = pushout.inr A.hom B.hom := rfl

/-- The cofan on two objects under `Y` whose vertex is the pushout of their structure
morphisms. -/
noncomputable abbrev cofan (A B : Under Y) : BinaryCofan A B :=
  BinaryCofan.mk (inl A B) (inr A B)

/-- **The coproduct of two objects under `Y` is the pushout of their structure morphisms.** -/
noncomputable def isColimitCofan (A B : Under Y) : IsColimit (cofan A B) :=
  BinaryCofan.IsColimit.mk (cofan A B) (fun f g => desc f g)
    (fun f g => by ext; exact pushout.inl_desc _ _ _)
    (fun f g => by ext; exact pushout.inr_desc _ _ _)
    fun f g m hf hg => by
      ext
      have hl : pushout.inl A.hom B.hom ≫ Under.Hom.right (desc f g) = Under.Hom.right f :=
        pushout.inl_desc _ _ _
      have hr : pushout.inr A.hom B.hom ≫ Under.Hom.right (desc f g) = Under.Hom.right g :=
        pushout.inr_desc _ _ _
      refine pushout.hom_ext ?_ ?_
      · rw [hl]; exact congrArg Under.Hom.right hf
      · rw [hr]; exact congrArg Under.Hom.right hg

/-- Any two objects under `Y` have a binary coproduct. -/
instance hasBinaryCoproduct (A B : Under Y) : HasBinaryCoproduct A B :=
  ⟨⟨⟨cofan A B, isColimitCofan A B⟩⟩⟩

/-- `CategoryTheory.Under Y` has binary coproducts when `C` has pushouts. -/
instance hasBinaryCoproducts : HasBinaryCoproducts (Under Y) :=
  hasBinaryCoproducts_of_hasColimit_pair _

end Stacks.UnderCoproducts
