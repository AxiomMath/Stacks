module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentPushforwardAb

/-!
# The Stacks 04DB correction of the degree-`n` term is the identity on sheaves of sets

`CategoryTheory.SimplicialSiteSituation.Augmentation.abelianComponentPushforwardIso` compares the
degree-`n` term `F ↦ a_{n,*}F_n` of the complex of Stacks 0D79 — which is the conjugation through
Stacks 04DB of the *composite* `a_{n,*}((-)_n)` of sheaves of sets — with the *composite of the
conjugations*, the restriction of abelian sheaves followed by the direct image of abelian sheaves
along the augmentation of degree `n`. Both sides have the same underlying sheaf of sets, and this
file proves that the comparison is the identity on it.

That is what lets a transposition along
`CategoryTheory.SimplicialSiteSituation.Augmentation.cechTermAdjunction`, which carries the
correction, be computed on sheaves of sets, where the cone law of Stacks 0D70 lives.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.mapCommGrpCompIso_hom_app_hom`: the
  comparison of `(F ⋙ G).mapCommGrp` with `F.mapCommGrp ⋙ G.mapCommGrp`, for the restriction to
  the component of degree `n` followed by the direct image along the augmentation of that
  degree, is the identity on underlying sheaves of sets.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.internalRestrictIso_hom_app_hom`: the
  internal form of the Stacks 04DB comparison for the restriction `g_n^{-1}` is the identity on
  underlying sheaves of sets.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.abelianComponentPushforwardIso_forget`:
  **the correction itself is the identity on underlying sheaves of sets.**

## Implementation notes

The statement is not proved by one definitional computation: asking the kernel to reduce
`(sheafCompose K (forget AddCommGrpCat)).map (abelianComponentPushforwardIso.hom.app X)` to an
identity in one step exhausts its budget — the comparison is a composite of two whiskerings of
comparisons that are each the identity only after the group-object layers are peeled off. It is
proved instead the way
`CategoryTheory.SimplicialSiteSituation.abelianTransitionOfFiber_forget` is: the composite is
first matched, by one `rfl` against a spelling that mirrors its own shape, with the composite of
the two factors' *underlying* morphisms; each factor is the identity by its own cheap `rfl`; and
the direct image of an identity is cancelled by `CategoryTheory.Functor.map_id`.

The three layers `.hom.hom.hom` of a morphism of commutative group objects are the passage from
the `CommGrp` morphism to its `Grp`, `Mon` and finally base-category underlying morphism.

The local instances of `Stacks.Sites.AbelianPullback` are reused by name, as in
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationComponentPushforwardAb.lean`: the
monoidal and braided structures must be the same terms the comparison was elaborated with, or
the `rfl`s below are not even type-correct.

## References

* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Topos.AbelianPushforward

universe u

namespace CategoryTheory.Functor

/-- An identity composed with a functor applied to an identity is an identity, stated at the
functor's own objects. Named rather than inlined for the reason
`CategoryTheory.Functor.map_id_comp_comp_id` is: at the objects a consumer's statement spells
out, the cancellations are not visible to `rw` at `implicit` transparency. -/
theorem id_comp_map_id {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (X : C) : 𝟙 (F.obj X) ≫ F.map (𝟙 X) = 𝟙 (F.obj X) := by
  rw [F.map_id, Category.id_comp]

/-- A functor applied to an identity, composed with an identity, is an identity, stated at the
functor's own objects. -/
theorem map_id_comp_id {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (X : C) : F.map (𝟙 X) ≫ 𝟙 (F.obj X) = 𝟙 (F.obj X) := by
  rw [F.map_id, Category.id_comp]

end CategoryTheory.Functor

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianMonoidalCategorySheaf
  Stacks.Sites.AbelianPullback.braidedCategorySheaf
  Stacks.Sites.AbelianPullback.braidedSheafToPresheaf
  Stacks.Sites.AbelianPullback.preservesFiniteLimitsSheafPushforward
  Stacks.Sites.AbelianPullback.braidedSheafPushforward
  Functor.Braided.ofChosenFiniteProducts

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (n : SimplexCategory)

/-- Taking commutative group objects of the restriction to the component of degree `n` followed
by the direct image along the augmentation of that degree, compared with the composite of the two
separately, is the identity on underlying sheaves of sets. -/
theorem mapCommGrpCompIso_hom_app_hom (M : CommGrp (Sheaf S.totalTopology (Type u))) :
    ((Functor.mapCommGrpCompIso (F := restrictSets S n)
        (G := (componentAugmentation S D K a n).pushforward)).hom.app M).hom.hom.hom = 𝟙 _ :=
  rfl

/-- The internal form of the comparison of Stacks 04DB for the restriction `g_n^{-1}` is the
identity on underlying sheaves of sets. -/
theorem internalRestrictIso_hom_app_hom (X : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    ((internalRestrictIso S n).hom.app X).hom.hom.hom = 𝟙 _ :=
  rfl

variable [HasSheafify K AddCommGrpCat.{u}]

/-- The Stacks 04DB correction, split into the underlying morphisms of its two factors. This is
the spelling against which the composite is definitionally the composite of the factors; the
`rfl` below is the only definitional step the statement needs. -/
theorem abelianComponentPushforwardIso_forget_aux (X : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    (sheafCompose K (forget AddCommGrpCat.{u})).map
        ((abelianComponentPushforwardIso S D K a n).hom.app X) =
      ((Functor.mapCommGrpCompIso (F := restrictSets S n)
            (G := (componentAugmentation S D K a n).pushforward)).hom.app
          ((Sites.AbelianSheaf.internalSheaf S.totalTopology).obj X)).hom.hom.hom ≫
        (componentAugmentation S D K a n).pushforward.map
          (((internalRestrictIso S n).hom.app X).hom.hom.hom) :=
  rfl

/-- **The Stacks 04DB correction of the degree-`n` term of the complex of Stacks 0D79 is the
identity on underlying sheaves of sets.** Both the comparison of `(g_n^{-1} ⋙ a_{n,*})` taken on
commutative group objects with the composite of the two taken separately, and the comparison of
Stacks 04DB for `g_n^{-1}` itself, are the identity there; and the direct image of an identity is
an identity. -/
theorem abelianComponentPushforwardIso_forget (X : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    (sheafCompose K (forget AddCommGrpCat.{u})).map
        ((abelianComponentPushforwardIso S D K a n).hom.app X) =
      𝟙 ((sheafCompose K (forget AddCommGrpCat.{u})).obj
        ((abelianComponentPushforward S D K a n).obj X)) := by
  rw [abelianComponentPushforwardIso_forget_aux, mapCommGrpCompIso_hom_app_hom,
    internalRestrictIso_hom_app_hom]
  exact CategoryTheory.Functor.id_comp_map_id
    (componentAugmentation S D K a n).pushforward _

omit [HasSheafify K AddCommGrpCat.{u}] in
/-- The comparison of the two ways of taking commutative group objects, the other way: the
identity on underlying sheaves of sets. -/
theorem mapCommGrpCompIso_inv_app_hom (M : CommGrp (Sheaf S.totalTopology (Type u))) :
    ((Functor.mapCommGrpCompIso (F := restrictSets S n)
        (G := (componentAugmentation S D K a n).pushforward)).inv.app M).hom.hom.hom =
      𝟙 (((restrictSets S n ⋙ (componentAugmentation S D K a n).pushforward).mapCommGrp.obj
        M).toGrp.toMon.X) :=
  rfl

/-- The internal form of the Stacks 04DB comparison for `g_n^{-1}`, the other way: the identity
on underlying sheaves of sets. -/
theorem internalRestrictIso_inv_app_hom (X : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    ((internalRestrictIso S n).inv.app X).hom.hom.hom =
      𝟙 (((Sites.AbelianSheaf.internalSheaf S.totalTopology ⋙
        (restrictSets S n).mapCommGrp).obj X).toGrp.toMon.X) :=
  rfl

/-- The inverse of the Stacks 04DB correction, split into the underlying morphisms of its two
factors. -/
theorem abelianComponentPushforwardIso_inv_forget_aux
    (X : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    (sheafCompose K (forget AddCommGrpCat.{u})).map
        ((abelianComponentPushforwardIso S D K a n).inv.app X) =
      (componentAugmentation S D K a n).pushforward.map
          (((internalRestrictIso S n).inv.app X).hom.hom.hom) ≫
        ((Functor.mapCommGrpCompIso (F := restrictSets S n)
            (G := (componentAugmentation S D K a n).pushforward)).inv.app
          ((Sites.AbelianSheaf.internalSheaf S.totalTopology).obj X)).hom.hom.hom :=
  rfl

/-- **The inverse of the Stacks 04DB correction is the identity on underlying sheaves of
sets.** -/
theorem abelianComponentPushforwardIso_inv_forget
    (X : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    (sheafCompose K (forget AddCommGrpCat.{u})).map
        ((abelianComponentPushforwardIso S D K a n).inv.app X) = 𝟙 _ := by
  rw [abelianComponentPushforwardIso_inv_forget_aux, internalRestrictIso_inv_app_hom,
    mapCommGrpCompIso_inv_app_hom]
  exact CategoryTheory.Functor.map_id_comp_id
    (componentAugmentation S D K a n).pushforward _

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
