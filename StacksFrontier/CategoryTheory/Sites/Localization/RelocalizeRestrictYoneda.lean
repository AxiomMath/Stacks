module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict

/-!
# Restriction of a representable presheaf along a slice functor

Let `m : A' ⟶ A` be a morphism of a category `C` and let `j^{-1}` denote restriction of
presheaves along `CategoryTheory.Over.map m`
(`CategoryTheory.OverShriek.relocalizeRestrict`). A morphism `κ : j(Z') ⟶ Z` of `C/A` induces a
morphism `h_{Z'} ⟶ j^{-1} h_Z` of presheaves on `C/A'`, sending a morphism `v : V ⟶ Z'` to
`j(v) ≫ κ`, and that morphism is an **isomorphism** as soon as `κ` is one and `Over.map m` is
fully faithful — in particular when `m` is an isomorphism.

Restriction carries the morphism of presheaves that the Yoneda lemma attaches to a section to
the morphism attached to the restricted section
(`CategoryTheory.OverShriek.restrictYonedaHom_comp_relocalizeRestrict_map`).

## Main definitions

* `CategoryTheory.OverShriek.restrictYonedaHom`: the comparison `h_{Z'} ⟶ j^{-1} h_Z`.

## Main results

* `CategoryTheory.OverShriek.isIso_restrictYonedaHom`: it is an isomorphism when `κ` is and
  `Over.map m` is fully faithful.
* `CategoryTheory.OverShriek.isIso_restrictYonedaHom_of_isPullback`: it is an isomorphism when
  the square `κ` sits in is cartesian, with no hypothesis on `m`.
* `CategoryTheory.OverShriek.restrictYonedaHom_comp_relocalizeRestrict_map`: it identifies the
  morphism named by a restricted section with the restriction of the morphism named by the
  section.
* `CategoryTheory.OverShriek.restrictYonedaHom_comp_yoneda_map` and
  `CategoryTheory.OverShriek.yoneda_map_comp_restrictYonedaHom`: it absorbs a represented
  morphism on either side, becoming the comparison attached to the composite.

## References

* [Stacks Project, Tag 001P](https://stacks.math.columbia.edu/tag/001P)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.OverShriek

universe v u

variable {C : Type u} [Category.{v} C] {A A' : C} (m : A' ⟶ A) {Z' : Over A'} {Z : Over A}

/-- The comparison `h_{Z'} ⟶ j^{-1} h_Z` attached to a morphism `κ : j(Z') ⟶ Z` of `C/A`: a
morphism `v : V ⟶ Z'` of `C/A'` is sent to `j(v) ≫ κ`, a morphism `j(V) ⟶ Z`, that is to a
section of `j^{-1} h_Z` over `V`. -/
def restrictYonedaHom (κ : (Over.map m).obj Z' ⟶ Z) :
    yoneda.obj Z' ⟶ (relocalizeRestrict m).obj (yoneda.obj Z) where
  app _ := ↾fun v => (Over.map m).map v ≫ κ
  naturality _ _ f := by
    ext v
    change (Over.map m).map (f.unop ≫ v) ≫ κ = (Over.map m).map f.unop ≫ (Over.map m).map v ≫ κ
    rw [Functor.map_comp, Category.assoc]

/-- The comparison evaluated at a morphism of `C/A'`. -/
@[simp] theorem restrictYonedaHom_app_apply (κ : (Over.map m).obj Z' ⟶ Z) (V : (Over A')ᵒᵖ)
    (v : (yoneda.obj Z').obj V) :
    (restrictYonedaHom m κ).app V v = (Over.map m).map v ≫ κ := rfl

/-- **The comparison is an isomorphism** when `κ` is an isomorphism and `CategoryTheory.Over.map m`
is fully faithful. -/
instance isIso_restrictYonedaHom [(Over.map m).Full] [(Over.map m).Faithful]
    (κ : (Over.map m).obj Z' ⟶ Z) [IsIso κ] : IsIso (restrictYonedaHom m κ) := by
  refine (NatTrans.isIso_iff_isIso_app _).mpr fun V => ?_
  refine (isIso_iff_bijective _).mpr ⟨fun v v' h => (Over.map m).map_injective
    ((cancel_mono κ).mp h), fun t => ⟨(Over.map m).preimage (t ≫ inv κ), ?_⟩⟩
  change (Over.map m).map ((Over.map m).preimage (t ≫ inv κ)) ≫ κ = t
  rw [Functor.map_preimage, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **The comparison `h_{Z'} ⟶ j^{-1} h_Z` is an isomorphism when the square `κ` sits in is
cartesian**, with no hypothesis on `m`. -/
theorem isIso_restrictYonedaHom_of_isPullback (κ : (Over.map m).obj Z' ⟶ Z)
    (h : IsPullback κ.left Z'.hom Z.hom m) : IsIso (restrictYonedaHom m κ) := by
  refine (NatTrans.isIso_iff_isIso_app _).mpr fun V => ?_
  refine (isIso_iff_bijective _).mpr ⟨fun v v' hvv => ?_, fun t => ?_⟩
  · refine Over.OverMorphism.ext (h.hom_ext ?_ ?_)
    · have hl : ((Over.map m).map v ≫ κ).left = ((Over.map m).map v' ≫ κ).left :=
        congrArg Over.Hom.left hvv
      simpa only [Over.comp_left, Over.map_map_left] using hl
    · rw [Over.w v, Over.w v']
  · have hw : t.left ≫ Z.hom = V.unop.hom ≫ m := Over.w t
    exact ⟨Over.homMk (h.lift t.left V.unop.hom hw) (h.lift_snd t.left V.unop.hom hw),
      Over.OverMorphism.ext (h.lift_fst t.left V.unop.hom hw)⟩

/-- **The comparison `h_{Z'} ⟶ j^{-1} h_Z` absorbs a represented morphism on the target.**
Following it with the restriction of the morphism of presheaves represented by `w : Z ⟶ W` is
the comparison attached to `κ ≫ w`. -/
theorem restrictYonedaHom_comp_yoneda_map {W : Over A} (κ : (Over.map m).obj Z' ⟶ Z)
    (w : Z ⟶ W) :
    restrictYonedaHom m κ ≫ (relocalizeRestrict m).map (yoneda.map w) =
      restrictYonedaHom m (κ ≫ w) := by
  ext V x
  show ((Over.map m).map x ≫ κ) ≫ w = (Over.map m).map x ≫ κ ≫ w
  rw [Category.assoc]

/-- **The comparison `h_{Z'} ⟶ j^{-1} h_Z` absorbs a represented morphism on the source.**
Preceding it with the morphism of presheaves represented by `v : Y' ⟶ Z'` is the comparison
attached to `j(v) ≫ κ`. -/
theorem yoneda_map_comp_restrictYonedaHom {Y' : Over A'} (κ : (Over.map m).obj Z' ⟶ Z)
    (v : Y' ⟶ Z') :
    yoneda.map v ≫ restrictYonedaHom m κ =
      restrictYonedaHom m ((Over.map m).map v ≫ κ) := by
  ext V x
  show (Over.map m).map (x ≫ v) ≫ κ = (Over.map m).map x ≫ (Over.map m).map v ≫ κ
  rw [Functor.map_comp, Category.assoc]

/-- **Restriction carries the morphism named by a section to the morphism named by its
restriction.** For `t` a section of `F` over `Z`, the morphism `h_{Z'} ⟶ j^{-1}F` named by the
restriction of `t` along `κ` is the comparison followed by the restriction of the morphism
`h_Z ⟶ F` named by `t`. -/
theorem restrictYonedaHom_comp_relocalizeRestrict_map (κ : (Over.map m).obj Z' ⟶ Z)
    (F : (Over A)ᵒᵖ ⥤ Type v) (t : F.obj (op Z))
    (s : ((relocalizeRestrict m).obj F).obj (op Z')) (hs : s = F.map κ.op t) :
    yonedaEquiv.symm s =
      restrictYonedaHom m κ ≫ (relocalizeRestrict m).map (yonedaEquiv.symm t) := by
  subst hs
  ext V v
  show F.map ((Over.map m).map v).op (F.map κ.op t) =
    F.map ((Over.map m).map v ≫ κ).op t
  rw [op_comp, F.map_comp]
  rfl

end CategoryTheory.OverShriek

end
