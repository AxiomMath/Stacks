module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Left Kan extensions and postcomposition

A pointwise left Kan extension is computed by colimits over the comma categories
`CostructuredArrow L Y`, so a functor `G` which preserves colimits of those shapes carries a
pointwise left Kan extension of `F` along `L` to a pointwise left Kan extension of `F ⋙ G`
along `L`. Consequently the canonical comparison `Lan_L(F ⋙ G) ⟶ (Lan_L F) ⋙ G` is an
isomorphism for such a `G`.

## Main definitions

* `CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionAtPostcompose₂` and
  `CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionPostcompose₂` transport the
  pointwise left Kan extension property along `CategoryTheory.Functor.LeftExtension.postcompose₂`.
* `CategoryTheory.Functor.lanCompRightIso` is the isomorphism
  `L.lan.obj (F ⋙ G) ≅ L.lan.obj F ⋙ G`.

## Main results

* `CategoryTheory.Functor.isLeftKanExtension_comp_right`: if `(F', α)` is a left Kan extension
  of `F` along `L`, then `(F' ⋙ G, α ⋙ G)` is a left Kan extension of `F ⋙ G` along `L`.
* `CategoryTheory.Functor.lanUnit_app_whiskerLeft_lanCompRightIso_hom` characterises
  `lanCompRightIso` by its compatibility with the units of the two left Kan extensions.

## Implementation notes

The hypothesis is `PreservesColimitsOfShape (CostructuredArrow L Y) G` for every `Y`, which is
what the pointwise description of the Kan extension consumes directly; in the intended
application `L` is representably flat, so these shapes are filtered and preservation of
filtered colimits suffices.

## References

* [Stacks Project, Tag 002P](https://stacks.math.columbia.edu/tag/002P)
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} {H : Type u₃} {H' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H] [Category.{v₄} H']

namespace LeftExtension

variable {L : C ⥤ D} {F : C ⥤ H} (E : LeftExtension L F) (G : H ⥤ H')

/-- If `G` preserves colimits indexed by `CostructuredArrow L Y` and `E` is a pointwise left
Kan extension at `Y`, then so is the left extension obtained from `E` by postcomposing with
`G`. -/
noncomputable def isPointwiseLeftKanExtensionAtPostcompose₂ (Y : D)
    [PreservesColimitsOfShape (CostructuredArrow L Y) G]
    (h : E.IsPointwiseLeftKanExtensionAt Y) :
    ((LeftExtension.postcompose₂ L F G).obj E).IsPointwiseLeftKanExtensionAt Y :=
  IsColimit.ofIsoColimit (isColimitOfPreserves G h)
    (Cocone.ext (Iso.refl _) (fun _ => by simp [LeftExtension.postcompose₂]))

/-- If `G` preserves colimits indexed by the comma categories `CostructuredArrow L Y` and `E` is
a pointwise left Kan extension, then so is the left extension obtained from `E` by
postcomposing with `G`. -/
noncomputable def isPointwiseLeftKanExtensionPostcompose₂
    [∀ Y : D, PreservesColimitsOfShape (CostructuredArrow L Y) G]
    (h : E.IsPointwiseLeftKanExtension) :
    ((LeftExtension.postcompose₂ L F G).obj E).IsPointwiseLeftKanExtension :=
  fun Y => E.isPointwiseLeftKanExtensionAtPostcompose₂ G Y (h Y)

end LeftExtension

variable {L : C ⥤ D} {F : C ⥤ H}

/-- Postcomposing a left Kan extension with a functor preserving the colimits which compute it
again gives a left Kan extension. -/
lemma isLeftKanExtension_comp_right (F' : D ⥤ H) (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] (G : H ⥤ H') [HasPointwiseLeftKanExtension L F]
    [∀ Y : D, PreservesColimitsOfShape (CostructuredArrow L Y) G] :
    (F' ⋙ G).IsLeftKanExtension
      (whiskerRight α G ≫ (Functor.associator L F' G).hom) :=
  ((LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
      (LeftExtension.postcompose₂ObjMkIso G α))
    ((LeftExtension.mk F' α).isPointwiseLeftKanExtensionPostcompose₂ G
      (isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α))).isLeftKanExtension

section

variable (L F) (G : H ⥤ H') [HasPointwiseLeftKanExtension L F]
  [∀ Y : D, PreservesColimitsOfShape (CostructuredArrow L Y) G]
  [∀ P : C ⥤ H, HasLeftKanExtension L P] [∀ P : C ⥤ H', HasLeftKanExtension L P]

/-- The canonical isomorphism `Lan_L(F ⋙ G) ≅ (Lan_L F) ⋙ G`, for a functor `G` preserving the
colimits which compute the left Kan extension of `F` along `L`. -/
noncomputable def lanCompRightIso : L.lan.obj (F ⋙ G) ≅ L.lan.obj F ⋙ G :=
  have := isLeftKanExtension_comp_right (L := L) (F := F) (L.lan.obj F) (L.lanUnit.app F) G
  leftKanExtensionUnique _ (L.lanUnit.app (F ⋙ G)) _
    (whiskerRight (L.lanUnit.app F) G ≫ (Functor.associator L (L.lan.obj F) G).hom)

/-- The isomorphism `lanCompRightIso` is the unique morphism of left extensions under
`F ⋙ G`. -/
lemma lanUnit_app_whiskerLeft_lanCompRightIso_hom :
    L.lanUnit.app (F ⋙ G) ≫ whiskerLeft L (lanCompRightIso L F G).hom =
      whiskerRight (L.lanUnit.app F) G ≫ (Functor.associator L (L.lan.obj F) G).hom :=
  have := isLeftKanExtension_comp_right (L := L) (F := F) (L.lan.obj F) (L.lanUnit.app F) G
  by simp [lanCompRightIso]

/-- The componentwise form of `lanUnit_app_whiskerLeft_lanCompRightIso_hom`. -/
lemma lanUnit_app_app_lanCompRightIso_hom_app (X : C) :
    (L.lanUnit.app (F ⋙ G)).app X ≫ (lanCompRightIso L F G).hom.app (L.obj X) =
      G.map ((L.lanUnit.app F).app X) := by
  have h := NatTrans.congr_app (lanUnit_app_whiskerLeft_lanCompRightIso_hom L F G) X
  simpa using h

end

end CategoryTheory.Functor
