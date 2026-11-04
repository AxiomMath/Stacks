module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentedPresheaf
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictProduct
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Representability of restrictions of presheaves to slices

For a morphism `f : V ⟶ U` of a category `C` and a presheaf `F` on `C/U`, write `F|_V` for its
restriction `(Over.map f).op ⋙ F` to `C/V`. This file collects the representability statements
about `F|_V` used to descend schemes along base changes:

* `F|_V` is representable when `F` is, provided `C` has pullbacks along `f`;
* `F|_V` is representable if and only if the product of `F` with the representable presheaf of
  `(V --f--> U)` is representable;
* restricting along a composite is restricting twice, so a section `s` of `f` lets one recover `F`
  from `F|_V`.

## Main results

* `CategoryTheory.OverShriek.isRepresentable_relocalizeRestrict`
* `CategoryTheory.OverShriek.isRepresentable_relocalizeRestrict_iff_prod`
* `CategoryTheory.OverShriek.isRepresentable_of_isRepresentable_relocalizeRestrict_of_section`
* `CategoryTheory.OverShriek.isRepresentable_relocalizeRestrict_comp`
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C]

/-- **Restriction preserves representability.** If `F` is represented by `X` over `U` and `C` has
pullbacks along `f`, then `F|_V` is represented by the pullback of `X` along `f`. -/
theorem isRepresentable_relocalizeRestrict {U V : C} (f : V ⟶ U) [HasPullbacksAlong f]
    (F : (Over U)ᵒᵖ ⥤ Type v) [F.IsRepresentable] :
    ((relocalizeRestrict f).obj F).IsRepresentable :=
  Functor.IsRepresentable.mk'
    (((Over.mapPullbackAdj f).compYonedaIso.app F.reprX) ≪≫
      (relocalizeRestrict f).mapIso F.reprW)

/-- Restricting along a composite is restricting twice. -/
noncomputable def relocalizeRestrictCompIso {U V W : C} (f : W ⟶ V) (g : V ⟶ U)
    (F : (Over U)ᵒᵖ ⥤ Type v) :
    (relocalizeRestrict f).obj ((relocalizeRestrict g).obj F) ≅
      (relocalizeRestrict (f ≫ g)).obj F :=
  Functor.isoWhiskerRight ((Functor.opComp (Over.map f) (Over.map g)).symm ≪≫
    NatIso.op (Over.mapComp f g)) F

/-- Restricting along a composite of restrictions preserves representability. -/
theorem isRepresentable_relocalizeRestrict_comp {U V W : C} (f : W ⟶ V) (g : V ⟶ U)
    [HasPullbacksAlong f] (F : (Over U)ᵒᵖ ⥤ Type v)
    [((relocalizeRestrict g).obj F).IsRepresentable] :
    ((relocalizeRestrict (f ≫ g)).obj F).IsRepresentable := by
  have := isRepresentable_relocalizeRestrict f ((relocalizeRestrict g).obj F)
  exact isRepresentable_of_natIso _ (relocalizeRestrictCompIso f g F)

/-- **A section recovers the presheaf.** If `s : U ⟶ V` is a section of `f : V ⟶ U`, `C` has
pullbacks along `s` and `F|_V` is representable, then `F` is representable. -/
theorem isRepresentable_of_isRepresentable_relocalizeRestrict_of_section {U V : C}
    (f : V ⟶ U) (s : U ⟶ V) (hs : s ≫ f = 𝟙 U) [HasPullbacksAlong s]
    (F : (Over U)ᵒᵖ ⥤ Type v) [((relocalizeRestrict f).obj F).IsRepresentable] :
    F.IsRepresentable := by
  have := isRepresentable_relocalizeRestrict_comp s f F
  rw [hs] at this
  have : ((Over.map (𝟙 U)).op ⋙ F).IsRepresentable := this
  exact isRepresentable_of_natIso _
    (Functor.isoWhiskerRight ((NatIso.op (Over.mapId U)).symm ≪≫ Functor.opId _) F ≪≫
      Functor.leftUnitor F)

/-- **Restriction is representable iff the product with `h_{(V →f U)}` is.** -/
theorem isRepresentable_relocalizeRestrict_iff_prod {U V : C} (f : V ⟶ U)
    (F : (Over U)ᵒᵖ ⥤ Type v) [HasBinaryProduct (yoneda.obj (Over.mk f)) F] :
    ((relocalizeRestrict f).obj F).IsRepresentable ↔
      (yoneda.obj (Over.mk f) ⨯ F).IsRepresentable := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · exact Functor.IsRepresentable.mk'
      (((relocalizeYonedaIso f).app ((relocalizeRestrict f).obj F).reprX).symm ≪≫
        (relocalizePresheafFunctor f).mapIso ((relocalizeRestrict f).obj F).reprW ≪≫
        relocalizeRestrictIsoProduct f F)
  · obtain ⟨e⟩ := nonempty_iso_yoneda_of_relocalize f ((relocalizeRestrict f).obj F)
      (ι := relocalizeRestrictIsoProduct f F ≪≫ (yoneda.obj (Over.mk f) ⨯ F).reprW.symm)
    exact Functor.IsRepresentable.mk' e.symm

end CategoryTheory.OverShriek
