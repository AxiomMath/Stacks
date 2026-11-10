module

public import Mathlib.Algebra.Category.MonCat.Shrink
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.Logic.Small.Set
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The inverse image of a morphism of sites is exact in every universe of sections

Stacks 00X1 asks of a morphism of sites `f : (D, K) → (C, J)`, given by a continuous functor
`u : C ⥤ D`, that the induced functor `u_s = f⁻¹` on sheaves of **sets** be exact. On a small
site, `Functor.IsMorphismOfSites` records that for sheaves of `Type u`-valued sets, `u` being
the site universe. Consumers, however, apply `f⁻¹` to sheaves whose sections live in a larger
universe — the systems of abelian sheaves of Stacks 0EXZ are indexed by a category whose own
universes need not be bounded by the site's. This file shows the condition does not depend on
that choice: left exactness of `f⁻¹` at `Type u` gives left exactness at `Type (max u w)` for
every `w`.

The argument is the standard reduction to small presheaves. Write `f⁻¹` as the left Kan
extension along `u.op` followed by sheafification. Every `Type (max u w)`-valued presheaf on a
`Type u`-small category is the filtered colimit of its `u`-small subfunctors
(`smallSubfunctorIsColimit`), the composite preserves all colimits, and finite limits commute
with filtered colimits in a category of sheaves, so it is enough to preserve finite limits of
diagrams of `u`-small presheaves (`preservesFiniteLimits_of_small`). Such a diagram is the
`uliftFunctor`-image of a diagram of `Type u`-valued presheaves
(`preservesFiniteLimits_of_comp_ulift`), on which the hypothesis applies.

## Main results

* `CategoryTheory.Functor.preservesFiniteLimits_sheafPullback_largeSections`: the inverse image
  of a morphism of sites is left exact on sheaves with sections in any larger universe.
* `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoiLargeSections`: consequently a
  morphism of sites induces a morphism of topoi between the categories of sheaves of sets with
  sections in any larger universe, not only in the site universe as in Stacks 00XC.
* `CategoryTheory.Limits.preservesColimitsOfShape_lim_of_colim`: when colimits of shape `J`
  commute with limits of shape `I`, the functor `lim` preserves colimits of shape `J`. This is
  the half of "filtered colimits commute with finite limits" that Mathlib states only for
  `colim`.

## Implementation notes

The reduction is carried out for the explicit construction
`Functor.sheafPullbackConstruction.sheafPullback`, the left Kan extension followed by
sheafification, and transported to the abstract `Functor.sheafPullback` — the chosen left
adjoint of restriction, which is the form in which consumers state the hypothesis — by Mathlib's
`Functor.sheafPullbackConstruction.sheafPullbackIso`.

The `local instance` priorities before the main theorem pin the instances the statement is
elaborated against. Without them the `UnivLE` side conditions of
`Limits.PreservesColimitsOfSize` are postponed as universe constraints which cannot be
discharged once the declaration abstracts its universe parameters.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w t z q

namespace CategoryTheory.Limits

/-- If colimits of shape `J` commute with limits of shape `I`, then `lim : (I ⥤ C) ⥤ C`
preserves colimits of shape `J`. Mathlib records the statement for `colim`; this is the
same fact read off the other functor. -/
theorem preservesColimitsOfShape_lim_of_colim
    {C : Type t} [Category.{z} C] {I : Type*} [Category I]
    {J : Type*} [Category J] [HasLimitsOfShape I C] [HasColimitsOfShape J C]
    [PreservesLimitsOfShape I (colim : (J ⥤ C) ⥤ C)] :
    PreservesColimitsOfShape J (lim : (I ⥤ C) ⥤ C) := by
  constructor
  intro D
  let e : colimit (D ⋙ lim) ≅ limit (colimit D) :=
    HasColimit.isoOfNatIso (limitFlipIsoCompLim D).symm ≪≫ colimitLimitIso D.flip
  have he : e.hom = colimit.post D lim := by
    refine colimit.hom_ext fun j => limit.hom_ext fun i => ?_
    have key : colimit.ι (limit D.flip) j ≫ (colimitLimitIso D.flip).hom ≫
        limit.π (colimit D) i = (limit.π D.flip i).app j ≫ (colimit.ι D j).app i :=
      ι_colimitLimitIso_limit_π D.flip j i
    simp only [e, Iso.trans_hom, HasColimit.ι_isoOfNatIso_hom_assoc,
      Iso.symm_hom, Category.assoc]
    rw [key]
    simp
  have : IsIso (colimit.post D lim) := he ▸ e.isIso_hom
  exact preservesColimit_of_isIso_post lim D

end CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The `u`-small subfunctors of a `Type (max u w)`-valued functor on a `Type u`-small
category. -/
private abbrev SmallSubfunctor {C : Type u} [Category.{u} C]
    (F : C ⥤ Type (max u w)) := { S : Subfunctor F // ∀ c, Small.{u} (S.obj c) }

private abbrev smallSubfunctorSemilatticeSup {C : Type u} [Category.{u} C]
    (F : C ⥤ Type (max u w)) : SemilatticeSup (SmallSubfunctor F) where
  sup S T := ⟨S.val ⊔ T.val, fun c => by
    have := S.property c
    have := T.property c
    exact small_union _ _⟩
  le_sup_left := fun S T => show S.val ≤ S.val ⊔ T.val from le_sup_left
  le_sup_right := fun S T => show T.val ≤ S.val ⊔ T.val from le_sup_right
  sup_le := fun S T R hS hT => show S.val ⊔ T.val ≤ R.val from sup_le hS hT

attribute [local instance] smallSubfunctorSemilatticeSup

private abbrev smallSubfunctorOrderBot {C : Type u} [Category.{u} C]
    (F : C ⥤ Type (max u w)) : OrderBot (SmallSubfunctor F) where
  bot := ⟨⊥, fun c => inferInstanceAs (Small.{u} (∅ : Set (F.obj c)))⟩
  bot_le := fun S => show (⊥ : Subfunctor F) ≤ S.val from bot_le

attribute [local instance] smallSubfunctorOrderBot

/-- The diagram of `u`-small subfunctors of a `Type (max u w)`-valued functor. -/
private def smallSubfunctorDiagram {C : Type u} [Category.{u} C]
    (F : C ⥤ Type (max u w)) : SmallSubfunctor F ⥤ C ⥤ Type (max u w) where
  obj S := S.val.toFunctor
  map h := Subfunctor.homOfLe (leOfHom h)

/-- The cocone on the diagram of `u`-small subfunctors with vertex the functor itself. -/
private def smallSubfunctorCocone {C : Type u} [Category.{u} C]
    (F : C ⥤ Type (max u w)) : Cocone (smallSubfunctorDiagram F) where
  pt := F
  ι := { app S := S.val.ι }

/-- Every section of a `Type (max u w)`-valued functor lies in a `u`-small subfunctor, namely
the one generated by it. -/
private theorem smallSubfunctor_cover {C : Type u} [Category.{u} C]
    (F : C ⥤ Type (max u w)) (c : C) (x : F.obj c) :
    ∃ S : SmallSubfunctor F, x ∈ S.val.obj c := by
  let S : Subfunctor F :=
    { obj d := Set.range (fun f : c ⟶ d => F.map f x)
      map f := by
        rintro y ⟨g, rfl⟩
        exact ⟨g ≫ f, by simp⟩ }
  exact ⟨⟨S, fun d => small_range _⟩, 𝟙 c, by simp⟩

/-- A `Type (max u w)`-valued functor on a `Type u`-small category is the filtered colimit of
its `u`-small subfunctors. -/
private noncomputable def smallSubfunctorIsColimit {C : Type u} [Category.{u} C]
    (F : C ⥤ Type (max u w)) : IsColimit (smallSubfunctorCocone F) := by
  apply evaluationJointlyReflectsColimits
  intro c
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨S, hx⟩ := smallSubfunctor_cover F c x
    exact ⟨S, ⟨x, hx⟩, rfl⟩
  · intro S x y h
    exact ⟨S, 𝟙 _, congrArg _ (Subtype.ext h)⟩

/-- A natural transformation between functors preserving filtered colimits is invertible as soon
as it is invertible at every `u`-small functor. -/
private theorem isIso_app_of_small {C : Type u} [Category.{u} C]
    {E : Type t} [Category.{z} E]
    (L L' : (C ⥤ Type (max u w)) ⥤ E)
    [PreservesFilteredColimitsOfSize.{max u w, max u w} L]
    [PreservesFilteredColimitsOfSize.{max u w, max u w} L']
    (α : L ⟶ L')
    (h : ∀ (F : C ⥤ Type (max u w)) [∀ c, Small.{u} (F.obj c)], IsIso (α.app F))
    (F : C ⥤ Type (max u w)) : IsIso (α.app F) := by
  have : IsIso (Functor.whiskerLeft (smallSubfunctorDiagram F) α) := by
    have : ∀ S, IsIso ((Functor.whiskerLeft (smallSubfunctorDiagram F) α).app S) := by
      intro S
      have : ∀ c, Small.{u} (S.val.toFunctor.obj c) := S.property
      change IsIso (α.app S.val.toFunctor)
      exact h _
    exact NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit (smallSubfunctorDiagram F) α
    (smallSubfunctorCocone F) (smallSubfunctorIsColimit F)

/-- The comparison of a limit with the limit of the image, natural in the diagram. -/
private noncomputable def limitComparisonNatTrans {C : Type*} [Category C] {E : Type*}
    [Category E] (I : Type*) [Category I] [HasLimitsOfShape I C] [HasLimitsOfShape I E]
    (G : C ⥤ E) : lim ⋙ G ⟶ (Functor.whiskeringRight I C E).obj G ⋙ lim where
  app D := limit.post D G
  naturality {X Y} f := by
    apply limit.hom_ext
    intro i
    dsimp
    simp only [limit.post_π, Functor.whiskerRight_app, limMap_π, Category.assoc,
      limit.post_π_assoc, ← G.map_comp]

/-- A colimit-preserving functor out of `Type (max u w)`-valued presheaves on a `Type u`-small
category is left exact as soon as it preserves the finite limits of diagrams of `u`-small
presheaves. -/
private theorem preservesFiniteLimits_of_small
    {C : Type u} [Category.{u} C] {E : Type t} [Category.{z} E]
    [HasFiniteLimits E] [HasColimitsOfSize.{max u w, max u w} E]
    (G : (C ⥤ Type (max u w)) ⥤ E)
    [PreservesColimitsOfSize.{max u w, max u w} G]
    (he : ∀ (K : Type (max u w)) [Category.{max u w} K] [IsFiltered K],
      PreservesFiniteLimits (colim : (K ⥤ E) ⥤ E))
    (h : ∀ (I : Type) [SmallCategory I] [FinCategory I]
      (F : I ⥤ C ⥤ Type (max u w)) [∀ i c, Small.{u} ((F.obj i).obj c)],
      PreservesLimit F G) : PreservesFiniteLimits G := by
  constructor
  intro I _ _
  have : PreservesFilteredColimitsOfSize.{max u w, max u w}
      (lim : (I ⥤ C ⥤ Type (max u w)) ⥤ _) := ⟨fun _ _ _ =>
    preservesColimitsOfShape_lim_of_colim⟩
  have : PreservesFilteredColimitsOfSize.{max u w, max u w}
      (lim : (I ⥤ E) ⥤ E) := ⟨fun K _ _ =>
    have := he K
    preservesColimitsOfShape_lim_of_colim⟩
  constructor
  intro F
  have : PreservesColimitsOfSize.{max u w, max u w}
      (Functor.curry : (I × C ⥤ Type (max u w)) ⥤ _) :=
    Functor.currying.symm.toAdjunction.leftAdjoint_preservesColimits
  let α := Functor.whiskerLeft (Functor.curry : (I × C ⥤ Type (max u w)) ⥤ _)
    (limitComparisonNatTrans I G)
  have : IsIso (α.app (Functor.uncurry.obj F)) := by
    apply isIso_app_of_small (C := I × C)
      (Functor.curry ⋙ (lim : (I ⥤ C ⥤ Type (max u w)) ⥤ _) ⋙ G)
      (Functor.curry ⋙ (Functor.whiskeringRight I _ _).obj G ⋙ lim) α
    intro P hP
    have : ∀ i c, Small.{u} (((Functor.curry.obj P).obj i).obj c) := fun i c => hP (i, c)
    have := h I (Functor.curry.obj P)
    exact inferInstanceAs (IsIso (limit.post (Functor.curry.obj P) G))
  have : IsIso (limit.post (Functor.curry.obj (Functor.uncurry.obj F)) G) :=
    ‹IsIso (α.app (Functor.uncurry.obj F))›
  have : PreservesLimit (Functor.curry.obj (Functor.uncurry.obj F)) G :=
    preservesLimit_of_isIso_post G _
  let e : Functor.curry.obj (Functor.uncurry.obj F) ≅ F :=
    (Functor.currying.unitIso.app F).symm
  exact preservesLimit_of_iso_diagram G e

/-- A colimit-preserving functor out of `Type (max u w)`-valued presheaves on a `Type u`-small
category is left exact as soon as its restriction along `uliftFunctor` is. -/
private theorem preservesFiniteLimits_of_comp_ulift
    {C : Type u} [Category.{u} C] {E : Type t} [Category.{z} E]
    [HasFiniteLimits E] [HasColimitsOfSize.{max u w, max u w} E]
    (G : (C ⥤ Type (max u w)) ⥤ E)
    [PreservesColimitsOfSize.{max u w, max u w} G]
    [PreservesFiniteLimits ((Functor.whiskeringRight C (Type u) (Type (max u w))).obj
      uliftFunctor.{w, u} ⋙ G)]
    (he : ∀ (K : Type (max u w)) [Category.{max u w} K] [IsFiltered K],
      PreservesFiniteLimits (colim : (K ⥤ E) ⥤ E)) : PreservesFiniteLimits G := by
  apply preservesFiniteLimits_of_small G he
  intro I _ _ F hF
  let P := Functor.uncurry.obj F
  have : FunctorToTypes.Small.{u} P := fun p => hF p.1 p.2
  let P₀ := FunctorToTypes.shrink.{u} P
  let F₀ := Functor.curry.obj P₀
  let W := (Functor.whiskeringRight C (Type u) (Type (max u w))).obj uliftFunctor.{w, u}
  let e₀ : P₀ ⋙ uliftFunctor.{w, u} ≅ P := NatIso.ofComponents
    (fun p => (Equiv.ulift.trans (equivShrink (P.obj p)).symm).toIso)
    (by
      intro p q f
      ext x
      change (equivShrink (P.obj q)).symm
        ((equivShrink (P.obj q)) (P.map f ((equivShrink (P.obj p)).symm x.down))) = _
      simp only [Equiv.symm_apply_apply]
      rfl)
  let e : F₀ ⋙ W ≅ F := Functor.curry.mapIso e₀ ≪≫ (Functor.currying.unitIso.app F).symm
  have : PreservesLimit (F₀ ⋙ W) G :=
    preservesLimit_of_preserves_limit_cone (isLimitOfPreserves W (limit.isLimit F₀))
      (isLimitOfPreserves (W ⋙ G) (limit.isLimit F₀))
  exact preservesLimit_of_iso_diagram G e

attribute [local instance 10000] Sheaf.instHasColimitsOfSize Sheaf.instHasColimitsOfShape
  Limits.Types.instPreservesColimitsOfSizeUliftFunctor
  PreservesColimitsOfSize.preservesColimitsOfShape PreservesColimitsOfShape.preservesColimit
  GrothendieckTopology.instPreservesSheafification
  preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise
  sheafPullbackConstruction.instIsRightAdjointSheafSheafPushforwardContinuousOfHasWeakSheafify

/-- **Exactness of the inverse image of a morphism of sites does not depend on the universe of
the sections.** For a morphism of sites `f : (D, K) → (C, J)` given by `a : C ⥤ D`, Stacks 00X1
asks `f⁻¹` to be left exact on `Type u`-valued sheaves, `u` being the universe of the two sites;
it is then left exact on `Type (max u w)`-valued sheaves for every `w`. -/
theorem preservesFiniteLimits_sheafPullback_largeSections
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {a : C ⥤ D} (h : a.IsMorphismOfSites J K) :
    letI := h.isContinuous
    PreservesFiniteLimits (a.sheafPullback (Type (max u w)) J K) := by
  let _ := h.isContinuous
  let G₀ := a.op.lan ⋙ presheafToSheaf K (Type u)
  let G := a.op.lan ⋙ presheafToSheaf K (Type (max u w))
  have : PreservesFiniteLimits G₀ := by
    let _ := h.preservesFiniteLimits
    let e : presheafToSheaf J (Type u) ⋙ a.sheafPullback (Type u) J K ≅ G₀ :=
      ((sheafificationAdjunction J (Type u)).comp
        (a.sheafAdjunctionContinuous (Type u) J K)).leftAdjointUniq
        ((a.op.lanAdjunction (Type u)).comp (sheafificationAdjunction K (Type u)))
    exact preservesFiniteLimits_of_natIso e
  let W := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max u w))).obj uliftFunctor.{w, u}
  let S := sheafCompose K uliftFunctor.{w, u}
  have : PreservesFiniteLimits S := by
    have : PreservesFiniteLimits (S ⋙ sheafToPresheaf K (Type (max u w))) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf K (Type u) ⋙
        (Functor.whiskeringRight Dᵒᵖ (Type u) (Type (max u w))).obj uliftFunctor.{w, u}))
    exact preservesFiniteLimits_of_reflects_of_preserves S (sheafToPresheaf K _)
  have (F : Cᵒᵖ ⥤ Type u) (d : Dᵒᵖ) :
      uliftFunctor.{w, u}.PreservesPointwiseLeftKanExtensionAt F a.op d :=
    Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit _ _ _ _
  have (F : Cᵒᵖ ⥤ Type u) : uliftFunctor.{w, u}.PreservesLeftKanExtension F a.op := by
    apply Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise
  let e : W ⋙ G ≅ G₀ ⋙ S :=
    Functor.isoWhiskerRight (uliftFunctor.{w, u}.lanCompIsoOfPreserves a.op).symm
      (presheafToSheaf K (Type (max u w))) ≪≫
    Functor.isoWhiskerLeft a.op.lan
      (sheafComposeNatIso K uliftFunctor.{w, u}
        (sheafificationAdjunction K (Type u)) (sheafificationAdjunction K (Type (max u w))))
  have : PreservesFiniteLimits (W ⋙ G) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesColimitsOfSize.{max u w, max u w} G :=
    ((a.op.lanAdjunction (Type (max u w))).comp
      (sheafificationAdjunction K (Type (max u w)))).leftAdjoint_preservesColimits
  have : PreservesFiniteLimits G := by
    apply preservesFiniteLimits_of_comp_ulift.{u, w} G
    intro I _ _
    have : HasExactColimitsOfShape I (Type (max u w)) := ⟨inferInstance⟩
    have : HasExactColimitsOfShape I (Dᵒᵖ ⥤ Type (max u w)) := inferInstance
    have := (sheafificationAdjunction K (Type (max u w))).hasExactColimitsOfShape I
    exact HasExactColimitsOfShape.preservesFiniteLimits
  have : PreservesFiniteLimits (sheafToPresheaf J (Type (max u w)) ⋙ G) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback a (Type (max u w)) J K) :=
    ‹PreservesFiniteLimits (sheafToPresheaf J (Type (max u w)) ⋙ G)›
  exact preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso a (Type (max u w)) J K).symm

/-- A continuous functor of small sites whose pullback of `Type q`-valued sheaves is left exact
is a morphism of topoi at that universe of sections. Stacks 00XC,
`CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi`, is the case `q` = the site
universe, where left exactness is the content of `Functor.IsMorphismOfSites`. -/
noncomputable def morphismOfTopoiOfPreservesFiniteLimits
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (a : C ⥤ D)
    [a.IsContinuous J K] [(a.sheafPushforwardContinuous (Type q) J K).IsRightAdjoint]
    (hq : PreservesFiniteLimits (a.sheafPullback (Type q) J K)) :
    MorphismOfTopoi (Sheaf K (Type q)) (Sheaf J (Type q)) where
  pushforward := a.sheafPushforwardContinuous (Type q) J K
  inverseImage := a.sheafPullback (Type q) J K
  adj := a.sheafAdjunctionContinuous (Type q) J K
  preservesFiniteLimits := hq

/-- **Stacks 00XC with sections in a larger universe.** A morphism of sites `f : (D, K) → (C, J)`
induces a morphism of topoi between the categories of `Type (max u w)`-valued sheaves, `u` being
the universe of the two sites. Stacks 00XC itself,
`CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi`, is the case `w = u`. -/
noncomputable def IsMorphismOfSites.morphismOfTopoiLargeSections
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {a : C ⥤ D} (h : a.IsMorphismOfSites J K) :
    MorphismOfTopoi (Sheaf K (Type (max u w))) (Sheaf J (Type (max u w))) :=
  haveI := h.isContinuous
  morphismOfTopoiOfPreservesFiniteLimits J K a
    (preservesFiniteLimits_sheafPullback_largeSections.{u, w} h)

end CategoryTheory.Functor

end
