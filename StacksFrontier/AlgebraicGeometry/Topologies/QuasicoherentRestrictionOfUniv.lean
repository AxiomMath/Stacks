module

public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalenceOfUniv

/-!
# Quasi-coherence along a continuous cocontinuous functor, in independent universes

Let `G : D ⥤ C` be a continuous and cocontinuous functor of sites, with the object and morphism
universes of `C` and `D` independent, and let `φ` be an isomorphism from a sheaf of rings `S` on
`D` to the restriction along `G` of a sheaf of rings `R` on `C`. This file shows that the
restriction along `G` of a quasi-coherent sheaf of `R`-modules is a quasi-coherent sheaf of
`S`-modules. The module universe is `max a a' b b' r m`, so that a global presentation on either
site lives in that one universe.

## Main results

* `Stacks.SheafOfModules.SiteTransport.hasGlobalPresentation_pushforward_ofUniv`: restriction
  along an isomorphism of structure sheaves whose restriction functor preserves colimits carries
  a global presentation to a global presentation.
* `Stacks.SheafOfModules.SiteTransport.over_pushforward_eq`: the restriction to `Y` of the
  restriction of a module along `G` is its restriction to `G.obj Y`, restricted along the
  localization of `G` at `Y`.
* `Stacks.SheafOfModules.SiteTransport.hasGlobalPresentation_over_pushforward`: a global
  presentation of the restriction of a module to `G.obj Y` gives one of the restriction, to `Y`,
  of the restriction of that module along `G`.
* `Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv`: the
  restriction of a quasi-coherent sheaf of modules along a continuous cocontinuous functor and an
  isomorphism of structure sheaves is quasi-coherent.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.SiteTransport

/-- **A global presentation is carried by restriction along an isomorphism of structure
sheaves** whose restriction functor on modules preserves colimits, for two sites in independent
object and morphism universes. -/
theorem hasGlobalPresentation_pushforward_ofUniv.{a, b, a', b', r, m}
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {D : Type a'} [Category.{b'} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{r}}
    {G : D ⥤ C} [G.IsContinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} K J).obj R) (hφ : IsIso φ)
    (hcol : PreservesColimitsOfSize.{max a a' b b' r m, max a a' b b' r m}
      (SheafOfModules.pushforward.{max a a' b b' r m} φ))
    (M : SheafOfModules.{max a a' b b' r m} R)
    (h : M.HasGlobalPresentation) :
    ((SheafOfModules.pushforward.{max a a' b b' r m} φ).obj M).HasGlobalPresentation := by
  have _ := hφ
  have _ := hcol
  have hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit φ) := by
    have : IsIso ((sheafToPresheaf K AddCommGrpCat.{r}).map
        ((SheafOfModules.toSheaf S).map (SheafOfModules.unitToPushforwardObjUnit φ))) := by
      change IsIso (Functor.whiskerRight φ.hom (forget₂ RingCat.{r} AddCommGrpCat.{r}))
      infer_instance
    have : IsIso ((SheafOfModules.toSheaf S).map
        (SheafOfModules.unitToPushforwardObjUnit φ)) :=
      isIso_of_reflects_iso _ (sheafToPresheaf K AddCommGrpCat.{r})
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf S)
  let F := SheafOfModules.pushforward.{max a a' b b' r m} φ
  let _ : F.PreservesZeroMorphisms := ⟨fun _ _ => by ext X x; rfl⟩
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{a, b, r, r,
      max a a' b b' r m} (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{a', b', r, r, max a a' b b' r m}
        (SheafOfModules.unit S) :=
    pushforwardUliftIso_ofUniv.{a, b, a', b', r, r, max a a' b b' r m} φ
        (SheafOfModules.unit R) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{a', b', r, r, max a a' b b' r m}
        (asIso (SheafOfModules.unitToPushforwardObjUnit φ)).symm
  exact hasGlobalPresentation_map_ofUniv.{a, b, a', b', r, max r m} M (F₀ := F) (F := F)
    hη₁ (uliftForPresentationBalancedIso.{a, b, a', b', r, m} F M) h

/-- The restriction to `Y` of the restriction of a sheaf of modules along a continuous functor
`G` is the restriction, along the localization of `G` at `Y`, of the restriction to `G.obj Y`.
-/
theorem over_pushforward_eq.{a, b, a', b', r, m}
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {D : Type a'} [Category.{b'} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{r}}
    (G : D ⥤ C) [G.IsContinuous K J]
    [∀ X : D, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} K J).obj R)
    (M : SheafOfModules.{max a a' b b' r m} R) (Y : D) :
    ((SheafOfModules.pushforward.{max a a' b b' r m} φ).obj M).over Y =
      (SheafOfModules.pushforward.{max a a' b b' r m} (F := Over.post (X := Y) G)
        (S := S.over Y) (R := R.over (G.obj Y))
        (((Over.forget Y).sheafPushforwardContinuous RingCat.{r} (K.over Y) K).map φ)).obj
        (M.over (G.obj Y)) := rfl

/-- **A global presentation of the restriction to `G.obj Y` is carried to one of the restriction
to `Y`** of the restriction of the module along `G`. -/
theorem hasGlobalPresentation_over_pushforward.{a, b, a', b', r, m}
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {D : Type a'} [Category.{b'} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{r}}
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    [∀ X : D, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} K J).obj R) (hφ : IsIso φ)
    (M : SheafOfModules.{max a a' b b' r m} R) (Y : D)
    (h : (M.over (G.obj Y)).HasGlobalPresentation) :
    (((SheafOfModules.pushforward.{max a a' b b' r m} φ).obj M).over Y).HasGlobalPresentation := by
  have _ := hφ
  have _ : HasSheafify (J.over (G.obj Y)) AddCommGrpCat.{max a a' b b' r m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max a a' b b' r m, b, max a b}
      (J.over (G.obj Y))
  have _ : (J.over (G.obj Y)).WEqualsLocallyBijective AddCommGrpCat.{max a a' b b' r m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{
      max a a' b b' r m, max a b, b} (J.over (G.obj Y))
  have _ : HasSheafify (K.over Y) AddCommGrpCat.{max a a' b b' r m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max a a' b b' r m, b', max a' b'} (K.over Y)
  have _ : (K.over Y).WEqualsLocallyBijective AddCommGrpCat.{max a a' b b' r m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{
      max a a' b b' r m, max a' b', b'} (K.over Y)
  have hcol : PreservesColimitsOfSize.{max a a' b b' r m, max a a' b b' r m}
      (SheafOfModules.pushforward.{max a a' b b' r m} (F := Over.post (X := Y) G)
        (S := S.over Y) (R := R.over (G.obj Y))
        (((Over.forget Y).sheafPushforwardContinuous RingCat.{r} (K.over Y) K).map φ)) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (Over.post (X := Y) G) _
  rw [over_pushforward_eq.{a, b, a', b', r, m} G φ M Y]
  exact hasGlobalPresentation_pushforward_ofUniv.{max a b, b, max a' b', b', r, m}
    (C := Over (G.obj Y)) (R := R.over (G.obj Y)) (D := Over Y) (S := S.over Y)
    (G := Over.post (X := Y) G)
    (((Over.forget Y).sheafPushforwardContinuous RingCat.{r} (K.over Y) K).map φ)
    (Functor.map_isIso _ φ) hcol (M.over (G.obj Y)) h

/-- **The restriction of a quasi-coherent sheaf of modules along a continuous cocontinuous
functor and an isomorphism of structure sheaves is quasi-coherent**, for two sites in independent
object and morphism universes. -/
theorem isQuasicoherentOnSite_pushforward_ofUniv.{a, b, a', b', r, m}
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {D : Type a'} [Category.{b'} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{r}}
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    [∀ X : D, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} K J).obj R) (hφ : IsIso φ)
    (M : SheafOfModules.{max a a' b b' r m} R) (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{max a a' b b' r m} φ).obj M).IsQuasicoherentOnSite := by
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation _
    (I := {Y : D // (((SheafOfModules.pushforward.{max a a' b b' r m} φ).obj M).over
      Y).HasGlobalPresentation})
    (W := fun i => i.1) (fun X => ?_) (fun i => i.2)
  obtain ⟨I, V, f, hcover, hV⟩ := hM.locally_hasGlobalPresentation (G.obj X)
  refine K.superset_covering (fun Y g hg => ?_) (G.cover_lift K J hcover)
  obtain ⟨i, c, -⟩ := (Sieve.mem_ofArrows_iff V f (G.map g)).mp hg
  exact ⟨⟨Y, hasGlobalPresentation_over_pushforward.{a, b, a', b', r, m} G φ hφ M Y
    (Stacks.SheafOfModules.hasGlobalPresentation_overMap M c (hV i))⟩, ⟨𝟙 Y⟩⟩

end Stacks.SheafOfModules.SiteTransport

end
