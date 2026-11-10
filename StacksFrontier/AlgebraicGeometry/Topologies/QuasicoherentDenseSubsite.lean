module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Quasi-coherence is carried by restriction along a continuous cocontinuous functor

Let `G : D ⥤ C` be a functor of sites which is both continuous and cocontinuous, and let
`φ : S ⟶ G_* R` be an *isomorphism* of sheaves of rings over it — the case of interest being the
inclusion of a dense subsite, where the structure sheaf of the subsite is by definition the
restriction of the structure sheaf of the ambient site.  Then restriction of sheaves of modules
along `φ` carries quasi-coherence: the restriction of a quasi-coherent module is quasi-coherent.

This is a form of Stacks 03DM for clause (6) of Stacks 03DL in which the comparison is a
restriction functor rather than an equivalence of sites.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_pushforward`: a global presentation is carried by
  such a restriction.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_pushforward`: **quasi-coherence is carried by such
  a restriction**, granted colimit preservation on the slices.
* `Stacks.Sites.overPost_isDenseSubsite`: the localization of a dense subsite inclusion at an
  object is again a dense subsite inclusion, no full faithfulness asked of the inclusion; its
  four conditions are `Stacks.Sites.overPost_functorPushforward_mem_iff`,
  `Stacks.Sites.overPost_isCoverDense`, `Stacks.Sites.overPost_isLocallyFull` and
  `Stacks.Sites.overPost_isLocallyFaithful`.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_restriction`: **the restriction of a quasi-coherent
  sheaf of modules along a continuous cocontinuous functor, over the restricted structure sheaf,
  is quasi-coherent.**

## Implementation notes

The colimit preservation on the slices is a hypothesis of
`isQuasicoherentOnSite_pushforward` and is discharged in
`isQuasicoherentOnSite_restriction` from `Stacks.SheafOfModules.pushforward_preservesColimits`,
whose sheafification hypotheses on the slice sites come from essential smallness.  Keeping it a
hypothesis in the first statement is what lets the second one choose those instances itself
rather than requiring them of its caller, where two candidate sheafification instances at a
still-unknown value universe would make the universe constraints unsolvable.

`Stacks.Sites.overPost_isDenseSubsite` asks no full faithfulness of the inclusion: the three local
conditions of `CategoryTheory.Functor.IsDenseSubsite` for `Over.post G` are proved from the
corresponding local conditions on `G`, each lift existing only after a further covering. The
special cocontinuous functor `v : C ⥤ C'` of [Stacks, Tag 03A2], and with it the one in [Stacks,
Tag 03CJ] and [Stacks, Tag 03CR], is only *locally* full and *locally* faithful.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m t u₁ v₁ u₂ v₂

namespace Stacks.SheafOfModules

/-- Restriction of modules commutes with raising the universe of the sections, both being
computed objectwise on sections. -/
noncomputable def pushforwardUliftForPresentationIso
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{r}} {S : Sheaf K RingCat.{r}}
    {G : D ⥤ C} [G.IsContinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} K J).obj R)
    (M : SheafOfModules.{m} R) :
    (SheafOfModules.pushforward.{max m t} φ).obj
        (SheafOfModules.uliftForPresentation.{u, v, r, m, t} M) ≅
      SheafOfModules.uliftForPresentation.{u, v, r, m, t}
        ((SheafOfModules.pushforward.{m} φ).obj M) := Iso.refl _

/-- **A global presentation is carried by restriction along an isomorphism of structure
sheaves.** -/
theorem hasGlobalPresentation_pushforward
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{r}} {S : Sheaf K RingCat.{r}}
    {G : D ⥤ C} [G.IsContinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} K J).obj R) [IsIso φ]
    (M : SheafOfModules.{m} R)
    [PreservesColimitsOfSize.{max u v r m, max u v r m}
      (SheafOfModules.pushforward.{max u v r m} φ)]
    (hM : M.HasGlobalPresentation) :
    ((SheafOfModules.pushforward.{m} φ).obj M).HasGlobalPresentation := by
  have hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit φ) := by
    have : IsIso ((sheafToPresheaf K AddCommGrpCat.{r}).map
        ((SheafOfModules.toSheaf S).map (SheafOfModules.unitToPushforwardObjUnit φ))) := by
      change IsIso (Functor.whiskerRight φ.hom (forget₂ RingCat.{r} AddCommGrpCat.{r}))
      infer_instance
    have : IsIso ((SheafOfModules.toSheaf S).map
        (SheafOfModules.unitToPushforwardObjUnit φ)) :=
      isIso_of_reflects_iso _ (sheafToPresheaf K AddCommGrpCat.{r})
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf S)
  have _ : (SheafOfModules.pushforward.{max u v r m} φ).PreservesZeroMorphisms :=
    ⟨fun _ _ => by ext X x; rfl⟩
  have η₁ : (SheafOfModules.pushforward.{max u v r m} φ).obj
        (SheafOfModules.uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit S) :=
    (pushforwardUliftForPresentationIso.{u, v, r, r, max u v m} φ (SheafOfModules.unit R)).trans
      (SheafOfModules.uliftForPresentationMapIso (asIso
        (SheafOfModules.unitToPushforwardObjUnit φ)).symm)
  exact hasGlobalPresentation_map (F₀ := SheafOfModules.pushforward.{m} φ)
    (F := SheafOfModules.pushforward.{max u v r m} φ) M η₁
    (pushforwardUliftForPresentationIso.{u, v, r, m, max u v r} φ M) hM

/-- **Quasi-coherence is carried by restriction along a continuous cocontinuous functor and an
isomorphism of structure sheaves**, granted that the restriction functors on the slices preserve
colimits. -/
theorem isQuasicoherentOnSite_pushforward
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{r}} {S : Sheaf K RingCat.{r}}
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} K J).obj R) [IsIso φ]
    [∀ X, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{max u v r m, max u v r m}
        (SheafOfModules.pushforward.{max u v r m}
          (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{r} (K.over X) K).map φ)))
    (M : SheafOfModules.{m} R) (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{m} φ).obj M).IsQuasicoherentOnSite := by
  constructor
  intro X
  obtain ⟨I, V, f, hcover, hV⟩ := hM.locally_hasGlobalPresentation (G.obj X)
  let L := Σ (Y : D), (Y ⟶ X) × (Σ i : I, G.obj Y ⟶ V i)
  refine ⟨L, fun l => l.1, fun l => l.2.1, ?_, ?_⟩
  · apply K.superset_covering _ (G.cover_lift K J hcover)
    intro Y g hg
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff V f (G.map g)).mp hg
    exact Sieve.ofArrows_mk (fun l : L => l.1) (fun l => l.2.1) ⟨Y, g, i, a⟩
  · intro l
    let G' := Over.post (X := l.1) G ⋙ Over.map l.2.2.2
    let ψ : S.over l.1 ⟶
        (G'.sheafPushforwardContinuous RingCat.{r} (K.over l.1) (J.over (V l.2.2.1))).obj
          (R.over (V l.2.2.1)) :=
      ((Over.forget l.1).sheafPushforwardContinuous RingCat.{r} (K.over l.1) K).map φ
    have _ : IsIso ψ := Functor.map_isIso _ φ
    have _ := h l.1 (V l.2.2.1) l.2.2.2
    exact hasGlobalPresentation_pushforward ψ (M.over (V l.2.2.1)) (hV l.2.2.1)

end Stacks.SheafOfModules

namespace Stacks.Sites

section OverPost

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (G : C ⥤ D) [G.IsDenseSubsite J K] (X : C)

include J K

/-- **A sieve on a slice of a dense subsite covers exactly when its image does.** -/
theorem overPost_functorPushforward_mem_iff {U : Over X} {T : Sieve U} :
    T.functorPushforward (Over.post (X := X) G) ∈ (K.over (G.obj X)) _ ↔ T ∈ (J.over X) U := by
  rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_functorPushforward_post]
  exact G.functorPushforward_mem_iff J K

/-- **A slice of a dense subsite is cover dense.** -/
theorem overPost_isCoverDense : (Over.post (X := X) G).IsCoverDense (K.over (G.obj X)) := by
  have _ : G.IsCoverDense K := Functor.IsDenseSubsite.isCoverDense J K G
  constructor
  intro Y
  rw [GrothendieckTopology.mem_over_iff]
  refine K.transitive (G.is_cover_of_isCoverDense K Y.left) _ ?_
  rintro Z h ⟨⟨W, lift, map, fac⟩⟩
  have hψ : ((G.imageSieve (map ≫ Y.hom)).functorPushforward G) ∈ K (G.obj W) :=
    (G.functorPushforward_mem_iff J K).mpr (Functor.IsDenseSubsite.imageSieve_mem J K G _)
  refine K.superset_covering ?_ (K.pullback_stable lift hψ)
  rintro Z' g ⟨W₃, c, p, ⟨d, hd⟩, hgp⟩
  refine ⟨(Over.post (X := X) G).obj (Over.mk d), Over.homMk (G.map c ≫ map) ?_, p,
    Presieve.in_coverByImage _ _, ?_⟩
  · exact (Category.assoc (G.map c) map Y.hom).trans hd.symm
  · rw [← fac, ← Category.assoc, hgp, Category.assoc]
    rfl

/-- **A slice of a dense subsite is locally full.** -/
theorem overPost_isLocallyFull : (Over.post (X := X) G).IsLocallyFull (K.over (G.obj X)) := by
  constructor
  intro U V f
  rw [overPost_functorPushforward_mem_iff (J := J) G X, GrothendieckTopology.mem_over_iff]
  refine J.transitive (Functor.IsDenseSubsite.imageSieve_mem J K G f.left) _ ?_
  rintro W₀ c₀ ⟨d₀, hd₀⟩
  have hw : f.left ≫ G.map V.hom = G.map U.hom := Over.w f
  have he : G.map (d₀ ≫ V.hom) = G.map (c₀ ≫ U.hom) := by
    rw [Functor.map_comp, Functor.map_comp, hd₀]
    exact (Category.assoc (G.map c₀) f.left (G.map V.hom)).trans
      (congrArg (fun k => G.map c₀ ≫ k) hw)
  refine J.superset_covering ?_ (Functor.IsDenseSubsite.equalizer_mem J K G _ _ he)
  intro W₁ c₁ hc₁
  simp only [Sieve.equalizer_apply] at hc₁
  have key : G.map (c₁ ≫ d₀) = G.map (c₁ ≫ c₀) ≫ f.left := by
    rw [Functor.map_comp, Functor.map_comp, hd₀]
    exact (Category.assoc (G.map c₁) (G.map c₀) f.left).symm
  exact ⟨Over.mk (c₁ ≫ c₀ ≫ U.hom), Over.homMk (c₁ ≫ c₀) (by simp), 𝟙 _,
    ⟨Over.homMk (c₁ ≫ d₀) (by simpa [Category.assoc] using hc₁), by ext; exact key⟩, by simp⟩

/-- **A slice of a dense subsite is locally faithful.** -/
theorem overPost_isLocallyFaithful :
    (Over.post (X := X) G).IsLocallyFaithful (K.over (G.obj X)) := by
  constructor
  intro U V f₁ f₂ he
  rw [overPost_functorPushforward_mem_iff (J := J) G X, GrothendieckTopology.mem_over_iff]
  have he' : G.map f₁.left = G.map f₂.left := congrArg (fun k => k.left) he
  refine J.superset_covering ?_ (Functor.IsDenseSubsite.equalizer_mem J K G _ _ he')
  intro W₀ c hc
  simp only [Sieve.equalizer_apply] at hc
  refine ⟨Over.mk (c ≫ U.hom), Over.homMk c, 𝟙 _, ?_, by simp⟩
  simp only [Sieve.equalizer_apply]
  ext
  exact hc

/-- The localization of a dense subsite inclusion at an object is again a dense subsite
inclusion: a covering sieve of the slice is one exactly when its image is, and the objects of
the slice over the image are covered by the images of objects of the slice.

No full faithfulness is asked of `G`. -/
theorem overPost_isDenseSubsite :
    (Over.post (X := X) G).IsDenseSubsite (J.over X) (K.over (G.obj X)) where
  isCoverDense' := overPost_isCoverDense (J := J) G X
  isLocallyFull' := overPost_isLocallyFull (J := J) G X
  isLocallyFaithful' := overPost_isLocallyFaithful (J := J) G X
  functorPushforward_mem_iff := overPost_functorPushforward_mem_iff (J := J) G X

end OverPost

end Stacks.Sites

namespace Stacks.SheafOfModules

/-- **The restriction of a quasi-coherent sheaf of modules along a continuous cocontinuous
functor, over the restricted structure sheaf, is quasi-coherent.** -/
theorem isQuasicoherentOnSite_restriction
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    [∀ X, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    (R : Sheaf J RingCat.{r}) (M : SheafOfModules.{m} R)
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{m} (F := G)
      (S := (G.sheafPushforwardContinuous RingCat.{r} K J).obj R)
      (𝟙 _)).obj M).IsQuasicoherentOnSite := by
  apply isQuasicoherentOnSite_pushforward G (𝟙 _) ?_ M hM
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have _ : G'.IsCocontinuous (K.over X) (J.over Y) :=
    isCocontinuous_comp _ _ (K.over X) (J.over (G.obj X))
  have sheafify : ∀ {E : Type (max u v)} [Category.{v} E] (T : GrothendieckTopology E),
      HasSheafify T AddCommGrpCat.{max u v r m} ∧
        T.WEqualsLocallyBijective AddCommGrpCat.{max u v r m} := fun T =>
    ⟨GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, max u v} T,
      AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m,
        max u v, v} T⟩
  obtain ⟨_, _⟩ := sheafify (K.over X)
  obtain ⟨_, _⟩ := sheafify (J.over Y)
  exact pushforward_preservesColimits G' _

end Stacks.SheafOfModules

end
