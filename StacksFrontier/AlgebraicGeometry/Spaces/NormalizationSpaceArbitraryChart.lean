module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasChart
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceQuotient

/-!
# The chart condition of the glued normalization at an arbitrary étale chart

`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceQuotient` glues the normalizations of
the charts of an algebraic space `F` along one surjective étale chart `w : h_U ⟶ F`, and
identifies the normalization `U^ν` of that chart with the fibre product of the glued object
with it. The chart condition of `AlgebraicGeometry.Space.NormalizationData` asks for the same
identification at *every* surjective étale chart, and this file supplies it.

Over a chart `w' : h_W ⟶ F` the identification is obtained by descent along the surjective
étale `V = W ×_F U ⟶ W`: the normalization `V^ν` is both `U^ν ×_U V` and `W^ν ×_W V` because
normalization commutes with étale base change (Tag 07TD), so the comparison morphism over `W`
has an isomorphism for its base change to `V^ν`, and is therefore itself an isomorphism — the
descent being carried out at the open immersions and at the surjective morphisms, where
effective descent along a surjective étale morphism of the site is available outright.

## Main results

* `AlgebraicGeometry.Space.NormSpaceGluing.exists_chartMap_of_etaleChart`: the normalization of
  an arbitrary étale chart `W` of `F` maps to the glued normalization, cartesianly over the
  chart. This is the chart condition of `AlgebraicGeometry.Space.NormalizationData` at `w'`.

## Implementation notes

The absolute normalization is a *functor of the object alone*: `V^ν` does not depend on the
structure morphism `V ⟶ F`, whereas the relative normalization of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasChart` is the normalization of the
chart `X ×_F V ⟶ V` and so has to be tracked along two different structure morphisms of `V` at
once. That is why the morphism of the relation which the refinement induces,
`AlgebraicGeometry.Space.NormalizationGluing.relRefine`, is reused unchanged while nothing
else of the relative development's arbitrary-chart argument is: here the cocycle computation is
four applications of rigidity rather than a chain of transition-morphism identities.

The descent of the comparison isomorphism is the same two-step argument as in the relative
case: the comparison is an open immersion because open immersions descend effectively along
surjective étale morphisms of the site
(`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion`), it is
surjective by
`AlgebraicGeometry.Space.presheaf_surjective_and_etale_of_surjectiveEtaleChart_unconditional`, and
a surjective open immersion of algebraic spaces is an isomorphism.

## References

* [Stacks Project, Tag 03GV](https://stacks.math.columbia.edu/tag/03GV)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.NormSpaceGluing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U R : BigFppfOver B S hS}
  (w : yoneda.obj U ⟶ F) (pr₁ pr₂ : R ⟶ U)
  (hsq : IsPullback (yoneda.map pr₁) (yoneda.map pr₂) w w)
  (hwet : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)
  (hwsurj : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)
  (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
      (irreducibleComponents V).Finite)
  (hR : ∀ V : ((BigFppfOver.toScheme B S hS).obj R).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj R)) →
      (irreducibleComponents V).Finite)
  (hR₂ : ∀ V : ((BigFppfOver.toScheme B S hS).obj (Limits.pullback pr₂ pr₁)).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj (Limits.pullback pr₂ pr₁))) →
      (irreducibleComponents V).Finite)
  (hF : IsAlgebraicSpace B S hS F)
  {W V : BigFppfOver B S hS} (w' : yoneda.obj W ⟶ F)
  (hw'et : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w')
  (j : V ⟶ W) (k : V ⟶ U)
  (hjk : IsPullback (yoneda.map j) (yoneda.map k) w' w)
  (hW : ∀ O : ((BigFppfOver.toScheme B S hS).obj W).Opens,
    IsCompact (O : Set ((BigFppfOver.toScheme B S hS).obj W)) →
      (irreducibleComponents O).Finite)
  (hV : ∀ O : ((BigFppfOver.toScheme B S hS).obj V).Opens,
    IsCompact (O : Set ((BigFppfOver.toScheme B S hS).obj V)) →
      (irreducibleComponents O).Finite)
  (hVV : ∀ O : ((BigFppfOver.toScheme B S hS).obj (Limits.pullback j j)).Opens,
    IsCompact (O : Set ((BigFppfOver.toScheme B S hS).obj (Limits.pullback j j))) →
      (irreducibleComponents O).Finite)

/-- Pullbacks of presheaves on the big fppf site over `S`, supplied directly: instance search
for them now times out. -/
local instance (priority := high) hasLimit_cospan_presheaf_NormalizationSpaceArbitraryChart
    {Z₁ Z₂ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z₁ ⟶ Z) (f : Z₂ ⟶ Z) :
    HasLimit (cospan g f) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/-- A composite of morphisms of the site sending generic points to generic points does so. -/
theorem mem_genericPoints_toScheme_map_comp {X Y Z : BigFppfOver B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z)
    (hf : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj X),
      (BigFppfOver.toScheme B S hS).map f η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj Y))
    (hg : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj Y),
      (BigFppfOver.toScheme B S hS).map g η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj Z)) :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj X),
      (BigFppfOver.toScheme B S hS).map (f ≫ g) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj Z) := fun η => by
  rw [Functor.map_comp, Scheme.Hom.comp_apply]
  exact hg ⟨_, hf η⟩

/-- For étale `j : V ⟶ W`, the kernel pair of `V^ν ⟶ W^ν` is the pair of morphisms of
normalizations induced by the projections of `V ×_W V`. -/
theorem isPullback_normSpaceMap_pullback_fst_snd
    [Etale ((BigFppfOver.toScheme B S hS).map j)]
    [Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst j j))]
    [Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd j j))]
    (hj : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj V),
      (BigFppfOver.toScheme B S hS).map j η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj W))
    (hf : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj (Limits.pullback j j)),
      (BigFppfOver.toScheme B S hS).map (Limits.pullback.fst j j) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj V))
    (hs : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj (Limits.pullback j j)),
      (BigFppfOver.toScheme B S hS).map (Limits.pullback.snd j j) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj V)) :
    IsPullback (normSpaceMap B S hS hV hVV (Limits.pullback.fst j j) hf)
      (normSpaceMap B S hS hV hVV (Limits.pullback.snd j j) hs)
      (normSpaceMap B S hS hW hV j hj) (normSpaceMap B S hS hW hV j hj) := by
  have hA := isPullback_normSpaceMap_of_etale B S hS hW hV j hj
  have hfj := mem_genericPoints_toScheme_map_comp B S hS _ j hf hj
  have hsj := mem_genericPoints_toScheme_map_comp B S hS _ j hs hj
  have houter := (isPullback_normSpaceMap_of_etale B S hS hV hVV _ hf).paste_vert
    (IsPullback.of_hasPullback j j)
  rw [← (isPullback_normSpaceMap_of_etale B S hS hV hVV _ hs).w, ← hA.w] at houter
  refine houter.of_bot ?_ hA
  rw [← normSpaceMap_comp B S hS hW hV hVV j _ hj hf hfj,
    ← normSpaceMap_comp B S hS hW hV hVV j _ hj hs hsj]
  exact normSpaceMap_congr B S hS hW hVV _ _ hfj hsj Limits.pullback.condition

include hR₂ hjk in
/-- The composite `V^ν ⟶ U^ν ⟶ U^ν/R^ν` is invariant under the kernel pair of `V^ν ⟶ W^ν`,
the invariance being the relation `U ×_F U` read at
`AlgebraicGeometry.Space.NormalizationGluing.relRefine`. -/
theorem normSpaceMap_pullback_fst_comp_normQuotientMap
    (hf : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj (Limits.pullback j j)),
      (BigFppfOver.toScheme B S hS).map (Limits.pullback.fst j j) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj V))
    (hs : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj (Limits.pullback j j)),
      (BigFppfOver.toScheme B S hS).map (Limits.pullback.snd j j) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj V))
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj V),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :
    yoneda.map (normSpaceMap B S hS hV hVV (Limits.pullback.fst j j) hf) ≫
        yoneda.map (normSpaceMap B S hS hU hV k hk) ≫
          normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR =
      yoneda.map (normSpaceMap B S hS hV hVV (Limits.pullback.snd j j) hs) ≫
        yoneda.map (normSpaceMap B S hS hU hV k hk) ≫
          normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR := by
  have hfk := mem_genericPoints_toScheme_map_comp B S hS _ k hf hk
  have _ : Etale ((BigFppfOver.toScheme B S hS).map pr₁) :=
    NormalizationGluing.etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet
  have gRR : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj (Limits.pullback j j)),
      (BigFppfOver.toScheme B S hS).map
          (NormalizationGluing.relRefine B S hS w pr₁ pr₂ hsq hwet w' j k hjk) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj R) :=
    mem_genericPoints_of_comp_etale B S hS _ pr₁ fun η => by
      rw [NormalizationGluing.relRefine_comp_pr₁]
      exact hfk η
  have e : ∀ (p : Limits.pullback j j ⟶ V)
      (hp : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj (Limits.pullback j j)),
        (BigFppfOver.toScheme B S hS).map p η.1 ∈
          genericPoints ((BigFppfOver.toScheme B S hS).obj V))
      (q : R ⟶ U) (r : normSpace B S hS R hR ⟶ normSpace B S hS U hU),
      r ≫ normSpaceProj B S hS U hU = normSpaceProj B S hS R hR ≫ q →
      NormalizationGluing.relRefine B S hS w pr₁ pr₂ hsq hwet w' j k hjk ≫ q = p ≫ k →
      normSpaceMap B S hS hV hVV p hp ≫ normSpaceMap B S hS hU hV k hk =
        normSpaceMap B S hS hR hVV
          (NormalizationGluing.relRefine B S hS w pr₁ pr₂ hsq hwet w' j k hjk) gRR ≫ r :=
    fun p hp q r hr hq => by
    refine normSpace_hom_ext B S hS hU hVV (p ≫ k)
      (mem_genericPoints_toScheme_map_comp B S hS _ k hp hk) ?_ ?_
    · rw [Category.assoc, normSpaceMap_comp_normSpaceProj, ← Category.assoc,
        normSpaceMap_comp_normSpaceProj, Category.assoc]
    · rw [Category.assoc, hr, ← Category.assoc, normSpaceMap_comp_normSpaceProj, Category.assoc,
        hq]
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    e _ hf _ _ (normRelFst_comp_normSpaceProj B S hS w pr₁ pr₂ hsq hwet hU hR)
      (NormalizationGluing.relRefine_comp_pr₁ B S hS w pr₁ pr₂ hsq hwet w' j k hjk),
    e _ hs _ _ (normRelSnd_comp_normSpaceProj B S hS w pr₁ pr₂ hsq hwet hU hR)
      (NormalizationGluing.relRefine_comp_pr₂ B S hS w pr₁ pr₂ hsq hwet w' j k hjk),
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    (isPullback_normQuotientMap_self B S hS w pr₁ pr₂ hsq hwet hU hR hR₂).w]

include hjk in
/-- A morphism `W^ν ⟶ U^ν/R^ν` descending `V^ν ⟶ U^ν ⟶ U^ν/R^ν` lies over `w'`. -/
theorem comp_normQuotientToBase_of_comp_eq
    [Etale ((BigFppfOver.toScheme B S hS).map j)]
    [Surjective ((BigFppfOver.toScheme B S hS).map j)]
    (hj : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj V),
      (BigFppfOver.toScheme B S hS).map j η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj W))
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj V),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U))
    (b : yoneda.obj (normSpace B S hS W hW) ⟶ normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR)
    (hb : yoneda.map (normSpaceMap B S hS hW hV j hj) ≫ b =
      yoneda.map (normSpaceMap B S hS hU hV k hk) ≫
        normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR) :
    b ≫ normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF =
      yoneda.map (normSpaceProj B S hS W hW) ≫ w' := by
  refine hom_ext_of_etale_atlas B S hS (isAlgebraicSpace_yoneda B S hS _).isSheaf hF.isSheaf
    (yoneda.map (normSpaceMap B S hS hW hV j hj))
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
      (surjective_toScheme_map_normSpaceMap B S hS hW hV j hj))
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
      (etale_toScheme_map_normSpaceMap B S hS hW hV j hj)) ?_
  calc yoneda.map (normSpaceMap B S hS hW hV j hj) ≫ b ≫
          normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF
      = (yoneda.map (normSpaceMap B S hS hU hV k hk) ≫
          normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR) ≫
          normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF := by
          rw [← Category.assoc, hb]
    _ = yoneda.map (normSpaceMap B S hS hU hV k hk ≫ normSpaceProj B S hS U hU) ≫ w := by
          rw [Category.assoc, (isPullback_normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF).w,
            Functor.map_comp, Category.assoc]
    _ = yoneda.map (normSpaceProj B S hS V hV) ≫ yoneda.map j ≫ w' := by
          rw [normSpaceMap_comp_normSpaceProj, Functor.map_comp, Category.assoc, hjk.w]
    _ = yoneda.map (normSpaceMap B S hS hW hV j hj ≫ normSpaceProj B S hS W hW) ≫ w' := by
          rw [normSpaceMap_comp_normSpaceProj, Functor.map_comp, Category.assoc]
    _ = yoneda.map (normSpaceMap B S hS hW hV j hj) ≫
          yoneda.map (normSpaceProj B S hS W hW) ≫ w' := by
          rw [Functor.map_comp, Category.assoc]

include hjk in
/-- The base change of the comparison `W^ν ⟶ (U^ν/R^ν) ×_F W` to `V` is `V^ν`. -/
theorem isPullback_comp_pullback_lift
    [Etale ((BigFppfOver.toScheme B S hS).map k)]
    (hj : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj V),
      (BigFppfOver.toScheme B S hS).map j η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj W))
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj V),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U))
    (b : yoneda.obj (normSpace B S hS W hW) ⟶ normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR)
    (hb : yoneda.map (normSpaceMap B S hS hW hV j hj) ≫ b =
      yoneda.map (normSpaceMap B S hS hU hV k hk) ≫
        normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR)
    (hbν : b ≫ normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF =
      yoneda.map (normSpaceProj B S hS W hW) ≫ w') :
    IsPullback
      (yoneda.map (normSpaceMap B S hS hW hV j hj) ≫
        Limits.pullback.lift b (yoneda.map (normSpaceProj B S hS W hW)) hbν)
      (yoneda.map (normSpaceProj B S hS V hV))
      (Limits.pullback.snd
        (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w') (yoneda.map j) := by
  refine IsPullback.of_right
    (h₁₂ := Limits.pullback.fst
      (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w')
    (v₁₃ := normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) (h₂₂ := w') ?_ ?_
    (IsPullback.of_hasPullback _ _)
  · rw [Category.assoc, Limits.pullback.lift_fst, hb, hjk.w]
    exact (isPullback_yoneda_map_normSpaceMap_of_etale B S hS hU hV k hk).paste_horiz
      (isPullback_normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF)
  · rw [Category.assoc, Limits.pullback.lift_snd, ← Functor.map_comp,
      normSpaceMap_comp_normSpaceProj, Functor.map_comp]

/-- If a square with an identity side is cartesian, the second projection of the chosen pullback
is an isomorphism. -/
theorem isIso_pullback_snd_of_isPullback_id {C : Type*} [Category C] {X Y Z : C}
    {a : X ⟶ Y} {f : Y ⟶ Z} {g : X ⟶ Z} [HasPullback f g] (h : IsPullback a (𝟙 X) f g) :
    IsIso (Limits.pullback.snd f g) := by
  rw [(cancel_epi h.isoPullback.hom).1
    (h.isoPullback_hom_snd.trans h.isoPullback.hom_inv_id.symm)]
  infer_instance

/-- A morphism from a representable to a sheaf whose base change along a surjective étale chart
is an isomorphism is itself an isomorphism. -/
theorem isIso_of_isIso_pullback_snd {N M : BigFppfOver B S hS}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P) (β : yoneda.obj N ⟶ P)
    {c : yoneda.obj M ⟶ P}
    (hcs : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hce : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    [IsIso (Limits.pullback.snd β c)] : IsIso β := by
  have _ : MorphismProperty.RespectsIso (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u}) := MorphismProperty.RespectsIso.inf _ _
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities := ⟨fun Z => by
    show AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map (𝟙 Z))
    rw [CategoryTheory.Functor.map_id]
    infer_instance⟩
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities := ⟨fun Z => by
    show AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (𝟙 Z))
    rw [CategoryTheory.Functor.map_id]
    infer_instance⟩
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities := ⟨fun Z => by
    refine ⟨?_, ?_⟩
    · rw [CategoryTheory.Functor.map_id]
      infer_instance
    · rw [CategoryTheory.Functor.map_id]
      infer_instance⟩
  have hN := (isAlgebraicSpace_yoneda B S hS N).isSheaf
  exact isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS _
    (presheaf_of_surjectiveEtaleChart
      (isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion B S hS) hN hP hcs hce
      (MorphismProperty.presheaf_of_isIso _ _))
    (presheaf_surjective_and_etale_of_surjectiveEtaleChart_unconditional B S hS hN hP hcs hce
      (MorphismProperty.presheaf_of_isIso _ _) (MorphismProperty.presheaf_of_isIso _ _)
      (MorphismProperty.presheaf_of_isIso _ _)).1

include hjk in
/-- The comparison `W^ν ⟶ (U^ν/R^ν) ×_F W` induced by a descended morphism is an isomorphism. -/
theorem isIso_pullback_lift_normSpaceProj
    [Etale ((BigFppfOver.toScheme B S hS).map j)]
    [Surjective ((BigFppfOver.toScheme B S hS).map j)]
    [Etale ((BigFppfOver.toScheme B S hS).map k)]
    (hj : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj V),
      (BigFppfOver.toScheme B S hS).map j η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj W))
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj V),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U))
    (b : yoneda.obj (normSpace B S hS W hW) ⟶ normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR)
    (hb : yoneda.map (normSpaceMap B S hS hW hV j hj) ≫ b =
      yoneda.map (normSpaceMap B S hS hU hV k hk) ≫
        normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR)
    (hbν : b ≫ normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF =
      yoneda.map (normSpaceProj B S hS W hW) ≫ w') :
    IsIso (Limits.pullback.lift b (yoneda.map (normSpaceProj B S hS W hW)) hbν) := by
  have hleft := isPullback_comp_pullback_lift B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF w' j k
    hjk hW hV hj hk b hb hbν
  have htop : IsPullback (yoneda.map (normSpaceMap B S hS hW hV j hj))
      (𝟙 (yoneda.obj (normSpace B S hS V hV)))
      (Limits.pullback.lift b (yoneda.map (normSpaceProj B S hS W hW)) hbν)
      (yoneda.map (normSpaceMap B S hS hW hV j hj) ≫
        Limits.pullback.lift b (yoneda.map (normSpaceProj B S hS W hW)) hbν) := by
    refine IsPullback.of_bot ?_ (Category.id_comp _).symm hleft
    rw [Category.id_comp, Limits.pullback.lift_snd]
    exact (isPullback_normSpaceMap_of_etale B S hS hW hV j hj).map yoneda
  have _ := isIso_pullback_snd_of_isPullback_id htop
  have hc : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange],
      P ((BigFppfOver.toScheme B S hS).map j) →
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (normSpaceMap B S hS hW hV j hj) ≫
          Limits.pullback.lift b (yoneda.map (normSpaceProj B S hS W hW)) hbν) := fun P _ hP => by
    have _ := MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)) (F := yoneda)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hleft.flip
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P j).2 hP)
  exact isIso_of_isIso_pullback_snd B S hS (isAlgebraicSpace_pullback B S hS
    (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w'
    (isAlgebraicSpace_normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR hR₂)
    (isAlgebraicSpace_yoneda B S hS W) hF).isSheaf _ (hc _ inferInstance) (hc _ inferInstance)

include hwsurj hw'et hjk hV hVV in
/-- **The chart condition at an arbitrary étale chart of `F`.** The normalization `W^ν` of a
chart `W` maps to the glued normalization `U^ν/R^ν`, and the square it forms with the
normalization morphism of `W` and the two morphisms to `F` is cartesian.

The refinement `V = W ×_F U` carries the identification: `V^ν` is the base change of `U^ν`
along `V ⟶ U` and of `W^ν` along `V ⟶ W`, both by Tag 07TD, so the composite
`V^ν ⟶ U^ν ⟶ U^ν/R^ν` is invariant under the kernel pair of the surjective étale
`V^ν ⟶ W^ν` — the invariance being the relation `U ×_F U` read at the morphism
`AlgebraicGeometry.Space.NormalizationGluing.relRefine` — and so descends to `W^ν`. The
comparison of `W^ν` with the fibre product becomes an isomorphism over `V^ν`, hence is an
open immersion and surjective, hence an isomorphism. -/
theorem exists_chartMap_of_etaleChart :
    ∃ b : yoneda.obj (normSpace B S hS W hW) ⟶
        normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR,
      IsPullback b (yoneda.map (normSpaceProj B S hS W hW))
        (normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF) w' := by
  classical
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : Etale ((BigFppfOver.toScheme B S hS).map j) :=
    NormalizationGluing.etale_toScheme_map_j B S hS w hwet w' j k hjk
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map j) :=
    NormalizationGluing.surjective_toScheme_map_j B S hS w hwsurj w' j k hjk
  have _ : Etale ((BigFppfOver.toScheme B S hS).map k) :=
    NormalizationGluing.etale_toScheme_map_k B S hS w w' hw'et j k hjk
  have hpbjj := (IsPullback.of_hasPullback j j).map (BigFppfOver.toScheme B S hS)
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst j j)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Etale.{u}) hpbjj.flip inferInstance
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd j j)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Etale.{u}) hpbjj inferInstance
  have gJ := mem_genericPoints_toScheme_map_of_flat B S hS j
  have gK := mem_genericPoints_toScheme_map_of_flat B S hS k
  have gFst := mem_genericPoints_toScheme_map_of_flat B S hS (Limits.pullback.fst j j)
  have gSnd := mem_genericPoints_toScheme_map_of_flat B S hS (Limits.pullback.snd j j)
  obtain ⟨b, hb, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS
    (isAlgebraicSpace_yoneda B S hS (normSpace B S hS W hW)).isSheaf
    (yoneda.map (normSpaceMap B S hS hW hV j gJ))
    ((isPullback_normSpaceMap_pullback_fst_snd B S hS j hW hV hVV gJ gFst gSnd).map yoneda)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
      (surjective_toScheme_map_normSpaceMap B S hS hW hV j gJ))
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
      (etale_toScheme_map_normSpaceMap B S hS hW hV j gJ))
    (isAlgebraicSpace_normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR hR₂).isSheaf
    (yoneda.map (normSpaceMap B S hS hU hV k gK) ≫
      normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR)
    (normSpaceMap_pullback_fst_comp_normQuotientMap B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ w' j k
      hjk hV hVV gFst gSnd gK)
  have hbν := comp_normQuotientToBase_of_comp_eq B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF w' j k
    hjk hW hV gJ gK b hb
  have _ := isIso_pullback_lift_normSpaceProj B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF w' j k
    hjk hW hV gJ gK b hb hbν
  exact ⟨b, IsPullback.of_iso_pullback ⟨hbν⟩
    (asIso (Limits.pullback.lift b (yoneda.map (normSpaceProj B S hS W hW)) hbν))
    (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)⟩

end AlgebraicGeometry.Space.NormSpaceGluing

end
