module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedAtFiniteStage

/-!
# Separatedness of a base change descends to a finite stage, under the chapter's convention

In Situation 0CPY let `Y = lim Y_i` be a directed limit of quasi-compact and quasi-separated
algebraic spaces with affine transition morphisms and distinguished index `0`, and let
`f₀ : 𝒳₀ ⟶ Y₀` be a 1-morphism from a quasi-compact and quasi-separated algebraic stack. If the
base change `Y ×_{Y₀} 𝒳₀ ⟶ Y` is separated, then so is `Y_i ×_{Y₀} 𝒳₀ ⟶ Y_i` for all
sufficiently large `i` (Stacks 0CPZ).

Here the system is asked to satisfy the chapter's standing convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, and nothing is asked of the size of the
index. The convention is what makes Stacks 08K1 hold
(`Space.MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`);
without it the statement fails, the limit in the site of a system whose true limit is too big
for the site being possibly empty. The Noetherian approximations of Stacks 07SU satisfy it
(`AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_etaleAtlas`).

The proof is that of
`AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_stage_of_forall_isProper`, with
Stacks 08K1 under the convention in place of its bounded form, so that no transport of the index
set is needed.

## Main results

* `DescentSituation.exists_isSeparated_stage_of_siteContainsBaseChangeLimits`: under the
  convention, separatedness of `Y ×_{Y₀} 𝒳₀ ⟶ Y` implies that of `Y_i ×_{Y₀} 𝒳₀ ⟶ Y_i` for all
  sufficiently large `i`.

## References

* [Stacks Project, Tag 0CPZ](https://stacks.math.columbia.edu/tag/0CPZ)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space.DescentSituation

open AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- **Properness of a base change is inherited along a factorization of the base.** Let
`φ : Y' ×_{Y₀} T ⟶ Y' ×_{Y₀} V` and `φ' : Y'' ×_{Y₀} T ⟶ Y'' ×_{Y₀} V` be base changes of a
morphism `m : T ⟶ V` of algebraic spaces over `b : V ⟶ Y₀`, along `q` and `q' = t ≫ q`. If `φ`
is proper, then so is `φ'`. -/
private theorem isProper_of_baseChange_of_comp
    {T V Y₀ Y' Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hV : IsAlgebraicSpace B S hS V)
    (hY₀ : IsAlgebraicSpace B S hS Y₀) (hY' : IsAlgebraicSpace B S hS Y')
    (hY'' : IsAlgebraicSpace B S hS Y'') {m : T ⟶ V} {b : V ⟶ Y₀} {q : Y' ⟶ Y₀}
    {q' : Y'' ⟶ Y₀} (t : Y'' ⟶ Y') (ht : t ≫ q = q')
    {φ : pullback q (m ≫ b) ⟶ pullback q b} (hφ₁ : φ ≫ pullback.fst _ _ = pullback.fst _ _)
    (hφ₂ : φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ m)
    {φ' : pullback q' (m ≫ b) ⟶ pullback q' b} (hφ'₁ : φ' ≫ pullback.fst _ _ = pullback.fst _ _)
    (hφ'₂ : φ' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ m) (hφ : IsProper B S hS φ) :
    IsProper B S hS φ' :=
  isProper_of_isPullback_of_isPullback B S hS
    (isAlgebraicSpace_pullback B S hS _ _ hY' hT hY₀)
    (isAlgebraicSpace_pullback B S hS _ _ hY' hV hY₀)
    (isAlgebraicSpace_pullback B S hS _ _ hY'' hT hY₀)
    (isAlgebraicSpace_pullback B S hS _ _ hY'' hV hY₀)
    (isPullback_snd_of_baseChange B S hS m b q φ hφ₁ hφ₂)
    (isPullback_snd_of_baseChange B S hS m b q' φ' hφ'₁ hφ'₂)
    (pullback.lift (pullback.fst _ _ ≫ t) (pullback.snd _ _)
      (by rw [Category.assoc, ht, pullback.condition]))
    (pullback.lift_snd _ _ _) hφ

/-- **Stacks 0CPZ, under the chapter's convention.** In Situation 0CPY, for a system satisfying
the convention of Section 70.2 (tag 07SD), let `f₀ : 𝒳₀ ⟶ Y₀` be a 1-morphism from a
quasi-compact and quasi-separated algebraic stack to the distinguished stage. If the base change
`Y ×_{Y₀} 𝒳₀ ⟶ Y` to the limit is separated, then the base change `Y_i ×_{Y₀} 𝒳₀ ⟶ Y_i` is
separated for all sufficiently large `i`. -/
theorem exists_isSeparated_stage_of_siteContainsBaseChangeLimits
    (D : DescentSituation B S hS hZ I)
    (hconv : haveI : Nonempty I := ⟨D.base⟩
      SiteContainsBaseChangeLimits B S hS D.system)
    (𝒳₀ : AlgebraicStacks.{u, w} B S hS)
    (f₀ : 𝒳₀ ⟶ algebraicSpaceStack.{u, w} B S hS (D.system.obj (op D.base))
      (D.algebraicSpace D.base))
    (h𝒳₀qc : IsQuasiCompactStack.{u, w} B S hS 𝒳₀.val 𝒳₀.property)
    (h𝒳₀qs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳₀)
    (hf : AlgebraicStacks.IsSeparated B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f₀
        (algebraicSpaceStackMap.{u, w} B S hS D.limitAlgebraicSpace (D.algebraicSpace D.base)
          (D.limitCone.π.app (op D.base)))).snd) :
    ∃ (i₀ : I) (h₀ : D.base ≤ i₀), ∀ (i : I) (hi : i₀ ≤ i),
      AlgebraicStacks.IsSeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f₀
          (algebraicSpaceStackMap.{u, w} B S hS (D.algebraicSpace i) (D.algebraicSpace D.base)
            (D.system.map (homOfLE (h₀.trans hi)).op))).snd := by
  have : Nonempty I := ⟨D.base⟩
  classical
  set Y₀ := D.system.obj (op D.base)
  have hY₀ : IsAlgebraicSpace B S hS Y₀ := D.algebraicSpace D.base
  -- an affine smooth chart of `𝒳₀`, Stacks 04YC
  obtain ⟨U, hU, u₀, hu₀surj, hu₀smooth⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳₀).1 h𝒳₀qc
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  obtain ⟨hu₀rep, hu₀sm⟩ := hu₀smooth
  -- the chart is locally essentially surjective
  have hu₀LES := localEssSurj_of_isSurjective_isSmooth B S hS u₀.hom hu₀rep
    (fun V yv hyv F hF he =>
      ⟨(pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS u₀ hu₀rep).1
          hu₀surj V yv hyv F hF he, hu₀sm V yv hyv F hF he⟩)
  -- the cover `U₀ ×_{Y₀} U₀ ⟶ 𝒳₀ ×_{Y₀} 𝒳₀`
  let g₀ := (AlgebraicStacks.mapCospan B S hS u₀ u₀ f₀).hom
  have hg₀ := AlgebraicStacks.localEssSurj_mapCospan B S hS u₀ f₀ hu₀LES
  -- `U₀ ×_{Y₀} U₀` is represented by a quasi-compact quasi-separated algebraic space
  have h𝒰₀ := isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U
  have hu₀f₀ : Stack.IsRepresentableByAlgebraicSpaces B S hS (u₀ ≫ f₀).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).property h𝒰₀ (u₀ ≫ f₀).hom
  let K₁ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (u₀ ≫ f₀).hom (u₀ ≫ f₀).hom
  have hK₁ : Bicategory.IsTwoFibreProduct K₁ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  obtain ⟨V₀, hV₀, ⟨eV₀⟩⟩ := isRepresentableByAlgebraicSpace_of_representable B S hS K₁.pt _
    K₁.fst (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ _ _ K₁ hK₁
      hu₀f₀) h𝒰₀
  have : (twoFibreProductStructureFunctor B S hS
      (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS U)
      (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val (u₀ ≫ f₀).hom (u₀ ≫ f₀).hom).IsFibered :=
    K₁.pt.property.isFibered
  have hpb₁ := isPullback_representingMap_twoFibreProductSquare B S hS
    (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS U)
    (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val (yoneda.obj U) (yoneda.obj U) Y₀
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (u₀ ≫ f₀).hom (u₀ ≫ f₀).hom V₀ eV₀
  have hyU := isAlgebraicSpace_yoneda B S hS U
  have hyUqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU
  have hyUqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj U) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj U) hZ
      ⟨U, inferInstance, ⟨Functor.RepresentableBy.yoneda U⟩⟩
  have hV₀qc : IsQuasiCompactSpace B S hS V₀ :=
    isQuasiCompactSpace_of_iso B S hS hpb₁.isoPullback.symm
      (isQuasiCompactSpace_pullback B S hS hZ _ _ hyU hY₀ hyUqc hyUqc (D.quasiSeparated D.base))
  have hV₀qs : IsAbsolutelyQuasiSeparated B S hS hZ V₀ :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hV₀
      (isAbsolutelyQuasiSeparated_pullback B S hS hZ _ _ hyU hyU hY₀ hyUqs hyUqs)
      (isQuasiSeparated_of_mono B S hS hpb₁.isoPullback.hom inferInstance)
  -- the base change of the relative diagonal of `f₀` along the cover
  let Δ₀ := relativeDiagonal.{u, u, u + 1} B S hS 𝒳₀.val
    (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀).val f₀.hom
  have hΔ₀ : Stack.IsRepresentableByAlgebraicSpaces B S hS Δ₀.hom :=
    isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f₀
  let Q₀ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g₀ Δ₀
  have hQ₀ : Bicategory.IsTwoFibreProduct Q₀ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  obtain ⟨T₀, hT₀, ⟨eT₀⟩⟩ := isRepresentableByAlgebraicSpace_of_representable B S hS Q₀.pt
    K₁.pt Q₀.fst (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ Δ₀ g₀
      Q₀ hQ₀ hΔ₀) ⟨V₀, hV₀, ⟨eV₀⟩⟩
  -- `f₀` is quasi-separated, `𝒳₀` being quasi-separated and `Y₀` an algebraic space
  have hY₀str : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (structureMorphism B S hS (algebraicSpaceStack.{u, w} B S hS Y₀ hY₀)).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS Y₀ hY₀) _
  have hf₀qs : AlgebraicStacks.IsQuasiSeparated B S hS f₀ :=
    AlgebraicStacks.isQuasiSeparated_of_isQuasiSeparatedOver B S hS f₀
      (AlgebraicStacks.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ 𝒳₀ h𝒳₀qs)
      (fun V y hy F hF he => isQuasiSeparated_of_mono B S hS _
        (mono_hom_algebraicSpaceMap_of_subsingleton B S hS V F hF
          (subsingleton_representing_of_relativeDiagonal B S hS _ _ _ hY₀str V y hy F he)))
  -- the induced morphism `m₀ : T₀ ⟶ V₀` is quasi-compact, quasi-separated and locally of finite
  -- type
  let m₀ := diagonalCoverBaseChangeMap B S hS f₀ g₀ V₀ eV₀ T₀ eT₀
  have hm₀qc : IsQuasiCompact B S hS m₀ :=
    prop_representingMap_of_hasRelativeProperty.{u, u} B S hS (quasiCompactProperty B S hS) Δ₀ hΔ₀
      hf₀qs.1 _ g₀ Q₀ hQ₀ T₀ V₀ hT₀ hV₀ eT₀ eV₀
  have hm₀qs : IsQuasiSeparated B S hS m₀ :=
    prop_representingMap_of_hasRelativeProperty.{u, u} B S hS (quasiSeparatedProperty B S hS) Δ₀ hΔ₀
      hf₀qs.2 _ g₀ Q₀ hQ₀ T₀ V₀ hT₀ hV₀ eT₀ eV₀
  have hlftBC : (locallyOfFiniteTypeProperty B S hS).IsStableUnderBaseChange :=
    isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  have hlftLT : (locallyOfFiniteTypeProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hm₀lft : IsLocallyOfFiniteType B S hS m₀ :=
    prop_representingMap_of_hasRelativeProperty.{u, u} B S hS (locallyOfFiniteTypeProperty B S hS)
      Δ₀ hΔ₀ (isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack B S hS f₀).2 _ g₀ Q₀ hQ₀
      T₀ V₀ hT₀ hV₀ eT₀ eV₀
  have hT₀qc : IsQuasiCompactSpace B S hS T₀ :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hV₀ hV₀qc hm₀qc
  have hT₀qs : IsAbsolutelyQuasiSeparated B S hS hZ T₀ :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hT₀ hV₀qs hm₀qs
  -- the limit of the system, and the situation of Stacks 084W for `m₀` over the stages `Y_i`
  let eL : D.limitCone.pt ≅ limit D.system :=
    D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system)
  let b₀ := diagonalCoverStructureMap B S hS f₀ g₀ V₀ eV₀
  let D' : MorphismDescentSituation B S hS hZ I :=
    { base := D.system
      base_isAlgebraicSpace := D.algebraicSpace
      transition_affine := D.transition_affine
      limit_isAlgebraicSpace := isAlgebraicSpace_of_iso B S hS eL D.limitAlgebraicSpace
      initial := D.base
      source₀ := T₀
      target₀ := V₀
      sourceToBase := m₀ ≫ b₀
      targetToBase := b₀
      map₀ := m₀
      map₀_over := rfl
      source₀_isAlgebraicSpace := hT₀
      target₀_isAlgebraicSpace := hV₀
      base₀_quasiCompact := D.quasiCompact _
      base₀_quasiSeparated := D.quasiSeparated _
      source₀_quasiCompact := hT₀qc
      source₀_quasiSeparated := hT₀qs
      target₀_quasiCompact := hV₀qc
      target₀_quasiSeparated := hV₀qs }
  -- the criterion of `AlgebraicGeometry.Stack.isSeparated_baseChange_iff_isProper` at a base
  -- `q : Y' ⟶ Y₀`
  have key : ∀ {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
      (q : Y' ⟶ Y₀),
      AlgebraicStacks.IsSeparated B S hS
          (twoFibreProductSquareAlgebraicStacks B S hS f₀
            (algebraicSpaceStackMap.{u, w} B S hS hY' hY₀ q)).snd ↔
        IsProper B S hS (pullback.lift (pullback.fst q (m₀ ≫ b₀)) (pullback.snd _ _ ≫ m₀)
          (by rw [pullback.condition, Category.assoc]) : pullback q (m₀ ≫ b₀) ⟶ pullback q b₀) :=
    fun hY' q => isSeparated_baseChange_iff_isProper B S hS f₀ g₀ V₀ eV₀ T₀ eT₀ hV₀
      hT₀ hg₀ hY' q _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  -- at the limit
  let qc := D.limitCone.π.app (op D.base)
  have hL := (key D.limitAlgebraicSpace qc).1 hf
  have hqL : eL.inv ≫ qc = limit.π D.system (op D.base) :=
    D.isLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit D.system) (op D.base)
  have hlim : IsProper B S hS D'.mapLimit :=
    isProper_of_baseChange_of_comp hT₀ hV₀ hY₀ D.limitAlgebraicSpace
      D'.limit_isAlgebraicSpace eL.inv hqL (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hL
  -- Stacks 08K1, under the convention
  obtain ⟨j₀, h₀, hj₀⟩ :=
    D'.exists_isProper_mapAt_of_siteContainsBaseChangeLimits hconv hlim hm₀lft
  refine ⟨j₀, h₀, fun i hi => ?_⟩
  let qi := D.system.map (homOfLE (h₀.trans hi)).op
  refine (key (D.algebraicSpace i) qi).2 ?_
  let t : D.system.obj (op i) ⟶ D.system.obj (op j₀) := D.system.map (homOfLE hi).op
  have hq : t ≫ D'.baseAtToInitial j₀ h₀ = qi := by
    show D.system.map _ ≫ D.system.map _ = D.system.map _
    rw [← D.system.map_comp]
    exact congrArg D.system.map (Subsingleton.elim _ _)
  exact isProper_of_baseChange_of_comp hT₀ hV₀ hY₀ (D.algebraicSpace j₀)
    (D.algebraicSpace i) t hq (D'.mapAt_fst j₀ h₀) (D'.mapAt_snd j₀ h₀)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hj₀

end AlgebraicGeometry.Space.DescentSituation

end
