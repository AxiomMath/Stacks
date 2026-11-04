module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowFiniteCoverFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackMapProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationStabilizerFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# Affine charts of a stack of finite type over an algebraic space, and their base changes

Let `Y` be a quasi-compact and quasi-separated algebraic space over `S` and `f : 𝒳 ⟶ Y` a
1-morphism of finite type from an algebraic stack. Then `𝒳` has a smooth surjective chart
`c : U ⟶ 𝒳` by an affine scheme `U`, and `c ≫ f` is 2-isomorphic to the 1-morphism of a morphism
`φ : U ⟶ Y` of algebraic spaces, which is of finite type and separated. Base changing along a
morphism `β : Y₁ ⟶ Y` of algebraic spaces, the algebraic space `Y₁ ×_Y U` is a chart of the
base change `Y₁ ×_Y 𝒳`, smooth and surjective when `c` is, over the projections; in particular
flatness and local finite presentation of `Y₁ ×_Y 𝒳 ⟶ Y₁` pass to `Y₁ ×_Y U ⟶ Y₁`. The last two
statements hold for any chart `G ⟶ 𝒳` by an algebraic space and any pullback square. These are the
charts on which the proof of [Stacks, Tag 0CQ4] reads flatness of a base change of `f`.

## Main results

* `AlgebraicGeometry.Stack.exists_isAffine_smooth_surjective_chart`: the affine chart.
* `AlgebraicGeometry.Stack.exists_smooth_surjective_baseChangedChart`: the base-changed chart.
* `AlgebraicGeometry.Stack.isFlat_isLocallyOfFinitePresentation_pullback_fst_of_isFlat`:
  flatness and local finite presentation read on the base-changed chart.

## References

* [Stacks Project, Tag 0CQ4](https://stacks.math.columbia.edu/tag/0CQ4)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A stack of finite type over a quasi-compact and quasi-separated algebraic space has an
affine smooth surjective chart over a finite type separated morphism of algebraic spaces.** For
`f : 𝒳 ⟶ Y` there are an affine `U`, a smooth surjective `c : h_U ⟶ 𝒳` and `φ : h_U ⟶ Y` of
finite type and separated with `c ≫ f` 2-isomorphic to the 1-morphism of `φ`. -/
theorem exists_isAffine_smooth_surjective_chart
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : AlgebraicStacks.IsFiniteType B S hS f) :
    ∃ (U : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
      (c : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
      (φ : yoneda.obj U ⟶ Y),
      AlgebraicStacks.IsSmooth B S hS c ∧ IsSurjective B S hS c ∧
        Nonempty (c ≫ f ≅
          algebraicSpaceStackMap.{u, w} B S hS (isAlgebraicSpace_yoneda B S hS U) hY φ) ∧
        Space.IsFiniteType B S hS φ ∧ Space.IsSeparated B S hS φ ∧
        Space.IsQuasiSeparated B S hS φ := by
  have hYst : IsQuasiCompactStack.{u, w} B S hS (algebraicSpaceStack.{u, w} B S hS Y hY).val
      (algebraicSpaceStack.{u, w} B S hS Y hY).property :=
    isQuasiCompactStack_fibredCategory.{u, w} B S hS Y hY hYqc _
  obtain ⟨U, hU, a, hasu, hasm⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1
      (isQuasiCompactStack_of_isQuasiCompactMorphism.{u, w} B S hS f hf.2 hYst)
  obtain ⟨e, hesm, hesu⟩ := exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U
  have hUs : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let c := e ≫ a
  have hcsm : AlgebraicStacks.IsSmooth B S hS c :=
    AlgebraicStacks.isSmooth_comp B S hS e a hesm
      (isSmooth_of_isRelativelySmooth.{u, w} B S hS a hasm)
  let φ : yoneda.obj U ⟶ Y :=
    representingMap B S hS (fibredCategory B S hS (yoneda.obj U)) (fibredCategory B S hS Y) _ _
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (c ≫ f).hom
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hsep : Space.IsSeparated B S hS φ :=
    Space.isSeparated_of_scheme_isSeparated B S hS inferInstance φ
  refine ⟨U, hU, c, φ, hcsm, isSurjective_comp B S hS e a hesu hasu,
    nonempty_iso_algebraicSpaceStackMap_of_representingMap_eq.{u, w} B S hS hUs hY _ φ rfl,
    ⟨?_, ?_⟩, hsep, Space.isQuasiSeparated_of_isSeparated B S hS hsep⟩
  · exact (AlgebraicStacks.isLocallyOfFiniteType_iff_isLocallyOfFiniteType_representingMap B S hS
      (𝒜 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hUs)
      (𝒞 := algebraicSpaceStack.{u, w} B S hS Y hY)
      (yoneda.obj U) Y (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (c ≫ f) hUs hY).1
      (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS c f
        (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
          (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm)) hf.1)
  · exact Space.isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal hY hYqs
      (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU) φ

/-- **The base change of a chart of `𝒳` over `Y` along `β : Y₁ ⟶ Y` is a chart of the base
change.** If `c : G ⟶ 𝒳`, `c ≫ f ≅ φ` and `T` is a pullback of `(β, φ)`, then for a 2-fibre
product `Q` of `(β, f)` there is `c' : T ⟶ Q`, smooth (surjective) when `c` is, over both legs. -/
theorem exists_smooth_surjective_baseChangedChart
    {Y Y₁ G T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hY₁ : IsAlgebraicSpace B S hS Y₁) (hG : IsAlgebraicSpace B S hS G)
    (hT : IsAlgebraicSpace B S hS T)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (β : Y₁ ⟶ Y) (c : algebraicSpaceStack.{u, w} B S hS G hG ⟶ 𝒳) (φ : G ⟶ Y)
    (e : c ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hG hY φ)
    {p₁ : T ⟶ Y₁} {p₂ : T ⟶ G} (h : IsPullback p₁ p₂ β φ)
    (Q : Bicategory.TwoCommSq (algebraicSpaceStackMap.{u, w} B S hS hY₁ hY β) f)
    (hQ : Bicategory.IsTwoFibreProduct Q) :
    ∃ c' : algebraicSpaceStack.{u, w} B S hS T hT ⟶ Q.pt,
      (AlgebraicStacks.IsSmooth B S hS c → AlgebraicStacks.IsSmooth B S hS c') ∧
      (IsSurjective B S hS c → IsSurjective B S hS c') ∧
      Nonempty (c' ≫ Q.fst ≅ algebraicSpaceStackMap.{u, w} B S hS hT hY₁ p₁) ∧
      Nonempty (c' ≫ Q.snd ≅ algebraicSpaceStackMap.{u, w} B S hS hT hG p₂ ≫ c) := by
  let Z := (algebraicSpaceStackSquare.{u, w} B S hS hY₁ hG hY hT h.w).reindexSnd e.symm
  have hI := isTwoFibreProduct_innerSq.{u, w} B S hS hQ
    (Bicategory.isTwoFibreProduct_reindexSnd e.symm
      (isTwoFibreProduct_algebraicSpaceStackSquare.{u, w} B S hS hY₁ hG hY hT h) :
      Bicategory.IsTwoFibreProduct Z)
  exact ⟨(Bicategory.innerSq hQ Z).fst,
    fun hc => AlgebraicStacks.isSmooth_baseChange B S hS c Q.snd _ hI hc,
    fun hc => isSurjective_of_isTwoFibreProduct B S hS _ (Bicategory.isTwoFibreProduct_swap hI) hc,
    ⟨(Bicategory.canLower hQ Z).isoFst.symm⟩, ⟨(Bicategory.innerSq hQ Z).iso⟩⟩

/-- **Flatness and local finite presentation of a base change of `f` are read on the base-changed
chart.** With `c : G ⟶ 𝒳` smooth, `c ≫ f ≅ φ` and `T` a pullback of `(β, φ)`, if `Q ⟶ Y₁` is flat
and locally of finite presentation for a 2-fibre product `Q` of `(β, f)`, so is `T ⟶ Y₁`. -/
theorem isFlat_isLocallyOfFinitePresentation_pullback_fst_of_isFlat
    {Y Y₁ G T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hY₁ : IsAlgebraicSpace B S hS Y₁) (hG : IsAlgebraicSpace B S hS G)
    (hT : IsAlgebraicSpace B S hS T)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (β : Y₁ ⟶ Y) (c : algebraicSpaceStack.{u, w} B S hS G hG ⟶ 𝒳) (φ : G ⟶ Y)
    (e : c ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hG hY φ)
    (hc : AlgebraicStacks.IsSmooth B S hS c)
    {p₁ : T ⟶ Y₁} {p₂ : T ⟶ G} (h : IsPullback p₁ p₂ β φ)
    (Q : Bicategory.TwoCommSq (algebraicSpaceStackMap.{u, w} B S hS hY₁ hY β) f)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQfl : AlgebraicStacks.IsFlat B S hS Q.fst)
    (hQlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS Q.fst) :
    Space.IsFlat B S hS p₁ ∧ Space.IsLocallyOfFinitePresentation B S hS p₁ := by
  obtain ⟨c', hsm, -, ⟨e₁⟩, -⟩ :=
    exists_smooth_surjective_baseChangedChart.{u, w} B S hS hY hY₁ hG hT f β c φ e h Q hQ
  have hc' := hsm hc
  exact ⟨(isFlat_algebraicSpaceStackMap_iff.{u, w} B S hS hT hY₁ p₁).1
      ((AlgebraicStacks.isFlat_iff_of_twoIso B S hS _ _
        (Bicategory.InducedBicategory.isoHom e₁)).1
        (AlgebraicStacks.isFlat_comp B S hS c' Q.fst
          (AlgebraicStacks.isFlat_of_isSmooth B S hS c' hc') hQfl)),
    (isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B S hS hT hY₁ p₁).1
      ((AlgebraicStacks.isLocallyOfFinitePresentation_iff_of_twoIso B S hS _ _
        (Bicategory.InducedBicategory.isoHom e₁)).1
        (AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS c' Q.fst
          (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c' hc') hQlfp))⟩

end AlgebraicGeometry.Stack

end
