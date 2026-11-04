module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedOfProperChartRelation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact

/-!
# Separatedness of a base change descends to a finite stage of a limit (Stacks 0CPZ)

In Situation 0CPY let `Y = lim Y_i` be a directed limit of quasi-compact and quasi-separated
algebraic spaces with affine transition morphisms and distinguished index `0`, and let
`f₀ : 𝒳₀ ⟶ Y₀` be a morphism from a quasi-compact and quasi-separated algebraic stack. If the
base change `Y ×_{Y₀} 𝒳₀ ⟶ Y` is separated, then so is `Y_i ×_{Y₀} 𝒳₀ ⟶ Y_i` for all sufficiently
large `i`.

## Main results

* `AlgebraicGeometry.Space.isProper_of_isPullback_of_isPullback`: a base change of a morphism
  of algebraic spaces is proper as soon as an earlier base change of it is.
* `AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_stage_of_forall_isProper`: the
  statement of Stacks 0CPZ, deduced from the descent of properness along a limit of bases
  (Stacks 08K1), which is taken as the argument `h08K1`.

## Implementation notes

The proof is the source's. Choose an affine scheme `U₀` with a smooth surjective `u₀ : U₀ ⟶ 𝒳₀`
(Stacks 04YC). Then `U₀ ×_{Y₀} U₀ ⟶ 𝒳₀ ×_{Y₀} 𝒳₀` is locally essentially surjective and the base
change of the relative diagonal of `f₀` along it is a morphism of algebraic spaces
`m₀ : R₀ ⟶ U₀ ×_{Y₀} U₀`, locally of finite type (Stacks 04XS) with `R₀` quasi-compact and
quasi-separated, because `f₀` is quasi-separated. Separatedness of `Y' ×_{Y₀} 𝒳₀ ⟶ Y'` is
properness of the base change of `m₀` to `Y'`
(`AlgebraicGeometry.Stack.isSeparated_baseChange_iff_isProper`); so the hypothesis at the limit
makes the base change of `m₀` to `Y` proper, Stacks 08K1 makes its base change to some `Y_i`
proper, and base change makes it proper at every later stage.

The index set may lie in any universe; it is required to be small compared to the cofinality of
the site's size cutoff, the convention of Stacks 07SF under which the situation of Stacks 084W
(`AlgebraicGeometry.Space.MorphismDescentSystem`, in which Stacks 08K1 is stated) is formed. That
bound makes the index set small in the universe of the site, and the situation is transported along
the order isomorphism with its `Shrink`; the distinguished stage is read there through the
identification of `Y_{e⁻¹(e 0)}` with `Y₀`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A base change of `m` along `q`, as a cartesian square.** For morphisms `m : T ⟶ V`,
`b : V ⟶ Y₀` and `q : Y' ⟶ Y₀` of presheaves, any `φ : Y' ×_{Y₀} T ⟶ Y' ×_{Y₀} V` with the two
components of the base change exhibits `φ` as the base change of `m` along the second projection
`Y' ×_{Y₀} V ⟶ V`. -/
theorem isPullback_snd_of_baseChange {T V Y₀ Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : T ⟶ V) (b : V ⟶ Y₀) (q : Y' ⟶ Y₀) (φ : pullback q (m ≫ b) ⟶ pullback q b)
    (hφ₁ : φ ≫ pullback.fst _ _ = pullback.fst _ _)
    (hφ₂ : φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ m) :
    IsPullback (pullback.snd q (m ≫ b)) φ m (pullback.snd q b) :=
  IsPullback.of_bot (by rw [hφ₁]; exact (IsPullback.of_hasPullback _ _).flip) hφ₂.symm
    (IsPullback.of_hasPullback _ _).flip

/-- **Properness of a base change is inherited by a later base change.** If `φ` and `φ'` are
base changes of one morphism `m` of algebraic spaces over `S`, along `n` and `n'`, and `n'`
factors through `n`, then `φ'` is proper as soon as `φ` is: `φ'` is then a base change of `φ`. -/
theorem isProper_of_isPullback_of_isPullback
    {T V P₁ P₂ P₁' P₂' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP₁ : IsAlgebraicSpace B S hS P₁) (hP₂ : IsAlgebraicSpace B S hS P₂)
    (hP₁' : IsAlgebraicSpace B S hS P₁') (hP₂' : IsAlgebraicSpace B S hS P₂')
    {m : T ⟶ V} {φ : P₁ ⟶ P₂} {s : P₁ ⟶ T} {n : P₂ ⟶ V} (h : IsPullback s φ m n)
    {φ' : P₁' ⟶ P₂'} {s' : P₁' ⟶ T} {n' : P₂' ⟶ V} (h' : IsPullback s' φ' m n')
    (c : P₂' ⟶ P₂) (hc : c ≫ n = n') (hφ : IsProper B S hS φ) : IsProper B S hS φ' := by
  let cT : P₁' ⟶ P₁ := h.lift s' (φ' ≫ c) (by rw [Category.assoc, hc, h'.w])
  have hleft : IsPullback cT φ' φ c := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [h.lift_fst]
    simpa [hc] using h'
  exact isProper_of_isPullback B S hS hP₁' hP₁ hP₂' hP₂ hleft hφ

end AlgebraicGeometry.Space


namespace AlgebraicGeometry.Space.DescentSituation

open AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]

/-- **Stacks 0CPZ, from Stacks 08K1.** In Situation 0CPY, with the index set small compared to the
cofinality of the site's size cutoff, let `f₀ : 𝒳₀ ⟶ Y₀` be a
1-morphism from a quasi-compact and quasi-separated algebraic stack to the distinguished stage.
If the base change `Y ×_{Y₀} 𝒳₀ ⟶ Y` to the limit is separated, then the base change
`Y_i ×_{Y₀} 𝒳₀ ⟶ Y_i` is separated for all sufficiently large `i`.

The descent of properness along a limit of bases, Stacks 08K1, is the argument `h08K1`. -/
theorem exists_isSeparated_stage_of_forall_isProper
    (h08K1 : ∀ {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
      (D' : MorphismDescentSystem B S hS hZ J),
      IsProper B S hS D'.mapLimit → IsLocallyOfFiniteType B S hS D'.map₀ →
        ∃ (j : J) (hj : D'.initial ≤ j), IsProper B S hS (D'.mapAt j hj))
    (D : DescentSituation B S hS hZ I)
    (hI : Cardinal.lift.{u} (Cardinal.mk I) < Cardinal.lift.{v} B.cutoff.ord.cof)
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
  -- the index set, transported to the universe of the site
  have : Small.{u} I := by
    obtain ⟨ι⟩ := Cardinal.lift_mk_le'.1 (hI.le.trans_eq (by rw [Cardinal.mk_out]) :
      Cardinal.lift.{u} (Cardinal.mk I) ≤
        Cardinal.lift.{v} (Cardinal.mk (B.cutoff.ord.cof).out))
    exact small_of_injective ι.injective
  let J := Shrink.{u} I
  let e : I ≃o J := orderIsoShrink I
  have : IsDirected J (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge (e.symm a) (e.symm b)
    exact ⟨e c, by simpa using e.monotone hac, by simpa using e.monotone hbc⟩⟩
  have hJ : Cardinal.mk J < B.cutoff.ord.cof := by
    have h₁ : Cardinal.lift.{v} (Cardinal.mk J) = Cardinal.lift.{u} (Cardinal.mk I) :=
      Cardinal.lift_mk_shrink'.{v, u} I
    have h₂ := hI
    rw [← h₁] at h₂
    exact Cardinal.lift_lt.1 h₂
  let E := e.symm.equivalence.op
  let sys : Jᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := E.functor ⋙ D.system
  -- the distinguished stage, read at `e 0`
  have hb₁ : D.base ≤ e.symm (e D.base) := (e.symm_apply_apply D.base).ge
  have hb₂ : e.symm (e D.base) ≤ D.base := (e.symm_apply_apply D.base).le
  let ι : sys.obj (op (e D.base)) ≅ Y₀ :=
    { hom := D.system.map
        (show E.functor.obj (op (e D.base)) ⟶ op D.base from (homOfLE hb₁).op)
      inv := D.system.map
        (show op D.base ⟶ E.functor.obj (op (e D.base)) from (homOfLE hb₂).op)
      hom_inv_id := (D.system.map_comp _ _).symm.trans
        ((congrArg D.system.map (Subsingleton.elim _ _)).trans (D.system.map_id _))
      inv_hom_id := (D.system.map_comp _ _).symm.trans
        ((congrArg D.system.map (Subsingleton.elim _ _)).trans (D.system.map_id _)) }
  -- the limit, read over the transported index set
  let cL := D.limitCone.whisker E.functor
  have hcL : IsLimit cL := D.isLimit.whiskerEquivalence E
  let eL : cL.pt ≅ limit sys := hcL.conePointUniqueUpToIso (limit.isLimit sys)
  -- the situation of Stacks 084W for `m₀` over the stages `Y_i`
  let b₀ := diagonalCoverStructureMap B S hS f₀ g₀ V₀ eV₀
  let D' : MorphismDescentSystem B S hS hZ J :=
    { base := sys
      indexSize := hJ
      base_isAlgebraicSpace := fun j => D.algebraicSpace (e.symm j)
      transition_affine := fun a => D.transition_affine _
      limit_isAlgebraicSpace := isAlgebraicSpace_of_iso B S hS eL D.limitAlgebraicSpace
      initial := e D.base
      source₀ := T₀
      target₀ := V₀
      sourceToBase := m₀ ≫ b₀ ≫ ι.inv
      targetToBase := b₀ ≫ ι.inv
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
  -- the base change of `m₀` along `q : Y' ⟶ Y₀`
  let φ : ∀ {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : Y' ⟶ Y₀),
      pullback q (m₀ ≫ b₀) ⟶ pullback q b₀ := fun q =>
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ m₀)
      (by rw [pullback.condition, Category.assoc])
  have hφ : ∀ {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : Y' ⟶ Y₀),
      IsPullback (pullback.snd q (m₀ ≫ b₀)) (φ q) m₀ (pullback.snd q b₀) := fun q =>
    isPullback_snd_of_baseChange B S hS m₀ b₀ q (φ q) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
  -- the criterion of `AlgebraicGeometry.Stack.isSeparated_baseChange_iff_isProper` at a base
  -- `q : Y' ⟶ Y₀`
  have key : ∀ {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
      (q : Y' ⟶ Y₀),
      AlgebraicStacks.IsSeparated B S hS
          (twoFibreProductSquareAlgebraicStacks B S hS f₀
            (algebraicSpaceStackMap.{u, w} B S hS hY' hY₀ q)).snd ↔
        IsProper B S hS (φ q) :=
    fun hY' q => isSeparated_baseChange_iff_isProper B S hS f₀ g₀ V₀ eV₀ T₀ eT₀ hV₀
      hT₀ hg₀ hY' q (φ q) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hPT : ∀ {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS Y')
      {Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS Y'')
      (q : Y' ⟶ Y'') (b : V₀ ⟶ Y''),
      IsAlgebraicSpace B S hS (pullback q (m₀ ≫ b)) ∧ IsAlgebraicSpace B S hS (pullback q b) :=
    fun hY' _ hY'' q b => ⟨isAlgebraicSpace_pullback B S hS _ _ hY' hT₀ hY'',
      isAlgebraicSpace_pullback B S hS _ _ hY' hV₀ hY''⟩
  -- at the limit
  let qc := D.limitCone.π.app (op D.base)
  have hL : IsProper B S hS (φ qc) := (key D.limitAlgebraicSpace _).1 hf
  have hqL : eL.inv ≫ qc = limit.π sys (op (e D.base)) ≫ ι.hom := by
    have h₁ := hcL.conePointUniqueUpToIso_inv_comp (limit.isLimit sys) (op (e D.base))
    have h₂ : cL.π.app (op (e D.base)) ≫ ι.hom = qc := D.limitCone.w _
    rw [← h₂, ← Category.assoc, h₁]
    rfl
  let cLim : pullback (limit.π sys (op (e D.base))) (b₀ ≫ ι.inv) ⟶ pullback qc b₀ :=
    pullback.lift (pullback.fst _ _ ≫ eL.inv) (pullback.snd _ _) (by
      rw [Category.assoc, hqL, ← Category.assoc, pullback.condition]
      simp)
  have hlim : IsProper B S hS D'.mapLimit :=
    isProper_of_isPullback_of_isPullback B S hS
      (hPT D.limitAlgebraicSpace hY₀ qc b₀).1 (hPT D.limitAlgebraicSpace hY₀ qc b₀).2
      (hPT D'.limit_isAlgebraicSpace (D.algebraicSpace _) _ _).1
      (hPT D'.limit_isAlgebraicSpace (D.algebraicSpace _) _ _).2
      (hφ qc)
      (isPullback_snd_of_baseChange B S hS m₀ (b₀ ≫ ι.inv) _ D'.mapLimit D'.mapLimit_fst
        D'.mapLimit_snd) cLim (pullback.lift_snd _ _ _) hL
  -- Stacks 08K1
  obtain ⟨j₀, h₀, hj₀⟩ := h08K1 D' hlim hm₀lft
  have hi₀ : D.base ≤ e.symm j₀ := hb₁.trans (e.symm.monotone h₀)
  refine ⟨e.symm j₀, hi₀, fun i hi => ?_⟩
  let qi := D.system.map (homOfLE (hi₀.trans hi)).op
  refine (key (D.algebraicSpace i) qi).2 ?_
  have hcomp : ∀ {a b c : Iᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c),
      D.system.map f ≫ D.system.map g = D.system.map h := fun f g h => by
    rw [← D.system.map_comp]
    exact congrArg D.system.map (Subsingleton.elim _ _)
  let t : D.system.obj (op i) ⟶ sys.obj (op j₀) :=
    D.system.map (show op i ⟶ E.functor.obj (op j₀) from (homOfLE hi).op)
  have hq : t ≫ D'.baseAtToInitial j₀ h₀ = qi ≫ ι.inv :=
    let k : op i ⟶ E.functor.obj (op (e D.base)) := (homOfLE (hb₂.trans (hi₀.trans hi))).op
    (hcomp _ _ k).trans (hcomp _ _ k).symm
  let ci : pullback qi b₀ ⟶ pullback (D'.baseAtToInitial j₀ h₀) (b₀ ≫ ι.inv) :=
    pullback.lift (pullback.fst _ _ ≫ t) (pullback.snd _ _) (by
      rw [Category.assoc, hq, ← Category.assoc, pullback.condition, Category.assoc])
  exact isProper_of_isPullback_of_isPullback B S hS
    (hPT (D.algebraicSpace (e.symm j₀)) (D.algebraicSpace _) _ _).1
    (hPT (D.algebraicSpace (e.symm j₀)) (D.algebraicSpace _) _ _).2
    (hPT (D.algebraicSpace i) hY₀ qi b₀).1 (hPT (D.algebraicSpace i) hY₀ qi b₀).2
    (isPullback_snd_of_baseChange B S hS m₀ (b₀ ≫ ι.inv) _ (D'.mapAt j₀ h₀)
      (D'.mapAt_fst j₀ h₀) (D'.mapAt_snd j₀ h₀))
    (hφ qi) ci (pullback.lift_snd _ _ _) hj₀

end AlgebraicGeometry.Space.DescentSituation

end
