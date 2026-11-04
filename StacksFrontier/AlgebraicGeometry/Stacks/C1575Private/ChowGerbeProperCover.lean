module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeOpenImage
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowCompactifiableCoverGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperClosedImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCompositionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverInduction
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Proper covers with an open compactification for a separated morphism with gerbe locus

This file assembles [Stacks, Tag 0CQ7]: let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite type
from an algebraic stack to a quasi-compact quasi-separated algebraic space, and let `V ⊆ Y` be a
quasi-compact open subspace with `𝒳_V ⟶ V` a gerbe. Then there are an open immersion `Z ⟶ Z̄`, a
proper `Z̄ ⟶ Y` and a proper `Z ⟶ 𝒳` over `Y` such that `|V|` lies in the image of `|Z|`.

The proof is the source's:

* by Stacks 09YC there is a finite surjective `W ⟶ Y` with `W` a scheme; by the initial remark
  (`AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover.of_baseChange`) it
  suffices to treat `𝒳 ×_Y W ⟶ W` and the inverse image of `V`, over which the base change is
  again a gerbe;
* over a scheme, a gerbe is flat and locally of finite presentation (Stacks 06QI), so Stacks 0CQ4
  gives a `V`-admissible blowup `b : Y' ⟶ Y` and a closed substack `𝒳' ⊆ 𝒳_{Y'}` which is flat and
  of finite presentation over `Y'` and contains every object over `b⁻¹V`; by the initial remark
  (`AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover.of_proper`) it suffices to
  treat `𝒳' ⟶ Y'` and `b⁻¹V`, over which `𝒳'` is still a gerbe since it contains everything over
  `b⁻¹V`;
* the flat case is `ChowGerbeOpenImage.hasProperCompactifiableCover_of_isFlat`, in the namespace
  `AlgebraicGeometry.Stack.AlgebraicStacks`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasProperCompactifiableCover_of_isGerbeOver`:
  [Stacks, Tag 0CQ7].

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

namespace ChowGerbeProperCover

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A gerbe stays a gerbe after restricting to a substack through which the base change
factors.** Let `ι : 𝒱 ⟶ 𝒴`, `f₂ : 𝒵 ⟶ 𝒴`, and `i : 𝒳' ⟶ 𝒵` a monomorphism such that the projection
`𝒱 ×_𝒴 𝒵 ⟶ 𝒵` factors through `i` up to 2-isomorphism. If `𝒱 ×_𝒴 𝒵 ⟶ 𝒱` is a gerbe, so is
`𝒱 ×_𝒴 𝒳' ⟶ 𝒱`: the two are 2-fibre products of the same cospan, because the base change of `i`
along a 1-morphism factoring through it is an equivalence (Stacks 04ZZ). -/
theorem isGerbeOver_fst_comp_of_factorsThrough {𝒱 𝒴 𝒵 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (ι : 𝒱 ⟶ 𝒴) (f₂ : 𝒵 ⟶ 𝒴) (i : 𝒳' ⟶ 𝒵) (hi : IsMonomorphism B S hS i)
    (g : (twoFibreProductSquareAlgebraicStacks B S hS ι f₂).pt ⟶ 𝒳')
    (θ : g ≫ i ≅ (twoFibreProductSquareAlgebraicStacks B S hS ι f₂).snd)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS ι f₂).fst) :
    IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS ι (i ≫ f₂)).fst := by
  let R₂ := twoFibreProductSquareAlgebraicStacks B S hS ι f₂
  have hR₂ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS ι f₂
  -- the square of the factorization of `R₂.snd` through the monomorphism `i`
  let T := ((selfCospanSquare B S hS i).pasteSnd
    (Bicategory.TwoCommSq.idCospan g)).swap.reindexFst θ
  have hT : Bicategory.IsTwoFibreProduct T :=
    Bicategory.isTwoFibreProduct_reindexFst θ (Bicategory.isTwoFibreProduct_swap
      (Bicategory.isTwoFibreProduct_pasteSnd _ (isTwoFibreProduct_selfCospanSquare B S hS i hi) _
        (Bicategory.isTwoFibreProduct_idCospan g)))
  have hP := Bicategory.isTwoFibreProduct_paste hR₂ hT
  have hR' := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS ι (i ≫ f₂)
  let ρ := Quotient.out (hR'.from (R₂.paste T))
  have hρ := isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS hP hR' ρ
  exact isGerbeOver_of_isEquivalence_comp B S hS ρ.hom _ _ hρ ρ.isoFst.symm hG

/-- The source of a proper morphism of algebraic spaces with quasi-compact, quasi-separated target
is quasi-compact and quasi-separated. -/
private theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isProper
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {g : X ⟶ Y} (hg : Space.IsProper B S hS g)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    Space.IsQuasiCompactSpace B S hS X ∧
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X :=
  ⟨Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hg.2.1.2,
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hX hYqs
      (Space.isQuasiSeparated_of_isSeparated B S hS hg.1)⟩

/-- **[Stacks, Tag 0CQ7] over a scheme base.** The conclusion of Stacks 0CQ7 for `f : 𝒳 ⟶ T` with
`T` an object of the site whose represented algebraic space is quasi-compact and
quasi-separated: Stacks 0CQ4 (over a scheme) flattens `f` by a `V`-admissible blowup, the
initial remark of the proof reduces to the flat substack, and the flat case concludes. -/
theorem hasProperCompactifiableCover_of_yoneda (T : BigFppfOver B S hS)
    (hY : IsAlgebraicSpace B S hS (yoneda.obj T))
    (hYqc : Space.IsQuasiCompactSpace B S hS (yoneda.obj T))
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (yoneda.obj T))
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj T) hY)
    (hfs : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (V : Subfunctor (yoneda.obj T)) (hV : Space.IsOpenSubspace B S hS V)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  classical
  -- a gerbe is flat and locally of finite presentation (Stacks 06QI)
  obtain ⟨hfl, hlfp⟩ := isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS _ hG
  -- Stacks 0CQ4 over a scheme
  obtain ⟨Y', b, hadm, Pp, hPc, hPV, hPfl⟩ :=
    exists_isAdmissibleBlowup_isClosedSubstack_isFlat_isFinitePresentation_of_yoneda
      T hY hYqc hYqs f hft (isQuasiSeparated_of_isSeparated B S hS hfs) V hV hVqc hfl hlfp
  have hb : Space.IsProper B S hS b.hom := Space.IsAdmissibleBlowup.isProper B S hS hadm
  let Q₂ := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f
  have hQ₂ : Bicategory.IsTwoFibreProduct Q₂ := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  obtain ⟨hPiso, hPalg, hci⟩ := hPc
  let i := fullSubcategoryInclusion Q₂.pt Pp hPalg
  obtain ⟨hf'fl, hf'fp⟩ := hPfl hPalg
  -- `Y'` is quasi-compact and quasi-separated, and `𝒳' ⟶ Y'` is separated
  obtain ⟨hY'qc, hY'qs⟩ :=
    isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isProper Y'.2 hY hb hYqc hYqs
  have hf'sep : IsSeparated B S hS (i ≫ Q₂.fst) :=
    isSeparated_comp B S hS i Q₂.fst (isSeparated_of_isClosedImmersion B S hS i hci)
      (isSeparated_baseChange_of_isTwoFibreProduct B S hS f _ Q₂.swap
        (Bicategory.isTwoFibreProduct_swap hQ₂) hfs)
  -- the open `V' = b⁻¹V`
  have hV' := Space.isOpenSubspace_preimage B S hS b.hom V hY Y'.2 hV
  have hV'qc : Space.IsQuasiCompactSpace B S hS (V.preimage b.hom).toFunctor :=
    Space.isQuasiCompactSpace_preimage_toFunctor B S hS B.contains_terminal hY hYqs Y'.2 hY'qc V
      hVqc b.hom
  -- `𝒳_{Y'}` is a gerbe over `V'`, and so is `𝒳'`, which contains every object over `V'`
  have hG₂ := isGerbeOver_baseChange_preimage hY Y'.2 f b.hom V hV hG
  have hfac : FactorsThroughSubstack (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 (V.preimage b.hom).ι) Q₂.fst).snd Pp := by
    have := hPiso
    rw [factorsThroughSubstack_iff_forall]
    intro X
    let R₂ := twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 (V.preimage b.hom).ι) Q₂.fst
    have hEq : R₂.fst ≫ algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 (V.preimage b.hom).ι =
        R₂.snd ≫ Q₂.fst :=
      Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS R₂.iso.hom.hom)
    have hz : Q₂.fst.hom.hom.obj (R₂.snd.hom.hom.obj X) =
        (algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 (V.preimage b.hom).ι).hom.hom.obj
          (R₂.fst.hom.hom.obj X) :=
      (congrArg (fun F => F.hom.hom.obj X) hEq).symm
    refine hPV _ ?_
    rw [hz]
    exact (R₂.fst.hom.hom.obj X).fiber.as.2
  have hi : IsMonomorphism B S hS i := by
    obtain ⟨h1, h2⟩ := full_and_faithful_homFunctor_of_isClosedImmersion B S hS i hci
    exact isMonomorphism_of_full_and_faithful B S hS i h1 h2
  have hG' := isGerbeOver_fst_comp_of_factorsThrough _ Q₂.fst i hi
    (factorsThroughSubstackHom _ hPalg hfac) (factorsThroughSubstackIso _ hPalg hfac) hG₂
  -- the flat case for `𝒳' ⟶ Y'`
  have h' : HasProperCompactifiableCover.{u, w} B S hS Y'.2 (i ≫ Q₂.fst) (V.preimage b.hom) :=
    ChowGerbeOpenImage.hasProperCompactifiableCover_of_isFlat hY'qc hY'qs hf'sep hf'fp.2.1 hf'fl
      hf'fp.1 hV' hV'qc hG'
  -- the initial remark of the proof
  have ha : IsProper B S hS (i ≫ Q₂.snd) :=
    isProper_comp B S hS _ _ (isProper_of_isClosedImmersion B S hS i hci)
      (isProper_baseChange B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f Q₂.swap
        (Bicategory.isTwoFibreProduct_swap hQ₂)
        ((isProper_algebraicSpaceStackMap_iff.{u, w} B S hS Y'.2 hY b.hom).2 hb))
  refine HasProperCompactifiableCover.of_proper B S hS hY Y'.2 f (i ≫ Q₂.fst) b.hom hb
    (i ≫ Q₂.snd) ha (Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso i Q₂.iso.symm ≪≫
      (Bicategory.associator _ _ _).symm) V (V.preimage b.hom) ?_ h'
  intro v hv
  have hv' : v ∈ Set.range (Space.pointsMap B S hS V.toFunctor (V.ι ≫ 𝟙 _)) := by
    rwa [Category.comp_id]
  obtain ⟨z, hz⟩ := ChowGerbeMerge.range_pointsMap_subset_of_isAdmissibleBlowup hadm (𝟙 _) hv'
  refine ⟨Space.pointsMap B S hS _ (V.preimage b.hom).ι z, ⟨z, rfl⟩, ?_⟩
  rw [← hz, Category.comp_id, Space.pointsMap_comp_apply]

end ChowGerbeProperCover

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **[Stacks, Tag 0CQ7].** Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an
algebraic space and `V ⊆ Y` an open subspace. Assume that `f` is separated and of finite type,
that `Y` is quasi-compact and quasi-separated, that `V` is quasi-compact, and that `𝒳_V` is a
gerbe over `V`. Then there are algebraic spaces `Z`, `Z̄`, an open immersion `j : Z ⟶ Z̄`, a proper
`ḡ : Z̄ ⟶ Y` and a proper `h : Z ⟶ 𝒳` with `h ≫ f` 2-isomorphic to `g = j ≫ ḡ`, such that `|V|`
is contained in the image of `|g|`. -/
@[stacks 0CQ7]
theorem hasProperCompactifiableCover_of_isGerbeOver {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hfs : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  -- Stacks 09YC: a finite surjective cover by a scheme
  obtain ⟨W, g, hgs, hgf⟩ := Space.existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace B S hS
    B.contains_terminal Y hY hYqc hYqs
  have hW := isAlgebraicSpace_yoneda B S hS W
  have hg : Space.IsProper B S hS g :=
    (Space.isProper_and_isLocallyQuasiFinite_of_isFinite B S hS hW hY g hgf).1
  refine HasProperCompactifiableCover.of_baseChange B S hS hY hW f g hg hgs V ?_
  let Q := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hW hY g) f
  have hQ : Bicategory.IsTwoFibreProduct Q := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  obtain ⟨hWqc, hWqs⟩ :=
    ChowGerbeProperCover.isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isProper hW hY hg
      hYqc hYqs
  have hV₁ := Space.isOpenSubspace_preimage B S hS g V hY hW hV
  exact ChowGerbeProperCover.hasProperCompactifiableCover_of_yoneda W hW hWqc hWqs Q.fst
    (isSeparated_baseChange_of_isTwoFibreProduct B S hS f _ Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) hfs)
    ⟨isLocallyOfFiniteType_baseChange B S hS f _ Q hQ hft.1,
      Stack.isQuasiCompactMorphism_baseChange B S hS f _ _ hQ hft.2⟩
    (V.preimage g) hV₁
    (Space.isQuasiCompactSpace_preimage_toFunctor B S hS B.contains_terminal hY hYqs hW hWqc V
      hVqc g)
    (isGerbeOver_baseChange_preimage hY hW f g V hV hG)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
