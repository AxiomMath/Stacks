module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowFiniteCoverFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaReductions
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessPresentationToType
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFppfCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange

/-!
# Chow covers restrict to closed substacks

The first step of the proof of Chow's lemma for algebraic stacks (Stacks 0CQ8) embeds `𝒳` as a
closed substack of an algebraic stack `𝒳'` separated and of finite presentation over `Y`
(Stacks 0CQ2), and says that it suffices to prove the theorem for `𝒳'`. This file proves that
reduction: a Chow cover `X' ⟶ 𝒳'`, `X' ⊆ X̄'` of `𝒳'` restricts to one of `𝒳`. The restriction
`X'' = X' ×_{𝒳'} 𝒳` is closed in `X'`, so `X'' ⟶ X̄'` is a quasi-compact immersion, which is an
open immersion into a closed subspace `W` of `X̄'` (Stacks 081U), and `W` is proper over `Y`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosedImmersion_representingMap_of_isClosedImmersion`:
  a closed immersion between algebraic stacks represented by algebraic spaces induces a closed
  immersion of the representing algebraic spaces.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_of_twoIso_of_represented`:
  quasi-compactness of 1-morphisms between represented algebraic stacks is invariant under
  2-isomorphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_isClosedImmersion`: the conclusion of
  Stacks 0CQ8 passes from `f' : 𝒳' ⟶ Y` to `f = i ≫ f'` along a closed immersion `i`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_forall_isFinitePresentation`: granted
  the statement of Stacks 0CQ2, Chow's lemma reduces to separated 1-morphisms of finite
  presentation.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 081U](https://stacks.math.columbia.edu/tag/081U)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed immersion between algebraic stacks represented by algebraic spaces induces a closed
immersion of the representing algebraic spaces** (Stacks 04SW against Stacks 04YL, part (2)). -/
theorem isClosedImmersion_representingMap_of_isClosedImmersion
    {𝒜 𝒞 : AlgebraicStacks.{u, w} B S hS} (F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver 𝒞.val.val.p
      (presheafOfCategories (H ⋙ typeToCat)).p)
    (hF : IsAlgebraicSpace B S hS F) (hH : IsAlgebraicSpace B S hS H) (c : 𝒜 ⟶ 𝒞)
    (hc : IsClosedImmersion B S hS c) {r : F ⟶ H}
    (hr : representingMap B S hS 𝒜.val 𝒞.val F H eF eH c.hom = r) :
    Space.IsClosedImmersion B S hS r := by
  subst hr
  have _hloc : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    have := Space.isClosedImmersion_isLocalAtTarget_fpqc.{u, u} B S hS
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have h := (hasRelativeProperty_iff_prop_representingMap B S hS
    (Space.closedImmersionProperty B S hS) c.hom hc.1 F H hF hH eF eH).1 hc.2
  exact h

/-- **Quasi-compactness of 1-morphisms between algebraic stacks represented by algebraic spaces
is invariant under 2-isomorphism**: both are read off the induced morphism of representing
algebraic spaces (Stacks 050T and 04SW), which only depends on the 2-isomorphism class. -/
theorem isQuasiCompactMorphism_of_twoIso_of_represented {𝒜 𝒞 : AlgebraicStacks.{u, w} B S hS}
    (F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver 𝒞.val.val.p
      (presheafOfCategories (H ⋙ typeToCat)).p)
    (hF : IsAlgebraicSpace B S hS F) (hH : IsAlgebraicSpace B S hS H) {a b : 𝒜 ⟶ 𝒞}
    (η : a ≅ b) (ha : IsQuasiCompactMorphism.{u, w} B S hS a) :
    IsQuasiCompactMorphism.{u, w} B S hS b := by
  rw [isQuasiCompactMorphism_iff_isQuasiCompact_representingMap B S hS F H eF eH b hF hH,
    ← representingMap_congr_twoIso B S hS F H eF eH (Bicategory.InducedBicategory.isoHom η)]
  exact (isQuasiCompactMorphism_iff_isQuasiCompact_representingMap B S hS F H eF eH a hF hH).1 ha

/-- The restriction of a Chow cover along a closed immersion, for a given 2-fibre product
`X' ×_{𝒳'} 𝒳`. -/
private theorem HasChowCover.of_isClosedImmersion_aux {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (hf' : IsFiniteType B S hS f')
    (i : 𝒳 ⟶ 𝒳') (hi : IsClosedImmersion B S hS i) (e : i ≫ f' ≅ f)
    {X' Xbar' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hXbar' : IsAlgebraicSpace B S hS Xbar')
    (a' : algebraicSpaceStack.{u, w} B S hS X' hX' ⟶ 𝒳') (j' : X' ⟶ Xbar') (p' : Xbar' ⟶ Y)
    (ha' : IsProper B S hS a') (has' : IsSurjective B S hS a')
    (hj' : Space.IsOpenImmersion B S hS j') (hp' : Space.IsProper B S hS p')
    (ea : a' ≫ f' ≅ algebraicSpaceStackMap.{u, w} B S hS hX' hY (j' ≫ p'))
    (P : Bicategory.TwoCommSq a' i) (hP : Bicategory.IsTwoFibreProduct P) :
    HasChowCover.{u, w} B S hS hY f := by
  have hPfst : IsClosedImmersion B S hS P.fst := isClosedImmersion_baseChange B S hS P hP hi
  -- the restriction `X'' = X' ×_{𝒳'} 𝒳` is an algebraic space
  obtain ⟨X'', hX'', ⟨eX''⟩⟩ := isRepresentableByAlgebraicSpace_of_representable B S hS
    P.pt.val (algebraicSpaceStack.{u, w} B S hS X' hX').val P.fst.hom hPfst.1
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS X' hX')
  obtain ⟨c, hc⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS X'' hX'') (𝒴 := P.pt) X'' X''
    (StacksRepresentableCFG.EquivalenceOver.refl _) eX'' (𝟙 X'')
  obtain ⟨r, hrdef⟩ : ∃ r : X'' ⟶ X', representingMap B S hS P.pt.val
      (algebraicSpaceStack.{u, w} B S hS X' hX').val X'' X' eX''
      (StacksRepresentableCFG.EquivalenceOver.refl _) P.fst.hom = r := ⟨_, rfl⟩
  have hr := isClosedImmersion_representingMap_of_isClosedImmersion B S hS X'' X' eX''
    (StacksRepresentableCFG.EquivalenceOver.refl _) hX'' hX' P.fst hPfst rfl
  rw [hrdef] at hr
  have hcr : representingMap B S hS (algebraicSpaceStack.{u, w} B S hS X'' hX'').val
      (algebraicSpaceStack.{u, w} B S hS X' hX').val X'' X'
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (c ≫ P.fst).hom = r := by
    have h := representingMap_comp B S hS X'' X'' X'
      (StacksRepresentableCFG.EquivalenceOver.refl _) eX''
      (StacksRepresentableCFG.EquivalenceOver.refl _) c.hom P.fst.hom
    rw [hc, Category.id_comp, hrdef] at h
    exact h
  obtain ⟨ec⟩ := nonempty_iso_algebraicSpaceStackMap_of_representingMap_eq B S hS hX'' hX'
    (c ≫ P.fst) r hcr
  -- `X' ⟶ X̄'` is quasi-compact
  have hqa : Space.IsQuasiCompact B S hS (j' ≫ p') :=
    (isQuasiCompactMorphism_algebraicSpaceStackMap_iff B S hS hX' hY (j' ≫ p')).1
      (isQuasiCompactMorphism_of_twoIso_of_represented B S hS X' Y
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) hX' hY ea
        (isQuasiCompactMorphism_comp B S hS a' f' ha'.2.1.2 hf'.2))
  have hj'q : Space.IsQuasiCompact B S hS j' :=
    Space.isQuasiCompact_of_comp_of_isQuasiSeparated B S hS j' p' hX' hY hqa
      (Space.isQuasiSeparated_of_isSeparated B S hS hp'.1)
  have himm : Space.IsImmersion B S hS (r ≫ j') :=
    Space.isImmersion_comp B S hS r j' (Space.isImmersion_of_isClosedImmersion B S hS hr)
      (Space.isImmersion_of_isOpenImmersion B S hS hj')
  have hrq : Space.IsQuasiCompact B S hS (r ≫ j') :=
    Space.isQuasiCompact_comp B S hS hX' hXbar' r j'
      (Space.isQuasiCompact_of_isClosedImmersion B S hS r hX'' hX' hr) hj'q
  -- Stacks 081U: `X'' ⟶ X̄'` is an open immersion into a closed subspace `W`
  obtain ⟨W, j, k, hW, hj, hk, hjk⟩ :=
    Space.exists_isOpenImmersion_isClosedImmersion_comp_eq_of_isQuasiCompact B S hS hXbar'
      (r ≫ j') himm hrq
  have hcP : IsProper B S hS c := by
    refine (isProper_iff_isProper_representingMap B S hS X'' X''
      (StacksRepresentableCFG.EquivalenceOver.refl _) eX'' c hX'' hX'').2 ?_
    rw [hc]
    exact Space.isProper_of_isIso B S hS (𝟙 X'')
  have hcS : IsSurjective B S hS c := by
    refine isSurjective_of_isSurjective_representingMap B S hS X'' X'' hX'' hX''
      (StacksRepresentableCFG.EquivalenceOver.refl _) eX'' c ?_
    rw [hc]
    intro x
    exact ⟨x, by rw [Space.pointsMap_id, id_eq]⟩
  have hcomp : algebraicSpaceStackMap.{u, w} B S hS hX'' hX' r ≫
      algebraicSpaceStackMap.{u, w} B S hS hX' hY (j' ≫ p') =
      algebraicSpaceStackMap.{u, w} B S hS hX'' hY (j ≫ k ≫ p') := by
    rw [← algebraicSpaceStackMap_comp B S hS hX'' hX' hY, ← Category.assoc, ← hjk,
      Category.assoc]
  refine ⟨X'', W, hX'', hW, c ≫ P.snd, j, k ≫ p',
    isProper_comp B S hS c P.snd hcP
      (isProper_baseChange B S hS a' i P.swap (Bicategory.isTwoFibreProduct_swap hP) ha'),
    isSurjective_comp B S hS c P.snd hcS (isSurjective_of_isTwoFibreProduct B S hS P hP has'), hj,
    Space.isProper_comp B S hS hW hXbar' hY k p'
      (Space.isProper_of_isClosedImmersion B S hS hW hXbar' k hk) hp', ⟨?_⟩⟩
  exact Bicategory.whiskerLeftIso (c ≫ P.snd) e.symm ≪≫ Bicategory.associator _ _ _ ≪≫
    Bicategory.whiskerLeftIso c ((Bicategory.associator _ _ _).symm ≪≫
      Bicategory.whiskerRightIso P.iso.symm f' ≪≫ Bicategory.associator _ _ _) ≪≫
    (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso ec (a' ≫ f') ≪≫
    Bicategory.whiskerLeftIso _ ea ≪≫ eqToIso hcomp

/-- **Chow covers restrict along closed immersions** (the first reduction of the proof of
Stacks 0CQ8). Let `i : 𝒳 ⟶ 𝒳'` be a closed immersion of algebraic stacks, `f' : 𝒳' ⟶ Y` a
1-morphism of finite type to an algebraic space and `f ≅ i ≫ f'`. If the conclusion of Chow's
lemma holds for `f'`, it holds for `f`.

Given the cover `a' : X' ⟶ 𝒳'` and `X' ⊆ X̄'`, the 2-fibre product `X'' = X' ×_{𝒳'} 𝒳` is an
algebraic space (Stacks 0300) proper and surjective over `𝒳` and closed in `X'`. The composite
`X'' ⟶ X' ⟶ X̄'` is a quasi-compact immersion, `X' ⟶ X̄'` being quasi-compact because `X' ⟶ Y` is
and `X̄' ⟶ Y` is separated; by Stacks 081U it is an open immersion into a closed subspace `W` of
`X̄'`, and `W ⟶ Y` is proper. -/
theorem HasChowCover.of_isClosedImmersion {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (hf' : IsFiniteType B S hS f')
    (i : 𝒳 ⟶ 𝒳') (hi : IsClosedImmersion B S hS i) (e : i ≫ f' ≅ f)
    (h' : HasChowCover.{u, w} B S hS hY f') :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨X', Xbar', hX', hXbar', a', j', p', ha', has', hj', hp', ⟨ea⟩⟩ := h'
  exact HasChowCover.of_isClosedImmersion_aux B S hS hY f f' hf' i hi e hX' hXbar' a' j' p' ha'
    has' hj' hp' ea _ (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a' i)

/-- **The first reduction of the proof of Stacks 0CQ8: finite presentation suffices.** Granted
the statement of Stacks 0CQ2 (`h0CQ2`: a separated 1-morphism of finite type `𝒳 ⟶ Y` to a
quasi-compact quasi-separated algebraic space factors as a closed immersion followed by a
separated 1-morphism of finite presentation), if the conclusion of Chow's lemma holds for every
separated 1-morphism of finite presentation to a quasi-compact quasi-separated algebraic space,
it holds for every separated 1-morphism of finite type.

**Unregistered: `h0CQ2` is a hypothesis**, a form of Stacks 0CQ2
(`AlgebraicGeometry.Stack.exists_separated_finitePresentation_closedImmersion`) with
exactly this conclusion. -/
theorem HasChowCover.of_forall_isFinitePresentation
    (h0CQ2 : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
      (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
      IsFiniteType B S hS f → IsSeparated B S hS f → Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
        ∃ (𝒳' : AlgebraicStacks.{u, w} B S hS)
          (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (i : 𝒳 ⟶ 𝒳'),
          IsSeparated B S hS f' ∧ IsFinitePresentation B S hS f' ∧
            IsClosedImmersion B S hS i ∧ Nonempty (i ≫ f' ≅ f))
    (hfp : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f → IsFinitePresentation B S hS f → HasChowCover.{u, w} B S hS hY f)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨𝒳', f', i, hsep', hfp', hi, ⟨e⟩⟩ := h0CQ2 Y hY 𝒳 f hft hsep hYqc hYqs
  exact HasChowCover.of_isClosedImmersion B S hS hY f f'
    (isFiniteType_of_isFinitePresentation B S hS f' hfp') i hi e
    (hfp Y hY hYqc hYqs 𝒳' f' hsep' hfp')

end AlgebraicGeometry.Stack.AlgebraicStacks

end
