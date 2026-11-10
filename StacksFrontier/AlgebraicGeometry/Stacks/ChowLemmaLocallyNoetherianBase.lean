module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.SectionExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowFiniteCoverFactorizationUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.Main
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaAssembly
public import StacksFrontier.AlgebraicGeometry.Stacks.StackFlatteningByBlowupLocallyNoetherian

/-!
# Chow's lemma for algebraic stacks over a Noetherian algebraic space

Let `Y` be a Noetherian algebraic space and `f : 𝒳 ⟶ Y` a separated 1-morphism of finite type
from an algebraic stack. Then there are algebraic spaces `X ⊆ X̄`, a proper surjective
1-morphism `X ⟶ 𝒳` and a proper `X̄ ⟶ Y` with `X ⟶ 𝒳 ⟶ Y` 2-isomorphic to `X ⟶ X̄ ⟶ Y`: this
is Chow's lemma for algebraic stacks ([Stacks, Tag 0CQ8]) over a Noetherian base, which is the
case its proof reduces to and the case used in the proof of [Stacks, Tag 0CQM].

## Main results

* `AlgebraicStacks.hasProperCompactifiableCover_of_isGerbeOver_of_noetherian`:
  [Stacks, Tag 0CQ7] over a quasi-compact, quasi-separated, locally Noetherian base.
* `AlgebraicStacks.hasChowCover_of_isNoetherian_of_isReducedStack_of_noetherian`:
  [Stacks, Tag 0CQ8] over a Noetherian algebraic space, for a reduced source; the general
  Noetherian case is the base's `AlgebraicStacks.hasChowCover_of_isNoetherian`.

## Implementation notes

The proofs are those of the source, in the forms of
`AlgebraicGeometry.Stack.AlgebraicStacks.hasProperCompactifiableCover_of_flat_case`,
`AlgebraicGeometry.Stack.AlgebraicStacks.hasProperCompactifiableCover_of_isGerbeOver_of` and
`AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_isNoetherian_of_isReducedStack`, with
their inputs supplied: Stacks 0CQ4 over the locally Noetherian base
(`exists_isAdmissibleBlowup_isClosedSubstack_isFlat_of_noetherian`),
Stacks 0CQ6 (`AlgebraicGeometry.Stack.exists_finite_surjective_zariskiLocal_factorization`) and
Stacks 0CPI (`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_extending_section_of_isProper`).
In the proof of Stacks 0CQ8 over a Noetherian `Y`, Stacks 0CQ7 is applied to an algebraic space
proper over `Y`, hence locally Noetherian, so Stacks 0CQ7 over a locally Noetherian base suffices.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The swap of the pasting of two canonical 2-fibre products `(a, g)` and `(k, fst)` is a
2-fibre product. -/
private noncomputable def isTwoFibreProduct_swap_pasteFst_twoFibreProductSquare
    {A C Z T : AlgebraicStacks.{u, w} B S hS} (a : A ⟶ Z) (g : C ⟶ Z) (k : T ⟶ A) :
    Bicategory.IsTwoFibreProduct
      ((twoFibreProductSquare B S hS a g).pasteFst
        (twoFibreProductSquare B S hS k (twoFibreProductSquare B S hS a g).fst)).swap :=
  Bicategory.isTwoFibreProduct_swap (Bicategory.isTwoFibreProduct_pasteFst _
    (isTwoFibreProduct_twoFibreProductSquare B S hS a g) _
    (isTwoFibreProduct_twoFibreProductSquare B S hS k _))

/-- Let `b : Y' ⟶ Y` be a 1-morphism of algebraic spaces, `V ⊆ Y` an open subspace with `𝒳_V` a
gerbe over `V`, and `𝒳' ⊆ 𝒳 ×_Y Y'` a full substack containing every object over `V' = b⁻¹V`.
Then `𝒳'_{V'}` is a gerbe over `V'`. -/
private theorem isGerbeOver_fst_fullSubcategory_of_isGerbeOver
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    {Y' : AlgebraicSpaces B S hS} (b : Y' ⟶ ⟨Y, hY⟩)
    (hV' : Space.IsOpenSubspace B S hS (V.preimage b.hom))
    (P : ObjectProperty (twoFibreProductSquare B S hS
      (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).pt.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased _ P))
    (hPV : ∀ x, ((twoFibreProductSquare B S hS
      (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj x).fiber.as ∈
        (V.preimage b.hom).obj (op ((twoFibreProductSquare B S hS
          (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj x).base) → P x)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    IsGerbeOver B S hS (twoFibreProductSquare B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 (V.preimage b.hom).ι)
      (fullSubcategoryInclusion _ P hP ≫ (twoFibreProductSquare B S hS
        (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst)).fst := by
  let Q := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f
  let V' : Subfunctor Y'.1 := V.preimage b.hom
  let c : V'.toFunctor ⟶ V.toFunctor := V.fromPreimage b.hom
  have hcι : c ≫ V.ι = V'.ι ≫ b.hom := Subfunctor.fromPreimage_ι V b.hom
  -- `(𝒳 ×_Y Y')_{V'} ⟶ V'` is a gerbe: two pastings of 2-fibre products over `V' ⟶ Y`.
  let GV := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f
  let W := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV'.1 hV.1 c) GV.fst
  have hW : Bicategory.IsTwoFibreProduct W :=
    isTwoFibreProduct_twoFibreProductSquare B S hS _ GV.fst
  have hWg : IsGerbeOver B S hS W.fst :=
    isGerbeOver_of_isTwoFibreProduct B S hS W.swap (Bicategory.isTwoFibreProduct_swap hW) hG
  let T := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 V'.ι)
    Q.fst
  have heq : algebraicSpaceStackMap.{u, w} B S hS hV'.1 hV.1 c ≫
        algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι =
      algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 V'.ι ≫
        algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom := by
    rw [← algebraicSpaceStackMap_comp, ← algebraicSpaceStackMap_comp, hcι]
  have hTg : IsGerbeOver B S hS T.fst :=
    isGerbeOver_snd_of_isGerbeOver_snd B S hS
      (Bicategory.isTwoFibreProduct_reindexSnd (eqToIso heq)
        (isTwoFibreProduct_swap_pasteFst_twoFibreProductSquare B S hS _ f _))
      (isTwoFibreProduct_swap_pasteFst_twoFibreProductSquare B S hS _ f _) hWg
  -- Every object of `(𝒳 ×_Y Y')_{V'}` lies in `𝒳'`, so `𝒳'_{V'} ⟶ V'` is a gerbe too.
  have hTP : ∀ d : T.pt.val.val.obj, P (T.snd.hom.hom.obj d) := by
    rintro ⟨U, x, y, hx, hy, e, he⟩
    refine hPV _ ?_
    have h : (Q.fst.hom.hom.obj y).fiber.as = Y'.1.map e.inv.base.op x.fiber.as.1 :=
      Discrete.eq_of_hom e.inv.fiber
    change (Q.fst.hom.hom.obj y).fiber.as ∈ V'.obj (op (Q.fst.hom.hom.obj y).base)
    rw [h]
    exact V'.map e.inv.base.op x.fiber.as.2
  let R := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV'.1 Y'.2 V'.ι)
    (fullSubcategoryInclusion Q.pt P hP ≫ Q.fst)
  let E := TwoFibreProductOver.fullSubcategorySndEquivalence P hTP
  let u : T.pt ⟶ R.pt := Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom ⟨E.functor, rfl⟩)
  exact isGerbeOver_of_isEquivalence_comp B S hS u R.fst T.fst E.isEquivalence_functor
    (Iso.refl _) hTg

/-- **The reduction of Stacks 0CQ7 to a flat 1-morphism of finite presentation, over a locally
Noetherian base.** Let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite type from an algebraic
stack to a quasi-compact, quasi-separated and locally Noetherian algebraic space, and `V ⊆ Y` a
quasi-compact open subspace with `𝒳_V` a gerbe over `V`. Given the conclusion of Stacks 0CQ7 for
flat 1-morphisms of finite presentation (`hflat`), the conclusion of Stacks 0CQ7 holds for
`(f, V)`.

The proof is that of `hasProperCompactifiableCover_of_flat_case`, with Stacks 0CQ4 over the
locally Noetherian base. -/
theorem hasProperCompactifiableCover_of_flat_case_of_noetherian
    (hflat : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
      (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
      (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      IsSeparated B S hS f → IsFiniteType B S hS f → IsFlat B S hS f →
      IsFinitePresentation B S hS f → Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      Space.IsQuasiCompactSpace B S hS V.toFunctor →
      IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst →
      HasProperCompactifiableCover.{u, w} B S hS hY f V)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hYN : Space.HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  -- Stacks 06QI: the gerbe `𝒳_V ⟶ V` is flat and locally of finite presentation.
  obtain ⟨hGfl, hGlfp⟩ := isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS _ hG
  -- Stacks 0CQ4.
  obtain ⟨Y', b, hb, P, hPc, hPV, hPfl⟩ :=
    exists_isAdmissibleBlowup_isClosedSubstack_isFlat_of_noetherian B S hS
      hY hYqc hYqs hYN f hft (isQuasiSeparated_of_isSeparated B S hS hsep) V hV hVqc hGfl hGlfp
  obtain ⟨-, hP, hci⟩ := hPc
  let Q := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f
  have hQ : Bicategory.IsTwoFibreProduct Q := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  let ι := fullSubcategoryInclusion Q.pt P hP
  let f' : fullSubcategoryAlgebraicStack Q.pt P hP ⟶
    algebraicSpaceStack.{u, w} B S hS Y'.1 Y'.2 := ι ≫ Q.fst
  -- `𝒳' ⟶ 𝒳` is proper.
  have hbp : Space.IsProper B S hS b.hom := Space.IsAdmissibleBlowup.isProper B S hS hb
  have hQsnd : IsProper B S hS Q.snd :=
    isProper_baseChange B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ)
      ((isProper_algebraicSpaceStackMap_iff.{u, w} B S hS Y'.2 hY b.hom).2 hbp)
  have ha : IsProper B S hS (ι ≫ Q.snd) :=
    isProper_comp B S hS ι Q.snd (isProper_of_isClosedImmersion B S hS ι hci) hQsnd
  -- `𝒳' ⟶ Y'` is separated, flat and of finite presentation, hence of finite type.
  have hf'sep : IsSeparated B S hS f' :=
    isSeparated_comp B S hS ι Q.fst (isSeparated_of_isClosedImmersion B S hS ι hci)
      (isSeparated_baseChange_of_isTwoFibreProduct B S hS f _ Q.swap
        (Bicategory.isTwoFibreProduct_swap hQ) hsep)
  obtain ⟨hf'fl, hf'fp⟩ := hPfl hP
  have hf'ft : IsFiniteType B S hS f' := isFiniteType_of_isFinitePresentation B S hS f' hf'fp
  -- `Y'` is quasi-compact and quasi-separated, being proper over `Y`.
  have hY'qc : Space.IsQuasiCompactSpace B S hS Y'.1 :=
    Space.isQuasiCompactSpace_of_isQuasiCompact B S hS hY hYqc b.hom hbp.2.1.2
  have hY'qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y'.1 :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal Y'.2 hYqs
      (Space.isQuasiSeparated_of_isSeparated B S hS hbp.1)
  -- `b` restricts to an isomorphism `V' = b⁻¹V ≅ V`, `V` missing the centre (Stacks 085T).
  let V' : Subfunctor Y'.1 := V.preimage b.hom
  have hV' : Space.IsOpenSubspace B S hS V' :=
    Space.isOpenSubspace_preimage B S hS b.hom V hY Y'.2 hV
  have hc : IsIso (V.fromPreimage b.hom) := by
    obtain ⟨Z, -, hdisj, hbl⟩ := hb
    refine Space.isIso_fromPreimage_of_le b.hom (Space.le_of_range_pointsMap_ι_subset B S hS
      (Space.openComplementOfClosedSubspace B S hS ⟨Y, hY⟩ Z).2 ?_)
      (Space.isIso_fromPreimage_openComplement hbl)
    change Space.subspacePointSet B S hS Y V ⊆ Space.subspacePointSet B S hS Y _
    rw [Space.subspacePointSet_openComplement]
    exact hdisj.subset_compl_right
  have hVV' := Space.range_pointsMap_subset_image_of_isAdmissibleBlowup (X := ⟨Y, hY⟩) _ hb
  -- The initial remark.
  exact HasProperCompactifiableCover.of_proper B S hS hY Y'.2 f f' b.hom hbp (ι ≫ Q.snd) ha
    (Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso ι Q.iso.symm ≪≫
      (Bicategory.associator _ _ _).symm) V V' hVV'
    (hflat Y'.1 Y'.2 _ f' V' hV' hf'sep hf'ft hf'fl hf'fp hY'qc hY'qs
      (hVqc.of_iso B S hS (asIso (V.fromPreimage b.hom)).symm)
      (isGerbeOver_fst_fullSubcategory_of_isGerbeOver B S hS hY f V hV b hV' P hP hPV hG))

/-- **Stacks 0CQ7 over a locally Noetherian base.** Let `f : 𝒳 ⟶ Y` be a 1-morphism from an
algebraic stack to an algebraic space and `V ⊆ Y` an open subspace, such that `f` is separated
and of finite type, `Y` is quasi-compact, quasi-separated and locally Noetherian, `V` is
quasi-compact and `𝒳_V` is a gerbe over `V`. Then there are algebraic spaces `Z ⊆ Z̄` (an open
immersion `j`), a proper `ḡ : Z̄ ⟶ Y` and a proper `h : Z ⟶ 𝒳` with `f ∘ h ≅ ḡ ∘ j`, such
that `|V|` lies in the image of `|Z|` (`HasProperCompactifiableCover`).

The proof is the source's, as in `hasProperCompactifiableCover_of_isGerbeOver_of`: the
reduction to the flat case by Stacks 0CQ4 over the locally Noetherian base, and the flat case
(`hasProperCompactifiableCover_of_isFlat_of`) from Stacks 0CQ6 and Stacks 0CPI. -/
theorem hasProperCompactifiableCover_of_isGerbeOver_of_noetherian
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hYN : Space.HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V :=
  hasProperCompactifiableCover_of_flat_case_of_noetherian B S hS
    (fun _ hY _ f V hV hsep hft hfl hfp hYqc hYqs hVqc hG =>
      hasProperCompactifiableCover_of_isFlat_of
        (Stack.exists_finite_surjective_zariskiLocal_factorization B S hS)
        Space.exists_isAdmissibleBlowup_extending_section_of_isProper
        hY f V hV hsep hft hfl hfp hYqc hYqs hVqc hG)
    hY f V hV hsep hft hYqc hYqs hYN hVqc hG

/-- **The Noetherian reduced case of Stacks 0CQ8.** Let `Y` be a Noetherian algebraic space and
`f : 𝒳 ⟶ Y` a separated 1-morphism of finite type from a reduced algebraic stack. Then the
conclusion of Chow's lemma holds for `f` (`HasChowCover`).

The proof is the source's, as in `hasChowCover_of_isNoetherian_of_isReducedStack`: the claim of
the proof (`exists_gerbe_claim_of_isNoetherian_of_isReducedStack`) gives `𝒳' ⟶ Y'` over
`𝒳 ⟶ Y`, through a proper surjective `𝒳' ⟶ 𝒳` and a proper `Y' ⟶ Y`, with a quasi-compact
open `V ⊆ Y'` over which `𝒳'` is a gerbe and whose points are dense in `|𝒳'|`; `Y'` is locally
Noetherian, being of finite type over `Y` (Stacks 04ZK), so Stacks 0CQ7 over a locally
Noetherian base applies to `(𝒳' ⟶ Y', V)`, and the resulting Chow cover descends to `f`. -/
theorem hasChowCover_of_isNoetherian_of_isReducedStack_of_noetherian
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.IsNoetherian B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hred : IsReducedStack B S hS 𝒳) (hsep : IsSeparated B S hS f)
    (hft : IsFiniteType B S hS f) :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨Y', hY', q', V, hV, 𝒳', f', b, hq', hb, hbs, hsep', hft', hY'qc, hY'qs, hVqc, hG,
      hdense, ⟨e⟩⟩ :=
    exists_gerbe_claim_of_isNoetherian_of_isReducedStack B S hS hY hYN f hsep hft hred
      (isQuasiCompactMorphism_inertiaProjectionAlgebraicStacks_of_isQuasiSeparated B S hS hY
        hYN.2.1 f (isQuasiSeparated_of_isSeparated B S hS hsep))
  have hY'N : Space.HasEtaleLocalProperty B S hS Y'
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hY' hY q' hq'.2.1.1 hYN.2.2
  exact HasChowCover.of_proper B S hS hY hY' f f' q' hq' b hb hbs e
    (HasChowCover.of_hasProperCompactifiableCover B S hS hY' f' V hV hG hdense
      (hasProperCompactifiableCover_of_isGerbeOver_of_noetherian B S hS hY' f' V hV hsep' hft'
        hY'qc hY'qs hY'N hVqc hG))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
