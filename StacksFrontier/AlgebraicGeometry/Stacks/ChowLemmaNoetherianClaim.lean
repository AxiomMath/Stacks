module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaNoetherianGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimit
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOfEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOverOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperClosedImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCompositionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImagePartialSection
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImagePointsClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningOpenImmersionIsomorphism

/-!
# The claim in the Noetherian case of Chow's lemma for algebraic stacks

Let `Y` be a Noetherian algebraic space and `f : 𝒳 ⟶ Y` a separated 1-morphism of finite type
from a reduced algebraic stack whose inertia projection is quasi-compact. The proof of Chow's lemma
for algebraic stacks (Stacks 0CQ8) reduces this case to Stacks 0CQ7 by producing a proper
`Y' ⟶ Y`, a quasi-compact open `V ⊆ Y'` and a proper surjective `b : 𝒳' ⟶ 𝒳` from an algebraic
stack separated and of finite type over `Y'`, such that `V ×_{Y'} 𝒳'` is a gerbe over `V` whose
points are dense in `|𝒳'|`. This is the *claim* of that proof.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_gerbe_claim_of_isNoetherian_of_isReducedStack`:
  the claim in the proof of Stacks 0CQ8.

## The proof

The source's. `exists_gerbe_isImmersion_isProper_of_isReducedStack` supplies a gerbe
`𝒲₁ ⟶ V₁` over a quasi-compact algebraic space, an open immersion `𝒲₁ ⟶ 𝒳` with dense image, a
proper `q : P ⟶ Y` and an immersion `j : V₁ ⟶ P` with `𝒲₁ ⟶ V₁ ⟶ P ⟶ Y` 2-isomorphic to
`𝒲₁ ⟶ 𝒳 ⟶ Y`.

1. `j` is quasi-compact (`j ≫ q` is, its source being quasi-compact and `Y` quasi-separated, and
   `q` is separated), so by **Stacks 081U** it factors as an open immersion `V₁ ⟶ Y'` followed
   by a closed immersion `Y' ⟶ P`; `Y' ⟶ Y` is proper, and `V` is the image of `V₁` in `Y'`.
2. The essential image of `𝒲₁ ⟶ 𝒳` is an open substack `𝒱` equivalent to `𝒲₁`
   (**Stacks 0506**), and `𝒱 ⟶ 𝒳` is quasi-compact, `𝒳` being locally Noetherian. The square
   over `Y` gives a section `s : 𝒱 ⟶ 𝒵 = Y' ×_Y 𝒳` of the proper projection `𝒵 ⟶ 𝒳` over `𝒱`.
3. `𝒳'` is the scheme theoretic image of `s` (**Stacks 0CPU**). It is proper over `𝒳` and
   separated of finite type over `Y'`; by **Stacks 0CPW** it is isomorphic to `𝒳` over `𝒱`, and by
   **Stacks 0CML** the image of `𝒱` is dense in `|𝒳'|`. So `𝒳' ⟶ 𝒳` is surjective, its image
   being closed and containing the dense image of `𝒱`.
4. The factorization of `s` through `𝒳'` and the gerbe `𝒱 ⟶ V` give `u : 𝒱 ⟶ V ×_{Y'} 𝒳'`.
   It is fully faithful, being the first factor of the open immersion `𝒱 ⟶ 𝒳` followed by a
   faithful 1-morphism. Its image on points is closed by **Stacks 0CPT** (`𝒱 ⟶ V` is a gerbe,
   hence universally closed by **Stacks 06R9**, and `V ×_{Y'} 𝒳' ⟶ V` is separated) and dense
   (`V ×_{Y'} 𝒳'` is open in `𝒳'`), so `u` is surjective on points. Every object of
   `V ×_{Y'} 𝒳'` then lies, in `𝒳'`, over `𝒱`, where Stacks 0CPW identifies `𝒳'` with `𝒱`; so
   `u` is essentially surjective, hence an equivalence, and `V ×_{Y'} 𝒳' ⟶ V` is a gerbe.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 081U](https://stacks.math.columbia.edu/tag/081U)
* [Stacks Project, Tag 0CPW](https://stacks.math.columbia.edu/tag/0CPW)
* [Stacks Project, Tag 0CML](https://stacks.math.columbia.edu/tag/0CML)
* [Stacks Project, Tag 0CPT](https://stacks.math.columbia.edu/tag/0CPT)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An immersion `j : V₁ ⟶ P` from a quasi-compact algebraic space into an algebraic space proper
over a Noetherian algebraic space `Y` factors as an open immersion `V₁ ⟶ Y'` followed by a proper
`Y' ⟶ Y` with `Y'` quasi-compact and quasi-separated. -/
theorem _root_.AlgebraicGeometry.Space.exists_isOpenImmersion_isProper_of_isImmersion
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.IsNoetherian B S hS B.contains_terminal Y)
    {V₁ P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV₁ : IsAlgebraicSpace B S hS V₁)
    (hP : IsAlgebraicSpace B S hS P) {q : P ⟶ Y} {j : V₁ ⟶ P} (hq : Space.IsProper B S hS q)
    (hj : Space.IsImmersion B S hS j) (hV₁qc : Space.IsQuasiCompactSpace B S hS V₁) :
    ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hY' : IsAlgebraicSpace B S hS Y') (j' : V₁ ⟶ Y')
      (q' : Y' ⟶ Y), Space.IsOpenImmersion B S hS j' ∧ j' ≫ q' = j ≫ q ∧
      Space.IsProper B S hS q' ∧ Space.IsQuasiCompactSpace B S hS Y' ∧
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' := by
  obtain ⟨Y', j', c, hY', hj', hc, hj'c⟩ :=
    Space.exists_isOpenImmersion_isClosedImmersion_comp_eq_of_isQuasiCompact B S hS hP j hj
      (Space.isQuasiCompact_of_comp_of_isQuasiSeparated B S hS j q hV₁ hY
        (Space.isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal hY hYN.2.1 hV₁qc
          (j ≫ q)) (Space.isQuasiSeparated_of_isSeparated B S hS hq.1))
  have hq' : Space.IsProper B S hS (c ≫ q) := Space.isProper_comp B S hS hY' hP hY c q
    (Space.isProper_of_isClosedImmersion B S hS hY' hP c hc) hq
  exact ⟨Y', hY', j', c ≫ q, hj', by rw [← hj'c, Category.assoc], hq',
    Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYN.1 hq'.2.1.2,
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hY' hYN.2.1
      (Space.isQuasiSeparated_of_isSeparated B S hS hq'.1)⟩

/-- **The claim in the proof of Stacks 0CQ8, Noetherian case.** Let `Y` be a Noetherian algebraic
space and `f : 𝒳 ⟶ Y` a separated 1-morphism of finite type from a reduced algebraic stack whose
inertia projection is quasi-compact. Then there are a proper morphism `q' : Y' ⟶ Y` of algebraic
spaces with `Y'` quasi-compact and quasi-separated, a quasi-compact open subspace `V ⊆ Y'`, and a
proper surjective 1-morphism `b : 𝒳' ⟶ 𝒳` from an algebraic stack with a separated 1-morphism of
finite type `f' : 𝒳' ⟶ Y'`, such that `b ≫ f` is 2-isomorphic to `f' ≫ q'`, `V ×_{Y'} 𝒳' ⟶ V`
is a gerbe, and the points of `𝒳'` over `V` are dense in `|𝒳'|`.

These are the hypotheses of Stacks 0CQ7 for `(f', V)` together with the two hypotheses of
`AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_hasProperCompactifiableCover`. -/
theorem exists_gerbe_claim_of_isNoetherian_of_isReducedStack
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.IsNoetherian B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hred : IsReducedStack B S hS 𝒳)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY' : IsAlgebraicSpace B S hS Y') (q' : Y' ⟶ Y)
      (V : Subfunctor Y') (hV : Space.IsOpenSubspace B S hS V)
      (𝒳' : AlgebraicStacks.{u, w} B S hS) (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y' hY')
      (b : 𝒳' ⟶ 𝒳),
      Space.IsProper B S hS q' ∧ IsProper B S hS b ∧ IsSurjective B S hS b ∧
      IsSeparated B S hS f' ∧ IsFiniteType B S hS f' ∧
      Space.IsQuasiCompactSpace B S hS Y' ∧
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' ∧
      Space.IsQuasiCompactSpace B S hS V.toFunctor ∧
      IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY' V.ι) f').fst ∧
      @Dense _ (pointTopology B S hS 𝒳'.val) (Set.range (pointsMap B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS
          (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY' V.ι) f').snd)) ∧
      Nonempty (b ≫ f ≅ f' ≫ algebraicSpaceStackMap.{u, w} B S hS hY' hY q') := by
  obtain ⟨V₁, hV₁, 𝒲₁, g₁, ι₁, P, hP, q, j, hg₁, hι₁, hι₁dense, hq, hj, hV₁qc, hjqsep, ⟨e₀⟩⟩ :=
    exists_gerbe_isImmersion_isProper_of_isReducedStack B S hS hY hYN f hsep hft hred hqc
  -- Step 1: `j` is quasi-compact, and factors as an open immersion followed by a closed one
  obtain ⟨Y', hY', j', q', hj', hjq, hq', hY'qc, hY'qs⟩ :=
    Space.exists_isOpenImmersion_isProper_of_isImmersion B S hS hY hYN hV₁ hP hq hj hV₁qc
  have : Mono j' := Space.mono_of_isOpenImmersion B S hS j' hj'
  let V := Subfunctor.range j'
  let φ : V₁ ≅ V.toFunctor := asIso (Subfunctor.toRange j')
  have hφ : φ.hom ≫ V.ι = j' := Subfunctor.toRange_ι j'
  have hV : Space.IsOpenSubspace B S hS V := Space.isOpenSubspace_subfunctorRange B S hS hV₁ hj'
  have hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor :=
    Space.isQuasiCompactSpace_of_iso B S hS φ hV₁qc
  -- Step 2: `𝒵 = Y' ×_Y 𝒳`
  let Q' := algebraicSpaceStackMap.{u, w} B S hS hY' hY q'
  let Z := twoFibreProductSquareAlgebraicStacks B S hS Q' f
  have hZ : Bicategory.IsTwoFibreProduct Z :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS Q' f
  have hQ'prop : IsProper B S hS Q' :=
    (isProper_algebraicSpaceStackMap_iff.{u, w} B S hS hY' hY _).2 hq'
  have hZsnd : IsProper B S hS Z.snd :=
    isProper_baseChange B S hS Q' f Z.swap (Bicategory.isTwoFibreProduct_swap hZ) hQ'prop
  have hZsndrep : IsRepresentableByAlgebraicSpaces B S hS Z.snd.hom.hom :=
    isRepresentableByAlgebraicSpaces_snd_of_isTwoFibreProduct B S hS Z hZ
      (isRepresentableByAlgebraicSpaces_algebraicSpaceStackMap.{u, w} B S hS hY' hY _)
  have hZfstsep : IsSeparated B S hS Z.fst :=
    isSeparated_baseChange_of_isTwoFibreProduct B S hS f Q' Z.swap
      (Bicategory.isTwoFibreProduct_swap hZ) hsep
  have hZfstft : IsFiniteType B S hS Z.fst := isFiniteType_baseChange B S hS f Q' Z hZ hft
  -- Step 3: the open substack `𝒱 ⊆ 𝒳` which is the image of `𝒲₁`, and a section over it
  have hι₁imm : IsImmersion B S hS ι₁ := isImmersion_of_isOpenImmersion B S hS ι₁ hι₁
  have hA := isAlgebraicStack_essImage ι₁ hι₁imm
  let V' : OpenSubstack 𝒳 := ⟨_, inferInstance, hA,
    isOpenImmersion_essImageInclusion ι₁ hι₁ hι₁imm hA⟩
  let 𝒱 := fullSubcategoryAlgebraicStack 𝒳 V'.property V'.isAlgebraic
  let iV : 𝒱 ⟶ 𝒳 := fullSubcategoryInclusion 𝒳 V'.property V'.isAlgebraic
  let E := equivalenceOfBasedEquivalence.{u, w} B S hS (𝒳 := 𝒲₁) (𝒴 := 𝒱)
    (essImageEquivalence ι₁ hι₁imm)
  have hEι : E.hom ≫ iV ≅ ι₁ := Bicategory.InducedBicategory.isoMk
    (Bicategory.InducedBicategory.isoMk (toEssImageBasedSquareIso ι₁))
  -- `𝒱 ⟶ 𝒳` is quasi-compact, `𝒳` being locally Noetherian
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hYat : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) (algebraicSpaceStack.{u, w} B S hS Y hY) :=
    (Stack.scheme_atlas_iff_etaleLocalProperty B S hS _ Y hY).2 hYN.2.2
  have hXat : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳 :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS f hft.1 hYat
  have hiVim : IsImmersion B S hS iV := isImmersion_of_isOpenImmersion B S hS iV V'.isOpenImmersion
  have hiVqc : IsQuasiCompactMorphism B S hS iV :=
    (Stack.isQuasiCompact_iff_baseChange_quasiCompact B S hS iV hiVim.1).mp
      (hasRelativeProperty_quasiCompact_of_isImmersion B S hS iV hiVim hXat)
  -- the gerbe and the square over `𝒱`
  let g₁' : 𝒱 ⟶ algebraicSpaceStack.{u, w} B S hS V₁ hV₁ := E.inv ≫ g₁
  let e₁ : g₁' ≫ algebraicSpaceStackMap.{u, w} B S hS hV₁ hY (j ≫ q) ≅ iV ≫ f :=
    Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso E.inv e₀ ≪≫
      Bicategory.whiskerLeftIso E.inv (Bicategory.whiskerRightIso hEι.symm f) ≪≫
      Bicategory.whiskerLeftIso E.inv (Bicategory.associator _ _ _) ≪≫
      (Bicategory.associator _ _ _).symm ≪≫
      Bicategory.whiskerRightIso ((Bicategory.associator _ _ _).symm ≪≫
        Bicategory.whiskerRightIso E.counit iV ≪≫ Bicategory.leftUnitor iV) f
  have hmap : algebraicSpaceStackMap.{u, w} B S hS hV₁ hY' j' ≫ Q' =
      algebraicSpaceStackMap.{u, w} B S hS hV₁ hY (j ≫ q) :=
    (algebraicSpaceStackMap_comp B S hS hV₁ hY' hY j' q').symm.trans (congrArg _ hjq)
  let T : Bicategory.TwoCommSq Q' f :=
    { pt := 𝒱
      fst := g₁' ≫ algebraicSpaceStackMap.{u, w} B S hS hV₁ hY' j'
      snd := iV
      iso := Bicategory.associator _ _ _ ≪≫ eqToIso (congrArg (g₁' ≫ ·) hmap) ≪≫ e₁ }
  let sP := canonicalPreHomAlgebraicStacks B S hS Q' f T
  let s : 𝒱 ⟶ Z.pt := sP.hom
  have hsfst : s ≫ Z.fst = g₁' ≫ algebraicSpaceStackMap.{u, w} B S hS hV₁ hY' j' := rfl
  have hssnd : s ≫ Z.snd = iV := rfl
  -- Step 4: the scheme theoretic image `𝒳'` of `s`
  have hPimg := isSchemeTheoreticImage_schemeTheoreticImageCandidate s
  let 𝒳' := fullSubcategoryAlgebraicStack Z.pt (schemeTheoreticImageCandidate s)
    hPimg.isAlgebraicStack
  let incl : 𝒳' ⟶ Z.pt := fullSubcategoryInclusion Z.pt (schemeTheoreticImageCandidate s)
    hPimg.isAlgebraicStack
  have hincl : IsClosedImmersion B S hS incl := hPimg.1.2.choose_spec
  have hinclprop : IsProper B S hS incl := isProper_of_isClosedImmersion B S hS incl hincl
  let f' := incl ≫ Z.fst
  let b := incl ≫ Z.snd
  have hb : IsProper B S hS b := isProper_comp B S hS incl Z.snd hinclprop hZsnd
  have hf'sep : IsSeparated B S hS f' := isSeparated_comp B S hS incl Z.fst hinclprop.1 hZfstsep
  have hf'ft : IsFiniteType B S hS f' := isFiniteType_comp B S hS incl Z.fst hinclprop.2.1 hZfstft
  let eb : b ≫ f ≅ f' ≫ Q' := Bicategory.associator _ _ _ ≪≫
    Bicategory.whiskerLeftIso incl Z.iso.symm ≪≫ (Bicategory.associator _ _ _).symm
  -- Stacks 0CPW: `𝒳' ⟶ 𝒳` is an isomorphism over `𝒱`
  let k : 𝒱 ⟶ 𝒳' := substackFactorizationHom B S hS V' s hPimg.isAlgebraicStack hPimg.2.1
  let kiso : k ≫ incl ≅ s := substackFactorizationIso B S hS V' s hPimg.isAlgebraicStack hPimg.2.1
  let R := twoFibreProductSquareAlgebraicStacks B S hS iV b
  let σ' : 𝒱 ⟶ R.pt := partialSectionImageSection B S hS Z.snd V' s hPimg.isAlgebraicStack
    (eqToIso hssnd) hPimg.2.1
  have hσ'fst : σ' ≫ R.fst = 𝟙 𝒱 := partialSectionImageSection_comp_fst B S hS Z.snd V' s
    hPimg.isAlgebraicStack (eqToIso hssnd) hPimg.2.1
  have hσ'snd : σ' ≫ R.snd = k := rfl
  -- Step 5: the 1-morphism `𝒱 ⟶ V ×_{Y'} 𝒳'`
  let iVs := algebraicSpaceStackMap.{u, w} B S hS hV.1 hY' V.ι
  let Φ := algebraicSpaceStackMap.{u, w} B S hS hV₁ hV.1 φ.hom
  have hΦ : Φ ≫ iVs = algebraicSpaceStackMap.{u, w} B S hS hV₁ hY' j' :=
    (algebraicSpaceStackMap_comp B S hS hV₁ hV.1 hY' φ.hom V.ι).symm.trans (congrArg _ hφ)
  let Q := twoFibreProductSquareAlgebraicStacks B S hS iVs f'
  let T₂ : Bicategory.TwoCommSq iVs f' :=
    { pt := 𝒱
      fst := g₁' ≫ Φ
      snd := k
      iso := Bicategory.associator _ _ _ ≪≫ eqToIso (congrArg (g₁' ≫ ·) hΦ) ≪≫
        eqToIso hsfst.symm ≪≫ Bicategory.whiskerRightIso kiso.symm Z.fst ≪≫
        Bicategory.associator _ _ _ }
  let u : 𝒱 ⟶ Q.pt := (canonicalPreHomAlgebraicStacks B S hS iVs f' T₂).hom
  have hufst : u ≫ Q.fst = g₁' ≫ Φ := rfl
  have husnd : u ≫ Q.snd = k := rfl
  have hQu (v) : pointsMap B S hS Q.snd (pointsMap B S hS u v) = pointsMap B S hS k v := by
    rw [← husnd, pointsMap_comp, Function.comp_apply]
  have hgerbe : IsGerbeOver B S hS (g₁' ≫ Φ) :=
    isGerbeOver_comp B S hS g₁' Φ
      (isGerbeOver_comp B S hS E.inv g₁ (isGerbeOver_of_isEquivalence B S hS E.inv
        (essImageEquivalence ι₁ hι₁imm).symm.equiv.isEquivalence_functor) hg₁)
      (isGerbeOver_algebraicSpaceStackMap.{u, w} B S hS hV₁ hV.1 φ)
  -- points
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS 𝒳'.val
  let _ := pointTopology B S hS Z.pt.val
  let _ := pointTopology B S hS Q.pt.val
  let _ := pointTopology B S hS 𝒱.val
  -- the image of `𝒱` is dense in `|𝒳'|` (Stacks 0CML)
  have hsqc : IsQuasiCompactMorphism B S hS s :=
    isQuasiCompactMorphism_of_isSeparated_of_comp_quasiCompact B S hS Z.snd V' s
      (isQuasiCompactMorphism_of_comp_of_isSurjective B S hS (𝟙 _) _ (s ≫ Z.snd)
        (Bicategory.leftUnitor _ ≪≫ eqToIso hssnd) (isSurjective_id B S hS _) hiVqc) hZsnd.1
  have hkdense : Dense (Set.range (pointsMap B S hS k)) := by
    refine (isEmbedding_pointsMap_of_isImmersion B S hS incl
      (isImmersion_of_isClosedImmersion B S hS incl hincl)).isInducing.dense_iff.2 fun x => ?_
    have h1 : pointsMap B S hS incl '' Set.range (pointsMap B S hS k) =
        Set.range (pointsMap B S hS s) := by
      rw [← Set.range_comp, ← pointsMap_comp, pointsMap_eq_of_iso B S hS kiso]
    rw [h1, ← range_pointsMap_eq_closure_of_isSchemeTheoreticImage B S hS s hsqc hPimg]
    exact ⟨x, rfl⟩
  -- `𝒳' ⟶ 𝒳` is surjective
  let kb : k ≫ b ≅ iV := (Bicategory.associator _ _ _).symm ≪≫
    Bicategory.whiskerRightIso kiso Z.snd ≪≫ eqToIso hssnd
  have hbsurj : IsSurjective B S hS b := by
    have hclosed : _root_.IsClosed (Set.range (pointsMap B S hS b)) :=
      (isClosed_of_universallyClosed B S hS b hb.2.2).isClosed_range
    have hsub : Set.range (pointsMap B S hS ι₁) ⊆ Set.range (pointsMap B S hS b) := by
      rintro _ ⟨w, rfl⟩
      refine ⟨pointsMap B S hS k (pointsMap B S hS E.hom w), ?_⟩
      simpa only [pointsMap_comp, Function.comp_apply] using (congrFun (pointsMap_eq_of_iso B S hS
        (hEι.symm ≪≫ Bicategory.whiskerLeftIso E.hom kb.symm)) w).symm
    exact Set.range_eq_univ.1
      (Set.eq_univ_of_subset (hclosed.closure_subset_iff.2 hsub) hι₁dense.closure_eq)
  -- the points of `𝒳'` over `V` are dense
  have hdense : Dense (Set.range (pointsMap B S hS Q.snd)) :=
    hkdense.mono (Set.range_subset_iff.2 fun v => ⟨_, hQu v⟩)
  -- the 1-morphism `𝒱 ⟶ V ×_{Y'} 𝒳'` is an equivalence
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS iVs f'
  have hiVs : IsOpenImmersion B S hS iVs :=
    isOpenImmersion_of_isOpenImmersion_representingMap B S hS iVs V.toFunctor Y' hV.1 hY'
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V.toFunctor hV.1)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (by rw [representingMap_associatedMap]; exact hV.2)
  have hQsnd : IsOpenImmersion B S hS Q.snd := isOpenImmersion_baseChange_snd B S hS Q hQ hiVs
  have hRsnd : IsOpenImmersion B S hS R.snd :=
    isOpenImmersion_baseChange_snd B S hS R
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS iV b) V'.isOpenImmersion
  obtain ⟨hQfull, hQfaith⟩ := full_and_faithful_homFunctor_of_isMonomorphism B S hS Q.snd
    (isMonomorphism_of_isOpenImmersion B S hS Q.snd hQsnd)
  have hbfaith : (CatFiberedInGroupoids.homFunctor b.hom).Faithful :=
    faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS b
      (isRepresentableByAlgebraicSpaces_comp B S hS incl.hom Z.snd.hom hincl.1 hZsndrep)
  have hQbfaith : (CatFiberedInGroupoids.homFunctor Q.snd.hom ⋙
      CatFiberedInGroupoids.homFunctor b.hom).Faithful := inferInstance
  let ε : CatFiberedInGroupoids.homFunctor u.hom ⋙ (CatFiberedInGroupoids.homFunctor Q.snd.hom ⋙
      CatFiberedInGroupoids.homFunctor b.hom) ≅ CatFiberedInGroupoids.homFunctor iV.hom :=
    underlyingIso B S hS ((Bicategory.associator _ _ _).symm ≪≫ kb)
  have hufaith : (CatFiberedInGroupoids.homFunctor u.hom).Faithful :=
    Functor.Faithful.of_comp_iso ε
  have hufull : (CatFiberedInGroupoids.homFunctor u.hom).Full :=
    Functor.Full.of_comp_faithful_iso ε
  -- `|𝒱| ⟶ |V ×_{Y'} 𝒳'|` is surjective: closed (Stacks 0CPT) with dense image
  have husurj : Function.Surjective (pointsMap B S hS u) := by
    have huc : UniversallyClosed B S hS (u ≫ Q.fst) := fun 𝒲 g => by
      let _ := pointTopology B S hS 𝒲.val
      let _ := pointTopology B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS g (g₁' ≫ Φ)).pt.val
      exact (Stack.universalHomeomorphism_of_isGerbeOver B S hS _ hgerbe 𝒲 g _
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g _)).isClosedMap
    have hQfstsep : IsSeparated B S hS Q.fst :=
      isSeparated_baseChange_of_isTwoFibreProduct B S hS f' iVs Q.swap
        (Bicategory.isTwoFibreProduct_swap hQ) hf'sep
    have hclosed := isClosed_range_of_comp_of_isSeparated B S hS u Q.fst huc hQfstsep
    have hinj := pointsMap_injective_of_fullyFaithful B S hS Q.snd
    have hopen := isOpenMap_pointsMap_of_isOpenImmersion B S hS Q.snd hQsnd
    have hsub : pointsMap B S hS Q.snd ⁻¹' Set.range (pointsMap B S hS k) ⊆
        Set.range (pointsMap B S hS u) := by
      rintro y ⟨v, hv⟩
      exact ⟨v, hinj ((hQu v).trans hv)⟩
    have hd : Dense (Set.range (pointsMap B S hS u)) := (hkdense.preimage hopen).mono hsub
    exact Set.range_eq_univ.1 (hclosed.closure_eq.symm.trans hd.closure_eq)
  -- essential surjectivity, through Stacks 0CPW
  have hRfst : (CatFiberedInGroupoids.homFunctor R.fst.hom).IsEquivalence :=
    isEquivalence_fst_of_isSchemeTheoreticImage_partialSection B S hS Z.snd V' s
      hZsndrep hZsnd.1 hiVqc (eqToIso hssnd) hPimg
  have huess : (CatFiberedInGroupoids.homFunctor u.hom).EssSurj := by
    refine ⟨fun y => ?_⟩
    obtain ⟨by', ⟨ey⟩⟩ := exists_schemeStack_hom_iso B S hS Q.pt y
    have hrange : Set.range (pointsMap B S hS (by' ≫ Q.snd)) ⊆
        Set.range (pointsMap B S hS R.snd) := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨v, hv⟩ := husurj (pointsMap B S hS by' t)
      refine ⟨pointsMap B S hS σ' v, ?_⟩
      rw [← Function.comp_apply (f := pointsMap B S hS R.snd), ← pointsMap_comp, hσ'snd,
        ← husnd, pointsMap_comp, pointsMap_comp, Function.comp_apply, Function.comp_apply, hv]
    obtain ⟨r, ⟨er⟩⟩ := exists_iso_of_range_pointsMap_subset B S hS R.snd hRsnd (by' ≫ Q.snd)
      hrange
    have hfr := Functor.congr_obj (congrArg (fun m => m.hom.hom.toFunctor) hσ'fst)
      ((CatFiberedInGroupoids.homFunctor R.fst.hom).obj r)
    exact ⟨(CatFiberedInGroupoids.homFunctor R.fst.hom).obj r,
      ⟨(CatFiberedInGroupoids.homFunctor Q.snd.hom).preimageIso
        ((CatFiberedInGroupoids.homFunctor R.snd.hom).mapIso
          ((CatFiberedInGroupoids.homFunctor R.fst.hom).preimageIso (eqToIso hfr)) ≪≫ er ≪≫
          (CatFiberedInGroupoids.homFunctor Q.snd.hom).mapIso ey)⟩⟩
  have hu : (CatFiberedInGroupoids.homFunctor u.hom).IsEquivalence := Functor.IsEquivalence.mk
  exact ⟨Y', hY', q', V, hV, 𝒳', f', b, hq', hb, hbsurj, hf'sep, hf'ft, hY'qc, hY'qs, hVqc,
    isGerbeOver_of_isEquivalence_comp B S hS u Q.fst (g₁' ≫ Φ) hu (eqToIso hufst) hgerbe,
    hdense, ⟨eb⟩⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
