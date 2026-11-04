module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowCompactifiableCoverGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaCompactifiableCover
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaNoetherianGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowNoetherianClaim
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageDominant
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageExistence

/-!
# Chow's lemma for algebraic stacks over a Noetherian base

This is the Noetherian case of the proof of Chow's lemma for algebraic stacks (Stacks 0CQ8): for
a separated 1-morphism of finite type `f : 𝒳 ⟶ Y` to a Noetherian algebraic space there are a
proper surjective `X ⟶ 𝒳` from an algebraic space and an open immersion `X ⟶ X̄` into an
algebraic space proper over `Y`, compatible over `Y`.

## The proof

The source's. Replace `𝒳` by its reduction (Stacks 050C). `𝒳` is quasi-separated over `Y`, so its
inertia is quasi-compact
(`AlgebraicStacks.isQuasiCompactMorphism_inertiaProjection_of_isQuasiSeparated`), and it
has a dense open gerbe `𝒲 ⟶ V₁` whose base immerses into some `ℙⁿ_Y`
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_gerbe_isImmersion_isProper_of_isReducedStack`:
Stacks 06RC, 06QD, 06QI, 06Q9, 06R9, 0CPM, 0CPQ, 088N). The immersion is quasi-compact, so it
is an open immersion `V₁ ⟶ Y'` into a closed subspace `Y'` of `ℙⁿ_Y` (Stacks 081U). Let `𝒳'` be
the scheme theoretic image of `Γ : 𝒲 ⟶ Y' ×_Y 𝒳` (Stacks 0CPV). By the claim
(`AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_fst_schemeTheoreticImage`) the restriction
of `𝒳' ⟶ Y'` to the image `V` of `V₁` is a gerbe, so Stacks 0CQ7 gives a proper compactifiable
cover of `|V|`; the points of `𝒳'` over `V` are dense (Stacks 0CML), so it is a Chow cover of
`𝒳' ⟶ Y'`. Finally `𝒳' ⟶ 𝒳` is proper with closed image containing the dense image of `𝒲`, and
`Y' ⟶ Y` is proper, so the cover descends.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_isNoetherian_of_isReducedStack`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_isNoetherian`: the Noetherian case of
  Stacks 0CQ8.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If `c ≫ b ≅ a`, the points in the image of `a` are in the image of `b`. -/
private theorem range_pointsMap_subset_of_comp_iso {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (c : 𝒳 ⟶ 𝒴) (b : 𝒴 ⟶ 𝒵) {a : 𝒳 ⟶ 𝒵} (e : c ≫ b ≅ a) :
    Set.range (pointsMap B S hS a) ⊆ Set.range (pointsMap B S hS b) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨pointsMap B S hS c x,
    (congrFun (pointsMap_comp B S hS c b) x).symm.trans (congrFun (pointsMap_eq_of_iso B S hS e) x)⟩

/-- **Chow's lemma for a reduced algebraic stack over a Noetherian algebraic space**, the case
"Assume `Y` is Noetherian and `𝒳` is reduced" of the proof of Stacks 0CQ8. -/
theorem hasChowCover_of_isNoetherian_of_isReducedStack
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.IsNoetherian B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hred : IsReducedStack B S hS 𝒳) :
    HasChowCover.{u, w} B S hS hY f := by
  have hqc := isQuasiCompactMorphism_inertiaProjection_of_isQuasiSeparated hY f
    (isQuasiSeparated_of_isSeparated B S hS hsep)
  obtain ⟨V₁, hV₁, 𝒲, g₁, ι, P, hP, q, j, hg₁, hι, hdense, hq, hj, hV₁qc, -, ⟨e⟩⟩ :=
    exists_gerbe_isImmersion_isProper_of_isReducedStack B S hS hY hYN f hsep hft hred hqc
  have hYqc : Space.IsQuasiCompactSpace B S hS Y := hYN.1
  have hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y := hYN.2.1
  -- Stacks 081U: `V₁ ⟶ Y'` open, `Y' ⟶ P` closed
  have hPqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal P :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hP hYqs
      (Space.isQuasiSeparated_of_isSeparated B S hS hq.1)
  have hjqc : Space.IsQuasiCompact B S hS j :=
    Space.isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal hP hPqs hV₁qc j
  obtain ⟨Y', k, i, hY', hk, hi, hki⟩ :=
    Space.exists_isOpenImmersion_isClosedImmersion_comp_eq_of_isQuasiCompact B S hS hP j hj hjqc
  let p : Y' ⟶ Y := i ≫ q
  have hp : Space.IsProper B S hS p :=
    Space.isProper_comp B S hS hY' hP hY i q
      (Space.isProper_of_isClosedImmersion B S hS hY' hP i hi) hq
  have hY'qc : Space.IsQuasiCompactSpace B S hS Y' :=
    Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hp.2.1.2
  have hY'qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hY' hYqs
      (Space.isQuasiSeparated_of_isSeparated B S hS hp.1)
  -- the open `V ⊆ Y'`, the image of `V₁`
  have : Mono k := Space.mono_of_presheaf_isOpenImmersion hk
  let V := Subfunctor.range k
  have hV : Space.IsOpenSubspace B S hS V := Space.isOpenSubspace_subfunctorRange B S hS hV₁ hk
  let t : V₁ ⟶ V.toFunctor := Subfunctor.toRange k
  have hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor :=
    Space.isQuasiCompactSpace_of_iso B S hS (asIso t) hV₁qc
  let gV := g₁ ≫ algebraicSpaceStackMap.{u, w} B S hS hV₁ hV.1 t
  have hgV : IsGerbeOver B S hS gV :=
    isGerbeOver_comp B S hS g₁ _ hg₁ (isGerbeOver_algebraicSpaceStackMap_of_isIso.{u, w} hV₁ hV.1 t)
  -- `𝒢 = Y' ×_Y 𝒳`
  let pm := algebraicSpaceStackMap.{u, w} B S hS hY' hY p
  let G := twoFibreProductSquareAlgebraicStacks B S hS pm f
  have hG : IsTwoFibreProduct G :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS pm f
  have hpm : IsProper B S hS pm := (isProper_algebraicSpaceStackMap_iff.{u, w} B S hS hY' hY p).2 hp
  have hf₀ : IsSeparated B S hS G.fst :=
    isSeparated_baseChange_of_isTwoFibreProduct B S hS f pm G.swap (isTwoFibreProduct_swap hG) hsep
  have hf₀ft : IsFiniteType B S hS G.fst := isFiniteType_baseChange B S hS f pm G hG hft
  have hπrep : IsRepresentableByAlgebraicSpaces B S hS G.snd.hom.hom :=
    isRepresentableByAlgebraicSpaces_snd_of_isTwoFibreProduct B S hS G hG
      (isRepresentableByAlgebraicSpaces_algebraicSpaceStackMap.{u, w} B S hS hY' hY p)
  have hπp : IsProper B S hS G.snd :=
    isProper_baseChange B S hS pm f G.swap (isTwoFibreProduct_swap hG) hpm
  -- `Γ : 𝒲 ⟶ 𝒢`
  have hjk : algebraicSpaceStackMap.{u, w} B S hS hV₁ hY (j ≫ q) =
      algebraicSpaceStackMap.{u, w} B S hS hV₁ hY' k ≫ pm := by
    rw [← hki, Category.assoc]
    exact algebraicSpaceStackMap_comp B S hS hV₁ hY' hY k p
  let T₀ : TwoCommSq pm f :=
    ⟨𝒲, g₁ ≫ algebraicSpaceStackMap.{u, w} B S hS hV₁ hY' k, ι,
      α_ _ _ _ ≪≫ eqToIso (congrArg (g₁ ≫ ·) hjk.symm) ≪≫ e⟩
  let Γ : 𝒲 ⟶ G.pt := (canonicalPreHomAlgebraicStacks B S hS pm f T₀).hom
  have htk : algebraicSpaceStackMap.{u, w} B S hS hV₁ hV.1 t ≫
      algebraicSpaceStackMap.{u, w} B S hS hV.1 hY' V.ι =
      algebraicSpaceStackMap.{u, w} B S hS hV₁ hY' k := by
    rw [← algebraicSpaceStackMap_comp B S hS hV₁ hV.1 hY' t V.ι, Subfunctor.toRange_ι]
  let eΓ : gV ≫ algebraicSpaceStackMap.{u, w} B S hS hV.1 hY' V.ι ≅ Γ ≫ G.fst :=
    α_ _ _ _ ≪≫ eqToIso (congrArg (g₁ ≫ ·) htk)
  -- `Γ` is quasi-compact: `𝒳` is locally Noetherian, so `ι` is, and `G.snd` is quasi-separated
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hYat : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) (algebraicSpaceStack.{u, w} B S hS Y hY) :=
    (Stack.scheme_atlas_iff_etaleLocalProperty B S hS _ Y hY).2 hYN.2.2
  have hXat : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳 :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS f hft.1 hYat
  have hιim : IsImmersion B S hS ι := isImmersion_of_isOpenImmersion B S hS ι hι
  have hιqc : Stack.IsQuasiCompactMorphism B S hS ι :=
    (Stack.isQuasiCompact_iff_baseChange_quasiCompact B S hS ι hιim.1).mp
      (hasRelativeProperty_quasiCompact_of_isImmersion B S hS ι hιim hXat)
  have hΓqc : IsQuasiCompactMorphism B S hS Γ :=
    isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS Γ G.snd hιqc
      (isQuasiSeparated_of_isSeparated B S hS hπp.1)
  -- `𝒳'`, the scheme theoretic image of `Γ`, and the claim
  let P' := schemeTheoreticImageCandidate Γ
  have hP' : IsSchemeTheoreticImage Γ P' := isSchemeTheoreticImage_schemeTheoreticImageCandidate Γ
  have hPiso : P'.IsClosedUnderIsomorphisms := hP'.1.1
  let incl := fullSubcategoryInclusion G.pt P' hP'.isAlgebraicStack
  have hincl : IsClosedImmersion B S hS incl := hP'.1.2.choose_spec
  have hinclp : IsProper B S hS incl := isProper_of_isClosedImmersion B S hS incl hincl
  let f' := incl ≫ G.fst
  have hG' := isGerbeOver_fst_schemeTheoreticImage hY' V hV G.fst hf₀ G.snd hπrep hπp.1 ι hι
    gV hgV Γ eΓ (Iso.refl _) hΓqc hP'
  -- Stacks 0CQ7 for `f' : 𝒳' ⟶ Y'`
  have hcov := (hasCompactifiableCovers_of_isGerbeOver hY' hY'qc hY'qs f'
    (isSeparated_comp B S hS incl G.fst hinclp.1 hf₀)
    (isFiniteType_comp B S hS incl G.fst hinclp.2.1 hf₀ft) V hV hVqc
    hG').hasProperCompactifiableCover
  -- the points of `𝒳'` over `V` are dense
  let Γ' := factorsThroughSubstackHom Γ hP'.isAlgebraicStack hP'.2.1
  have hΓ'dense := dense_range_pointsMap_substackFactorizationHom B S hS Γ hΓqc hP'
  let M := twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY' V.ι) f'
  let T₁ : TwoCommSq (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY' V.ι) f' :=
    ⟨𝒲, gV, Γ', eΓ ≪≫ whiskerRightIso
      (factorsThroughSubstackIso Γ hP'.isAlgebraicStack hP'.2.1).symm G.fst ≪≫ α_ _ _ _⟩
  let u₁ := (canonicalPreHomAlgebraicStacks B S hS _ f' T₁).hom
  have hMdense : @Dense _ (pointTopology B S hS (fullSubcategoryAlgebraicStack G.pt P'
      hP'.isAlgebraicStack).val) (Set.range (pointsMap B S hS M.snd)) := by
    let := pointTopology B S hS
      (fullSubcategoryAlgebraicStack G.pt P' hP'.isAlgebraicStack).val
    exact hΓ'dense.mono (range_pointsMap_subset_of_comp_iso u₁ M.snd (Iso.refl _))
  have hf'cover : HasChowCover.{u, w} B S hS hY' f' :=
    HasChowCover.of_hasProperCompactifiableCover B S hS hY' f' V hV hG' hMdense hcov
  -- `𝒳' ⟶ 𝒳` is proper and surjective
  let b := incl ≫ G.snd
  have hb : IsProper B S hS b := isProper_comp B S hS incl G.snd hinclp hπp
  have hbs : IsSurjective B S hS b := by
    let _ := pointTopology B S hS 𝒳.val
    let _ := pointTopology B S hS
      (fullSubcategoryAlgebraicStack G.pt P' hP'.isAlgebraicStack).val
    have hclosed : _root_.IsClosed (Set.range (pointsMap B S hS b)) :=
      (isClosed_of_universallyClosed B S hS b hb.2.2).isClosed_range
    have hsub := range_pointsMap_subset_of_comp_iso Γ' b ((α_ _ _ _).symm ≪≫ whiskerRightIso
      (factorsThroughSubstackIso Γ hP'.isAlgebraicStack hP'.2.1) G.snd)
    exact Set.range_eq_univ.1 <|
      Set.eq_univ_of_subset (hclosed.closure_subset_iff.2 hsub) hdense.closure_eq
  exact HasChowCover.of_proper B S hS hY hY' f f' p hp b hb hbs
    (α_ _ _ _ ≪≫ whiskerLeftIso incl G.iso.symm ≪≫ (α_ _ _ _).symm) hf'cover

/-- **Chow's lemma for algebraic stacks over a Noetherian algebraic space** (the Noetherian case
of Stacks 0CQ8). Let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite type from an algebraic
stack to a Noetherian algebraic space. Then there are algebraic spaces `X` and `X̄`, a proper
surjective `X ⟶ 𝒳`, an open immersion `X ⟶ X̄` and a proper `X̄ ⟶ Y` making the triangle
2-commute.

Replace `𝒳` by its reduction (Stacks 050C) and apply
`AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_isNoetherian_of_isReducedStack`. -/
theorem hasChowCover_of_isNoetherian
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.IsNoetherian B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    HasChowCover.{u, w} B S hS hY f :=
  HasChowCover.of_forall_isReducedStack B S hS
    (fun _ hY hYN _ f hred hsep hft =>
      hasChowCover_of_isNoetherian_of_isReducedStack hY hYN f hsep hft hred)
    hY hYN f hsep hft

end AlgebraicGeometry.Stack.AlgebraicStacks

end
