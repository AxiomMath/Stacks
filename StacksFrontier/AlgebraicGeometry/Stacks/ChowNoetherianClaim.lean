module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowNoetherianClaimHelpers
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.GraphMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeUniversalHomeo
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionsStableUnderBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubspaceOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackEtaleCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedSubstackLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalConditions
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationRelativeInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningOpenImmersionIsomorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# The claim in the proof of Chow's lemma for algebraic stacks

Let `Y'` be an algebraic space, `V ⊆ Y'` an open subspace, `f₀ : 𝒢 ⟶ Y'` a separated
1-morphism from an algebraic stack, `π : 𝒢 ⟶ 𝒳` a separated 1-morphism representable by
algebraic spaces and `ι : 𝒲 ⟶ 𝒳` an open immersion. Let `gV : 𝒲 ⟶ V` be a gerbe and
`Γ : 𝒲 ⟶ 𝒢` a quasi-compact 1-morphism lying over `gV` in `Y'` and over `ι` in `𝒳`, and let
`𝒳' ⊆ 𝒢` be its scheme theoretic image. The claim of the proof of Stacks 0CQ8 is that
`V ×_{Y'} 𝒳' ⟶ V` is a gerbe: `V ×_{Y'} 𝒳'` is `𝒲`.

In the source, `𝒢 = ℙⁿ_Y ×_Y 𝒳` (here a closed subspace `Y'` of it), `π` the projection, `𝒲` the
gerbe locus and `Γ` the 1-morphism `j`.

## The proof

The source's. The lift `Γ_V : 𝒲 ⟶ V ×_{Y'} 𝒢` of `Γ` is an immersion: it is its graph over `𝒳`, a
closed immersion because `V ×_{Y'} 𝒢 ⟶ 𝒳` is separated and representable by algebraic spaces,
followed by the base change of the open immersion `ι`. It is universally closed, its composite with
the separated projection to `V` being the gerbe `gV` (Stacks 06R9, Stacks 0CPT), so it is a closed
immersion. By Stacks 0CMK the inverse image of `𝒳'` in the open `V ×_{Y'} 𝒢` is the scheme
theoretic image of the base change of `Γ`, which factors through the closed essential image of
`Γ_V` because `V ×_{Y'} 𝒢 ⟶ 𝒢` is fully faithful; so that inverse image is the essential image of
`Γ_V`, and `Γ_V` is an equivalence onto it. That inverse image is `V ×_{Y'} 𝒳'`
(Stacks 003Q with the inverse image square), and its projection to `V` is `gV` up to that
equivalence.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_fst_schemeTheoreticImage`.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 0CMK](https://stacks.math.columbia.edu/tag/0CMK)
* [Stacks Project, Tag 0CPT](https://stacks.math.columbia.edu/tag/0CPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A universally closed immersion through a separated map to a gerbe.** If `a : 𝒲 ⟶ 𝒩` lies
over the open immersion `ι : 𝒲 ⟶ 𝒳` along a separated `q : 𝒩 ⟶ 𝒳` representable by algebraic
spaces, then `a` is an immersion: it is its graph over `𝒳`, a closed immersion as the relative
diagonal of `q` is (Stacks 04YS), followed by the base change of `ι`, an open immersion. -/
theorem isImmersion_of_comp_isOpenImmersion {𝒲 𝒩 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (a : 𝒲 ⟶ 𝒩) (q : 𝒩 ⟶ 𝒳) (ι : 𝒲 ⟶ 𝒳) (η : ι ≅ a ≫ q)
    (hι : IsOpenImmersion B S hS ι) (hqrep : IsRepresentableByAlgebraicSpaces B S hS q.hom.hom)
    (hq : IsSeparated B S hS q) : IsImmersion B S hS a := by
  have hΔ : Stack.IsClosedImmersion B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒩.val 𝒳.val q.hom) :=
    isClosedImmersion_relativeDiagonal_of_universallyClosed B S hS q hqrep
      (presheaf_locallyOfFiniteType_relativeDiagonal B S hS q hqrep)
      (universallyClosed_of_isProper B S hS _ hq)
  have hgr : IsClosedImmersion B S hS (Stack.graph B S hS a ι q η) :=
    ⟨isRepresentableByAlgebraicSpaces_graph B S hS a ι q η,
      isClosedImmersion_graph_of_isClosedImmersion_relativeDiagonal B S hS a ι q η hΔ⟩
  have hpr : IsOpenImmersion B S hS (twoFibreProductSquareAlgebraicStacks B S hS ι q).snd :=
    isOpenImmersion_baseChange_snd B S hS _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS ι q) hι
  exact isImmersion_of_twoIso (Stack.graph_snd_iso B S hS a ι q η).symm
    (isImmersion_comp B S hS _ _ (AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS _ hgr)
      (isImmersion_of_isOpenImmersion B S hS _ hpr))

/-- A gerbe is universally closed: it is a universal homeomorphism (Stacks 06R9). -/
theorem universallyClosed_of_isGerbeOver {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳 ⟶ 𝒴)
    (hg : IsGerbeOver B S hS g) : UniversallyClosed B S hS g := fun 𝒵 k => by
  let := pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS k g).pt.val
  let := pointTopology B S hS 𝒵.val
  exact (Stack.universalHomeomorphism_of_isGerbeOver B S hS g hg 𝒵 k _
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k g)).isClosedMap

/-- **The claim in the proof of Stacks 0CQ8.** Let `V ⊆ Y'` be an open subspace of an algebraic
space, `f₀ : 𝒢 ⟶ Y'` separated, `π : 𝒢 ⟶ 𝒳` separated and representable by algebraic spaces,
`ι : 𝒲 ⟶ 𝒳` an open immersion, `gV : 𝒲 ⟶ V` a gerbe and `Γ : 𝒲 ⟶ 𝒢` a quasi-compact
1-morphism lying over `gV` and over `ι`. If `P` cuts out the scheme theoretic image `𝒳'` of `Γ`,
then `V ×_{Y'} 𝒳' ⟶ V` is a gerbe.

`Γ` lifts to `Γ_V : 𝒲 ⟶ V ×_{Y'} 𝒢`, an immersion over `𝒳`
(`isImmersion_of_comp_isOpenImmersion`) and universally closed since its composite with the
separated projection to `V` is the gerbe `gV` (Stacks 06R9, Stacks 0CPT), hence a closed
immersion. By Stacks 0CMK the inverse image `Q` of `P` in `V ×_{Y'} 𝒢` is the scheme theoretic
image of the base change of `Γ`; that base change factors through the essential image of `Γ_V`,
`V ×_{Y'} 𝒢 ⟶ 𝒢` being an open immersion, hence fully faithful (Stacks 04ZZ). So `Γ_V` is an
equivalence onto the substack `Q`, which is `V ×_{Y'} 𝒳'` by Stacks 003Q, and its projection to
`V` is `gV` up to that equivalence. -/
theorem isGerbeOver_fst_schemeTheoreticImage
    {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
    (V : Subfunctor Y') (hV : Space.IsOpenSubspace B S hS V)
    {𝒳 𝒢 𝒲 : AlgebraicStacks.{u, w} B S hS}
    (f₀ : 𝒢 ⟶ algebraicSpaceStack.{u, w} B S hS Y' hY') (hf₀ : IsSeparated B S hS f₀)
    (π : 𝒢 ⟶ 𝒳) (hπrep : IsRepresentableByAlgebraicSpaces B S hS π.hom.hom)
    (hπ : IsSeparated B S hS π) (ι : 𝒲 ⟶ 𝒳) (hι : IsOpenImmersion B S hS ι)
    (gV : 𝒲 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1)
    (hgV : IsGerbeOver B S hS gV) (Γ : 𝒲 ⟶ 𝒢)
    (eΓ : gV ≫ algebraicSpaceStackMap.{u, w} B S hS hV.1 hY' V.ι ≅ Γ ≫ f₀)
    (eι : Γ ≫ π ≅ ι) (hΓqc : IsQuasiCompactMorphism B S hS Γ)
    {P : ObjectProperty 𝒢.val.val.obj} (hP : IsSchemeTheoreticImage Γ P) :
    IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY' V.ι)
      (fullSubcategoryInclusion 𝒢 P hP.isAlgebraicStack ≫ f₀)).fst := by
  set v := algebraicSpaceStackMap.{u, w} B S hS hV.1 hY' V.ι with hvdef
  let N := twoFibreProductSquareAlgebraicStacks B S hS v f₀
  have hN : IsTwoFibreProduct N :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS v f₀
  let T₀ : TwoCommSq v f₀ := ⟨𝒲, gV, Γ, eΓ⟩
  let ΓV : 𝒲 ⟶ N.pt := (canonicalPreHomAlgebraicStacks B S hS v f₀ T₀).hom
  -- `V ×_{Y'} 𝒢 ⟶ 𝒢` is an open immersion
  have hv : IsOpenImmersion B S hS v :=
    isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion B S hS hV.1 hY' hV.2
  have hNsnd : IsOpenImmersion B S hS N.snd := isOpenImmersion_baseChange_snd B S hS N hN hv
  -- `Γ_V` is an immersion
  have hqrep : IsRepresentableByAlgebraicSpaces B S hS (N.snd ≫ π).hom.hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS _ _ hNsnd.1 hπrep
  have hqsep : IsSeparated B S hS (N.snd ≫ π) :=
    isSeparated_comp B S hS _ _ (isSeparated_of_isMonomorphism B S hS _
      (isMonomorphism_of_isOpenImmersion B S hS _ hNsnd)) hπ
  have hΓVimm : IsImmersion B S hS ΓV :=
    isImmersion_of_comp_isOpenImmersion ΓV (N.snd ≫ π) ι (eι.symm ≪≫ α_ ΓV N.snd π) hι hqrep
      hqsep
  -- `Γ_V` is universally closed, hence a closed immersion
  have hNfst : IsSeparated B S hS N.fst :=
    isSeparated_baseChange_of_isTwoFibreProduct B S hS f₀ v N.swap (isTwoFibreProduct_swap hN)
      hf₀
  have hΓVuc : UniversallyClosed B S hS ΓV :=
    universallyClosed_of_comp_of_isSeparated B S hS ΓV N.fst
      (universallyClosed_of_isGerbeOver gV hgV) hNfst
  have hΓVci : IsClosedImmersion B S hS ΓV :=
    isClosedImmersion_of_isImmersion_of_universallyClosed B S hS ΓV hΓVimm hΓVuc
  -- the inverse image `Q` of `P` lies in the essential image of `Γ_V` (Stacks 0CMK)
  have hPiso : P.IsClosedUnderIsomorphisms := hP.1.1
  have hNff := full_and_faithful_homFunctor_of_isMonomorphism B S hS N.snd
    (isMonomorphism_of_isOpenImmersion B S hS _ hNsnd)
  have := hNff.1
  have := hNff.2
  have hQle : P.inverseImage N.snd.hom.hom.toFunctor ≤
      (CatFiberedInGroupoids.homFunctor ΓV.hom).essImage := by
    have h0CMK := isSchemeTheoreticImage_inverseImage_of_isFlat Γ N.snd hΓqc
      (isFlat_of_isOpenImmersion B S hS _ hNsnd) hP
    refine h0CMK.2.2 _ (isClosedSubstack_essImage ΓV hΓVci) ?_
    refine (factorsThroughSubstack_iff_forall _).2 fun x => ?_
    exact ⟨x.y, ⟨(Functor.FullyFaithful.ofFullyFaithful
      (CatFiberedInGroupoids.homFunctor N.snd.hom)).preimageIso x.iso.symm⟩⟩
  -- `Γ_V` is an equivalence onto `Q`
  have hmem : ∀ W : 𝒲.val.val.obj,
      P.inverseImage N.snd.hom.hom.toFunctor (ΓV.hom.hom.toFunctor.obj W) :=
    (factorsThroughSubstack_iff_forall Γ).1 hP.2.1
  let hQalg := isAlgebraicStack_inverseImage N.snd P hP.isAlgebraicStack
  let φ : 𝒲 ⟶ fullSubcategoryAlgebraicStack N.pt (P.inverseImage N.snd.hom.hom.toFunctor)
      hQalg :=
    InducedBicategory.mkHom (InducedBicategory.mkHom
      { toFunctor := ObjectProperty.lift _ ΓV.hom.hom.toFunctor hmem
        w := ΓV.hom.hom.w })
  have hΓVff := full_and_faithful_homFunctor_of_isClosedImmersion B S hS ΓV hΓVci
  have := hΓVff.1
  have := hΓVff.2
  have hφ : (CatFiberedInGroupoids.homFunctor φ.hom).IsEquivalence := by
    change (ObjectProperty.lift _ ΓV.hom.hom.toFunctor hmem).IsEquivalence
    have : (ObjectProperty.lift _ ΓV.hom.hom.toFunctor hmem).EssSurj := ⟨fun c => by
      obtain ⟨W, ⟨e⟩⟩ := hQle _ c.property
      exact ⟨W, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso e⟩⟩⟩
    exact Functor.IsEquivalence.mk
  let T := inverseImageSquare N.snd P hP.isAlgebraicStack
  have hgQ : IsGerbeOver B S hS (N.paste T).fst :=
    isGerbeOver_of_isEquivalence_comp B S hS φ (N.paste T).fst gV hφ (Iso.refl _) hgV
  -- `Q` is `V ×_{Y'} 𝒳'` (Stacks 003Q)
  have hpaste : IsTwoFibreProduct (N.paste T) :=
    isTwoFibreProduct_paste hN (isTwoFibreProduct_inverseImageSquare N.snd P hP.isAlgebraicStack)
  let M := twoFibreProductSquareAlgebraicStacks B S hS v
    (fullSubcategoryInclusion 𝒢 P hP.isAlgebraicStack ≫ f₀)
  have hM : IsTwoFibreProduct M := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _
  let d : TwoCommSq.PreHom (N.paste T) M := _root_.Quotient.out (hM.from (N.paste T))
  exact isGerbeOver_of_isEquivalence_comp B S hS d.hom M.fst (N.paste T).fst
    (isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hpaste hM d) d.isoFst.symm hgQ

end AlgebraicGeometry.Stack.AlgebraicStacks

end
