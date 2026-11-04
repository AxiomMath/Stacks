module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DenseOpenEmbeddingIntoAffineSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceOverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackMapProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaReductions
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseOpenGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationDescentComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeUniversalHomeo
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionsStableUnderBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedSubstackLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationUniversallyInjectiveCoverCorrected
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningOpenImmersionIsomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphism

/-!
# The gerbe locus in the proof of Chow's lemma for algebraic stacks

These are steps of the proof of Chow's lemma for algebraic stacks (Stacks 0CQ8) over a
Noetherian algebraic space `Y`. Let `f : 𝒳 ⟶ Y` be separated and of finite type and let
`𝒲 ⟶ 𝒳` be an open immersion from an algebraic stack which is a gerbe. Then `𝒲` is a gerbe
over an algebraic space `V` and `𝒲 ⟶ 𝒳 ⟶ Y` factors as `𝒲 ⟶ V ⟶ Y` with `V ⟶ Y` of finite
presentation and separated: locally of finite presentation by Stacks 06QI and Stacks 06Q9,
quasi-compact because `𝒲 ⟶ Y` is and the gerbe is surjective, and separated by Stacks 0CPQ
applied to `𝒲 ⟶ V ⟶ Y`, the gerbe being a universal homeomorphism (Stacks 06R9).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_gerbeBase_isFinitePresentation_isSeparated`:
  the factorization through the base of the gerbe, of finite presentation and separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_gerbe_isImmersion_isProper_of_isGerbe`: after
  shrinking to a dense open of the base (Stacks 088N), the base immerses into `ℙⁿ_Y`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_gerbe_isImmersion_isProper_of_isReducedStack`:
  the same for the dense open gerbe of a reduced algebraic stack (Stacks 06RC).

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The base of the gerbe locus, in the proof of Stacks 0CQ8.** Let `Y` be a Noetherian
algebraic space, `f : 𝒳 ⟶ Y` a separated 1-morphism of finite type from an algebraic stack and
`ι : 𝒲 ⟶ 𝒳` an open immersion from an algebraic stack which is a gerbe. Then there are an
algebraic space `V`, a 1-morphism `g : 𝒲 ⟶ V` making `𝒲` a gerbe over `V` and a morphism
`φ : V ⟶ Y` of finite presentation and separated with `g ≫ φ` 2-isomorphic to `ι ≫ f`.

The factorization is the universality of the gerbe for 1-morphisms to algebraic spaces. The
gerbe is flat, locally of finite presentation and surjective (Stacks 06QI) and `ι ≫ f` is
locally of finite presentation (Stacks 0DQJ), so `φ` is (Stacks 06Q9). `ι` is quasi-compact
(Stacks 0CPM, `𝒳` being locally Noetherian by Stacks 06R6), so `φ` is quasi-compact. The gerbe
is a universal homeomorphism (Stacks 06R9), hence universally injective, and `ι ≫ f` is
separated, so `φ` is separated by Stacks 0CPQ. -/
theorem exists_gerbeBase_isFinitePresentation_isSeparated
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.IsNoetherian B S hS B.contains_terminal Y)
    {𝒳 𝒲 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) (ι : 𝒲 ⟶ 𝒳)
    (hι : IsOpenImmersion B S hS ι) (h𝒲 : IsGerbe B S hS 𝒲) :
    ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
      (g : 𝒲 ⟶ algebraicSpaceStack.{u, w} B S hS V hV) (φ : V ⟶ Y),
      IsGerbeOver B S hS g ∧
        Nonempty (g ≫ algebraicSpaceStackMap.{u, w} B S hS hV hY φ ≅ ι ≫ f) ∧
        Space.IsFinitePresentation B S hS φ ∧ Space.IsSeparated B S hS φ := by
  obtain ⟨V, hV, g, hg⟩ := exists_isGerbeOver_algebraicSpaceStack B S hS h𝒲
  obtain ⟨φ, ⟨e⟩⟩ := exists_twoIso_comp_algebraicSpaceStackMap_of_isGerbeOver B S hS hV hY g hg
    (ι ≫ f)
  let Φ := algebraicSpaceStackMap.{u, w} B S hS hV hY φ
  obtain ⟨hgflat, hglfp⟩ := isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS g hg
  have hgsurj : Stack.IsSurjective B S hS g := isSurjective_of_isGerbeOver B S hS g hg
  -- the algebraic stack of `Y` and `𝒳` are locally Noetherian
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hYat : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) (algebraicSpaceStack.{u, w} B S hS Y hY) :=
    (Stack.scheme_atlas_iff_etaleLocalProperty B S hS _ Y hY).2 hYN.2.2
  have hXat : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳 :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS f hft.1 hYat
  -- local finite presentation
  have hιflfp : IsLocallyOfFinitePresentation B S hS (ι ≫ f) :=
    isLocallyOfFinitePresentation_comp B S hS ι f
      (isLocallyOfFinitePresentation_of_isOpenImmersion B S hS ι hι)
      (isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS f hYat hft.1)
  have hgΦlfp : IsLocallyOfFinitePresentation B S hS (g ≫ Φ) :=
    (isLocallyOfFinitePresentation_iff_of_twoIso B S hS _ _
      (Stack.algStackHomIso B S hS e.symm)).1 hιflfp
  have hΦlfp : IsLocallyOfFinitePresentation B S hS Φ :=
    isLocallyOfFinitePresentation_of_comp_of_fppf B S hS g Φ hgΦlfp hgsurj hgflat hglfp
  -- quasi-compactness
  have hιim : IsImmersion B S hS ι := isImmersion_of_isOpenImmersion B S hS ι hι
  have hιqc : Stack.IsQuasiCompactMorphism B S hS ι :=
    (Stack.isQuasiCompact_iff_baseChange_quasiCompact B S hS ι hιim.1).mp
      (hasRelativeProperty_quasiCompact_of_isImmersion B S hS ι hιim hXat)
  have hΦqc : Stack.IsQuasiCompactMorphism B S hS Φ :=
    Stack.isQuasiCompactMorphism_of_comp_of_isSurjective B S hS g (ι ≫ f) Φ e hgsurj
      (Stack.isQuasiCompactMorphism_comp B S hS ι f hιqc hft.2)
  -- separatedness
  have hιfsep : IsSeparated B S hS (ι ≫ f) :=
    isSeparated_comp B S hS ι f
      (isSeparated_of_isMonomorphism B S hS ι (isMonomorphism_of_isOpenImmersion B S hS ι hι))
      hsep
  have hgΦsep : IsSeparated B S hS (g ≫ Φ) :=
    isSeparated_of_equivalence B S hS (ι ≫ f) (g ≫ Φ) (BasedFunctor.id _)
      (Stack.algStackHomHomIso B S hS e.symm) (inferInstanceAs (𝟭 _).IsEquivalence) hιfsep
  have hΦsep : IsSeparated B S hS Φ :=
    isSeparated_of_isSeparated_comp_of_universallyInjective_of_isRepresentableByAlgebraicSpaces
      B S hS g Φ hgsurj hgflat hglfp
      (Stack.universallyInjective_of_universalHomeomorphism B S hS
        (Stack.universalHomeomorphism_of_isGerbeOver B S hS g hg))
      hgΦsep (isRepresentableByAlgebraicSpaces_algebraicSpaceStackMap.{u, w} B S hS hV hY φ)
  have hφsep : Space.IsSeparated B S hS φ :=
    (isSeparated_algebraicSpaceStackMap_iff.{u, w} B S hS hV hY φ).1 hΦsep
  refine ⟨V, hV, g, φ, hg, ⟨e⟩, ⟨?_, ?_, Space.isQuasiSeparated_of_isSeparated B S hS hφsep⟩,
    hφsep⟩
  · exact (isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B S hS hV hY φ).1 hΦlfp
  · exact (isQuasiCompactMorphism_algebraicSpaceStackMap_iff.{u, w} B S hS hV hY φ).1 hΦqc

/-- **The gerbe locus over a dense open of its base, immersed in `ℙⁿ_Y`, in the proof of
Stacks 0CQ8.** Let `Y` be a Noetherian algebraic space, `f : 𝒳 ⟶ Y` a separated 1-morphism of
finite type from an algebraic stack and `ι : 𝒲 ⟶ 𝒳` an open immersion with dense image from an
algebraic stack which is a gerbe. Then there are an algebraic space `V₁`, a gerbe
`g₁ : 𝒲₁ ⟶ V₁`, an open immersion `ι₁ : 𝒲₁ ⟶ 𝒳` with dense image, a proper morphism
`q : P ⟶ Y` of algebraic spaces and an immersion `j : V₁ ⟶ P` with `V₁` quasi-compact, `j ≫ q`
separated, and `g₁ ≫ j ≫ q` 2-isomorphic to `ι₁ ≫ f`.

`V₁` is the dense open of the base `V` of the gerbe (of finite presentation and separated over
`Y` by `exists_gerbeBase_isFinitePresentation_isSeparated`) which Stacks 088N immerses into
`𝔸ⁿ_Y`, and `P = ℙⁿ_Y` (`AlgebraicGeometry.Space.exists_isProper_isOpenImmersion_affineSpaceOver`).
`𝒲₁` is the base change of the gerbe `𝒲 ⟶ V` to `V₁`, a gerbe by Stacks 06QE and open in `𝒲`;
its image in `|𝒲|` is the preimage of the dense image of `|V₁|` under the homeomorphism
`|𝒲| ⟶ |V|` (Stacks 06R9, Stacks 04XH), hence dense. -/
theorem exists_gerbe_isImmersion_isProper_of_isGerbe
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.IsNoetherian B S hS B.contains_terminal Y)
    {𝒳 𝒲 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) (ι : 𝒲 ⟶ 𝒳)
    (hι : IsOpenImmersion B S hS ι) (h𝒲 : IsGerbe B S hS 𝒲)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS ι))) :
    ∃ (V₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV₁ : IsAlgebraicSpace B S hS V₁)
      (𝒲₁ : AlgebraicStacks.{u, w} B S hS) (g₁ : 𝒲₁ ⟶ algebraicSpaceStack.{u, w} B S hS V₁ hV₁)
      (ι₁ : 𝒲₁ ⟶ 𝒳) (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS P)
      (q : P ⟶ Y) (j : V₁ ⟶ P),
      IsGerbeOver B S hS g₁ ∧ IsOpenImmersion B S hS ι₁ ∧
        @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS ι₁)) ∧
        Space.IsProper B S hS q ∧ Space.IsImmersion B S hS j ∧
        Space.IsQuasiCompactSpace B S hS V₁ ∧ Space.IsSeparated B S hS (j ≫ q) ∧
        Nonempty (g₁ ≫ algebraicSpaceStackMap.{u, w} B S hS hV₁ hY (j ≫ q) ≅ ι₁ ≫ f) := by
  obtain ⟨V, hV, g, φ, hg, ⟨e⟩, hφfp, hφsep⟩ :=
    exists_gerbeBase_isFinitePresentation_isSeparated B S hS hY hYN f hsep hft ι hι h𝒲
  -- Stacks 088N and the compactification `𝔸ⁿ_Y ⊆ ℙⁿ_Y`
  obtain ⟨W, hW, hWdense, n, i, hi, hifac⟩ :=
    Space.exists_denseOpen_isImmersion_affineSpaceOver B S hS B.contains_terminal φ hV hY hYN hφfp
  obtain ⟨P, hP, q, k, hq, hk, hkq⟩ := Space.exists_isProper_isOpenImmersion_affineSpaceOver
    B S hS hY n
  have hWalg : IsAlgebraicSpace B S hS W.toFunctor := hW.1
  have hjq : (i ≫ k) ≫ q = W.ι ≫ φ := by rw [Category.assoc, hkq, hifac]
  have hVN : Space.IsNoetherian B S hS B.contains_terminal V :=
    Space.isNoetherian_of_isFinitePresentation B S hS B.contains_terminal φ hV hY hφfp hYN
  -- the base change of the gerbe to `W`
  let a := algebraicSpaceStackMap.{u, w} B S hS hWalg hV W.ι
  let sq := twoFibreProductSquareAlgebraicStacks B S hS a g
  have hsq : Bicategory.IsTwoFibreProduct sq :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a g
  have ha : IsOpenImmersion B S hS a :=
    isOpenImmersion_of_isOpenImmersion_representingMap B S hS a W.toFunctor V hWalg hV
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS W.toFunctor hWalg)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (by rw [representingMap_associatedMap]; exact hW.2)
  have hg₁ : IsGerbeOver B S hS sq.fst :=
    isGerbeOver_of_isTwoFibreProduct B S hS sq.swap (Bicategory.isTwoFibreProduct_swap hsq) hg
  have hsnd : IsOpenImmersion B S hS sq.snd :=
    isOpenImmersion_baseChange_snd B S hS sq hsq ha
  -- density
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS 𝒲.val
  let _ := pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS V hV).val
  have hadense : Dense (Set.range (pointsMap B S hS a)) :=
    dense_range_pointsMap_algebraicSpaceStackMap_of_isDenseOpenSubspace.{u, w} B S hS hV
      ⟨hW, hWdense⟩
  have hghomeo := isHomeomorph_pointsMap_of_isGerbeOver B S hS g hg
  have hsnddense : Dense (Set.range (pointsMap B S hS sq.snd)) := by
    refine (hadense.preimage hghomeo.isOpenMap).mono ?_
    rintro x ⟨v, hv⟩
    obtain ⟨p, -, hp⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS sq hsq v x hv
    exact ⟨p, hp⟩
  have hι₁dense : Dense (Set.range (pointsMap B S hS (sq.snd ≫ ι))) := by
    rw [pointsMap_comp, Set.range_comp]
    exact (show DenseRange (pointsMap B S hS ι) from hdense).dense_image
      (continuous_pointsMap B S hS _ 𝒳.val ι.hom.hom) hsnddense
  refine ⟨W.toFunctor, hWalg, sq.pt, sq.fst, sq.snd ≫ ι, P, hP, q, i ≫ k, hg₁,
    isOpenImmersion_comp B S hS sq.snd ι hsnd hι, hι₁dense, hq,
    Space.isImmersion_comp B S hS i k hi (Space.isImmersion_of_isOpenImmersion B S hS hk),
    Space.isQuasiCompactSpace_of_isImmersion_of_isNoetherian B S hS (hZ := B.contains_terminal)
      hV hWalg hVN W.ι (Space.isImmersion_of_isOpenImmersion B S hS hW.2), ?_, ⟨?_⟩⟩
  · rw [hjq]
    exact Space.isSeparated_comp B S hS W.ι φ
      (Space.isSeparated_of_mono (B := B) (S := S) (hS := hS) W.ι inferInstance) hφsep
  · have hmap : algebraicSpaceStackMap.{u, w} B S hS hWalg hY ((i ≫ k) ≫ q) =
        a ≫ algebraicSpaceStackMap.{u, w} B S hS hV hY φ := by
      rw [hjq]
      exact algebraicSpaceStackMap_comp B S hS hWalg hV hY W.ι φ
    exact eqToIso (congrArg (sq.fst ≫ ·) hmap) ≪≫ (Bicategory.associator _ _ _).symm ≪≫
      Bicategory.whiskerRightIso sq.iso _ ≪≫ Bicategory.associator _ _ _ ≪≫
      Bicategory.whiskerLeftIso sq.snd e ≪≫ (Bicategory.associator _ _ _).symm

/-- **The gerbe locus of a reduced algebraic stack, in the proof of Stacks 0CQ8.** Let `Y` be a
Noetherian algebraic space and `f : 𝒳 ⟶ Y` a separated 1-morphism of finite type from a reduced
algebraic stack whose inertia projection is quasi-compact. Then the conclusion of
`exists_gerbe_isImmersion_isProper_of_isGerbe` holds: there are a gerbe `g₁ : 𝒲₁ ⟶ V₁` over a
quasi-compact algebraic space, an open immersion `ι₁ : 𝒲₁ ⟶ 𝒳` with dense image, a proper
`q : P ⟶ Y` and an immersion `j : V₁ ⟶ P` with `j ≫ q` separated and `g₁ ≫ j ≫ q` 2-isomorphic to
`ι₁ ≫ f`.

`𝒳` has a dense open substack which is a gerbe (Stacks 06RC); apply
`exists_gerbe_isImmersion_isProper_of_isGerbe` to its inclusion. -/
theorem exists_gerbe_isImmersion_isProper_of_isReducedStack
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.IsNoetherian B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hred : IsReducedStack B S hS 𝒳)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    ∃ (V₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV₁ : IsAlgebraicSpace B S hS V₁)
      (𝒲₁ : AlgebraicStacks.{u, w} B S hS) (g₁ : 𝒲₁ ⟶ algebraicSpaceStack.{u, w} B S hS V₁ hV₁)
      (ι₁ : 𝒲₁ ⟶ 𝒳) (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS P)
      (q : P ⟶ Y) (j : V₁ ⟶ P),
      IsGerbeOver B S hS g₁ ∧ IsOpenImmersion B S hS ι₁ ∧
        @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS ι₁)) ∧
        Space.IsProper B S hS q ∧ Space.IsImmersion B S hS j ∧
        Space.IsQuasiCompactSpace B S hS V₁ ∧ Space.IsSeparated B S hS (j ≫ q) ∧
        Nonempty (g₁ ≫ algebraicSpaceStackMap.{u, w} B S hS hV₁ hY (j ≫ q) ≅ ι₁ ≫ f) := by
  obtain ⟨W, hWdense, hWgerbe⟩ := exists_openSubstack_dense_isGerbe B S hS 𝒳 hred hqc
  exact exists_gerbe_isImmersion_isProper_of_isGerbe B S hS hY hYN f hsep hft W.inclusion
    W.isOpenImmersion hWgerbe hWdense

end AlgebraicGeometry.Stack.AlgebraicStacks

end
