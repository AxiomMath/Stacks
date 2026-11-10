module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparisonSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GraphMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# The scheme theoretic image of a section over an open substack (Stacks 0CPW)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is representable by
algebraic spaces and separated, let `𝒱 ⊆ 𝒴` be an open substack whose inclusion `𝒱 ⟶ 𝒴` is
quasi-compact, and let `s : 𝒱 ⟶ 𝒳` be a *section of `f` over `𝒱`*, that is a 1-morphism
together with a 2-isomorphism `s ≫ f ≅ (𝒱 ⟶ 𝒴)`. Let `𝒴'` be the scheme theoretic image of `s`,
a closed substack of `𝒳`. **Stacks 0CPW** asserts that `𝒴' ⟶ 𝒴` — the inclusion of `𝒴'`
followed by `f` — is an isomorphism over `𝒱`, i.e. that the projection `𝒴' ×_𝒴 𝒱 ⟶ 𝒱` is an
equivalence.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isSeparated_of_comp_quasiCompact`: a
  section over an open substack of a separated 1-morphism whose composite with that 1-morphism is
  quasi-compact is itself quasi-compact (**Stacks 050Y** with **Stacks 050E** part (1)).
* `AlgebraicGeometry.Stack.partialSectionImageSection` and
  `AlgebraicGeometry.Stack.essSurj_fst_partialSectionImageSquare`: the factorization of `s`
  through `𝒴'` is a section of the projection `𝒴' ×_𝒴 𝒱 ⟶ 𝒱`, which is therefore essentially
  surjective.
* `AlgebraicGeometry.Stack.isClosedSubstack_essImage_partialSectionGraph`: the essential image of
  the graph `𝒱 ⟶ 𝒱 ×_𝒴 𝒳` of `s` is a closed substack, `f` being separated.
* `AlgebraicGeometry.Stack.exists_iso_partialSectionGraph_obj`: every object of `𝒱 ×_𝒴 𝒳` lying
  over `𝒴'` is isomorphic to one on the graph of `s`.
* `AlgebraicGeometry.Stack.isEquivalence_fst_of_isSchemeTheoreticImage_partialSection`:
  **Stacks 0CPW**.

## The proof

The source's, with the reduction to an algebraic-space target replaced by a direct argument on
`𝒱 ×_𝒴 𝒳`. The section `s` is quasi-compact by **Stacks 050Y**, so the scheme theoretic image
commutes with the flat base change `𝒱 ×_𝒴 𝒳 ⟶ 𝒳` of the open immersion `𝒱 ⟶ 𝒴`
(**Stacks 0CMK**): the inverse image of `𝒴'` in `𝒱 ×_𝒴 𝒳` is the scheme theoretic image of the
base change of `s`. That base change factors through the graph of `s`, a section of the separated
projection `𝒱 ×_𝒴 𝒳 ⟶ 𝒱`, hence a closed immersion (the comparison of Stacks 050H with the
relative diagonal of `f`, a closed immersion by **Stacks 04YS**), whose essential image is a
closed substack (**Stacks 0506**). So the inverse image of `𝒴'` lies on the graph, which is the
content of **Stacks 0CP3** in this setting: every object of `𝒴' ×_𝒴 𝒱` is isomorphic, over its
image in `𝒱`, to the image of an object of `𝒱`. Fullness of the projection follows, since the
graph is a section of the projection to `𝒱` on the nose; faithfulness holds because `f` is
representable by algebraic spaces, hence faithful (Stacks 04Y5), and essential surjectivity
because the projection has a section.

## Implementation notes

The scheme theoretic image is a property `P` of the objects of `𝒳` with
`AlgebraicGeometry.Stack.IsSchemeTheoreticImage s P`; it exists by Stacks 0CPU
(`AlgebraicGeometry.Stack.isSchemeTheoreticImage_schemeTheoreticImageCandidate`), and the full
subcategory it cuts out is an algebraic stack by
`AlgebraicGeometry.Stack.IsSchemeTheoreticImage.isAlgebraicStack`.

An open substack is `AlgebraicGeometry.Stack.OpenSubstack`, a structure, so the algebraic stack
`𝒱` is spelled `fullSubcategoryAlgebraicStack 𝒴 V.property V.isAlgebraic` and the 1-morphism
`𝒱 ⟶ 𝒴` is the corresponding `fullSubcategoryInclusion`. "Isomorphism over `𝒱`" is read, as
everywhere in this development, as the underlying functor of the projection being an equivalence
of categories: `CategoryTheory.Functor.IsEquivalence` of
`(… ).fst.hom.hom.toFunctor`, the shape of
`AlgebraicGeometry.Stack.sectionSecondProjection_isEquivalence`.

The graph of `s` is used in two forms: `AlgebraicGeometry.Stack.graph`, the mediating
1-morphism of the universal property, which is the one shown to be a closed immersion, and the
strict comparison `AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks` of
`AlgebraicGeometry.Stack.graphCone`, whose composite with the projection to `𝒱` is the identity on
the nose. The two are 2-isomorphic, so they have the same essential image.

## References

* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CMK](https://stacks.math.columbia.edu/tag/0CMK)
* [Stacks Project, Tag 0CP3](https://stacks.math.columbia.edu/tag/0CP3)
* [Stacks Project, Tag 0CPW](https://stacks.math.columbia.edu/tag/0CPW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The first step of Stacks 0CPW.** Let `f : 𝒳 ⟶ 𝒴` be a separated 1-morphism of algebraic
stacks over `S`, let `𝒱 ⊆ 𝒴` be an open substack and let `s : 𝒱 ⟶ 𝒳` be such that the composite
`s ≫ f` is quasi-compact. Then `s` is quasi-compact.

A separated 1-morphism is quasi-separated by **Stacks 050E** part (1), and **Stacks 050Y** says
that a quasi-compact composite with quasi-separated second factor has quasi-compact first factor.

The hypothesis is on the composite `s ≫ f`; for a partial section it follows from
quasi-compactness of `𝒱 ⟶ 𝒴`, to which the composite is 2-isomorphic, by Stacks 050X applied to
the identity. -/
theorem isQuasiCompactMorphism_of_isSeparated_of_comp_quasiCompact (f : 𝒳 ⟶ 𝒴)
    (V : OpenSubstack 𝒴)
    (s : fullSubcategoryAlgebraicStack 𝒴 V.property V.isAlgebraic ⟶ 𝒳)
    (hsqc : IsQuasiCompactMorphism B S hS (s ≫ f))
    (hf : AlgebraicStacks.IsSeparated B S hS f) :
    IsQuasiCompactMorphism B S hS s :=
  isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS s f hsqc
    (AlgebraicStacks.isQuasiSeparated_of_isSeparated B S hS hf)

section PartialSection

variable (f : 𝒳 ⟶ 𝒴) (V : OpenSubstack 𝒴)
  (s : fullSubcategoryAlgebraicStack 𝒴 V.property V.isAlgebraic ⟶ 𝒳)
  {P : ObjectProperty 𝒳.val.val.obj}
  (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))

/-- The factorization of a 1-morphism through the substack cut out by `P`, read as a 1-morphism
of algebraic stacks: `AlgebraicGeometry.Stack.FactorsThroughSubstack` supplies a 1-morphism over
the big fppf site of `S`, and the 2-category of algebraic stacks has the 1-morphisms of the
ambient one, so it is reached by two applications of
`CategoryTheory.Bicategory.InducedBicategory.mkHom`, exactly as
`AlgebraicGeometry.Stack.substackMapOfLe` does. -/
noncomputable def substackFactorizationHom (hfac : FactorsThroughSubstack s P) :
    fullSubcategoryAlgebraicStack 𝒴 V.property V.isAlgebraic ⟶
      fullSubcategoryAlgebraicStack 𝒳 P hA :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom hfac.choose)

/-- The factorization `AlgebraicGeometry.Stack.substackFactorizationHom` composed with the
inclusion of the substack is the original 1-morphism, up to the 2-isomorphism that
`AlgebraicGeometry.Stack.FactorsThroughSubstack` carries. -/
noncomputable def substackFactorizationIso (hfac : FactorsThroughSubstack s P) :
    substackFactorizationHom B S hS V s hA hfac ≫ fullSubcategoryInclusion 𝒳 P hA ≅ s :=
  Bicategory.InducedBicategory.isoMk
    (Bicategory.InducedBicategory.isoMk hfac.choose_spec.some)

/-- **The 2-commutative square exhibiting the factorization of a section over `𝒱` as a section
of the projection.** Let `s : 𝒱 ⟶ 𝒳` be a section of `f : 𝒳 ⟶ 𝒴` over the open substack
`𝒱 ⊆ 𝒴` and let it factor through the substack cut out by `P`. The square has apex `𝒱`, first
leg the identity of
`𝒱` and second leg the factorization `k : 𝒱 ⟶ 𝒴'`, over the cospan
`(𝒱 ⟶ 𝒴, 𝒴' ⟶ 𝒳 ⟶ 𝒴)`. Its filler is the partial-section 2-isomorphism composed with the
factorization 2-isomorphism, reassociated. -/
noncomputable def partialSectionImageSquare
    (hsec : s ≫ f ≅ fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic)
    (hfac : FactorsThroughSubstack s P) :
    Bicategory.TwoCommSq (fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic)
      (fullSubcategoryInclusion 𝒳 P hA ≫ f) where
  pt := fullSubcategoryAlgebraicStack 𝒴 V.property V.isAlgebraic
  fst := 𝟙 _
  snd := substackFactorizationHom B S hS V s hA hfac
  iso :=
    Bicategory.leftUnitor (fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic) ≪≫ hsec.symm ≪≫
      (Bicategory.whiskerRightIso (substackFactorizationIso B S hS V s hA hfac) f).symm ≪≫
      Bicategory.associator (substackFactorizationHom B S hS V s hA hfac)
        (fullSubcategoryInclusion 𝒳 P hA) f

/-- **The geometric half of Stacks 0CPW: the factorization of a section over `𝒱` is a section of
the projection.** The strict comparison of
`AlgebraicGeometry.Stack.partialSectionImageSquare` with the canonical 2-fibre product square of
the same cospan is a 1-morphism `𝒱 ⟶ 𝒴' ×_𝒴 𝒱`. -/
noncomputable def partialSectionImageSection
    (hsec : s ≫ f ≅ fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic)
    (hfac : FactorsThroughSubstack s P) :
    fullSubcategoryAlgebraicStack 𝒴 V.property V.isAlgebraic ⟶
      (twoFibreProductSquareAlgebraicStacks B S hS
        (fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic)
        (fullSubcategoryInclusion 𝒳 P hA ≫ f)).pt :=
  (canonicalPreHomAlgebraicStacks B S hS
    (fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic)
    (fullSubcategoryInclusion 𝒳 P hA ≫ f)
    (partialSectionImageSquare B S hS f V s hA hsec hfac)).hom

/-- `AlgebraicGeometry.Stack.partialSectionImageSection` is a section of the projection
`𝒴' ×_𝒴 𝒱 ⟶ 𝒱` on the nose: the strict comparison of a 2-commutative square with the canonical
2-fibre product square has its composite with each projection equal to the corresponding leg, and
the first leg of `AlgebraicGeometry.Stack.partialSectionImageSquare` is the identity. -/
theorem partialSectionImageSection_comp_fst
    (hsec : s ≫ f ≅ fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic)
    (hfac : FactorsThroughSubstack s P) :
    partialSectionImageSection B S hS f V s hA hsec hfac ≫
        (twoFibreProductSquareAlgebraicStacks B S hS
          (fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic)
          (fullSubcategoryInclusion 𝒳 P hA ≫ f)).fst =
      𝟙 (fullSubcategoryAlgebraicStack 𝒴 V.property V.isAlgebraic) :=
  canonicalPreHomAlgebraicStacks_hom_comp_fst B S hS
    (fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic)
    (fullSubcategoryInclusion 𝒳 P hA ≫ f)
    (partialSectionImageSquare B S hS f V s hA hsec hfac)

/-- **The projection to `𝒱` is essentially surjective.** The projection `𝒴' ×_𝒴 𝒱 ⟶ 𝒱` of the
base change along `𝒱 ⟶ 𝒴` of a substack of `𝒳` through which a partial section factors is
essentially surjective on underlying categories: it has a section, by
`AlgebraicGeometry.Stack.partialSectionImageSection_comp_fst`, and the underlying functor of a
composite of 1-morphisms of algebraic stacks is the composite of the underlying functors, so
every object of `𝒱` is literally the image of one of `𝒴' ×_𝒴 𝒱`. -/
theorem essSurj_fst_partialSectionImageSquare
    (hsec : s ≫ f ≅ fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic)
    (hfac : FactorsThroughSubstack s P) :
    (twoFibreProductSquareAlgebraicStacks B S hS
        (fullSubcategoryInclusion 𝒴 V.property V.isAlgebraic)
        (fullSubcategoryInclusion 𝒳 P hA ≫ f)).fst.hom.hom.toFunctor.EssSurj := by
  have h := congrArg (fun m => m.hom.hom.toFunctor)
    (partialSectionImageSection_comp_fst B S hS f V s hA hsec hfac)
  exact ⟨fun Z => ⟨(partialSectionImageSection B S hS f V s hA hsec hfac).hom.hom.toFunctor.obj Z,
    ⟨eqToIso (Functor.congr_obj h Z)⟩⟩⟩

end PartialSection

/-! ### The proof of Stacks 0CPW -/

section Proof

open TwoFibreProductOver

/-- The open substack `V`, as an algebraic stack. -/
local notation "𝒱[" V "]" =>
  fullSubcategoryAlgebraicStack _ (OpenSubstack.property V) (OpenSubstack.isAlgebraic V)
/-- The inclusion of the open substack `V` into the ambient algebraic stack. -/
local notation "ι[" V "]" =>
  fullSubcategoryInclusion _ (OpenSubstack.property V) (OpenSubstack.isAlgebraic V)

variable (f : 𝒳 ⟶ 𝒴) (V : OpenSubstack 𝒴) (s : 𝒱[V] ⟶ 𝒳) (η : ι[V] ≅ s ≫ f)

/-- **The graph of a section over `𝒱` cuts out a closed substack.** Let `f : 𝒳 ⟶ 𝒴` be
representable by algebraic spaces and separated and let `s : 𝒱 ⟶ 𝒳` be a section of `f` over the
open substack `𝒱`, with `η : (𝒱 ⟶ 𝒴) ≅ s ≫ f`. The objects of `𝒱 ×_𝒴 𝒳` isomorphic to the image
of an object of `𝒱` under the strict graph of `s` form a closed substack.

The graph `𝒱 ⟶ 𝒱 ×_𝒴 𝒳` is a base change of the comparison `𝒱 ×_𝒳 𝒳 ⟶ 𝒱 ×_𝒴 𝒳`
(`AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison`), which is a base change of the
relative diagonal of `f` (Stacks 04Z1); that diagonal is a closed immersion by **Stacks 04YS**, so
the graph is a closed immersion, and its essential image is a closed substack by
**Stacks 0506**. The strict graph built from the canonical comparison is 2-isomorphic to the
graph, so has the same essential image. -/
theorem isClosedSubstack_essImage_partialSectionGraph
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hf : AlgebraicStacks.IsSeparated B S hS f) :
    IsClosedSubstack (twoFibreProductSquareAlgebraicStacks B S hS ι[V] f).pt
      (CatFiberedInGroupoids.homFunctor (canonicalPreHomAlgebraicStacks B S hS ι[V] f
        (graphCone B S hS s ι[V] f η)).hom.hom).essImage := by
  have hΔ : Stack.IsClosedImmersion B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :=
    isClosedImmersion_relativeDiagonal_of_universallyClosed B S hS f hrep
      (presheaf_locallyOfFiniteType_relativeDiagonal B S hS f hrep)
      (universallyClosed_of_isProper B S hS _ hf)
  have hcmp := relativeProperty_baseChange.{u, u, u + 1} B S hS
    (fun _ _ k => Space.IsClosedImmersion B S hS k.hom)
    𝒳.val (twoFibreProductAlgebraicStack B S hS f f).val
    (twoFibreProductAlgebraicStack B S hS (s ≫ f) (𝟙 𝒳 ≫ f)).val
    (relativeDiagonalAlgebraicStacks B S hS f).hom
    (comparisonCospanRight B S hS s (𝟙 𝒳) f).hom
    (comparisonSquare B S hS s (𝟙 𝒳) f)
    (isTwoFibreProduct_comparisonSquare B S hS s (𝟙 𝒳) f) hΔ
  have hgraph : AlgebraicStacks.IsClosedImmersion B S hS (graph B S hS s ι[V] f η) :=
    ⟨isRepresentableByAlgebraicSpaces_graph B S hS s ι[V] f η,
      relativeProperty_graph_of_comparison B S hS
        (fun _ _ k => Space.IsClosedImmersion B S hS k.hom) s ι[V] f η hcmp⟩
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS ι[V] f)
    (graphMorphism B S hS s ι[V] f η)
    (canonicalPreHomAlgebraicStacks B S hS ι[V] f (graphCone B S hS s ι[V] f η))
  have he : (CatFiberedInGroupoids.homFunctor (graph B S hS s ι[V] f η).hom).essImage =
      (CatFiberedInGroupoids.homFunctor (canonicalPreHomAlgebraicStacks B S hS ι[V] f
        (graphCone B S hS s ι[V] f η)).hom.hom).essImage := by
    let e := CatFiberedInGroupoids.underlyingIso (algebraicStacksTwoIsoHom B S hS θ)
    ext x
    exact ⟨fun h => h.ofNatIso e, fun h => h.ofNatIso e.symm⟩
  exact he ▸ AlgebraicStacks.isClosedSubstack_essImage (graph B S hS s ι[V] f η) hgraph

/-- **An object of `𝒱 ×_𝒴 𝒳` over an object of `𝒱` through `s`.** An object `x = (a, x₀, φ)` of
`𝒱 ×_𝒴 𝒳` together with an isomorphism `x₀ ≅ s(c)` over the identity is isomorphic to the image
of `c` under the strict graph of `s`: the comparison `φ` and `η` identify `a` with `c` over the
identity, and `𝒱 ⟶ 𝒴` is fully faithful. -/
theorem nonempty_iso_partialSectionGraph_obj {U : BigFppfOver B S hS}
    (x : (twoFibreProductSquareAlgebraicStacks B S hS ι[V] f).pt.val.val.obj)
    (c : 𝒱[V].val.val.obj)
    (hx : x.base = U) (hc : 𝒱[V].val.val.p.obj c = U)
    (e : x.y ≅ s.hom.hom.obj c) (he : 𝒳.val.val.p.IsHomLift (𝟙 U) e.hom) :
    Nonempty ((canonicalPreHomAlgebraicStacks B S hS ι[V] f
      (graphCone B S hS s ι[V] f η)).hom.hom.hom.obj c ≅ x) := by
  let σ := (canonicalPreHomAlgebraicStacks B S hS ι[V] f (graphCone B S hS s ι[V] f η)).hom
  let ψ := (σ.hom.hom.obj c).iso
  have hψ : 𝒴.val.val.p.IsHomLift (𝟙 U) ψ.hom := hc ▸ (σ.hom.hom.obj c).vertical
  have hφ : 𝒴.val.val.p.IsHomLift (𝟙 U) x.iso.hom := hx ▸ x.vertical
  let e₀ : (σ.hom.hom.obj c).x.obj ≅ x.x.obj := ψ ≪≫ f.hom.hom.toFunctor.mapIso e.symm ≪≫ x.iso.symm
  have he₀ : 𝒴.val.val.p.IsHomLift (𝟙 U) e₀.hom := by
    change 𝒴.val.val.p.IsHomLift (𝟙 U) (ψ.hom ≫ f.hom.hom.toFunctor.map e.inv ≫ x.iso.inv)
    exact @IsHomLift.comp_of_lift_id _ _ _ _ 𝒴.val.val.p U _ _ _ ψ.hom _ hψ
      (@IsHomLift.comp_of_lift_id _ _ _ _ 𝒴.val.val.p U _ _ _ _ _
        (Functor.isHomLift_map_of_comp_eq f.hom.hom.w (𝟙 U) e.inv)
        (IsHomLift.lift_id_inv _ U x.iso))
  refine ⟨isoMkVertical (U := U) (ObjectProperty.isoMk _ e₀) e.symm
    ((Functor.isHomLift_comp_iff _ _ _ _).2 he₀) ?_ ?_⟩
  · change 𝒳.val.val.p.IsHomLift (𝟙 U) e.inv
    infer_instance
  · change (ψ.hom ≫ f.hom.hom.toFunctor.map e.inv ≫ x.iso.inv) ≫ x.iso.hom =
      ψ.hom ≫ f.hom.hom.toFunctor.map e.inv
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The geometric core of Stacks 0CPW.** Let `f : 𝒳 ⟶ 𝒴` be representable by algebraic spaces
and separated, let `s : 𝒱 ⟶ 𝒳` be a quasi-compact section of `f` over the open substack `𝒱`, and
let `P` cut out the scheme theoretic image of `s`. Then every object of `𝒱 ×_𝒴 𝒳` whose image in
`𝒳` lies in `P` is isomorphic to the image of an object of `𝒱` under the strict graph of `s`.

The projection `𝒱 ×_𝒴 𝒳 ⟶ 𝒳` is a base change of the open immersion `𝒱 ⟶ 𝒴`, hence flat, so by
**Stacks 0CMK** the inverse image of `P` along it is the scheme theoretic image of the base change
`(𝒱 ×_𝒴 𝒳) ×_𝒳 𝒱 ⟶ 𝒱 ×_𝒴 𝒳` of `s`. That base change factors through the essential image of the
graph of `s`, a closed substack because `f` is separated
(`AlgebraicGeometry.Stack.isClosedSubstack_essImage_partialSectionGraph`), so the minimality of
the scheme theoretic image puts the inverse image of `P` inside it. -/
theorem exists_iso_partialSectionGraph_obj
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hf : AlgebraicStacks.IsSeparated B S hS f) (hsqc : IsQuasiCompactMorphism B S hS s)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage s P)
    (x : (twoFibreProductSquareAlgebraicStacks B S hS ι[V] f).pt.val.val.obj)
    (hx : P ((twoFibreProductSquareAlgebraicStacks B S hS ι[V] f).snd.hom.hom.obj x)) :
    ∃ c, Nonempty ((canonicalPreHomAlgebraicStacks B S hS ι[V] f
      (graphCone B S hS s ι[V] f η)).hom.hom.hom.obj c ≅ x) := by
  have hE := isClosedSubstack_essImage_partialSectionGraph B S hS f V s η hrep hf
  have := hE.1
  have hb : AlgebraicStacks.IsFlat B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS ι[V] f).snd :=
    AlgebraicStacks.isFlat_baseChange B S hS ι[V] f
      (twoFibreProductSquareAlgebraicStacks B S hS ι[V] f).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS ι[V] f))
      (AlgebraicStacks.isFlat_of_isSmooth B S hS _
        (AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS _ V.isOpenImmersion))
  refine (isSchemeTheoreticImage_inverseImage_of_isFlat s _ hsqc hb hP).2.2 _ hE
    ((factorsThroughSubstack_iff_forall _).2 fun t => ?_) x hx
  obtain ⟨_, _, c, rfl, hc, e, he⟩ := t
  exact ⟨c, nonempty_iso_partialSectionGraph_obj B S hS f V s η _ c rfl hc e he⟩

/-- **Stacks 0CPW.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is
representable by algebraic spaces and separated, let `𝒱 ⊆ 𝒴` be an open substack such that
`𝒱 ⟶ 𝒴` is quasi-compact, and let `s : 𝒱 ⟶ 𝒳` be a 1-morphism with `f ∘ s ≅ id_𝒱`, i.e. with a
2-isomorphism `s ≫ f ≅ (𝒱 ⟶ 𝒴)`. Let `P` cut out the scheme theoretic image `𝒴'` of `s`
(Stacks 0CMI). Then `𝒴' ⟶ 𝒴` is an isomorphism over `𝒱`: the projection `𝒴' ×_𝒴 𝒱 ⟶ 𝒱` is an
equivalence of categories.

`s` is quasi-compact by **Stacks 050Y**, as `s ≫ f` is 2-isomorphic to the quasi-compact
`𝒱 ⟶ 𝒴` and `f` is quasi-separated. The projection has a section, so it is essentially surjective
(`AlgebraicGeometry.Stack.essSurj_fst_partialSectionImageSquare`). It is faithful because `f` is,
being representable by algebraic spaces. It is full because every object of `𝒴' ×_𝒴 𝒱`, read in
`𝒱 ×_𝒴 𝒳`, is isomorphic to the image of an object of `𝒱` under the graph of `s`
(`AlgebraicGeometry.Stack.exists_iso_partialSectionGraph_obj`, which is where **Stacks 0CMK** and
the separatedness of `f` enter), and the graph is a section of the projection to `𝒱`. -/
@[stacks 0CPW]
theorem isEquivalence_fst_of_isSchemeTheoreticImage_partialSection
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hf : AlgebraicStacks.IsSeparated B S hS f)
    (hVqc : IsQuasiCompactMorphism B S hS ι[V]) (hsec : s ≫ f ≅ ι[V])
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage s P) :
    Functor.IsEquivalence (twoFibreProductSquareAlgebraicStacks B S hS ι[V]
      (fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack ≫ f)).fst.hom.hom.toFunctor := by
  have hsqc : IsQuasiCompactMorphism B S hS s :=
    isQuasiCompactMorphism_of_isSeparated_of_comp_quasiCompact B S hS f V s
      (isQuasiCompactMorphism_of_comp_of_isSurjective B S hS (𝟙 _) _ (s ≫ f)
        (Bicategory.leftUnitor _ ≪≫ hsec) (isSurjective_id B S hS _) hVqc) hf
  let σ := (canonicalPreHomAlgebraicStacks B S hS ι[V] f (graphCone B S hS s ι[V] f hsec.symm)).hom
  -- an object of `𝒴' ×_𝒴 𝒱`, read in `𝒱 ×_𝒴 𝒳`
  let G : (twoFibreProductSquareAlgebraicStacks B S hS ι[V]
      (fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack ≫ f)).pt.val.val.obj →
      (twoFibreProductSquareAlgebraicStacks B S hS ι[V] f).pt.val.val.obj := fun w =>
    ⟨w.base, w.x, w.y.obj, w.hx, w.hy, w.iso, w.vertical⟩
  have hG : ∀ w, ∃ c, Nonempty (σ.hom.hom.obj c ≅ G w) := fun w =>
    exists_iso_partialSectionGraph_obj B S hS f V s hsec.symm hrep hf hsqc hP (G w) w.y.property
  have hfull : (twoFibreProductSquareAlgebraicStacks B S hS ι[V]
      (fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack ≫ f)).fst.hom.hom.toFunctor.Full := by
    refine ⟨fun {w w'} α => ?_⟩
    obtain ⟨c, ⟨θ⟩⟩ := hG w
    obtain ⟨c', ⟨θ'⟩⟩ := hG w'
    let A := (twoFibreProductSquareAlgebraicStacks B S hS ι[V] f).fst.hom.hom.toFunctor
    let u : c ⟶ c' := A.map θ.hom ≫ α ≫ A.map θ'.inv
    let m : G w ⟶ G w' := θ.inv ≫ σ.hom.hom.map u ≫ θ'.hom
    have hma : A.map m = α := by
      rw [Functor.map_comp, Functor.map_comp]
      change A.map θ.inv ≫ (A.map θ.hom ≫ α ≫ A.map θ'.inv) ≫ A.map θ'.hom = α
      simp only [Category.assoc, Iso.inv_hom_id_map_assoc]
      refine (Category.assoc _ _ _).trans ?_
      exact (congrArg (α ≫ ·) (A.mapIso θ').inv_hom_id).trans (Category.comp_id α)
    exact ⟨⟨m.hbase, m.a, ObjectProperty.homMk m.b, m.ha,
      (Functor.isHomLift_comp_iff _ _ _ _).2 m.hb, m.w⟩, hma⟩
  have hfaithful : (twoFibreProductSquareAlgebraicStacks B S hS ι[V]
      (fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack ≫ f)).fst.hom.hom.toFunctor.Faithful := by
    refine ⟨fun {w w'} M₁ M₂ h => ?_⟩
    change M₁.a = M₂.a at h
    refine Hom.ext' h (ObjectProperty.hom_ext P
      ((AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces
        B S hS f hrep).map_injective ?_))
    exact (cancel_epi w.iso.hom).1 ((h ▸ M₁.w).symm.trans M₂.w)
  exact ⟨hfaithful, hfull,
    essSurj_fst_partialSectionImageSquare B S hS f V s hP.isAlgebraicStack hsec hP.2.1⟩

end Proof

end AlgebraicGeometry.Stack

end
