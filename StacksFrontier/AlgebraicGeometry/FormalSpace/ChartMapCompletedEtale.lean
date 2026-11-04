module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrumRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjectiveRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverRefinement

/-!
# A representable étale change of charts is a completed étale localization

Let `S` be a scheme contained in a big fppf site `B`. A chart map `t : U ⟶ V` of affine formal
algebraic spaces over `S` and a representable étale change of its source and target,

```
U' ⟶ U
↓      ↓
V' ⟶ V
```

give a second chart map `t' : U' ⟶ V'`. The proof of **Stacks 0ANG** needs this square read on
rings: the chart rings of `U'` and `V'` are the completions of étale ring maps out of the chart
rings of `U` and `V`, and the ring map presenting `t'` is the completed vertical map of the
resulting localization diagram of Situation 0CBA. That is exactly
`AlgebraicGeometry.FormalSpace.IsCompletedEtaleLocalizationOfChartMap`, and this file concludes
it.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_etale_bicontinuous_presentation_of_isRepresentableEtale`:
  for a weakly admissible ring `A` with countably generated zero neighbourhoods presenting a
  chart `V` of the site and a representable étale morphism `V' ⟶ V` out of an affine formal
  algebraic space, **any** prescribed presentation `A'` of `V'` by a weakly admissible ring is
  bicontinuously isomorphic to the completion `CompletionOver (A → A₁)` of an étale
  `A`-algebra `A₁`, compatibly with the given morphism.
* `AlgebraicGeometry.FormalSpace.isCompletedEtaleLocalizationOfChartMap_of_presentation`:
  `AlgebraicGeometry.FormalSpace.IsCompletedEtaleLocalizationOfChartMap` holds for a
  representable étale square whose lower chart map is presented by rings of the class `C`.

## Implementation notes

Both statements have to meet an *arbitrary prescribed* presentation of the upper chart map,
because that is how
`AlgebraicGeometry.FormalSpace.IsCompletedEtaleLocalizationOfChartMap` quantifies: the
consumer of the predicate, `AlgebraicGeometry.FormalSpace.ChartPropertyAscendsAlongAffineEtale'`,
has to prove `AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap` for `t'`, which is
itself a statement about every presentation of `t'`. The essential-surjectivity clause of
**Stacks 0AN8**, `AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf`, produces a
presentation of its own choosing instead, so the two have to be compared, and that comparison
is full faithfulness of `Spf` — **Stacks 0AN0** — in the bicontinuous form
`AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_of_formalSpectrum_iso`.

The cardinality side condition of
`AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf` is not an extra hypothesis here.
A ring of the class `C` has countably generated zero neighbourhoods, and
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_isCountablyGenerated` bounds such a ring by the
cutoff of the site: a countable chain of weak ideals of definition embeds it into a countable
product of quotients that lie in the site.

The commutativity of the localization diagram is *not* checked by hand on rings. Both of its
two composites `A → R → R₁^∧` are continuous homomorphisms over `S`, and the square of
formal spectra they induce is the given square of sheaves transported along the four
identifications; faithfulness of `Spf` — the uniqueness half of
`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq` — then forces
the two ring maps to agree.

## What is left of `HasEtaleRefinementOfSourceCover`

`AlgebraicGeometry.FormalSpace.isCompletedEtaleLocalizationOfChartMap_of_presentation` asks the
*lower* chart map `t` for a presentation by rings of the class `C`, and that is not a
convenience: the predicate demands one existentially, while
`AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf` runs the other way — from a
presentation of the base to one of an étale cover of it, never back. So the presentation of `t`
cannot be manufactured from a presentation of `t'`.

That hypothesis is the standing hypothesis of the source. Stacks 0ANG is stated for a morphism
of **locally countably indexed** formal algebraic spaces, so its charts `Xᵢ`, `Yᵢ` are countably
indexed and `Xᵢ ⟶ Yᵢ` is a morphism of `WAdm^{count}`;
`AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` carries that hypothesis on the
two ends of `f`, and
`FormalSpace.exists_finite_affineEtaleRefinement_completedEtaleLocalization_of_sourceCover` below
delivers everything that predicate asks for except its second presentation clause, asking
countable indexedness of the members of the covering directly — the step from "locally countably
indexed" to "the charts are countably indexed" is the implication (2) ⟹ (1) of Stacks 0AKX,
which the library does not carry.

## References

* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] sheaf_hasColimits

/-- **The essential-surjectivity clause of Stacks 0AN8 against a prescribed presentation.** Let
`A` be a weakly admissible topological ring over `S` with countably generated zero
neighbourhoods, let `V' ⟶ Spf A` be a representable étale morphism out of an affine formal
algebraic space and let `A'` be *any* weakly admissible topological ring over `S` presenting
`V'`. Then there is an étale `A`-algebra `A₁` and a bicontinuous isomorphism
`CompletionOver (A → A₁) ≃+* A'`, and the continuous homomorphism `A → A'` presenting
`V' ⟶ Spf A` is the canonical map `A → CompletionOver (A → A₁)` read through it.

The étale algebra and an identification of `V'` with the formal spectrum of its completion are
`AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf`; the comparison of that
identification with the prescribed one is **Stacks 0AN0** in the form
`AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_of_formalSpectrum_iso`.

NO TAG IS ATTACHED. Stacks 0AN8 asserts an equivalence of categories; what is used here is its
essential surjectivity, which is unnumbered in the source and already carried — with essential
surjectivity excluded by name — by the two declarations tagged 0AN8. -/
theorem exists_etale_bicontinuous_presentation_of_isRepresentableEtale
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hAcount : (nhds (0 : A)).IsCountablyGenerated) (D : QuotientSystem B S hS A)
    {A' : Type u} [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    [IsLinearTopology A' A'] (hA' : TopologicalRing.IsWeaklyAdmissible A')
    (D' : QuotientSystem B S hS A') {V' : FppfSheaf B S hS}
    (eV' : V' ≅ formalSpectrum D') (r : V' ⟶ formalSpectrum D)
    (hV' : IsAffineFormalAlgebraicSpace B S hS V')
    (hr : IsRepresentableEtale B S hS r) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : Algebra A A₁) (_ : Algebra.Etale A A₁)
      (ψ : ContinuousHom D D')
      (e : TopologicalRing.CompletionOver (algebraMap A A₁) ≃+* A'),
      Continuous e ∧ Continuous e.symm ∧
        ψ.toRingHom =
            e.toRingHom.comp
              (TopologicalRing.CompletionOver.canonicalMap (algebraMap A A₁)) ∧
          r = eV'.hom ≫ formalSpectrumMap hA ψ := by
  obtain ⟨A₁, _, _, hA₁et, Dz, c, ε, hc, hεr⟩ :=
    isEssentiallySurjectiveSpf B S hS A hA D
      (hasLargeSite_of_mk_lt_cutoff D (mk_lt_cutoff_of_isCountablyGenerated B S hS D hA hAcount))
      V' r hV' hr
  have hzwa : TopologicalRing.IsWeaklyAdmissible
      (TopologicalRing.CompletionOver (algebraMap A A₁)) :=
    TopologicalRing.completionOver_isWeaklyAdmissible _ hA
  obtain ⟨b, -, φ, hb, -, hφ, -, hφc, hφcs⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hzwa hA' (eV'.symm ≪≫ ε)
  have hbφ : b.toRingHom = φ.toRingHom := RingHom.ext fun x ↦ (congrFun hφ x).symm
  refine ⟨A₁, inferInstance, inferInstance, hA₁et, ContinuousHom.comp hzwa hA b c, φ, hφc,
    hφcs, ?_, ?_⟩
  · rw [ContinuousHom.comp_toRingHom, hbφ, hc]
  · have hcomp := formalSpectrumMap_comp hA hzwa c b (ContinuousHom.comp hzwa hA b c) rfl
    rw [← hcomp, hb]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact hεr.symm

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)

/-- **A representable étale change of charts presented by rings of the class is a completed
étale localization.** Let `t : U ⟶ V` be a chart map presented by a continuous homomorphism
`g : A →+* R` of rings of the class `C`, and let

```
U' --q--> U
|t'       |t
V' --r--> V
```

be a commutative square with `q` and `r` representable étale and `U'`, `V'` affine formal
algebraic spaces. Then `t'` is a completed étale localization of `t` in the sense of
`AlgebraicGeometry.FormalSpace.IsCompletedEtaleLocalizationOfChartMap`.

Given a presentation of `t'` by `g' : A' →+* R'`,
`AlgebraicGeometry.FormalSpace.exists_etale_bicontinuous_presentation_of_isRepresentableEtale`
turns `r` into an étale `A`-algebra `A₁` with `CompletionOver (A → A₁) ≃+* A'` and `q` into an
étale `R`-algebra `R₁` with `CompletionOver (R → R₁) ≃+* R'`. The localization diagram is these
two étale maps with `g` for its vertical map and `g'`, read through the two isomorphisms, for
its completed vertical map; its commutativity is the given square of sheaves, transported along
the four identifications and brought back to rings by faithfulness of `Spf`.

The hypothesis `hCwa` says that every ring of the class is weakly admissible with a countable
fundamental system of open ideals, as in
`FormalSpace.hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap`; it holds
for the classes `WAdmᶜᵒᵘⁿᵗ`, `WAdmᵃᵈⁱᶜ*` and `WAdmᴺᵒᵉᵗʰ`.

NO TAG IS ATTACHED: this is a step inside the proof of Stacks 0ANG, not a numbered statement of
the source, and the two source results it rests on — Stacks 0AN8 and Stacks 0AN0 — are
registered where they are proved. -/
theorem isCompletedEtaleLocalizationOfChartMap_of_presentation
    (hCwa : ∀ (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X], C X →
      TopologicalRing.IsWeaklyAdmissible X ∧ (nhds (0 : X)).IsCountablyGenerated)
    {U V U' V' : FppfSheaf B S hS} {t : U ⟶ V} {t' : U' ⟶ V'} (q : U' ⟶ U) (r : V' ⟶ V)
    (hU' : IsAffineFormalAlgebraicSpace B S hS U')
    (hV' : IsAffineFormalAlgebraicSpace B S hS V')
    (hq : IsRepresentableEtale B S hS q) (hr : IsRepresentableEtale B S hS r)
    (hsquare : q ≫ t = t' ≫ r)
    {A R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (hCA : C A) (hCR : C R) (D : QuotientSystem B S hS A)
    (E : QuotientSystem B S hS R) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
    (g : ContinuousHom D E)
    (hg : t = eU.hom ≫ formalSpectrumMap (hCwa A hCA).1 g ≫ eV.inv) :
    IsCompletedEtaleLocalizationOfChartMap B S hS C t t' := by
  intro A' R' _ _ _ _ _ _ _ _ hCA' hCR' hA' D' E' eU' eV' g' hg' Goal hGoal
  obtain ⟨hA, hAc⟩ := hCwa A hCA
  obtain ⟨hR, hRc⟩ := hCwa R hCR
  obtain ⟨hR', -⟩ := hCwa R' hCR'
  -- the chart `V'` of `V` and the chart `U'` of `U`, presented by completed étale ring maps
  obtain ⟨A₁, _, _, hA₁et, ψA, eA, heAc, heAcs, hψA, hrA⟩ :=
    exists_etale_bicontinuous_presentation_of_isRepresentableEtale B S hS hA hAc D
      hA' D' eV' (r ≫ eV.hom) hV'
      (IsRepresentableEtale.comp B S hS hr (isRepresentableEtale_of_isIso B S hS eV.hom))
  obtain ⟨R₁, _, _, hR₁et, ψR, eR, heRc, heRcs, hψR, hqR⟩ :=
    exists_etale_bicontinuous_presentation_of_isRepresentableEtale B S hS hR hRc E
      hR' E' eU' (q ≫ eU.hom) hU'
      (IsRepresentableEtale.comp B S hS hq (isRepresentableEtale_of_isIso B S hS eU.hom))
  -- the square of formal spectra: the given square, transported along the four identifications
  have hgeo : formalSpectrumMap hR ψR ≫ formalSpectrumMap hA g =
      formalSpectrumMap hA' g' ≫ formalSpectrumMap hA ψA := by
    refine (Iso.cancel_iso_hom_left eU' _ _).mp ?_
    have hleft : eU'.hom ≫ formalSpectrumMap hR ψR ≫ formalSpectrumMap hA g =
        q ≫ eU.hom ≫ formalSpectrumMap hA g := by
      rw [← Category.assoc, ← hqR, Category.assoc]
    have hmid : eU.hom ≫ formalSpectrumMap hA g = t ≫ eV.hom := by
      rw [hg]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hright : eU'.hom ≫ formalSpectrumMap hA' g' ≫ formalSpectrumMap hA ψA =
        t' ≫ eV'.hom ≫ formalSpectrumMap hA ψA := by
      rw [hg']
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [hleft, hright, hmid, ← hrA, ← Category.assoc, ← Category.assoc, hsquare]
  -- faithfulness of `Spf` turns that square into the commutativity of the ring square
  have hkey : ψR.toRingHom.comp g.toRingHom = g'.toRingHom.comp ψA.toRingHom := by
    have hceq : ContinuousHom.comp hR hA ψR g = ContinuousHom.comp hA' hA g' ψA := by
      refine (existsUnique_continuousHom_formalSpectrumMap_eq hA hR'
        (formalSpectrumMap hR ψR ≫ formalSpectrumMap hA g)).unique
        (formalSpectrumMap_comp hA hR g ψR _ rfl).symm ?_
      rw [← formalSpectrumMap_comp hA hA' ψA g' _ rfl, hgeo]
    simpa only [ContinuousHom.comp_toRingHom] using congrArg ContinuousHom.toRingHom hceq
  refine hGoal A R A₁ R₁ hCA hCR hA D E eU eV g hg
    { toA' := algebraMap R R₁
      toB' := algebraMap A A₁
      map := g.toRingHom
      completedMap := eR.symm.toRingHom.comp (g'.toRingHom.comp eA.toRingHom)
      weaklyAdmissibleA := hR
      weaklyAdmissibleB := hA
      countableA := hRc
      countableB := hAc
      etaleA := RingHom.etale_algebraMap.mpr hR₁et
      etaleB := RingHom.etale_algebraMap.mpr hA₁et
      continuousMap := g.continuous
      continuousCompletedMap := heRcs.comp (g'.continuous.comp heAc)
      commutes := ?_ } rfl eA eR heAc heAcs heRc heRcs ?_
  · refine RingHom.ext fun x ↦ ?_
    have h1 := RingHom.congr_fun hψR (g.toRingHom x)
    have h2 := RingHom.congr_fun hψA x
    have h3 := RingHom.congr_fun hkey x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe] at h1 h2 h3 ⊢
    rw [← h2, ← h3, h1, RingEquiv.symm_apply_apply]
  · refine RingHom.ext fun x ↦ ?_
    simp

/-- **A representable étale change of countably indexed charts is a completed étale
localization.** For the class `WAdmᶜᵒᵘⁿᵗ` of countably indexed weakly admissible rings the
presentation hypothesis of
`AlgebraicGeometry.FormalSpace.isCompletedEtaleLocalizationOfChartMap_of_presentation` is not
needed as a hypothesis: it follows from the geometric hypothesis of the source, that the two
ends of the lower chart map are **countably indexed** affine formal algebraic spaces.

The implication (1) ⟹ (2) of **Stacks 0AN1**,
`AlgebraicGeometry.FormalSpace.hasCountableWeakPresentation_of_isCountablyIndexedAffine`,
presents `U` and `V` by weakly admissible rings with countably generated zero neighbourhoods —
which is membership in the class, by definition of
`TopologicalRing.IsCountablyWeaklyAdmissible` — and **Stacks 0AN0** then presents `t` itself by
a continuous homomorphism between them.

This is the shape in which the proof of Stacks 0ANG uses the recognition of Stacks 0AN8: that
proof is run for a morphism of locally countably indexed formal algebraic spaces, whose charts
are countably indexed. NO TAG IS ATTACHED, for the reason given on
`AlgebraicGeometry.FormalSpace.isCompletedEtaleLocalizationOfChartMap_of_presentation`. -/
theorem isCompletedEtaleLocalizationOfChartMap_of_isCountablyIndexedAffine
    {U V U' V' : FppfSheaf B S hS} {t : U ⟶ V} {t' : U' ⟶ V'} (q : U' ⟶ U) (r : V' ⟶ V)
    (hU : IsCountablyIndexedAffine B S hS U) (hV : IsCountablyIndexedAffine B S hS V)
    (hU' : IsAffineFormalAlgebraicSpace B S hS U')
    (hV' : IsAffineFormalAlgebraicSpace B S hS V')
    (hq : IsRepresentableEtale B S hS q) (hr : IsRepresentableEtale B S hS r)
    (hsquare : q ≫ t = t' ≫ r) :
    IsCompletedEtaleLocalizationOfChartMap B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible t t' := by
  obtain ⟨PU, hUwa, hUc⟩ := hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS U hU
  obtain ⟨PV, hVwa, hVc⟩ := hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS V hV
  obtain ⟨eU⟩ := PU.iso
  obtain ⟨eV⟩ := PV.iso
  obtain ⟨g, hgeq, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hVwa hUwa (eU.inv ≫ t ≫ eV.hom)
  refine isCompletedEtaleLocalizationOfChartMap_of_presentation B S hS _
    (fun _ _ _ _ _ hX ↦ hX) q r hU' hV' hq hr hsquare ⟨hVwa, hVc⟩ ⟨hUwa, hUc⟩ PV.system
    PU.system eU eV g ?_
  rw [hgeq]
  simp

/-- **The refinement of a covering of the source against an affine étale diagram, with its
target-side squares presented.** This is
`AlgebraicGeometry.FormalSpace.exists_finite_affineEtaleRefinement_of_sourceCover` together with
the first presentation clause of
`AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'`: when the members `U i` and
`V i` of the covering being refined are countably indexed, every square `W s ⟶ Z s` over the
chart map `U (k s) ⟶ V (k s)` is a completed étale localization of it at the class
`WAdmᶜᵒᵘⁿᵗ`, by
`AlgebraicGeometry.FormalSpace.isCompletedEtaleLocalizationOfChartMap_of_isCountablyIndexedAffine`.

Countable indexedness of the members is what the standing hypothesis of **Stacks 0ANG** — that
the two ends of `f` are locally countably indexed — provides, through the implication (2) ⟹ (1)
of **Stacks 0AKX**; that implication is not in the library, so countable indexedness is asked of
the members directly, exactly as
`isCompletedEtaleLocalizationOfChartMap_of_isCountablyIndexedAffine` asks it of the two ends of a
single chart map.

What separates this from `HasEtaleRefinementOfSourceCover'` at `C = WAdmᶜᵒᵘⁿᵗ` is the second
presentation clause, `AlgebraicGeometry.FormalSpace.IsCompletedEtaleFiniteCoverOfChartMap`,
which needs finite-product infrastructure the library does not carry.

NO TAG IS ATTACHED: like the refinement it extends, this is a step inside the proof of
Stacks 0ANG rather than a numbered statement of the source. -/
theorem exists_finite_affineEtaleRefinement_completedEtaleLocalization_of_sourceCover
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    {I : Type (u + 1)} (U V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X) (v : ∀ i, V i ⟶ Y)
    (t : ∀ i, U i ⟶ V i) (hUcover : IsAffineEtaleCover B S hS U u)
    (hVaffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (V i))
    (hVetale : ∀ i, IsRepresentableEtale B S hS (v i))
    (hVsquare : ∀ i, u i ≫ f = t i ≫ v i)
    (hUcount : ∀ i, IsCountablyIndexed B S hS (U i))
    (hVcount : ∀ i, IsCountablyIndexed B S hS (V i))
    {U₀ V₀ : FppfSheaf B S hS} (a : U₀ ⟶ X) (b : V₀ ⟶ Y) (τ : U₀ ⟶ V₀)
    (hU₀ : IsAffineFormalAlgebraicSpace B S hS U₀)
    (hV₀ : IsAffineFormalAlgebraicSpace B S hS V₀)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b)
    (hsquare : a ≫ f = τ ≫ b) :
    ∃ (σ : Type (u + 1)) (_ : Finite σ) (k : σ → I) (W Z : σ → FppfSheaf B S hS)
      (p : ∀ s, W s ⟶ U₀) (q : ∀ s, W s ⟶ U (k s)) (m : ∀ s, W s ⟶ Z s)
      (r : ∀ s, Z s ⟶ V (k s)) (c : ∀ s, Z s ⟶ V₀),
      IsAffineEtaleCover B S hS W p ∧ (∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s)) ∧
        (∀ s, IsRepresentableEtale B S hS (q s)) ∧
        (∀ s, IsRepresentableEtale B S hS (r s)) ∧
        (∀ s, IsRepresentableEtale B S hS (c s)) ∧
        (∀ s, q s ≫ t (k s) = m s ≫ r s) ∧ (∀ s, p s ≫ τ = m s ≫ c s) ∧
        ∀ s, IsCompletedEtaleLocalizationOfChartMap B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible (t (k s)) (m s) := by
  obtain ⟨σ, hσ, k, W, Z, p, q, m, r, c, hWcover, hZaffine, hq, hr, hc, hsq₁, hsq₂⟩ :=
    exists_finite_affineEtaleRefinement_of_sourceCover B S hS f U V u v t hUcover hVaffine
      hVetale hVsquare a b τ hU₀ hV₀ ha hb hsquare
  exact ⟨σ, hσ, k, W, Z, p, q, m, r, c, hWcover, hZaffine, hq, hr, hc, hsq₁, hsq₂,
    fun s ↦ isCompletedEtaleLocalizationOfChartMap_of_isCountablyIndexedAffine B S hS (q s)
      (r s) ⟨hUcover.1 (k s), hUcount (k s)⟩ ⟨hVaffine (k s), hVcount (k s)⟩ (hWcover.1 s)
      (hZaffine s) (hq s) (hr s) (hsq₁ s)⟩

end AlgebraicGeometry.FormalSpace

end
