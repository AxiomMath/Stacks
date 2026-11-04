module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartLocalizationDiagram
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass

/-!
# Descent of a chart property along a single surjective affine étale square

Let `S` be a scheme contained in a big fppf site `B`. Axioms (2) and (3) of Situation
**Stacks 0CBA** — the fields `faithfullyFlatDescent` and `finiteProduct` of
`TopologicalRing.PropertyIsLocal` — are read on affine formal algebraic spaces by
`AlgebraicGeometry.FormalSpace.ChartPropertyDescendsAlongFiniteAffineEtaleCover`, which descends
`P` along a *finite* affine étale covering of the source. This file proves what axiom (2) alone
gives: the descent of `P` along a *single* surjective representable étale change of source,
with no assembly of a family of charts into one étale algebra — which is where axiom (3), and
Stacks 0AN9 at a finite product, would be needed.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_of_surjectiveChartSquare`: if
  `P` is a local property of morphisms of rings of the class `C` and `t : U ⟶ V` is a morphism
  of affine formal algebraic spaces which fits in a commuting square over a *surjective*
  representable étale change of source and a representable étale change of target on which `P`
  holds, then `P` holds on `t`.

## The route

The square is turned into a `TopologicalRing.LocalizationDiagram` by
`AlgebraicGeometry.FormalSpace.exists_localizationDiagram_of_chartSquare`, whose lower map
presents `t` and whose upper map presents the given map of charts, so that `P` holds on the
upper map by hypothesis. Axiom (2) of Situation 0CBA then carries `P` down to `t`, provided the
étale ring map `R → R'` forming the source edge of the diagram is faithfully flat. That is
exactly where **Stacks 0AN9** enters: the morphism `Spf R'^∧ ⟶ Spf R` which that edge presents
is the given change of source, which is surjective, and
`AlgebraicGeometry.FormalSpace.etaleFormalSpectrumMap_surjective_tfae` turns surjectivity of
such a morphism into faithful flatness of the étale ring map presenting it.

## Why only one member

For a covering with several members the source's proof (the proof of **Stacks 0ANG**) applies
the axiom (2) once per member, to the square whose source edge is an *identity*, and then axiom (3)
to assemble the resulting family `A → R_s^∧` into the single map `A → ∏_s R_s^∧` before
applying axiom (2) a last time. Both steps need ring-theoretic identifications that this
library does not carry: `TopologicalRing.CompletionOver` of an identity ring map identified with
the ring itself, and `TopologicalRing.CompletionOver` of a finite product of étale algebras
identified with the product of their completions, together with a `QuotientSystem` for that
product ring presenting the coproduct of the charts. With a single member none of them is
needed: the given square is already a localization diagram, and its source edge is already the
étale algebra Stacks 0AN9 asks for.

The inputs beyond `hP` are those of
`AlgebraicGeometry.FormalSpace.chartPropertyAscendsAlongAffineEtale_of_propertyIsLocal`, and
none of them is a statement about formal algebraic spaces; see that declaration and the module
documentation of `StacksFrontier/AlgebraicGeometry/FormalSpace/ChartLocalizationDiagram.lean` for
each.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- **Axiom (2) of Situation 0CBA, read on affine formal algebraic charts for a single
surjective chart change.** Let `P` be a local property of morphisms of rings of the class `C`
and let

    W ⟶ Z
    │     │
    U ⟶ V

be a commuting square of affine formal algebraic spaces whose vertical maps are representable
étale and whose left vertical map `W ⟶ U` is surjective. If `P` holds on the upper map `W ⟶ Z`
then `P` holds on the lower map `t : U ⟶ V`.

This is the content of axiom (2) for the data of one member of a covering as in
`AlgebraicGeometry.FormalSpace.ChartPropertyDescendsAlongFiniteAffineEtaleCover`, the hypothesis
`hdesc` of
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover`: with a
one-element index type the covering hypothesis there is local surjectivity of the single member,
which is `hpsurj` below, although the comparison of `Sigma.desc` over a one-element type with
that member is not formalized. What the general case needs beyond this lemma is recorded in
this file's module documentation.

The square is turned into a `TopologicalRing.LocalizationDiagram` by
`AlgebraicGeometry.FormalSpace.exists_localizationDiagram_of_chartSquare`; the étale ring map
forming its source edge is faithfully flat by **Stacks 0AN9**,
`AlgebraicGeometry.FormalSpace.etaleFormalSpectrumMap_surjective_tfae`, because the morphism of
formal spectra it presents is the surjective map `W ⟶ U`; and the field
`TopologicalRing.PropertyIsLocal.faithfullyFlatDescent` carries `P` from the upper map of the
diagram to its lower map, which presents `t`. The property is then transported to an arbitrary
presentation of `t` as in
`AlgebraicGeometry.FormalSpace.chartPropertyAscendsAlongAffineEtale_of_propertyIsLocal`, whose
inputs beyond `hP` these are, the presentations of the two lower charts by rings of the class
being `hpU` and `hpV`. -/
theorem hasPropertyOnAffineChartMap_of_surjectiveChartSquare_of_presentation
    (h0AN8 : IsEssentiallySurjectiveSpf B S hS)
    (hCw : ClassIsWeaklyAdmissible C)
    (hCcompl : ClassIsStableUnderEtaleCompletion C)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} C P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    (hP : TopologicalRing.PropertyIsLocal P C)
    {U V W Z : FppfSheaf B S hS} (t : U ⟶ V) (p : W ⟶ U) (m : W ⟶ Z) (r : Z ⟶ V)
    (hpU : HasPresentationOfClass B S hS C U) (hpV : HasPresentationOfClass B S hS C V)
    (hW : IsAffineFormalAlgebraicSpace B S hS W)
    (hZ : IsAffineFormalAlgebraicSpace B S hS Z)
    (hp : IsRepresentableEtale B S hS p) (hr : IsRepresentableEtale B S hS r)
    (hpsurj : Sheaf.IsLocallySurjective p) (hsq : p ≫ t = m ≫ r)
    (hm : HasPropertyOnAffineChartMap B S hS C P m) :
    HasPropertyOnAffineChartMap B S hS C P t := by
  obtain ⟨A, _, _, _, _, D, hCA, hAw, hAc, hAcard, ⟨eV⟩⟩ := hpV
  obtain ⟨R, _, _, _, _, E, hCR, hRw, hRc, hRcard, ⟨eU⟩⟩ := hpU
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hAw hRw
    (eU.inv ≫ t ≫ eV.hom)
  have hgt : t = eU.hom ≫ formalSpectrumMap hAw g ≫ eV.inv := by rw [hg]; simp
  have hpe : IsRepresentableEtale B S hS (p ≫ eU.hom) :=
    IsRepresentableEtale.comp B S hS hp (isRepresentableEtale_iso_hom B S hS eU)
  have hre : IsRepresentableEtale B S hS (r ≫ eV.hom) :=
    IsRepresentableEtale.comp B S hS hr (isRepresentableEtale_iso_hom B S hS eV)
  have hsq' : (p ≫ eU.hom) ≫ formalSpectrumMap hAw g = m ≫ r ≫ eV.hom := by
    rw [hg, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hsq, Category.assoc]
  obtain ⟨R', A', _, _, Dg, E', D', g', cq, eU', eV', hmap, hcm, hcq, hεq, hpres'⟩ :=
    exists_localizationDiagram_of_chartSquare B S hS h0AN8 hAw hRw hAc hRc hAcard hRcard g
      m (p ≫ eU.hom) (r ≫ eV.hom) hW hZ hpe hre hsq'
  have hCAc : C (TopologicalRing.CompletionOver Dg.toB') :=
    hCcompl Dg.toB' hCA hAw Dg.etaleB
  have hCRc : C (TopologicalRing.CompletionOver Dg.toA') :=
    hCcompl Dg.toA' hCR hRw Dg.etaleA
  have hAc' := TopologicalRing.completionOver_isWeaklyAdmissible Dg.toB' hAw
  -- `P` on the upper map of the diagram, which presents the given map of charts
  have hPcm : P Dg.completedMap := by
    rw [hcm]
    exact hm (TopologicalRing.CompletionOver Dg.toB')
      (TopologicalRing.CompletionOver Dg.toA') hCAc hCRc hAc' D' E' eU' eV' g' hpres'
  -- the source edge of the diagram is faithfully flat, by Stacks 0AN9
  have hff : Dg.toA'.FaithfullyFlat := by
    have hfac : eU'.inv ≫ p ≫ eU.hom = formalSpectrumMap hRw cq := by
      rw [← hεq, Iso.inv_hom_id_assoc]
    have hep : Epi p := (Sheaf.isLocallySurjective_iff_epi p).mp hpsurj
    have hls : Sheaf.IsLocallySurjective (formalSpectrumMap hRw cq) := by
      rw [Sheaf.isLocallySurjective_iff_epi, ← hfac]
      infer_instance
    have hiff : IsSurjective B S hS (formalSpectrumMap hRw cq) ↔ Dg.toA'.FaithfullyFlat :=
      (etaleFormalSpectrumMap_surjective_tfae B S hS Dg.toA' Dg.etaleA hRw E E' cq hcq).out 1 2
    exact hiff.mp (isSurjective_of_isLocallySurjective B S hS hls)
  have hPg : P g.toRingHom := by
    rw [← hmap]
    exact hP.faithfullyFlatDescent Dg hCR hCA hCRc hCAc hff hPcm
  -- transport `P` to an arbitrary presentation of `t`
  intro A₁ R₁ _ _ _ _ _ _ _ _ hCA₁ hCR₁ hA₁ D₁ E₁ eU₁ eV₁ g₁ hg₁
  have hR₁ : TopologicalRing.IsWeaklyAdmissible R₁ := hCw R₁ hCR₁
  obtain ⟨gv, -, φ, hgv, -, hφ, -, hφc, hφc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hA₁ hAw (eV.symm ≪≫ eV₁)
  obtain ⟨gu, -, χ, hgu, -, hχ, -, hχc, hχc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hRw hR₁ (eU₁.symm ≪≫ eU)
  have hφr : φ.toRingHom = gv.toRingHom := RingHom.ext fun x ↦ congrFun hφ x
  have hχr : χ.toRingHom = gu.toRingHom := RingHom.ext fun x ↦ congrFun hχ x
  have hg₁eq : g₁ = ContinuousHom.comp hRw hA₁ gu (ContinuousHom.comp hAw hA₁ g gv) := by
    refine (existsUnique_continuousHom_formalSpectrumMap_eq hA₁ hR₁
      (eU₁.inv ≫ t ≫ eV₁.hom)).unique (by rw [hg₁]; simp) ?_
    rw [← formalSpectrumMap_comp_eq hRw hA₁ gu (ContinuousHom.comp hAw hA₁ g gv),
      ← formalSpectrumMap_comp_eq hAw hA₁ g gv, hgu, hgv, hgt]
    simp
  have hfin : g₁.toRingHom = χ.toRingHom.comp (g.toRingHom.comp φ.toRingHom) := by
    rw [hg₁eq, ContinuousHom.comp_toRingHom, ContinuousHom.comp_toRingHom, hφr, hχr]
  rw [hfin]
  exact htgt hCA₁ hCR hCR₁ _ χ (g.continuous.comp hφc) hχc hχc'
    (hsrc hCA hCA₁ hCR g.toRingHom φ g.continuous hφc hφc' hPg)

/-- **Axiom (2) of Situation 0CBA, read on affine formal algebraic charts for a single
surjective chart change**, with the presentations of the two lower charts supplied by `hpres`:
`hasPropertyOnAffineChartMap_of_surjectiveChartSquare_of_presentation` asked of every chart. -/
theorem hasPropertyOnAffineChartMap_of_surjectiveChartSquare
    (h0AN8 : IsEssentiallySurjectiveSpf B S hS)
    (hpres : ChartsHavePresentationOfClass B S hS C)
    (hCw : ClassIsWeaklyAdmissible C)
    (hCcompl : ClassIsStableUnderEtaleCompletion C)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} C P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    (hP : TopologicalRing.PropertyIsLocal P C)
    {U V W Z : FppfSheaf B S hS} (t : U ⟶ V) (p : W ⟶ U) (m : W ⟶ Z) (r : Z ⟶ V)
    (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hW : IsAffineFormalAlgebraicSpace B S hS W)
    (hZ : IsAffineFormalAlgebraicSpace B S hS Z)
    (hp : IsRepresentableEtale B S hS p) (hr : IsRepresentableEtale B S hS r)
    (hpsurj : Sheaf.IsLocallySurjective p) (hsq : p ≫ t = m ≫ r)
    (hm : HasPropertyOnAffineChartMap B S hS C P m) :
    HasPropertyOnAffineChartMap B S hS C P t :=
  hasPropertyOnAffineChartMap_of_surjectiveChartSquare_of_presentation B S hS C P h0AN8 hCw
    hCcompl hsrc htgt hP t p m r (hpres U hU) (hpres V hV) hW hZ hp hr hpsurj hsq hm

end AlgebraicGeometry.FormalSpace

end
