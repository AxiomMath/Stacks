module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful

/-!
# A localization diagram out of a commuting square of affine formal charts

Let `S` be a scheme contained in a big fppf site `B`. Situation **Stacks 0CBA** phrases the
three locality axioms of a property `P` of continuous homomorphisms — Stacks 0AND, Stacks 0ANE
and Stacks 0ANF, the three fields of `TopologicalRing.PropertyIsLocal` — in terms of a
*localization diagram*: a commuting square of continuous ring maps whose horizontal arrows are
étale and whose vertical arrows are the given map and the map induced on the completions. That
datum is `TopologicalRing.LocalizationDiagram` of
`StacksFrontier/Topology/Algebra/AdicTopology/LocalProperties.lean`.

The three axioms say nothing about a *geometric* square — a commuting square of affine formal
algebraic spaces over `S` whose vertical maps are representable and étale, which is the shape
in which condition (1) of **Stacks 0ANG** presents its data. The passage from the second to the
first is what this file supplies.

## Main definitions

* `AlgebraicGeometry.FormalSpace.ChartsHavePresentationOfClass`,
  `AlgebraicGeometry.FormalSpace.ClassIsWeaklyAdmissible`,
  `AlgebraicGeometry.FormalSpace.ClassIsStableUnderEtaleCompletion` and
  `AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderSourceIso`: the four inputs, besides
  Stacks 0AN8, that the chart reading of axiom (1) of Situation 0CBA needs of the class of
  rings and of the property.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_localizationDiagram_of_chartSquare`: a commuting square
  whose target edge `Spf R ⟶ Spf A` is presented by a continuous homomorphism `g : A → R` and
  whose two vertical maps are representable étale maps from affine formal algebraic spaces is
  the formal spectrum of a `TopologicalRing.LocalizationDiagram` whose lower map is `g`, and
  whose upper map presents the remaining edge of the square.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_iso_hom`: an isomorphism of fppf sheaves
  is representable étale.
* `AlgebraicGeometry.FormalSpace.chartPropertyAscendsAlongAffineEtale_of_propertyIsLocal`:
  the axiom (1) of a local property of Situation 0CBA, read on affine formal algebraic charts —
  the hypothesis `hasc` of
  `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover`,
  which is the implication (3) ⟹ (1) of **Stacks 0ANG** — follows from
  `TopologicalRing.PropertyIsLocal` together with the inputs above.

## The one input of the diagram

The essential-surjectivity clause of **Stacks 0AN8**, which this library carries only in the
hypothesis-shaped form `AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf`: a chart of
`Spf R` representable and étale over it is `Spf` of the completion of an étale `R`-algebra.
Applied to the two vertical maps of the square, it produces the two étale ring maps `R → R'`
and `A → A'` which are the horizontal edges of the localization diagram, and the two
identifications of the upper corners with the formal spectra of the completions.

Nothing else is needed. The upper map of the diagram, and the commutativity of its square of
ring maps, are both produced by **Stacks 0AN0** — full faithfulness of `Spf`, in the form
`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`: the upper map
is the unique continuous homomorphism whose formal spectrum is the upper edge of the geometric
square, read through the two identifications, and the square of ring maps commutes because both
of its composites are continuous homomorphisms whose formal spectra agree, namely with the
diagonal of the geometric square.

The statement takes the lower corners of the square *already presented*, by `D` and `E`, and
its lower edge already in the form `Spf g`. That is the shape in which Stacks 0AN8 can be
applied at all — its base has to be a formal spectrum — and it is also the shape in which the
charts of condition (1) of Stacks 0ANG arrive, since
`AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap` quantifies over exactly such
presentations.

## What the chart reading of axiom (1) needs beyond the diagram

Four things, each named above and none of them a statement about formal algebraic spaces.

The charts of a square of condition (1) are only *affine formal algebraic spaces*, whereas the
localization diagram needs them presented by rings of the class `C`, weakly admissible,
countably indexed and below the cardinal cutoff of the site. That is Stacks 0AKX, carried as
`ChartsHavePresentationOfClass`. The class has to consist of weakly admissible rings and to be
stable under completion along an étale map, neither of which an arbitrary predicate `C` is;
those are `ClassIsWeaklyAdmissible` and `ClassIsStableUnderEtaleCompletion`. And the property
has to be invariant under isomorphism of sources and of targets, because the two presentations
of the upper edge of the square — the one the diagram produces, out of
`TopologicalRing.CompletionOver` types, and the arbitrary one that
`AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap` quantifies over — agree only up to
isomorphism of the presenting rings. The Stacks Project obtains that invariance from axiom (1)
itself, an isomorphism being étale and a complete ring being its own completion; here the
completion of a complete ring is only *isomorphic* to it, so the derivation is circular. See
the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalSpace/Restricted/FlatTargetIsoInvariance.lean`, where the
same obstruction is met and the invariance is proved by hand for two specific properties.

Axioms (2) and (3) of Situation 0CBA are *not* read on charts here: their chart reading,
`AlgebraicGeometry.FormalSpace.ChartPropertyDescendsAlongFiniteAffineEtaleCover`, descends `P`
along a finite affine étale covering, so it needs the étale algebra of the covering assembled
as a finite product — Stacks 0AN9 — which this library does not carry.

## References

* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
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

/-- The geometric half of the construction: **Stacks 0AN8** on the two vertical maps of the
square writes its upper corners as the formal spectra of the completions of an étale
`R`-algebra and an étale `A`-algebra, and **Stacks 0AN0** then presents the upper edge of the
square by a continuous homomorphism between those completions and forces the square of ring
maps to commute. -/
private theorem exists_etaleCompletionSquare_of_chartSquare
    (h0AN8 : IsEssentiallySurjectiveSpf B S hS)
    {A R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hR : TopologicalRing.IsWeaklyAdmissible R)
    (hAcard : Cardinal.mk A < B.cutoff) (hRcard : Cardinal.mk R < B.cutoff)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS R} (g : ContinuousHom D E)
    {U' V' : FppfSheaf B S hS} (t' : U' ⟶ V')
    (q : U' ⟶ formalSpectrum E) (r : V' ⟶ formalSpectrum D)
    (hU' : IsAffineFormalAlgebraicSpace B S hS U')
    (hV' : IsAffineFormalAlgebraicSpace B S hS V')
    (hq : IsRepresentableEtale B S hS q) (hr : IsRepresentableEtale B S hS r)
    (hsq : q ≫ formalSpectrumMap hA g = t' ≫ r) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (E' : QuotientSystem B S hS (TopologicalRing.CompletionOver (algebraMap R R')))
      (D' : QuotientSystem B S hS (TopologicalRing.CompletionOver (algebraMap A A')))
      (g' : ContinuousHom D' E') (cq : ContinuousHom E E') (eU' : U' ≅ formalSpectrum E')
      (eV' : V' ≅ formalSpectrum D'),
      cq.toRingHom = TopologicalRing.CompletionOver.canonicalMap (algebraMap R R') ∧
        eU'.hom ≫ formalSpectrumMap hR cq = q ∧
        (TopologicalRing.CompletionOver.canonicalMap (algebraMap R R')).comp g.toRingHom =
          g'.toRingHom.comp
            (TopologicalRing.CompletionOver.canonicalMap (algebraMap A A')) ∧
        t' = eU'.hom ≫ formalSpectrumMap
          (TopologicalRing.completionOver_isWeaklyAdmissible (algebraMap A A') hA) g'
            ≫ eV'.inv := by
  classical
  obtain ⟨R', _, _, _, E', cq, eU', hcq, hεq⟩ := h0AN8 R hR hRcard E U' q hU' hq
  obtain ⟨A', _, _, _, D', cr, eV', hcr, hεr⟩ := h0AN8 A hA hAcard D V' r hV' hr
  have hE' := TopologicalRing.completionOver_isWeaklyAdmissible (algebraMap R R') hR
  have hD' := TopologicalRing.completionOver_isWeaklyAdmissible (algebraMap A A') hA
  obtain ⟨g', hg', -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hD' hE'
    (eU'.inv ≫ t' ≫ eV'.hom)
  have hcomp : ContinuousHom.comp hR hA cq g = ContinuousHom.comp hD' hA g' cr := by
    refine (existsUnique_continuousHom_formalSpectrumMap_eq hA hE'
      (formalSpectrumMap hR cq ≫ formalSpectrumMap hA g)).unique
      (formalSpectrumMap_comp_eq hR hA cq g).symm ?_
    rw [← formalSpectrumMap_comp_eq hD' hA g' cr, hg', Category.assoc, Category.assoc, hεr,
      ← hsq, ← hεq, Category.assoc, Iso.inv_hom_id_assoc]
  refine ⟨R', inferInstance, inferInstance, inferInstance, A', inferInstance, inferInstance,
    inferInstance, E', D', g', cq, eU', eV', hcq, hεq, ?_, ?_⟩
  · rw [← hcq, ← hcr, ← ContinuousHom.comp_toRingHom hR hA cq g,
      ← ContinuousHom.comp_toRingHom hD' hA g' cr, hcomp]
  · rw [hg']
    simp

/-- **A localization diagram of Situation 0CBA out of a commuting square of affine formal
charts.** Let `g : A → R` be a continuous homomorphism of weakly admissible topological rings
over `S`, both countably indexed and below the cardinal cutoff of the site, presented by the
quotient systems `D` and `E`. Let

    U' ⟶ V'
    │      │
    Spf R ⟶ Spf A

be a commuting square whose upper corners are affine formal algebraic spaces, whose vertical
maps `q` and `r` are representable and étale, and whose lower edge is `Spf g`.

Then there are an étale `R`-algebra `R'`, an étale `A`-algebra `A'` and a
`TopologicalRing.LocalizationDiagram R A R' A'` whose lower map is `g` and whose upper map
`A'^∧ → R'^∧` presents the upper edge `t'` of the square, under identifications of `U'` with
`Spf R'^∧` and of `V'` with `Spf A'^∧`.

The canonical map `R → R'^∧` of the source edge is returned as well, as a continuous
homomorphism `cq` presenting the vertical map `q` of the square. That is what makes
**Stacks 0AN9** applicable to the source edge, as in
`AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_of_surjectiveChartSquare`: it reads
surjectivity of `q` as faithful flatness of the étale ring map `R → R'`.

The hypothesis `h0AN8` is the essential-surjectivity clause of Stacks 0AN8; see
`AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf`. Everything else is Stacks 0AN0. -/
theorem exists_localizationDiagram_of_chartSquare
    (h0AN8 : IsEssentiallySurjectiveSpf B S hS)
    {A R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hR : TopologicalRing.IsWeaklyAdmissible R)
    (hAc : (nhds (0 : A)).IsCountablyGenerated) (hRc : (nhds (0 : R)).IsCountablyGenerated)
    (hAcard : Cardinal.mk A < B.cutoff) (hRcard : Cardinal.mk R < B.cutoff)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS R} (g : ContinuousHom D E)
    {U' V' : FppfSheaf B S hS} (t' : U' ⟶ V')
    (q : U' ⟶ formalSpectrum E) (r : V' ⟶ formalSpectrum D)
    (hU' : IsAffineFormalAlgebraicSpace B S hS U')
    (hV' : IsAffineFormalAlgebraicSpace B S hS V')
    (hq : IsRepresentableEtale B S hS q) (hr : IsRepresentableEtale B S hS r)
    (hsq : q ≫ formalSpectrumMap hA g = t' ≫ r) :
    ∃ (R' A' : Type u) (_ : CommRing R') (_ : CommRing A')
      (Dg : TopologicalRing.LocalizationDiagram R A R' A')
      (E' : QuotientSystem B S hS (TopologicalRing.CompletionOver Dg.toA'))
      (D' : QuotientSystem B S hS (TopologicalRing.CompletionOver Dg.toB'))
      (g' : ContinuousHom D' E') (cq : ContinuousHom E E') (eU' : U' ≅ formalSpectrum E')
      (eV' : V' ≅ formalSpectrum D'),
      Dg.map = g.toRingHom ∧ Dg.completedMap = g'.toRingHom ∧
        cq.toRingHom = TopologicalRing.CompletionOver.canonicalMap Dg.toA' ∧
        eU'.hom ≫ formalSpectrumMap hR cq = q ∧
        t' = eU'.hom ≫ formalSpectrumMap
          (TopologicalRing.completionOver_isWeaklyAdmissible Dg.toB' hA) g' ≫ eV'.inv := by
  obtain ⟨R', _, _, _, A', _, _, _, E', D', g', cq, eU', eV', hcq, hεq, hring, hpres⟩ :=
    exists_etaleCompletionSquare_of_chartSquare B S hS h0AN8 hA hR hAcard hRcard g t' q r
      hU' hV' hq hr hsq
  exact ⟨R', A', inferInstance, inferInstance,
    { toA' := algebraMap R R'
      toB' := algebraMap A A'
      map := g.toRingHom
      completedMap := g'.toRingHom
      weaklyAdmissibleA := hR
      weaklyAdmissibleB := hA
      countableA := hRc
      countableB := hAc
      etaleA := RingHom.etale_algebraMap.2 inferInstance
      etaleB := RingHom.etale_algebraMap.2 inferInstance
      continuousMap := g.continuous
      continuousCompletedMap := g'.continuous
      commutes := hring },
    E', D', g', cq, eU', eV', rfl, rfl, hcq, hεq, hpres⟩

/-- An isomorphism of fppf sheaves is representable étale: it is the base change of the
identity of its target along itself, a square which is cartesian because its two horizontal
maps are isomorphisms. -/
theorem isRepresentableEtale_iso_hom {X Y : FppfSheaf B S hS} (e : X ≅ Y) :
    IsRepresentableEtale B S hS e.hom := by
  have hsq : IsPullback e.hom e.hom (𝟙 Y) (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact isRepresentableEtale_of_isPullback B S hS hsq (isRepresentableEtale_id B S hS Y)

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The fppf sheaf `W` is the formal spectrum of a ring of the class `C` which is weakly
admissible, has a countable fundamental system of neighbourhoods of zero and lies below the
cardinal cutoff of the site. These are the conditions under which a chart can serve as a corner
of a `TopologicalRing.LocalizationDiagram` built by
`AlgebraicGeometry.FormalSpace.exists_localizationDiagram_of_chartSquare`. -/
abbrev HasPresentationOfClass (W : FppfSheaf B S hS) : Prop :=
  ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
    (_ : IsLinearTopology R R) (Q : QuotientSystem B S hS R),
    C R ∧ TopologicalRing.IsWeaklyAdmissible R ∧
      (nhds (0 : R)).IsCountablyGenerated ∧ Cardinal.mk R < B.cutoff ∧
        Nonempty (W ≅ formalSpectrum Q)

/-- Every affine formal algebraic space over `S` is the formal spectrum of a ring of the class
`C`, weakly admissible, countably indexed and below the cardinal cutoff of the site.

For the class of countably indexed weakly admissible rings this is the implication (2) ⟹ (1)
of **Stacks 0AKX** together with Stacks 0AIK; the library's
`AlgebraicGeometry.FormalSpace.exists_quotientSystem_of_isCountablyIndexed` supplies all of it
except the cardinal bound once the chart is known to be countably indexed, which is what Stacks
0AKX provides and this library does not carry. -/
abbrev ChartsHavePresentationOfClass : Prop :=
  ∀ W : FppfSheaf B S hS, IsAffineFormalAlgebraicSpace B S hS W → HasPresentationOfClass B S hS C W

/-- Every ring of the class `C` is weakly admissible. This holds for each of the four classes
at which the library instantiates Situation 0CBA — countably indexed weakly admissible rings,
adic\* rings, adic Noetherian rings and Noetherian adic rings — but `C` itself is an arbitrary
predicate, so the four implications are not available from `C` alone. -/
abbrev ClassIsWeaklyAdmissible : Prop :=
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R

/-- The class `C` is stable under completion along an étale ring map: the completion of an
étale algebra over a ring of `C` along the weak ideals of definition of that ring is again of
`C`. This is what makes the two upper corners of a localization diagram built from a chart
square testable by `P`, which the axioms of `TopologicalRing.PropertyIsLocal` require of
them. -/
abbrev ClassIsStableUnderEtaleCompletion : Prop :=
  ∀ {R R' : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R] [CommRing R'] (ι : R →+* R'),
    C R → TopologicalRing.IsWeaklyAdmissible R → ι.Etale →
      C (TopologicalRing.CompletionOver ι)

/-- A property of morphisms of topological rings is *invariant under isomorphism of sources* on
the class `C` when precomposing a continuous morphism with a continuous ring isomorphism of rings
of the class whose inverse is continuous leaves the property unchanged; only continuous morphisms,
the morphisms of the category of rings of the class, are quantified over. This is the
source-side companion of
`AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderTargetIsoOn`, and it is unavailable from
the axioms of `TopologicalRing.PropertyIsLocal` for exactly the reason recorded there: the
Stacks Project derives it from axiom (1) of Situation 0CBA by identifying a complete ring with
its own completion, whereas the completed corners of a
`TopologicalRing.LocalizationDiagram` are `TopologicalRing.CompletionOver` types, only
isomorphic to the rings they complete. -/
abbrev PropertyIsInvariantUnderSourceIso : Prop :=
  ∀ {A A' R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A]
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R],
    C A → C A' → C R →
    ∀ (ψ : A →+* R) (e : A' ≃+* A), Continuous ψ → Continuous e → Continuous e.symm →
      P ψ → P (ψ.comp e.toRingHom)

/-- **Axiom (1) of Situation 0CBA, read on one square of affine formal algebraic charts.** If `P`
is a local property of morphisms of rings of the class `C`, then a representable étale change of
source and of target carries `P` from a map `t` of affine formal algebraic charts, both presented
by rings of the class, to the induced map `t'`. Asked of every chart, this is
`AlgebraicGeometry.FormalSpace.ChartPropertyAscendsAlongAffineEtale`, the hypothesis `hasc` of
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover`, the
implication (3) ⟹ (1) of **Stacks 0ANG**.

The route is the one the source takes. The two lower charts of the square are presented by
rings `A` and `R` of the class, and Stacks 0AN0 presents the lower edge by a continuous
homomorphism `g : A → R`, on which `P` holds by assumption.
`AlgebraicGeometry.FormalSpace.exists_localizationDiagram_of_chartSquare` turns the square into
a `TopologicalRing.LocalizationDiagram` with `g` for its lower map, and axiom (1) of Situation
0CBA carries `P` to its upper map `A'^∧ → R'^∧`. That map presents the upper edge of the
square, so it agrees with any other presentation of that edge up to isomorphisms of the two
presenting rings, by Stacks 0AN0 again, and `P` is carried across those isomorphisms.

Five inputs beyond `hP` are named. `h0AN8` is the essential-surjectivity clause of Stacks 0AN8,
the one input of the localization diagram. `hpU` and `hpV` are the presentations of the lower
charts by rings of the class, which is Stacks 0AKX for the charts of a locally countably indexed
or locally adic\* formal algebraic space. `hCw`, `hCcompl` are the two properties of the class
that Situation 0CBA presupposes and an arbitrary predicate `C` does not have. `hsrc` and `htgt`
are invariance of `P` under isomorphism of sources and of targets, which the Stacks Project
obtains from axiom (1) by identifying a complete ring with its own completion and which this
library cannot; see
`AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderTargetIsoOn`. -/
theorem hasPropertyOnAffineChartMap_of_etaleSquare_of_propertyIsLocal
    (h0AN8 : IsEssentiallySurjectiveSpf B S hS)
    (hCw : ClassIsWeaklyAdmissible C)
    (hCcompl : ClassIsStableUnderEtaleCompletion C)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} C P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    (hP : TopologicalRing.PropertyIsLocal P C)
    {U V U' V' : FppfSheaf B S hS} (t : U ⟶ V) (t' : U' ⟶ V') (q : U' ⟶ U) (r : V' ⟶ V)
    (hpU : HasPresentationOfClass B S hS C U) (hpV : HasPresentationOfClass B S hS C V)
    (hU' : IsAffineFormalAlgebraicSpace B S hS U')
    (hV' : IsAffineFormalAlgebraicSpace B S hS V')
    (hq : IsRepresentableEtale B S hS q) (hr : IsRepresentableEtale B S hS r)
    (hsq : q ≫ t = t' ≫ r) (ht : HasPropertyOnAffineChartMap B S hS C P t) :
    HasPropertyOnAffineChartMap B S hS C P t' := by
  obtain ⟨A, _, _, _, _, D, hCA, hAw, hAc, hAcard, ⟨eV⟩⟩ := hpV
  obtain ⟨R, _, _, _, _, E, hCR, hRw, hRc, hRcard, ⟨eU⟩⟩ := hpU
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hAw hRw
    (eU.inv ≫ t ≫ eV.hom)
  have hPg : P g.toRingHom := ht A R hCA hCR hAw D E eU eV g (by rw [hg]; simp)
  have hqe : IsRepresentableEtale B S hS (q ≫ eU.hom) :=
    IsRepresentableEtale.comp B S hS hq (isRepresentableEtale_iso_hom B S hS eU)
  have hre : IsRepresentableEtale B S hS (r ≫ eV.hom) :=
    IsRepresentableEtale.comp B S hS hr (isRepresentableEtale_iso_hom B S hS eV)
  have hsq' : (q ≫ eU.hom) ≫ formalSpectrumMap hAw g = t' ≫ r ≫ eV.hom := by
    rw [hg, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hsq, Category.assoc]
  obtain ⟨R', A', _, _, Dg, E', D', g', -, eU', eV', hmap, hcm, -, -, hpres'⟩ :=
    exists_localizationDiagram_of_chartSquare B S hS h0AN8 hAw hRw hAc hRc hAcard hRcard g
      t' (q ≫ eU.hom) (r ≫ eV.hom) hU' hV' hqe hre hsq'
  have hCAc : C (TopologicalRing.CompletionOver Dg.toB') :=
    hCcompl Dg.toB' hCA hAw Dg.etaleB
  have hCRc : C (TopologicalRing.CompletionOver Dg.toA') :=
    hCcompl Dg.toA' hCR hRw Dg.etaleA
  have hPcm : P Dg.completedMap :=
    hP.localizationPreserves Dg hCR hCA hCRc hCAc (by rw [hmap]; exact hPg)
  intro A₁ R₁ _ _ _ _ _ _ _ _ hCA₁ hCR₁ hA₁ D₁ E₁ eU₁ eV₁ g₁ hg₁
  have hR₁ : TopologicalRing.IsWeaklyAdmissible R₁ := hCw R₁ hCR₁
  have hAc' := TopologicalRing.completionOver_isWeaklyAdmissible Dg.toB' hAw
  have hRc' := TopologicalRing.completionOver_isWeaklyAdmissible Dg.toA' hRw
  obtain ⟨gv, -, φ, hgv, -, hφ, -, hφc, hφc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hA₁ hAc' (eV'.symm ≪≫ eV₁)
  obtain ⟨gu, -, χ, hgu, -, hχ, -, hχc, hχc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hRc' hR₁ (eU₁.symm ≪≫ eU')
  have hφr : φ.toRingHom = gv.toRingHom := RingHom.ext fun x ↦ congrFun hφ x
  have hχr : χ.toRingHom = gu.toRingHom := RingHom.ext fun x ↦ congrFun hχ x
  have hg₁eq : g₁ = ContinuousHom.comp hRc' hA₁ gu (ContinuousHom.comp hAc' hA₁ g' gv) := by
    refine (existsUnique_continuousHom_formalSpectrumMap_eq hA₁ hR₁
      (eU₁.inv ≫ t' ≫ eV₁.hom)).unique (by rw [hg₁]; simp) ?_
    rw [← formalSpectrumMap_comp_eq hRc' hA₁ gu (ContinuousHom.comp hAc' hA₁ g' gv),
      ← formalSpectrumMap_comp_eq hAc' hA₁ g' gv, hgu, hgv, hpres']
    simp
  have hfin : g₁.toRingHom = χ.toRingHom.comp (Dg.completedMap.comp φ.toRingHom) := by
    rw [hg₁eq, ContinuousHom.comp_toRingHom, ContinuousHom.comp_toRingHom, hcm, hφr, hχr]
  rw [hfin]
  exact htgt hCA₁ hCRc hCR₁ _ χ (Dg.continuousCompletedMap.comp hφc) hχc hχc'
    (hsrc hCAc hCA₁ hCRc Dg.completedMap φ Dg.continuousCompletedMap hφc hφc' hPcm)

/-- **Axiom (1) of Situation 0CBA, read on affine formal algebraic charts**, for every chart:
`AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_of_etaleSquare_of_propertyIsLocal`
with the presentations of the two lower charts supplied by `hpres`. -/
theorem chartPropertyAscendsAlongAffineEtale_of_propertyIsLocal
    (h0AN8 : IsEssentiallySurjectiveSpf B S hS)
    (hpres : ChartsHavePresentationOfClass B S hS C)
    (hCw : ClassIsWeaklyAdmissible C)
    (hCcompl : ClassIsStableUnderEtaleCompletion C)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} C P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    (hP : TopologicalRing.PropertyIsLocal P C) :
    ChartPropertyAscendsAlongAffineEtale B S hS C P :=
  fun t t' q r hU hV hU' hV' hq hr hsq ht ↦
    hasPropertyOnAffineChartMap_of_etaleSquare_of_propertyIsLocal B S hS C P h0AN8 hCw hCcompl
      hsrc htgt hP t t' q r (hpres _ hU) (hpres _ hV) hU' hV' hq hr hsq ht

end AlgebraicGeometry.FormalSpace

end
