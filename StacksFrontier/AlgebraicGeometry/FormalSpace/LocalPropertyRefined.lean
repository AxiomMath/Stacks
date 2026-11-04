module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.CategoryTheory.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverSelf
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Local properties of morphisms of formal algebraic spaces: the presented forms

Forms of the axioms of a local property of Situation 0CBA, read on affine formal algebraic spaces
through Stacks 0AN8 and Stacks 0AN9, in which the étale changes of chart are presented by completed
étale localizations, and the implication (3) ⇒ (1) of Stacks 0ANG for these forms.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsCompletedEtaleLocalizationOfChartMap`: a chart map is a
  completed étale localization of another.
* `AlgebraicGeometry.FormalSpace.IsCompletedEtaleFiniteCoverOfChartMap`: a finite affine étale
  covering of the source of a chart map is presented by completed étale localizations.
* `AlgebraicGeometry.FormalSpace.ChartPropertyAscendsAlongAffineEtale'`: axiom (1) of a local
  property.
* `AlgebraicGeometry.FormalSpace.ChartPropertyDescendsAlongFiniteAffineEtaleCover'`: axioms (2)
  and (3) of a local property.
* `AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'`: the presented refinement of
  a source covering against affine étale diagrams.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover'`:
  Stacks 0ANG, condition (3) implies condition (1).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The chart map `t' : U' ⟶ V'` is a *completed étale localization* of the chart map
`t : U ⟶ V`: for every presentation of `t'` by a continuous homomorphism of rings of the class
`C` there are a presentation of `t` and a localization diagram of Situation 0CBA whose vertical
map is the homomorphism presenting `t` and whose completed vertical map is, up to bicontinuous
isomorphisms of its source and of its target, the homomorphism presenting `t'`. This is the
conclusion of Stacks 0AN8 for a representable étale change of source and of target. The data
produced for each presentation of `t'` is passed to an arbitrary continuation `Goal`. -/
abbrev IsCompletedEtaleLocalizationOfChartMap {U V U' V' : FppfSheaf B S hS}
    (t : U ⟶ V) (t' : U' ⟶ V') : Prop :=
  ∀ (A' R' : Type u) [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
      [IsLinearTopology A' A'] [CommRing R'] [TopologicalSpace R'] [IsTopologicalRing R']
      [IsLinearTopology R' R'],
    C A' → C R' → ∀ (hA' : TopologicalRing.IsWeaklyAdmissible A')
      (D' : QuotientSystem B S hS A') (E' : QuotientSystem B S hS R')
      (eU' : U' ≅ formalSpectrum E') (eV' : V' ≅ formalSpectrum D')
      (g' : ContinuousHom D' E'),
      t' = eU'.hom ≫ formalSpectrumMap hA' g' ≫ eV'.inv →
    ∀ Goal : Prop,
      (∀ (A R A₁ R₁ : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
          [IsLinearTopology A A] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
          [IsLinearTopology R R] [CommRing A₁] [CommRing R₁],
          C A → C R → ∀ (hA : TopologicalRing.IsWeaklyAdmissible A)
            (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS R)
            (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
            t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
          ∀ (Dia : TopologicalRing.LocalizationDiagram R A R₁ A₁),
            Dia.map = g.toRingHom →
          ∀ (eA : TopologicalRing.CompletionOver Dia.toB' ≃+* A')
            (eR : TopologicalRing.CompletionOver Dia.toA' ≃+* R'),
            Continuous eA → Continuous eA.symm → Continuous eR → Continuous eR.symm →
            g'.toRingHom = (eR.toRingHom.comp Dia.completedMap).comp eA.symm.toRingHom →
          Goal) →
        Goal

/-- Axiom (1) of a local property of Situation 0CBA, read on affine formal algebraic spaces
through the equivalence of Stacks 0AN8: a representable étale change of source and of target
carries `P` from a map of affine formal algebraic spaces to the induced map, the change being
presented by a completed étale localization diagram. -/
abbrev ChartPropertyAscendsAlongAffineEtale' : Prop :=
  ∀ {U V U' V' : FppfSheaf B S hS} (t : U ⟶ V) (t' : U' ⟶ V') (q : U' ⟶ U) (r : V' ⟶ V),
    IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
    IsAffineFormalAlgebraicSpace B S hS U' → IsAffineFormalAlgebraicSpace B S hS V' →
    IsRepresentableEtale B S hS q → IsRepresentableEtale B S hS r → q ≫ t = t' ≫ r →
    IsCompletedEtaleLocalizationOfChartMap B S hS C t t' →
    HasPropertyOnAffineChartMap B S hS C P t → HasPropertyOnAffineChartMap B S hS C P t'

/-- The finite affine étale covering `{Wₛ ⟶ U}` of the source of a chart map `t : U ⟶ V`, with
its maps `mₛ : Wₛ ⟶ Zₛ` into representable étale charts of the target, is *presented by
completed étale localizations*: for every presentation of `t` by a continuous homomorphism
`g : A →+* R` of rings of the class `C` there are

* a finite index type `ι` in the universe of the chart rings and a map `κ : ι → σ` selecting a
  subfamily, together with rings `Zr i` and `Wr i` of the class `C` presenting `m (κ i)`;
* for every `i` an étale ring map `bz i : A →+* Bz i` and a bicontinuous isomorphism
  `CompletionOver (bz i) ≃+* Zr i`, exhibiting the chart `Z (κ i)` of `V` as the formal spectrum
  of a completed étale localization of the chart `A` of `V`;
* an étale, faithfully flat ring map `c : R →+* R₁` and a bicontinuous isomorphism
  `CompletionOver c ≃+* ∀ i, Wr i`, exhibiting the covering as the formal spectrum of a
  completed étale localization of the chart `R` of `U`, compatibly with `t`.

The data produced for each presentation of `t` is passed to an arbitrary continuation `Goal`. -/
abbrev IsCompletedEtaleFiniteCoverOfChartMap {U V : FppfSheaf B S hS} (t : U ⟶ V)
    {σ : Type (u + 1)} (W Z : σ → FppfSheaf B S hS) (m : ∀ s, W s ⟶ Z s) : Prop :=
  ∀ (A R : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R],
    C A → C R → ∀ (hA : TopologicalRing.IsWeaklyAdmissible A)
      (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS R)
      (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
      t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
    ∀ Goal : Prop,
      (∀ (ι : Type u) [Fintype ι] (κ : ι → σ) (Zr Wr Bz : ι → Type u) (R₁ : Type u)
          [∀ i, CommRing (Zr i)] [∀ i, TopologicalSpace (Zr i)]
          [∀ i, IsTopologicalRing (Zr i)] [∀ i, IsLinearTopology (Zr i) (Zr i)]
          [∀ i, CommRing (Wr i)] [∀ i, TopologicalSpace (Wr i)]
          [∀ i, IsTopologicalRing (Wr i)] [∀ i, IsLinearTopology (Wr i) (Wr i)]
          [∀ i, CommRing (Bz i)] [CommRing R₁]
          [IsLinearTopology (∀ i, Wr i) (∀ i, Wr i)],
          (∀ i, C (Zr i)) → (∀ i, C (Wr i)) → C (∀ i, Wr i) →
          ∀ (hZ : ∀ i, TopologicalRing.IsWeaklyAdmissible (Zr i))
            (Dz : ∀ i, QuotientSystem B S hS (Zr i))
            (Ew : ∀ i, QuotientSystem B S hS (Wr i))
            (eW : ∀ i, W (κ i) ≅ formalSpectrum (Ew i))
            (eZ : ∀ i, Z (κ i) ≅ formalSpectrum (Dz i))
            (μ : ∀ i, ContinuousHom (Dz i) (Ew i)),
            (∀ i, m (κ i) = (eW i).hom ≫ formalSpectrumMap (hZ i) (μ i) ≫ (eZ i).inv) →
          ∀ (bz : ∀ i, A →+* Bz i), (∀ i, (bz i).Etale) →
          ∀ (ez : ∀ i, TopologicalRing.CompletionOver (bz i) ≃+* Zr i),
            (∀ i, Continuous (ez i)) → (∀ i, Continuous (ez i).symm) →
          ∀ (c : R →+* R₁), c.Etale → c.FaithfullyFlat →
          ∀ (ew : TopologicalRing.CompletionOver c ≃+* ∀ i, Wr i),
            Continuous ew → Continuous ew.symm →
            ew.toRingHom.comp
                  ((TopologicalRing.CompletionOver.canonicalMap c).comp g.toRingHom) =
                (RingHom.pi fun i ↦ (μ i).toRingHom.comp ((ez i).toRingHom.comp
                  (TopologicalRing.CompletionOver.canonicalMap (bz i)))) →
          Goal) →
        Goal

/-- Axioms (2) and (3) of a local property of Situation 0CBA, read on affine formal algebraic
spaces through the equivalences of Stacks 0AN8 and Stacks 0AN9: `P` descends to `t : U ⟶ V` from a
finite affine étale covering `{Wₛ ⟶ U}` whose members map to representable étale charts `Zₛ ⟶ V` of
the target by maps with `P`, compatibly with `t`, the covering being presented by completed étale
localizations. -/
abbrev ChartPropertyDescendsAlongFiniteAffineEtaleCover' : Prop :=
  ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V), IsAffineFormalAlgebraicSpace B S hS U →
    IsAffineFormalAlgebraicSpace B S hS V →
    ∀ (σ : Type (u + 1)), Finite σ → ∀ (W Z : σ → FppfSheaf B S hS) (p : ∀ s, W s ⟶ U)
      (m : ∀ s, W s ⟶ Z s) (r : ∀ s, Z s ⟶ V),
      IsAffineEtaleCover B S hS W p →
      (∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s)) →
      (∀ s, IsRepresentableEtale B S hS (r s)) → (∀ s, p s ≫ t = m s ≫ r s) →
      IsCompletedEtaleFiniteCoverOfChartMap B S hS C t W Z m →
      (∀ s, HasPropertyOnAffineChartMap B S hS C P (m s)) →
      HasPropertyOnAffineChartMap B S hS C P t

/-- The source covering of `f` refines against affine étale diagrams, with presentations: if
`X` and `Y` are locally countably indexed, then for every affine étale covering `{Uᵢ ⟶ X}` of the
source with factorizations `Uᵢ ⟶ Vᵢ ⟶ Y` through affine formal algebraic spaces representable
étale over the target, and every commutative square `U₀ ⟶ V₀` over `f` with `U₀`, `V₀` affine and
representable étale over `X`, `Y`, there is a finite affine étale covering `{Wₛ ⟶ U₀}` whose
members map to a member `U (k s)` of the given covering and to a representable étale chart `Zₛ`
of `V₀` over `V (k s)`, both squares commuting. Moreover each map `Wₛ ⟶ Zₛ` is a completed étale
localization of `U (k s) ⟶ V (k s)`, and the covering of `U₀` is presented by completed étale
localizations.

This is the refinement constructed in the proof of Stacks 0ANG. -/
abbrev HasEtaleRefinementOfSourceCover' {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  IsLocallyCountablyIndexed B S hS X → IsLocallyCountablyIndexed B S hS Y →
  ∀ {I : Type (u + 1)} (U V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X) (v : ∀ i, V i ⟶ Y)
      (t : ∀ i, U i ⟶ V i), IsAffineEtaleCover B S hS U u →
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (V i)) →
      (∀ i, IsRepresentableEtale B S hS (v i)) → (∀ i, u i ≫ f = t i ≫ v i) →
    ∀ (U₀ V₀ : FppfSheaf B S hS) (a : U₀ ⟶ X) (b : V₀ ⟶ Y) (τ : U₀ ⟶ V₀),
      IsAffineFormalAlgebraicSpace B S hS U₀ → IsAffineFormalAlgebraicSpace B S hS V₀ →
      IsRepresentableEtale B S hS a → IsRepresentableEtale B S hS b → a ≫ f = τ ≫ b →
    ∃ (σ : Type (u + 1)) (_ : Finite σ) (k : σ → I) (W Z : σ → FppfSheaf B S hS)
      (p : ∀ s, W s ⟶ U₀) (q : ∀ s, W s ⟶ U (k s)) (m : ∀ s, W s ⟶ Z s)
      (r : ∀ s, Z s ⟶ V (k s)) (c : ∀ s, Z s ⟶ V₀),
      IsAffineEtaleCover B S hS W p ∧ (∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s)) ∧
        (∀ s, IsRepresentableEtale B S hS (q s)) ∧
        (∀ s, IsRepresentableEtale B S hS (r s)) ∧
        (∀ s, IsRepresentableEtale B S hS (c s)) ∧
        (∀ s, q s ≫ t (k s) = m s ≫ r s) ∧ (∀ s, p s ≫ τ = m s ≫ c s) ∧
        (∀ s, IsCompletedEtaleLocalizationOfChartMap B S hS C (t (k s)) (m s)) ∧
        IsCompletedEtaleFiniteCoverOfChartMap B S hS C τ W Z m

/-- Stacks 0ANG, condition (3) implies condition (1): let `X` and `Y` be locally countably
indexed. If `P` holds on an affine étale covering of the source of `f`, whose members factor
through affine formal algebraic spaces representable étale over the target, then `P` holds on
every affine étale diagram over `f`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover'
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hasc : ChartPropertyAscendsAlongAffineEtale' B S hS C P)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover' B S hS C P)
    (href : HasEtaleRefinementOfSourceCover' B S hS C f)
    (hf : HasPropertyAfterSourceCover B S hS C P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P f := by
  obtain ⟨I, U, u, hUcover, hfac⟩ := hf
  choose V v t hVaffine hVetale hVsquare hVproperty using hfac
  intro U₀ V₀ a b τ hU₀ hV₀ ha hb hsquare
  obtain ⟨σ, hσ, k, W, Z, p, q, m, r, c, hWcover, hZaffine, hq, hr, hc, hsq₁, hsq₂, hloc,
    hcover⟩ :=
    href hX hY U V u v t hUcover hVaffine hVetale hVsquare U₀ V₀ a b τ hU₀ hV₀ ha hb hsquare
  exact hdesc τ hU₀ hV₀ σ hσ W Z p m c hWcover hZaffine hc hsq₂ hcover fun s ↦
    hasc (t (k s)) (m s) (q s) (r s) (hUcover.1 (k s)) (hVaffine (k s)) (hWcover.1 s)
      (hZaffine s) (hq s) (hr s) (hsq₁ s) (hloc s) (hVproperty (k s))

end AlgebraicGeometry.FormalSpace

end
