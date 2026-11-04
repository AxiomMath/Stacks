module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty

/-!
# Base change of a local property of morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `P` and `Q` be properties of
continuous homomorphisms of Noetherian adic topological rings, and suppose `P` is stable under
base change by `Q` in the sense of **Stacks 0GBG**. For morphisms `f : X ⟶ Y` and `g : Z ⟶ Y`
of locally Noetherian formal algebraic spaces over `S`, the remark draws the consequence that
the equivalent conditions of Stacks 0ANG transfer from `(f, P)` and `(g, Q)` to
`(pr₂ : X ×_Y Z ⟶ Z, P)`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsAffineEtaleChartMap`: a continuous homomorphism of
  topological rings is the chart map of some affine étale diagram over a morphism.
* `AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderTargetIso`: invariance of a morphism
  property of Noetherian adic rings under isomorphism of targets.
* `AlgebraicGeometry.FormalSpace.IsChartBaseChangeOf`: a morphism of affine formal algebraic
  spaces is, on chart rings, a completed tensor-product base change of a chart map of `f`
  along a chart map of `g`.
* `AlgebraicGeometry.FormalSpace.HasBaseChangeCoverOverPullbackSnd`: the covering of
  `X ×_Y Z` by fibre products of charts constructed in the proof of Stacks 0GBD.
* `AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryAffineEtaleDiagram`: the implication
  (3) ⟹ (1) of Stacks 0ANG.

## Main results

* `AlgebraicGeometry.FormalSpace.IsAffineEtaleChartMap.property`: condition (1) of Stacks 0ANG
  holds on every chart map of the morphism.
* `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_pullback_snd`: **Stacks 0GBG**,
  condition (3) of Stacks 0ANG for the second projection.
* `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_pullback_snd` and
  `AlgebraicGeometry.FormalSpace.transfersBaseChangeOnAffineEtaleDiagrams`: **Stacks 0GBG**,
  the transfer of condition (1) of Stacks 0ANG to the second projection, for a single pair of
  properties and uniformly over all pairs.
* `hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_stableBaseChange`: **Stacks 0GBF**,
  the same transfer for a property stable under base change outright, with no condition at all
  on the morphism being based along.

## Implementation notes

Conditions (1) and (3) of Stacks 0ANG quantify over presentations of the charts as formal
spectra, so "the arrow of `WAdm^{Noeth}` that `f` gives rise to on a pair of charts" is not a
function of `f`; it is captured here by the predicate `IsAffineEtaleChartMap`, and condition
(1) is exactly the assertion that every ring map so captured has the property.

The proof follows Stacks 0GBD, whose argument Remark 0GBG invokes. Its geometric half — that
`X ×_Y Z` is covered by the fibre products `U ×_V W` of charts `U ⟶ X` and `W ⟶ Z` over a
chart `V ⟶ Y`, and that Stacks 0AN0 presents such a fibre product as the formal spectrum of
the completed tensor product of the chart rings — is not in the library and is carried as the
hypothesis `HasBaseChangeCoverOverPullbackSnd`, which mentions neither `P` nor `Q`. What is
proved here is the other half: that on such a covering the base-change axiom of the stability
bundle turns conditions (1) for `f` and `g` into condition (3) for the second projection.

Passing from condition (3) back to condition (1) is the implication (3) ⟹ (1) of Stacks 0ANG,
of which the library has only (1) ⟹ (2); it is carried as the hypothesis
`SourceCoverImpliesEveryAffineEtaleDiagram`. The presentation of a chart of the fibre product
by the completed tensor product is an isomorphism of chart rings rather than an equality, so
`P` must not distinguish a target from an isomorphic one; for a local property in the sense of
Stacks 0ANI this follows from descent along the isomorphism, which is faithfully flat and
étale, and the library does not derive it, so it too is a hypothesis.

## References

* [Stacks Project, Tag 0GBF](https://stacks.math.columbia.edu/tag/0GBF)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A continuous homomorphism `φ : A₁ →+* A₂` of topological rings is a *chart map* of
`f : X ⟶ Y` when it presents the upper horizontal arrow of some commutative square whose
vertical maps are representable étale maps from affine formal algebraic spaces. These are the
arrows of `WAdm^{Noeth}` over which condition (1) of Stacks 0ANG quantifies. -/
def IsAffineEtaleChartMap {X Y : FppfSheaf B S hS} (f : X ⟶ Y) {A₁ A₂ : Type u}
    [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
    [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂] [IsLinearTopology A₂ A₂]
    (φ : A₁ →+* A₂) : Prop :=
  ∃ (U V : FppfSheaf B S hS) (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V),
    IsAffineFormalAlgebraicSpace B S hS U ∧ IsAffineFormalAlgebraicSpace B S hS V ∧
      IsRepresentableEtale B S hS a ∧ IsRepresentableEtale B S hS b ∧ a ≫ f = t ≫ b ∧
      ∃ (hA₁ : TopologicalRing.IsWeaklyAdmissible A₁) (D : QuotientSystem B S hS A₁)
        (E : QuotientSystem B S hS A₂) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
        (ψ : ContinuousHom D E),
        t = eU.hom ≫ formalSpectrumMap hA₁ ψ ≫ eV.inv ∧ ψ.toRingHom = φ

/-- A morphism having a local property on every affine étale diagram has it on every chart
map: condition (1) of Stacks 0ANG is exactly the assertion that `P` holds for every arrow of
`WAdm^{Noeth}` arising from the morphism on a pair of charts. -/
theorem IsAffineEtaleChartMap.property
    {C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop}
    {P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop}
    {X Y : FppfSheaf B S hS} {f : X ⟶ Y} {A₁ A₂ : Type u}
    [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
    [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂] [IsLinearTopology A₂ A₂]
    {φ : A₁ →+* A₂} (hφ : IsAffineEtaleChartMap B S hS f φ)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f) (h₁ : C A₁) (h₂ : C A₂) : P φ := by
  obtain ⟨U, V, a, b, t, hU, hV, ha, hb, hsq, hA₁, D, E, eU, eV, ψ, hψ, hcomp⟩ := hφ
  exact hcomp ▸ hf U V a b t hU hV ha hb hsq A₁ A₂ h₁ h₂ hA₁ D E eU eV ψ hψ

/-- A property of morphisms of Noetherian adic topological rings is *invariant under
isomorphism of targets* when composing a morphism with a continuous ring isomorphism of
Noetherian adic rings whose inverse is continuous leaves the property unchanged. For a local
property in the sense of Stacks 0ANI this is a consequence of descent along the isomorphism. -/
abbrev PropertyIsInvariantUnderTargetIso
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop) : Prop :=
  ∀ {A R R' : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [IsNoetherianRing A]
      [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
      [IsNoetherianRing R]
      [CommRing R'] [TopologicalSpace R'] [IsTopologicalRing R'] [IsLinearTopology R' R']
      [IsNoetherianRing R'],
    TopologicalRing.IsAdic A → TopologicalRing.IsAdic R → TopologicalRing.IsAdic R' →
    ∀ (ψ : A →+* R) (e : R ≃+* R'), Continuous e → Continuous e.symm →
      P ψ → P (e.toRingHom.comp ψ)

/-- The implication (3) ⟹ (1) of **Stacks 0ANG** for the property `P` and the class of rings
`C`: a morphism with `P` on an affine étale covering of its source, with factorizations
through affine étale charts of its target, has `P` on every affine étale diagram. -/
abbrev SourceCoverImpliesEveryAffineEtaleDiagram
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop) : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (h : X ⟶ Y), HasPropertyAfterSourceCover B S hS C P h →
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P h

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A morphism `t : U ⟶ W` of affine formal algebraic spaces is a *chart base change* of
`f : X ⟶ Y` along `g : Z ⟶ Y` when, for every presentation of `t` by Noetherian adic chart
rings, the chart ring of `U` is the completed tensor product of a chart map of `f` with the
chart ring of `W` over a chart ring of `Y`, compatibly with `t`. This is the conclusion of
Stacks 0AN0 for the fibre product of charts formed in the proof of Stacks 0GBD.

The data produced for each presentation is handed to a continuation `Goal`; this is the
elimination form of the corresponding existential statement, and lets the chart rings carry
their topological ring structures as instance arguments. -/
abbrev IsChartBaseChangeOf {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {U W : FppfSheaf B S hS} (t : U ⟶ W) : Prop :=
  ∀ (A R : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [IsNoetherianRing A]
      [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
      [IsNoetherianRing R],
    TopologicalRing.IsAdic A → TopologicalRing.IsAdic R →
    ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
      (E : QuotientSystem B S hS R) (eU : U ≅ formalSpectrum E) (eW : W ≅ formalSpectrum D)
      (φ : ContinuousHom D E), t = eU.hom ≫ formalSpectrumMap hA φ ≫ eW.inv →
    ∀ Goal : Prop,
      (∀ (A₀ A₁ : Type u) [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
          [IsLinearTopology A₀ A₀] [IsNoetherianRing A₀]
          [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
          [IsNoetherianRing A₁] [Algebra A₀ A₁] [Algebra A₀ A]
          (e : TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A) ≃+* R),
          TopologicalRing.IsAdic A₀ → TopologicalRing.IsAdic A₁ →
          Continuous (algebraMap A₀ A₁) → Continuous (algebraMap A₀ A) →
          IsAffineEtaleChartMap B S hS f (algebraMap A₀ A₁) →
          IsAffineEtaleChartMap B S hS g (algebraMap A₀ A) →
          Continuous e → Continuous e.symm →
          e.toRingHom.comp (algebraMap A
              (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A))) =
            φ.toRingHom → Goal) →
        Goal

/-- The geometric input of **Stacks 0GBD**, whose argument Remark 0GBG invokes: an affine
étale covering of `X ×_Y Z` each member of which factors through an affine étale chart of `Z`
by a morphism that is a chart base change of `f` along `g`. In Stacks 0GBD the covering is by
the fibre products `U ×_V W` of charts `U ⟶ X` and `W ⟶ Z` over a chart `V ⟶ Y`. -/
abbrev HasBaseChangeCoverOverPullbackSnd {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y) :
    Prop :=
  ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ pullback f g),
    IsAffineEtaleCover B S hS U u ∧
      ∀ i, ∃ (W : FppfSheaf B S hS) (w : W ⟶ Z) (t : U i ⟶ W),
        IsAffineFormalAlgebraicSpace B S hS W ∧ IsRepresentableEtale B S hS w ∧
          u i ≫ pullback.snd f g = t ≫ w ∧ IsChartBaseChangeOf B S hS f g t

/-- A chart base change of `f` along `g` has `P` on its chart map, whenever `P` is stable
under base change by `Q` and `f`, `g` satisfy condition (1) of Stacks 0ANG for `P` and `Q`.
This is the ring-theoretic heart of **Stacks 0GBG**: the base-change axiom of the stability
bundle, applied to the two chart maps that the base change is formed from. -/
theorem hasPropertyOnAffineChartMap_of_isChartBaseChangeOf
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPQ : TopologicalRing.IsStableUnderBaseChangeBy.{u} P Q)
    (hiso : PropertyIsInvariantUnderTargetIso.{u} P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) Q g)
    {U W : FppfSheaf B S hS} (t : U ⟶ W) (ht : IsChartBaseChangeOf B S hS f g t) :
    HasPropertyOnAffineChartMap B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P t := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eW φ hφ
  have hnA : IsNoetherianRing A := hCA.2
  have hnR : IsNoetherianRing R := hCR.2
  refine ht A R hCA.1 hCR.1 hA D E eU eW φ hφ _ ?_
  intro A₀ A₁ _ _ _ _ _ _ _ _ _ _ _ _ e hA₀ hA₁ hc₀ hc₁ hfc hgc he hesymm heq
  have hP : P (algebraMap A₀ A₁) :=
    hfc.property B S hS hf ⟨hA₀, inferInstance⟩ ⟨hA₁, inferInstance⟩
  have hQ : Q (algebraMap A₀ A) := hgc.property B S hS hg ⟨hA₀, inferInstance⟩ hCA
  obtain ⟨hTadic, hTnoeth, hT⟩ := hPQ.baseChange hA₀ hA₁ hCA.1 hc₀ hc₁ hP hQ
  have hTn := hTnoeth
  exact heq ▸ hiso hCA.1 hTadic hCR.1 _ e he hesymm hT

/-- **Stacks 0GBG**, in the form that the argument of Stacks 0GBD produces: if `P` is stable
under base change by `Q` and `f : X ⟶ Y`, `g : Z ⟶ Y` satisfy condition (1) of Stacks 0ANG for
`P` and for `Q`, then the second projection `X ×_Y Z ⟶ Z` satisfies condition (3) of Stacks
0ANG for `P`.

The covering of `X ×_Y Z` by fibre products of charts, with the presentation of those fibre
products by completed tensor products, is the hypothesis `hcover`; it mentions neither `P` nor
`Q`. The isomorphism invariance of `P` implied by the locality of Stacks 0ANI is `hiso`. -/
@[stacks 0GBG "condition (3) for pr₂, with the 0GBD cover and iso-invariance assumed"]
theorem hasPropertyAfterSourceCover_pullback_snd
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPQ : TopologicalRing.IsStableUnderBaseChangeBy.{u} P Q)
    (hiso : PropertyIsInvariantUnderTargetIso.{u} P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) Q g) :
    HasPropertyAfterSourceCover B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (pullback.snd f g) := by
  obtain ⟨I, U, u, hU, hfac⟩ := hcover
  refine ⟨I, U, u, hU, fun i ↦ ?_⟩
  obtain ⟨W, w, t, hW, hw, hsq, ht⟩ := hfac i
  exact ⟨W, w, t, hW, hw, hsq,
    hasPropertyOnAffineChartMap_of_isChartBaseChangeOf B S hS P Q hPQ hiso f g hf hg t ht⟩

/-- **Stacks 0GBG.** Let `P` be stable under base change by `Q` for Noetherian adic
topological rings. If `f : X ⟶ Y` and `g : Z ⟶ Y` are morphisms of locally Noetherian formal
algebraic spaces over `S` satisfying condition (1) of Stacks 0ANG for `P` and for `Q`
respectively, then the second projection `X ×_Y Z ⟶ Z` satisfies condition (1) for `P`.

Condition (3) is what the argument of Stacks 0GBD gives; the passage back to condition (1) is
the implication (3) ⟹ (1) of Stacks 0ANG, carried as the hypothesis `h31`. -/
@[stacks 0GBG "condition (1) for pr₂, with the 0GBD cover, 0ANG (3) ⟹ (1) and iso-invariance"]
theorem hasPropertyOnEveryAffineEtaleDiagram_pullback_snd
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPQ : TopologicalRing.IsStableUnderBaseChangeBy.{u} P Q)
    (hiso : PropertyIsInvariantUnderTargetIso.{u} P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) Q g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (pullback.snd f g) :=
  h31 _ (hasPropertyAfterSourceCover_pullback_snd B S hS P Q hPQ hiso f g hcover hf hg)

/-- **Stacks 0GBG**, uniformly over all pairs of properties: whenever `P` is stable under base
change by `Q` for Noetherian adic topological rings, condition (1) of Stacks 0ANG transfers
from `(f, P)` and `(g, Q)` to `(X ×_Y Z ⟶ Z, P)`.

The three inputs of the single-pair statement are asked of every property local in the sense
of Stacks 0ANI, which is how the stability bundle of Stacks 0GBG supplies locality, and of
every pair of morphisms. -/
@[stacks 0GBG "the transfer for every property pair, on the same three hypotheses"]
theorem transfersBaseChangeOnAffineEtaleDiagrams
    (hiso : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian.{u} P → PropertyIsInvariantUnderTargetIso.{u} P)
    (h31 : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian.{u} P →
        SourceCoverImpliesEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (hcover : ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y),
      HasBaseChangeCoverOverPullbackSnd B S hS f g) :
    ∀ (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
      TopologicalRing.IsStableUnderBaseChangeBy.{u} P Q →
      ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y),
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) Q g →
            HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (pullback.snd f g) := by
  intro P Q hPQ _X _Y _Z f g hf hg
  exact hasPropertyOnEveryAffineEtaleDiagram_pullback_snd B S hS P Q hPQ
    (hiso P hPQ.isLocalP) (h31 P hPQ.isLocalP) f g (hcover f g) hf hg

/-- The property of morphisms of topological rings that holds of every morphism satisfies
condition (1) of Stacks 0ANG over every morphism of fppf sheaves, for every class of rings.
This is what the morphism being based along has to satisfy in the variant of Stacks 0GBF, where
no condition is imposed on it. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_true
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C (fun _ ↦ True) f := by
  intro _U _V _a _b _t _hU _hV _ha _hb _hsq A R
  intros
  trivial

/-- **Stacks 0GBF**, the variant of Stacks 0GBD for locally Noetherian formal algebraic
spaces: let `P` be stable under base change for Noetherian adic topological rings in the sense
of Stacks 0GBF. If `f : X ⟶ Y` satisfies condition (1) of Stacks 0ANG for `P`, then for every
`g : Z ⟶ Y` the second projection `X ×_Y Z ⟶ Z` satisfies condition (1) for `P`.

Nothing is asked of `g`, exactly as the definition of Stacks 0GBF imposes no condition on the
morphism being based along: stability under base change is stability under base change by the
property that holds of every morphism, and that property is local, so the statement is the one
of Stacks 0GBG with `Q` instantiated there.

The three further hypotheses are those the Stacks 0GBG statements already carry, for the same
reasons: `hcover` is the geometric input of Stacks 0GBD, `h31` the implication (3) ⟹ (1) of
Stacks 0ANG, and `hiso` the invariance of `P` under isomorphism of targets. -/
@[stacks 0GBF "the 0GBD variant for locally Noetherian formal algebraic spaces"]
theorem hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_stableBaseChange
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.IsStableUnderBaseChangeNoetherian.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIso.{u} P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (pullback.snd f g) :=
  hasPropertyOnEveryAffineEtaleDiagram_pullback_snd B S hS P (fun _ ↦ True)
    (hP.isStableUnderBaseChangeBy _ TopologicalRing.propertyIsLocalNoetherian_true)
    hiso h31 f g hcover hf (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g)

end

end AlgebraicGeometry.FormalSpace

end
