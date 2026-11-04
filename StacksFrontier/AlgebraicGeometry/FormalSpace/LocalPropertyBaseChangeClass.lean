module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange

/-!
# The chart argument of Stacks 0GBD over an arbitrary class of topological rings

`StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange` runs the chart argument of
**Stacks 0GBD** for Noetherian adic rings, the class `WAdm^{Noeth}` of Stacks 0GBG and 0GBF. The
argument uses nothing about the class beyond the base-change axiom it is handed, so it is carried
out here once for an arbitrary class `C` of topological rings and instantiated elsewhere — at
`WAdm^{adic*}` for **Stacks 0GBE** in
`StacksFrontier/AlgebraicGeometry/FormalSpace/AdicStarBaseChange.lean`, and at the countably indexed
rings in `StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexedPullbackProperty.lean`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderTargetIsoOn`: invariance of a morphism
  property under isomorphism of targets within a class of topological rings.
* `AlgebraicGeometry.FormalSpace.CompletedTensorBaseChangeAxiom`: the base-change axiom of a
  stability bundle, in the form the chart argument consumes it.
* `AlgebraicGeometry.FormalSpace.IsChartBaseChangeOn` and
  `AlgebraicGeometry.FormalSpace.HasBaseChangeCoverOverPullbackSndOn`: chart base changes and the
  covering of a fibre product by them, for chart rings of the class.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_pullback_snd_of_baseChangeAxiom`,
  and its `hasPropertyOnEveryAffineEtaleDiagram` counterpart: the chart argument at an arbitrary
  class of topological rings, giving conditions (3) and (1) of Stacks 0ANG for the second
  projection.
* `AlgebraicGeometry.FormalSpace.completedTensorBaseChangeAxiom_of_isStableUnderBaseChangeBy`:
  stability under base change in the sense of Stacks 0GBG gives the base-change axiom at
  `WAdm^{Noeth}`.

## References

* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0GBE](https://stacks.math.columbia.edu/tag/0GBE)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A property of morphisms of topological rings is *invariant under isomorphism of targets*
on a class `C` of rings when composing a continuous morphism with a continuous ring isomorphism
of rings of the class whose inverse is continuous leaves the property unchanged: invariance under
isomorphism of targets in the category of rings of the class, as Situation 0CBA asks of a local
property. Only continuous morphisms are quantified over, these being the morphisms of that
category. The Stacks Project has
this for every local property from axiom (1) of Situation 0CBA, an isomorphism being étale;
that route is unavailable here, because it identifies a complete ring with its own completion
and this library has there only an isomorphism, across which carrying the property is this
condition itself. It is proved for flatness and for flatness together with the property of
Stacks 0GBW in `StacksFrontier/AlgebraicGeometry/FormalSpace/Restricted/FlatTargetIsoInvariance`.
-/
abbrev PropertyIsInvariantUnderTargetIsoOn
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop) : Prop :=
  ∀ {A R R' : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A]
      [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
      [CommRing R'] [TopologicalSpace R'] [IsTopologicalRing R'] [IsLinearTopology R' R'],
    C A → C R → C R' →
    ∀ (ψ : A →+* R) (e : R ≃+* R'), Continuous ψ → Continuous e → Continuous e.symm →
      P ψ → P (e.toRingHom.comp ψ)

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The base-change axiom of a stability bundle, in the form the chart argument of Stacks 0GBD
consumes it: for an arrow `A₀ → A₁` with `P` and an arrow `A₀ → A` with `Q` between rings of
the class `C`, the completed tensor product `A₁ ⊗̂_{A₀} A` is again of the class and
`A → A₁ ⊗̂_{A₀} A` has `P`.

Stability under base change is defined once for each class of rings — Stacks 0GBG and Stacks
0GBF for `WAdm^{Noeth}`, Stacks 0GBE for `WAdm^{adic*}` — and each of those notions gives this
one at its own class. Nothing else about the class is used below, so the chart argument is
carried out once and instantiated. -/
abbrev CompletedTensorBaseChangeAxiom
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop) : Prop :=
  ∀ {A₀ A₁ A : Type u} [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
      [IsLinearTopology A₀ A₀]
      [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [Algebra A₀ A₁] [Algebra A₀ A],
    C A₀ → C A₁ → C A →
    Continuous (algebraMap A₀ A₁) → Continuous (algebraMap A₀ A) →
    P (algebraMap A₀ A₁) → Q (algebraMap A₀ A) →
      C (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) ∧
        P (algebraMap A (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)))

/-- A morphism `t : U ⟶ W` of affine formal algebraic spaces is a *chart base change* of
`f : X ⟶ Y` along `g : Z ⟶ Y` when, for every presentation of `t` by chart rings of the class
`C`, the chart ring of `U` is the completed tensor product of a chart map of `f` with the
chart ring of `W` over a chart ring of `Y`, compatibly with `t`. This is the conclusion of
Stacks 0AN0 for the fibre product of charts formed in the proof of Stacks 0GBD.

The data produced for each presentation is handed to a continuation `Goal`; this is the
elimination form of the corresponding existential statement, and lets the chart rings carry
their topological ring structures as instance arguments. -/
abbrev IsChartBaseChangeOn
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {U W : FppfSheaf B S hS} (t : U ⟶ W) : Prop :=
  ∀ (A R : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A]
      [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R],
    C A → C R →
    ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
      (E : QuotientSystem B S hS R) (eU : U ≅ formalSpectrum E) (eW : W ≅ formalSpectrum D)
      (φ : ContinuousHom D E), t = eU.hom ≫ formalSpectrumMap hA φ ≫ eW.inv →
    ∀ Goal : Prop,
      (∀ (A₀ A₁ : Type u) [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
          [IsLinearTopology A₀ A₀]
          [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
          [Algebra A₀ A₁] [Algebra A₀ A]
          (e : TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A) ≃+* R),
          C A₀ → C A₁ →
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
abbrev HasBaseChangeCoverOverPullbackSndOn
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ pullback f g),
    IsAffineEtaleCover B S hS U u ∧
      ∀ i, ∃ (W : FppfSheaf B S hS) (w : W ⟶ Z) (t : U i ⟶ W),
        IsAffineFormalAlgebraicSpace B S hS W ∧ IsRepresentableEtale B S hS w ∧
          u i ≫ pullback.snd f g = t ≫ w ∧ IsChartBaseChangeOn B S hS C f g t

/-- A chart base change of `f` along `g` has `P` on its chart map, whenever the
base-change axiom holds on the class `C` and `f`, `g` satisfy condition (1) of Stacks 0ANG for
`P` and `Q`. This is the ring-theoretic heart of the argument of **Stacks 0GBD**: the
base-change axiom, applied to the two chart maps that the base change is formed from. -/
theorem hasPropertyOnAffineChartMap_of_isChartBaseChangeOn
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hbc : CompletedTensorBaseChangeAxiom.{u} C P Q)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C Q g)
    {U W : FppfSheaf B S hS} (t : U ⟶ W) (ht : IsChartBaseChangeOn B S hS C f g t) :
    HasPropertyOnAffineChartMap B S hS C P t := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eW φ hφ
  refine ht A R hCA hCR hA D E eU eW φ hφ _ ?_
  intro A₀ A₁ _ _ _ _ _ _ _ _ _ _ e hA₀ hA₁ hc₀ hc₁ hfc hgc he hesymm heq
  have hP : P (algebraMap A₀ A₁) := hfc.property B S hS hf hA₀ hA₁
  have hQ : Q (algebraMap A₀ A) := hgc.property B S hS hg hA₀ hCA
  obtain ⟨hCT, hT⟩ := hbc hA₀ hA₁ hCA hc₀ hc₁ hP hQ
  have hcont : Continuous (algebraMap A
      (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A))) := by
    have h : algebraMap A (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) =
        e.symm.toRingHom.comp φ.toRingHom := by
      rw [← heq]; ext x; simp
    rw [h]
    exact hesymm.comp φ.continuous
  exact heq ▸ hiso hCA hCT hCR _ e hcont he hesymm hT

/-- The chart argument of **Stacks 0GBD** at an arbitrary class of topological rings: on the
covering `hcover` the base-change axiom turns condition (1) of Stacks 0ANG for `f` and `g`
into condition (3) for the second projection `X ×_Y Z ⟶ Z`. -/
theorem hasPropertyAfterSourceCover_pullback_snd_of_baseChangeAxiom
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hbc : CompletedTensorBaseChangeAxiom.{u} C P Q)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSndOn B S hS C f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C Q g) :
    HasPropertyAfterSourceCover B S hS C P (pullback.snd f g) := by
  obtain ⟨I, U, u, hU, hfac⟩ := hcover
  refine ⟨I, U, u, hU, fun i ↦ ?_⟩
  obtain ⟨W, w, t, hW, hw, hsq, ht⟩ := hfac i
  exact ⟨W, w, t, hW, hw, hsq,
    hasPropertyOnAffineChartMap_of_isChartBaseChangeOn B S hS C P Q hbc hiso f g hf hg t ht⟩

/-- The chart argument of **Stacks 0GBD** at an arbitrary class of topological rings, in the
form of condition (1) of Stacks 0ANG for the second projection. The passage from condition (3)
to condition (1) is the implication (3) ⟹ (1) of Stacks 0ANG, carried as `h31`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_baseChangeAxiom
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hbc : CompletedTensorBaseChangeAxiom.{u} C P Q)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSndOn B S hS C f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C Q g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P (pullback.snd f g) :=
  h31 _ (hasPropertyAfterSourceCover_pullback_snd_of_baseChangeAxiom B S hS C P Q hbc hiso f g
    hcover hf hg)

/-- Stability of `P` under base change by `Q` for Noetherian adic rings, the notion of **Stacks
0GBG**, gives the base-change axiom at the class `WAdm^{Noeth}`: the conclusion of its
base-change clause is exactly that the completed tensor product is Noetherian adic again and
that the base change of the `P`-arrow has `P`. -/
theorem completedTensorBaseChangeAxiom_of_isStableUnderBaseChangeBy
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPQ : TopologicalRing.IsStableUnderBaseChangeBy.{u} P Q) :
    CompletedTensorBaseChangeAxiom.{u}
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P Q := by
  intro A₀ A₁ A _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC₀ hC₁ hCA hc₀ hc₁ hP hQ
  have _ : IsNoetherianRing A₀ := hC₀.2
  have _ : IsNoetherianRing A₁ := hC₁.2
  have _ : IsNoetherianRing A := hCA.2
  obtain ⟨hTadic, hTnoeth, hT⟩ := hPQ.baseChange hC₀.1 hC₁.1 hCA.1 hc₀ hc₁ hP hQ
  exact ⟨⟨hTadic, hTnoeth⟩, hT⟩

end

end AlgebraicGeometry.FormalSpace

end
