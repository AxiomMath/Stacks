module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagram

/-!
# Base change of a local property of morphisms of formal algebraic spaces: the refined forms

For a property of morphisms of Noetherian adic topological rings which is local in the sense
of Situation 0CBA, we show that it is invariant under isomorphism of targets, that condition (3)
of Stacks 0ANG implies condition (1), and that stability of the property under base change
transfers to base changes of morphisms of formal algebraic spaces (Stacks 0GBD, 0GBF, 0GBG).
The results on base change and on condition (3) of Stacks 0ANG take their missing geometric
inputs as hypotheses, so none of them carries a `@[stacks]` attribute.

These are the refined forms of declarations of
`StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange`: a declaration of that module
whose statement was strengthened keeps its original statement there, and its strengthened form
lives here under a primed name.

## Main definitions

* `PropertyIsInvariantUnderTargetIso'`: invariance of a property of ring maps under
  composition with a bicontinuous isomorphism of the target.

## Main results

* `propertyIsInvariantUnderTargetIso_of_propertyIsLocalNoetherian`: a local property is
  invariant under isomorphism of targets.
* `sourceCoverImpliesEveryAffineEtaleDiagram_of_propertyIsLocal`: Stacks 0ANG, condition (3)
  implies condition (1), granted a presented étale refinement of a covering of every source.
* `hasPropertyOnEveryAffineEtaleDiagram_pullback_snd'`: Stacks 0GBG, granted the covering of
  the fibre product and the implication (3) ⟹ (1) of Stacks 0ANG.
* `hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_stableBaseChange'`: Stacks 0GBF, under
  the same two hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A property of morphisms of Noetherian adic topological rings is *invariant under
isomorphism of targets* when composing a continuous morphism with a ring isomorphism of
Noetherian adic rings which is continuous in both directions leaves the property unchanged.
This is the target half of presentation independence, which locality in the sense of Situation
0CBA records as its first axiom; see
`AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderTargetIso_of_propertyIsLocalNoetherian`. -/
abbrev PropertyIsInvariantUnderTargetIso'
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop) : Prop :=
  ∀ {A R R' : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [IsNoetherianRing A]
      [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
      [IsNoetherianRing R]
      [CommRing R'] [TopologicalSpace R'] [IsTopologicalRing R'] [IsLinearTopology R' R']
      [IsNoetherianRing R'],
    TopologicalRing.IsAdic A → TopologicalRing.IsAdic R → TopologicalRing.IsAdic R' →
    ∀ (ψ : A →+* R) (e : R ≃+* R'), Continuous ψ → Continuous e → Continuous e.symm →
      P ψ → P (e.toRingHom.comp ψ)

/-- Precomposing with the inverse of `RingEquiv.refl A` changes nothing. -/
private theorem comp_refl_symm {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    f.comp (RingEquiv.refl A).symm.toRingHom = f := RingHom.ext fun x ↦ by simp

/-- **Invariance under isomorphism of targets holds for every property local in the sense of
Stacks 0ANI.** Composing with `e : R ≃+* R'` is the isomorphism-invariance of Situation 0CBA
taken with the identity of the source, and the identity contributes nothing: `RingHom.id A` is
the ring homomorphism underlying the inverse of `RingEquiv.refl A`, and precomposing with it
leaves `e ∘ ψ` unchanged. -/
theorem propertyIsInvariantUnderTargetIso_of_propertyIsLocalNoetherian
    {P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop}
    (hP : TopologicalRing.PropertyIsLocalNoetherian'.{u} P) :
    PropertyIsInvariantUnderTargetIso'.{u} P := by
  intro A R R' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hR hR' ψ e hψ he hes hψP
  have h := (hP.isomorphismInvariant (RingEquiv.refl A) e continuous_id continuous_id he hes ψ hψ
    ⟨hA, inferInstance⟩ ⟨hR, inferInstance⟩ ⟨hA, inferInstance⟩ ⟨hR', inferInstance⟩).mp hψP
  rwa [comp_refl_symm] at h

/-- **Stacks 0ANG, condition (3) implies condition (1), for every morphism of formal algebraic
spaces over `S`.** A property of arrows which is local in the sense of Situation 0CBA on a class
`C` of topological rings closed under the completion of Stacks 0AN6 along an étale ring map
satisfies the implication for every morphism, granted that every morphism has a presented étale
refinement of a covering of its source.

The two locality axioms read on affine formal algebraic spaces are
`hasPropertyOnAffineChartMap_of_isCompletedEtaleLocalizationOfChartMap` and
`hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap`; the refinement is the
geometric input of Stacks 0AJ2 and quasi-compactness of an affine formal algebraic space,
together with the recognition of Stacks 0AN8 that its members are presented by completions of
étale ring maps.

The conclusion is written out rather than given as
`AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryAffineEtaleDiagram`, because it carries the
standing hypothesis of Stacks 0ANG that the two ends of the morphism are locally countably
indexed, which that abbreviation — quantifying over arbitrary morphisms of fppf sheaves — does
not. Stacks 0ANG is stated only for morphisms of locally countably indexed formal algebraic
spaces, so the unrestricted implication is not a consequence of it. -/
theorem sourceCoverImpliesEveryAffineEtaleDiagram_of_propertyIsLocal
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsLocal' P C)
    (hCwa : ∀ (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X], C X →
      TopologicalRing.IsWeaklyAdmissible X ∧ (nhds (0 : X)).IsCountablyGenerated)
    (hCcomp : ∀ {X Y : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] (φ : X →+* Y),
      TopologicalRing.IsWeaklyAdmissible X → φ.Etale → C X →
        C (TopologicalRing.CompletionOver φ))
    (href : ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y),
      HasEtaleRefinementOfSourceCover' B S hS C f) :
    ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y), IsLocallyCountablyIndexed B S hS X →
      IsLocallyCountablyIndexed B S hS Y → HasPropertyAfterSourceCover B S hS C P f →
        HasPropertyOnEveryAffineEtaleDiagram B S hS C P f := fun f hX hY hf ↦
  hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover' B S hS C P f hX hY
    (fun _ _ _ _ _ _ _ _ _ _ _ hloc ht ↦
      hasPropertyOnAffineChartMap_of_isCompletedEtaleLocalizationOfChartMap B S hS C P
        hP.toPropertyIsLocal hP.isomorphismInvariant hCcomp hloc ht)
    (fun t _ _ _ _ W Z _ m _ _ _ _ _ hcover hPm ↦
      hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap B S hS C P
        hP.toPropertyIsLocal hP.isomorphismInvariant hCwa hCcomp t W Z m hcover hPm)
    (href f) hf

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A chart base change of `f` along `g` has `P` on its chart map, whenever `P` is stable
under base change by `Q` and `f`, `g` satisfy condition (1) of Stacks 0ANG for `P` and `Q`.
This is the ring-theoretic heart of **Stacks 0GBG**: the base-change axiom of the stability
bundle, applied to the two chart maps that the base change is formed from.

The presentation of the chart of the fibre product by the completed tensor product is a
bicontinuous isomorphism of chart rings rather than an equality, so `P` must not distinguish a
target from an isomorphic one; that is the first axiom of locality in the sense of Situation
0CBA, `TopologicalRing.PropertyIsLocal'.isomorphismInvariant`, which the stability bundle of
Stacks 0GBG carries in its field `isLocalP`. -/
theorem hasPropertyOnAffineChartMap_of_isChartBaseChangeOf'
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPQ : TopologicalRing.IsStableUnderBaseChangeBy'.{u} P Q)
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
  refine (hPQ.isLocalP.isomorphismInvariant (RingEquiv.refl A) e.symm continuous_id
    continuous_id hesymm (by simpa using he) φ.toRingHom φ.continuous hCA hCR hCA
    ⟨hTadic, hTn⟩).mpr ?_
  have hcomp : (e.symm.toRingHom.comp φ.toRingHom).comp (RingEquiv.refl A).symm.toRingHom =
      algebraMap A
        (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) := by
    rw [comp_refl_symm]
    refine RingHom.ext fun x ↦ ?_
    have hx := RingHom.congr_fun heq x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe] at hx ⊢
    rw [← hx, RingEquiv.symm_apply_apply]
  exact hcomp ▸ hT

/-- **Stacks 0GBG**, in the form that the argument of Stacks 0GBD produces: if `P` is stable
under base change by `Q` and `f : X ⟶ Y`, `g : Z ⟶ Y` satisfy condition (1) of Stacks 0ANG for
`P` and for `Q`, then the second projection `X ×_Y Z ⟶ Z` satisfies condition (3) of Stacks
0ANG for `P`.

The covering of `X ×_Y Z` by fibre products of charts, with the presentation of those fibre
products by completed tensor products, is `hcover`; it mentions neither `P` nor `Q`, and it is
the geometric half of Stacks 0GBD, which rests on clause (3) of Stacks 0AN3. No `@[stacks]`
attribute sits on this statement, because that clause is missing from the library and
`HasBaseChangeCoverOverPullbackSnd` is therefore a Prop nothing concludes. -/
theorem hasPropertyAfterSourceCover_pullback_snd'
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPQ : TopologicalRing.IsStableUnderBaseChangeBy'.{u} P Q)
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
    hasPropertyOnAffineChartMap_of_isChartBaseChangeOf' B S hS P Q hPQ f g hf hg t ht⟩

/-- **Stacks 0GBG.** Let `P` be stable under base change by `Q` for Noetherian adic
topological rings. If `f : X ⟶ Y` and `g : Z ⟶ Y` are morphisms of locally Noetherian formal
algebraic spaces over `S` satisfying condition (1) of Stacks 0ANG for `P` and for `Q`
respectively, then the second projection `X ×_Y Z ⟶ Z` satisfies condition (1) for `P`.

Condition (3) is what the argument of Stacks 0GBD gives, on its geometric input `hcover`; the
passage back to condition (1) is the implication (3) ⟹ (1) of Stacks 0ANG, which is `h31`.
Each of the two rests on geometry the library does not have — `hcover` on clause (3) of Stacks
0AN3, and `h31`, through
`AlgebraicGeometry.FormalSpace.sourceCoverImpliesEveryAffineEtaleDiagram_of_propertyIsLocal`,
on the presented étale refinement `HasEtaleRefinementOfSourceCover'` — so no `@[stacks]`
attribute sits on this statement. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_pullback_snd'
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPQ : TopologicalRing.IsStableUnderBaseChangeBy'.{u} P Q)
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
  h31 _ (hasPropertyAfterSourceCover_pullback_snd' B S hS P Q hPQ f g hcover hf hg)

/-- **Stacks 0GBG**, uniformly over all pairs of properties: whenever `P` is stable under base
change by `Q` for Noetherian adic topological rings, condition (1) of Stacks 0ANG transfers
from `(f, P)` and `(g, Q)` to `(X ×_Y Z ⟶ Z, P)`.

The two remaining inputs of the single-pair statement are asked of every property local in the
sense of Stacks 0ANI, which is how the stability bundle of Stacks 0GBG supplies locality, and of
every pair of morphisms. Both are geometric and both are missing from the library — `h31`
reduces to the presented étale refinement of a covering of the source and `hcover` to clause (3)
of Stacks 0AN3 — so no `@[stacks]` attribute sits on this statement. -/
theorem transfersBaseChangeOnAffineEtaleDiagrams'
    (h31 : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian'.{u} P →
        SourceCoverImpliesEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (hcover : ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y),
      HasBaseChangeCoverOverPullbackSnd B S hS f g) :
    ∀ (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
      TopologicalRing.IsStableUnderBaseChangeBy'.{u} P Q →
      ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y),
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) Q g →
            HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (pullback.snd f g) := by
  intro P Q hPQ _X _Y _Z f g hf hg
  exact hasPropertyOnEveryAffineEtaleDiagram_pullback_snd' B S hS P Q hPQ
    (h31 P hPQ.isLocalP) f g (hcover f g) hf hg

/-- **Stacks 0GBF**, the variant of Stacks 0GBD for locally Noetherian formal algebraic
spaces: let `P` be stable under base change for Noetherian adic topological rings in the sense
of Stacks 0GBF. If `f : X ⟶ Y` satisfies condition (1) of Stacks 0ANG for `P`, then for every
`g : Z ⟶ Y` the second projection `X ×_Y Z ⟶ Z` satisfies condition (1) for `P`.

Nothing is asked of `g`, exactly as the definition of Stacks 0GBF imposes no condition on the
morphism being based along: stability under base change is stability under base change by the
property that holds of every morphism, and that property is local, so the statement is the one
of Stacks 0GBG with `Q` instantiated there.

The two further hypotheses are those the Stacks 0GBG statements already carry, for the same
reasons: `hcover` is the geometric input of Stacks 0GBD, resting on clause (3) of Stacks 0AN3,
and `h31` the implication (3) ⟹ (1) of Stacks 0ANG, resting on the presented étale refinement
of a covering of the source. Both are missing from the library, so no `@[stacks]` attribute
sits on this statement; the definition of stability under base change, which is the other half
of Stacks 0GBF, is registered on
`TopologicalRing.IsStableUnderBaseChangeNoetherian'`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_stableBaseChange'
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.IsStableUnderBaseChangeNoetherian'.{u} P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (pullback.snd f g) :=
  hasPropertyOnEveryAffineEtaleDiagram_pullback_snd' B S hS P (fun _ ↦ True)
    (hP.isStableUnderBaseChangeBy _ TopologicalRing.propertyIsLocalNoetherian_true')
    h31 f g hcover hf (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g)

end

end AlgebraicGeometry.FormalSpace

end
