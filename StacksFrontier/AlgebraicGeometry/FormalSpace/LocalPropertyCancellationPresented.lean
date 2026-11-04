module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCancellation

/-!
# Cancellation of a local property of morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0GBM** says that if `P` is a
local property of morphisms of `WAdm^{count}` with the cancellation property of Situation
0GBL, and `f : X ⟶ Y`, `g : Y ⟶ Z` are morphisms of locally countably indexed formal algebraic
spaces over `S` such that `g ∘ f` and `g` satisfy the equivalent conditions of Stacks 0ANG,
then so does `f`. **Stacks 0GBP** defines the cancellation property for a local property of
morphisms of `WAdm^{Noeth}` and asserts the same for morphisms of locally Noetherian formal
algebraic spaces.

## Main results

* `hasPropertyOnEveryAffineEtaleDiagram_of_comp_of_isLocallyNoetherian`:
  **Stacks 0GBP**, the variant of Stacks 0GBM for locally Noetherian formal algebraic spaces.

## Implementation notes

The argument is the one of Stacks 0GBM, whose covering the library builds for an arbitrary
class of rings and atlas property in
`AlgebraicGeometry.FormalSpace.exists_presentedSourceCover_of_comp_of_atlas`: an
affine étale covering `{Uᵢ ⟶ X}` with factorizations `Uᵢ ⟶ Vᵢ ⟶ Y` and `Vᵢ ⟶ Wᵢ ⟶ Z` through
affine étale charts taken inside Noetherian atlases of `X`, `Y` and `Z`, with `P` on each
`Vᵢ ⟶ Wᵢ` by condition (1) for `g`. Condition (1) for `g ∘ f` gives `P` on `Uᵢ ⟶ Wᵢ`, and the
cancellation property gives `P` on `Uᵢ ⟶ Vᵢ`. Condition (1) of Stacks 0ANG quantifies over
presentations of the two charts, so applying the ring-level axiom needs a presentation of the
last chart `Wᵢ` by a Noetherian adic ring and a realization of `Vᵢ ⟶ Wᵢ` by a continuous
homomorphism; the first is the presenting ring of the Noetherian chart (Stacks 0AIC), the
second is Stacks 0AN0, whose uniqueness clause identifies the composite with any realization
of `Uᵢ ⟶ Wᵢ`; this is
`AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_of_comp_of_spfPresentation`. Here
that covering is instantiated at the class `WAdm^{Noeth}` and at Noetherian atlases.

This gives condition (3) for `f` on a covering whose members and target charts are presented
by Noetherian adic rings, which is what the implication (3) ⟹ (1) of Stacks 0ANG for the
Noetherian class consumes,
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover`;
condition (2) follows by (1) ⟹ (2).

## References

* [Stacks Project, Tag 0GBL](https://stacks.math.columbia.edu/tag/0GBL)
* [Stacks Project, Tag 0GBM](https://stacks.math.columbia.edu/tag/0GBM)
* [Stacks Project, Tag 0GBP](https://stacks.math.columbia.edu/tag/0GBP)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- **Stacks 0GBP.** Let `P` be a local property of morphisms of `WAdm^{Noeth}` in the sense of
Remark 0ANI: it satisfies the three axioms of Situation 0CBA for morphisms of `WAdm^{Noeth}`,
which is `hP`, and is invariant under isomorphism of source and target, which Situation 0CBA
assumes and is `hPiso`. Suppose `P` has the *cancellation property*: for arrows `B → A` and
`C → B` of `WAdm^{Noeth}`, `P(C → B) ∧ P(C → A) ⟹ P(B → A)`, which is `hcancel`. Then the
variant of Stacks 0GBM holds for morphisms between locally Noetherian formal algebraic spaces:
if `f : X ⟶ Y` and `g : Y ⟶ Z` are such that `g ∘ f` and `g` satisfy the equivalent conditions
of Stacks 0ANG for `P` on `WAdm^{Noeth}`, so does `f`, and the conclusion lists all three of
them.

The covering is the one of the proof of Stacks 0GBM,
`AlgebraicGeometry.FormalSpace.exists_presentedSourceCover_of_comp_of_atlas`, built on the
Noetherian atlases of `X`, `Y` and `Z`: its charts stay Noetherian along representable étale
maps by clause (5) of Stacks 0AKQ and are presented by their presenting rings, which are
Noetherian and adic, so the cancellation property applies through Stacks 0AN0 and gives
condition (3) for `f` on a covering with presented members. The implication (3) ⟹ (1) of
Stacks 0ANG on such a covering is
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover`,
at the class `WAdm^{Noeth}`; condition (2) follows by (1) ⟹ (2). -/
@[stacks 0GBP "the variant of Stacks 0GBM for morphisms between locally Noetherian formal \
algebraic spaces; the definition of the cancellation property is \
TopologicalRing.HasNoetherianCancellationProperty"]
theorem hasPropertyOnEveryAffineEtaleDiagram_of_comp_of_isLocallyNoetherian
    (hP : TopologicalRing.PropertyIsLocalNoetherian.{u} P)
    (hcancel : TopologicalRing.HasNoetherianCancellationProperty.{u} P)
    (hPiso : TopologicalRing.IsomorphismInvariant.{u} P
      (fun R _ _ _ _ ↦ TopologicalRing.IsNoetherianAdic R))
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hfg : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P
      (f ≫ g))
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P f ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsNoetherianAdic P f ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic P f := by
  obtain ⟨I, U, V, u, v, t, hUcover, hVaffine, hv, hsq₁, ht, hUpres, hVpres⟩ :=
    exists_presentedSourceCover_of_comp_of_atlas B S hS _ P
      (fun _ _ _ _ _ h ↦ h.1.isWeaklyAdmissible)
      (fun hA hM hR φ ψ hφ hψ hPψ hPφψ ↦ hcancel φ ψ hR hM hA hφ hψ ⟨hPψ, hPφψ⟩)
      (IsNoetherian B S hS)
      (fun e hV' hV he hVn ↦ isNoetherian_of_isRepresentable' B S hS e hV' hV he.1
        (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS e he) hVn)
      (fun V _ hV ↦ exists_spfPresentation_of_isNoetherian B S hS V hV)
      f g hX.2 hY.1 hY.2 hZ.1 hZ.2 hfg hg
  have h1 : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P f :=
    hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover B S hS _ P hP hPiso
      (fun _ _ _ _ _ hR ↦ ⟨hR.1.isWeaklyAdmissible, Rig.countablyGenerated_nhds_of_isAdicRing hR.1⟩)
      (fun {R₁ R₂} _ _ _ _ _ φ _ het hX ↦ by
        let := φ.toAlgebra
        have : Algebra.Etale R₁ R₂ := het
        have : IsNoetherianRing R₁ := hX.2
        exact TopologicalRing.completionOver_isNoetherianAdic φ hX
          (Algebra.FiniteType.isNoetherianRing R₁ R₂))
      (fun e he he' hX ↦ TopologicalRing.isNoetherianAdic_of_ringEquiv e he he' hX)
      f U V u v t hUcover hVaffine hv hsq₁ ht hUpres hVpres
  exact ⟨h1, hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal' B S hS _ P f
    hX.1 hY.1 h1, ⟨I, U, u, hUcover, fun i ↦ ⟨V i, v i, t i, hVaffine i, hv i, hsq₁ i, ht i⟩⟩⟩

end AlgebraicGeometry.FormalSpace

end
