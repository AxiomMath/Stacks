module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyEquivalence
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic

/-!
# Stability under base change at the class of countably indexed weakly admissible rings

Let `P` be a local property of morphisms of `WAdm^count` which is stable under base change in
the sense of **Stacks 0GBC**, that is `TopologicalRing.IsStableUnderBaseChange P`. The chart
argument of **Stacks 0GBD** consumes stability under base change in the uniform shape
`AlgebraicGeometry.FormalSpace.CompletedTensorBaseChangeAxiom`, which asks in addition that the
completed tensor product be again an object of the class. This file supplies that shape at
`WAdm^count`.

The library already carries the two other instances of the same bridge: Stacks 0GBG for
`WAdm^Noeth` (`completedTensorBaseChangeAxiom_of_isStableUnderBaseChangeBy`) and Stacks 0GBE
for `WAdm^{adic*}` (`completedTensorBaseChangeAxiom_of_adicStarStableBaseChange`). The class of
Stacks 0GBD itself was missing, which is why the chart argument could not be instantiated at
`WAdm^count` at all.

Membership of the completed tensor product in `WAdm^count` is Lemma 87.4.12 (Stacks 0GB4) read
at that class: weak admissibility is
`TopologicalRing.completedTensorProduct_isWeaklyAdmissible` and the countable fundamental
system of neighbourhoods of zero is
`TopologicalRing.isCountablyGenerated_nhds_zero_completedTensorProduct`.

Nothing is asked of the morphism being based along, exactly as the definition of Stacks 0GBC
imposes no condition on it: its slot is filled by the property that holds of every morphism,
which satisfies condition (1) of Stacks 0ANG over every morphism of fppf sheaves by
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_true`.

## Main results

* `TopologicalRing.isCountablyWeaklyAdmissible_completedTensorProduct`: **Lemma 87.4.12
  (Stacks 0GB4) on the class `WAdm^count`**, the well definedness that the notion of Stacks
  0GBC needs.
* `AlgebraicGeometry.FormalSpace.completedTensorBaseChangeAxiom_of_isStableUnderBaseChange`:
  stability under base change in the sense of Stacks 0GBC supplies the base-change axiom that
  the chart argument of Stacks 0GBD consumes, at the class `WAdm^count`.

## References

* [Stacks Project, Tag 0GBC](https://stacks.math.columbia.edu/tag/0GBC)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public noncomputable section

universe u

namespace TopologicalRing

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Lemma 87.4.12 (Stacks 0GB4) on the class `WAdm^count`.** The completed tensor product of
two countably indexed weakly admissible topological rings over a third is again one: it is
weakly admissible and its fundamental system of neighbourhoods of zero is countable.

This is the well definedness that the notion of stability under base change of Stacks 0GBC
needs, and it is what the chart argument of Stacks 0GBD needs of the class beyond the
stability clause itself, in order to transport `P` along the isomorphism identifying the chart
ring of a fibre product of charts with the completed tensor product. -/
@[stacks 0GB4 "the weakly_admissible and countable_basis clauses, assembled as membership in \
WAdm^count"]
public theorem isCountablyWeaklyAdmissible_completedTensorProduct {A₀ A₁ A : Type u}
    [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
    [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [Algebra A₀ A₁] [Algebra A₀ A]
    (h₁ : IsCountablyWeaklyAdmissible A₁) (hA : IsCountablyWeaklyAdmissible A) :
    IsCountablyWeaklyAdmissible
      (CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) :=
  ⟨completedTensorProduct_isWeaklyAdmissible h₁.1.1 hA.1.1,
    isCountablyGenerated_nhds_zero_completedTensorProduct h₁.2 hA.2⟩

end

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A local property of morphisms of `WAdm^count` stable under base change, in the sense of
**Stacks 0GBC**, satisfies the base-change axiom that the chart argument of Stacks 0GBD
consumes at the class `WAdm^count`.

The stability clause of Stacks 0GBC gives the property of `C → A ⊗̂_B C`. That the completed
tensor product is again an object of `WAdm^count` is Lemma 87.4.12, which is
`TopologicalRing.isCountablyWeaklyAdmissible_completedTensorProduct` here. Nothing is asked of
the morphism being based along, so the axiom is supplied with the property that holds of every
morphism in that slot. -/
theorem completedTensorBaseChangeAxiom_of_isStableUnderBaseChange
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.IsStableUnderBaseChange.{u} P) :
    CompletedTensorBaseChangeAxiom.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P (fun _ ↦ True) := by
  intro A₀ A₁ A _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₀ h₁ hA hc₁ hcA hp _
  exact ⟨TopologicalRing.isCountablyWeaklyAdmissible_completedTensorProduct h₁ hA,
    hP.baseChange h₀ h₁ hA hc₁ hcA hp⟩

end

open CategoryTheory CategoryTheory.Limits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The whole conclusion of **Stacks 0GBD** for the second projection: the three conditions of
Stacks 0ANG are equivalent for `pr₂ : X ×_Y Z ⟶ Z` and all three of them hold.

Let `P` be a local property of morphisms of `WAdm^count` stable under base change, that is
`TopologicalRing.IsStableUnderBaseChange P` (Stacks 0GBC), and let `f : X ⟶ Y`, `g : Z ⟶ Y` be
morphisms of locally countably indexed formal algebraic spaces over `S`. If `f` satisfies
condition (1) of Stacks 0ANG, then so does `pr₂`, and so do conditions (2) and (3), and the
three are equivalent for `pr₂`.

The equivalence is `AlgebraicGeometry.FormalSpace.hasProperty_tfae`, the library's assembly of
the three conditions of Stacks 0ANG, read at `pr₂`; the three conditions are the abbreviations
`HasPropertyOnEveryAffineEtaleDiagram`, `HasPropertyAfterTargetCover` and
`HasPropertyAfterSourceCover` that the legs of Stacks 0ANG registered in this library speak
about. Condition (3) is the chart argument of Stacks 0GBD, carried out once at an arbitrary
class in `hasPropertyAfterSourceCover_pullback_snd_of_baseChangeAxiom` and instantiated at
`WAdm^count` through
`completedTensorBaseChangeAxiom_of_isStableUnderBaseChange` above; condition (1) is the
implication (3) ⟹ (1) of Stacks 0ANG, whose covering refinement is proved in
`hasEtaleRefinementOfSourceCover`; condition (2) is the implication (1) ⟹ (2), whose fibre
products come from this library's Stacks 0AJ3 through
`isFormalAlgebraicSpace_pullback_chart`, so that Stacks 0AJ3 is not assumed.

Five inputs the library does not carry stay as hypotheses, and this statement therefore
carries no tag. `hcover` is the geometric half of Stacks 0GBD — the covering of `X ×_Y Z` by
fibre products of charts, presented by completed tensor products through Stacks 0AN3 clause
(3); `hiso` is the invariance of `P` under isomorphism of targets; `hchart` is the pair of
chart-level locality axioms, which needs the essential-surjectivity clause of Stacks 0AN8;
`hcolim` is Stacks 0AIU; and `hpb` is Stacks 0GBB clause (1) for `X ×_Y Z`. Nothing else is
assumed: the hypotheses on `P`, on `g` and on `f` are the source's. -/
theorem hasProperty_pullback_snd_of_isStableUnderBaseChange
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.IsStableUnderBaseChange.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P)
    (hchart : TopologicalRing.PropertyIsLocal P TopologicalRing.IsCountablyWeaklyAdmissible →
      ChartPropertyAscendsAlongAffineEtale B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible P ∧
        ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible P)
    (hcolim : ColimitOfThickeningsIsFormalAlgebraicSpace B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hpb : IsLocallyCountablyIndexed B S hS (pullback f g))
    (hcover : HasBaseChangeCoverOverPullbackSndOn B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f) :
    List.TFAE
        [ HasPropertyOnEveryAffineEtaleDiagram B S hS
            TopologicalRing.IsCountablyWeaklyAdmissible P (pullback.snd f g),
          HasPropertyAfterTargetCover B S hS
            TopologicalRing.IsCountablyWeaklyAdmissible P (pullback.snd f g),
          HasPropertyAfterSourceCover B S hS
            TopologicalRing.IsCountablyWeaklyAdmissible P (pullback.snd f g) ] ∧
      HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible P (pullback.snd f g) ∧
        HasPropertyAfterTargetCover B S hS
            TopologicalRing.IsCountablyWeaklyAdmissible P (pullback.snd f g) ∧
          HasPropertyAfterSourceCover B S hS
            TopologicalRing.IsCountablyWeaklyAdmissible P (pullback.snd f g) := by
  have h3 : HasPropertyAfterSourceCover B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P (pullback.snd f g) :=
    hasPropertyAfterSourceCover_pullback_snd_of_baseChangeAxiom B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P (fun _ ↦ True)
      (completedTensorBaseChangeAxiom_of_isStableUnderBaseChange P hP) hiso f g hcover hf
      (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g)
  have h1 := hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible P (pullback.snd f g)
    (hchart hP.isLocal).1 (hchart hP.isLocal).2
    (hasEtaleRefinementOfSourceCover B S hS hcolim (pullback.snd f g) hpb.1 hZ.1) h3
  have h2 := hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible P (pullback.snd f g) hZ.1
    (isFormalAlgebraicSpace_pullback_chart B S hS hcolim hpb.1 hZ.1) h1
  exact ⟨hasProperty_tfae B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
    (pullback.snd f g) hpb hZ hP.isLocal hchart hcolim, h1, h2, h3⟩

end AlgebraicGeometry.FormalSpace

end
