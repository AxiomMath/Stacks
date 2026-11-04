module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum

/-!
# Flat morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of locally
Noetherian formal algebraic spaces over `S` is *flat* (Stacks 0GCC) when for every commutative
square

```
U ⟶ V
↓     ↓
X ⟶ Y
```

with `U` and `V` affine formal algebraic spaces and `U ⟶ X`, `V ⟶ Y` representable by
algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a flat map of adic Noetherian
topological rings.

Flatness so defined is stable under composition (Stacks 0GCF), because the ring map attached to
a square for the composite is the composite of the ring maps attached to a square for each
factor, and flatness of ring maps is stable under composition.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsFlat`: **Stacks 0GCC**.
* `AlgebraicGeometry.FormalSpace.PresentedEtaleChart`: an affine chart of a formal algebraic
  space which is representable by algebraic spaces and étale and is presented by an adic
  Noetherian topological ring.
* `AlgebraicGeometry.FormalSpace.HasIntermediateCharts`: the condition that every affine étale
  square for a composite factors through such a chart of the intermediate space.

## Implementation notes

An affine formal algebraic space is presented by a formal spectrum, so "the morphism `U ⟶ V`
corresponds to a flat map of rings" is rendered by quantifying over presentations: over adic
Noetherian topological rings `A`, `C`, over quotient systems `D`, `E` presenting them over `S`,
over identifications `U ≅ Spf E` and `V ≅ Spf D`, and over continuous homomorphisms `g : A → C`
whose formal spectrum map is the given chart morphism. Every such `g` is then required to be
flat. This is the rendering used for the other chart-tested conditions of the chapter, such as
`AlgebraicGeometry.FormalSpace.IsRigFlat`, and as there the locally Noetherian hypotheses on
`X` and `Y` are imposed by applications rather than built into the predicate, which lets it be
used before those hypotheses are available. The representability and
étaleness conditions on the charts use the notions of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValued`, since the sheaves carrying formal algebraic
spaces take values in `Type (u + 1)`. Being an `abbrev`, the predicate hands its
universal-quantifier interface directly to consumers with no unfolding lemma.

Composition is the one place where the chart-tested shape of the condition needs an input this
library does not have. A square for `g ∘ f` relates a chart of `X` to a chart of `Z` and says
nothing about `Y`, so flatness of the two factors can only be applied after the square has been
factored through an affine representable étale chart of `Y`. Producing such a factorization is
the content of Stacks 0GCD — the comparison of Definition 0GCC with the criteria tested on an
affine étale covering — together with Stacks 0AKY, the locally Noetherian condition that
supplies the charts with adic Noetherian presentations; neither is part of this library, and
both are what `AlgebraicGeometry.FormalSpace.HasIntermediateCharts` records. That condition is
purely a factorization statement: it asserts nothing about flatness, so a consumer of it still
has to compose the two ring maps that the factorization produces. The ring presenting the
intermediate chart varies with the square, so the condition carries it in the bundled form
`AlgebraicGeometry.FormalSpace.PresentedEtaleChart` rather than as an existential over a type
together with its algebraic and topological instances.

## References

* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GCD](https://stacks.math.columbia.edu/tag/0GCD)
* [Stacks Project, Tag 0GCF](https://stacks.math.columbia.edu/tag/0GCF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Stacks 0GCC.** A morphism of formal algebraic spaces over `S` is *flat* when every
morphism between affine, representable, étale charts of its source and target is induced by a
flat continuous homomorphism of adic Noetherian topological rings. -/
@[stacks 0GCC]
abbrev IsFlat (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (U V : FppfSheaf B S hS)
    (_hU : IsAffineFormalAlgebraicSpace B S hS U)
    (_hV : IsAffineFormalAlgebraicSpace B S hS V)
    (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V)
    (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a.hom)
    (hb : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS b.hom),
    Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) a.hom ha →
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) b.hom hb →
      a ≫ f = t ≫ b → ∀ (A C : Type u)
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
          [IsNoetherianRing A]
        [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
          [IsNoetherianRing C],
        TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
        ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
          (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E)
          (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
          t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
            g.toRingHom.Flat

/-- An affine chart of a formal algebraic space `Y` over `S` which is representable by
algebraic spaces and étale and whose source is the formal spectrum of an adic Noetherian
topological ring over `S`. These are the charts on which the conditions of Stacks 0GCC are
tested. -/
structure PresentedEtaleChart (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : FppfSheaf B S hS) where
  /-- The topological ring presenting the chart. -/
  ring : Type u
  /-- Its ring structure. -/
  [commRing : CommRing ring]
  /-- Its topology. -/
  [topologicalSpace : TopologicalSpace ring]
  /-- Addition and multiplication are continuous. -/
  [isTopologicalRing : IsTopologicalRing ring]
  /-- The topology has a basis of ideals. -/
  [isLinearTopology : IsLinearTopology ring ring]
  /-- The ring is Noetherian. -/
  [isNoetherianRing : IsNoetherianRing ring]
  /-- The topology is adic. -/
  isAdic : TopologicalRing.IsAdic ring
  /-- The ring is weakly admissible, so that it has a formal spectrum. -/
  weaklyAdmissible : TopologicalRing.IsWeaklyAdmissible ring
  /-- The data presenting the ring over the base scheme. -/
  system : QuotientSystem B S hS ring
  /-- The formal spectrum is an affine formal algebraic space over `S`. -/
  affine : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum system)
  /-- The chart itself. -/
  chart : formalSpectrum system ⟶ Y
  /-- The chart is representable by algebraic spaces. -/
  representable :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS chart.hom
  /-- The chart is étale. -/
  etale : Space.HasPropertyULift.{u + 1} B S hS
    (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) chart.hom representable

attribute [instance] PresentedEtaleChart.commRing PresentedEtaleChart.topologicalSpace
  PresentedEtaleChart.isTopologicalRing PresentedEtaleChart.isLinearTopology
  PresentedEtaleChart.isNoetherianRing

/-- The *intermediate-chart condition* for a composable pair `f : X ⟶ Y`, `g : Y ⟶ Z` of
morphisms of formal algebraic spaces over `S`: every commutative square relating an affine
representable étale chart of `X` to one of `Z` over `g ∘ f` factors through an affine
representable étale chart of `Y` presented by an adic Noetherian topological ring, the
factorization being compatible with the presentations on both sides. The condition asserts a
factorization only; it says nothing about any of the three morphisms being flat. -/
abbrev HasIntermediateCharts (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  ∀ (U W : FppfSheaf B S hS)
    (_hU : IsAffineFormalAlgebraicSpace B S hS U)
    (_hW : IsAffineFormalAlgebraicSpace B S hS W)
    (a : U ⟶ X) (c : W ⟶ Z) (t : U ⟶ W)
    (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a.hom)
    (hc : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c.hom),
    Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) a.hom ha →
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) c.hom hc →
      a ≫ f ≫ g = t ≫ c → ∀ (A C : Type u)
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
          [IsNoetherianRing A]
        [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
          [IsNoetherianRing C],
        TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
        ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
          (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E)
          (eW : W ≅ formalSpectrum D) (φ : ContinuousHom D E),
          t = eU.hom ≫ formalSpectrumMap hA φ ≫ eW.inv →
            ∃ (P : PresentedEtaleChart B S hS Y) (σ : ContinuousHom P.system E)
              (ρ : ContinuousHom D P.system),
              a ≫ f = (eU.hom ≫ formalSpectrumMap P.weaklyAdmissible σ) ≫ P.chart ∧
                P.chart ≫ g = (formalSpectrumMap hA ρ ≫ eW.inv) ≫ c ∧
                φ.toRingHom = σ.toRingHom.comp ρ.toRingHom

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end AlgebraicGeometry.FormalSpace

end
