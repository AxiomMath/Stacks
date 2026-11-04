module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.NormalMorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Section
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Statements of the inputs to the Stacks 057K chain

The four results `057I`, `055W`, `057J`, `057K` of the Stacks Project sit on top of three
results that are not yet available: Tag `0570` (a Cohen–Macaulay point closed in its fibre has
a regular immersed quasi-finite slice), Tag `055P` (the locus of fibrewise connected components
along a section is locally constructible) and Tag `055R` (that locus is open for a flat family
with geometrically reduced fibres).

This file writes those three statements down, and the statements of `057I`, `055W` and `057J`
themselves, as `Prop`-valued abbreviations. The proofs in this directory then take the
statements they still lack as explicit hypotheses of exactly this shape, so that each becomes a
one-line application once the corresponding result is proved.

## Main definitions

* `AlgebraicGeometry.Statement0570`, `AlgebraicGeometry.Statement055P`,
  `AlgebraicGeometry.Statement055R`: the three missing inputs.
* `AlgebraicGeometry.Statement057I`, `AlgebraicGeometry.Statement055W`,
  `AlgebraicGeometry.Statement057J`: the three intermediate conclusions of the chain, proved
  conditionally in this directory.

## Implementation notes

The binders are the ones the Stacks statements use, including the instance-implicit ones, so
that a theorem of the corresponding shape discharges a hypothesis by `exact`. Each abbreviation
is a single universe-polymorphic `Prop`; the universe variable is the one of the schemes
involved.

## References

* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
* [Stacks Project, Tag 055P](https://stacks.math.columbia.edu/tag/055P)
* [Stacks Project, Tag 055R](https://stacks.math.columbia.edu/tag/055R)
* [Stacks Project, Tag 057I](https://stacks.math.columbia.edu/tag/057I)
* [Stacks Project, Tag 055W](https://stacks.math.columbia.edu/tag/055W)
* [Stacks Project, Tag 057J](https://stacks.math.columbia.edu/tag/057J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms Topology

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0570.** A Cohen–Macaulay point of a locally finitely presented
morphism which is closed in its fibre admits a regularly immersed slice through it which is
flat, locally of finite presentation and locally quasi-finite over the base, and whose fibre
over the image point is the single given point. -/
abbrev Statement0570 : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X),
    (∃ hf : ∀ y : S, IsLocallyNoetherian (f.fiber y), Scheme.Hom.IsCohenMacaulayAt f hf x) →
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) →
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : Z) (hi : IsImmersion i),
      letI := hi
      i z = x ∧ Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i ∧
        Flat (i ≫ f) ∧ LocallyOfFinitePresentation (i ≫ f) ∧
        LocallyQuasiFinite (i ≫ f) ∧
        {z' : Z | (i ≫ f) z' = f x} = {z}

/-- **Stacks Project, Tag 055P.** For a morphism of finite presentation with a specified
section, the union of the connected components of the fibres containing the section is locally
constructible in the source. -/
abbrev Statement055P : Prop :=
  ∀ (D : ConnectedAlongSection.{u}) [LocallyOfFinitePresentation D.f] [QuasiCompact D.f]
    [QuasiSeparated D.f], IsLocallyConstructible D.locus

/-- **Stacks Project, Tag 055R.** For a flat morphism of finite presentation with geometrically
reduced fibres and a specified section, the union of the fibrewise connected components
containing that section is open in the source. -/
abbrev Statement055R : Prop :=
  ∀ (D : ConnectedAlongSection.{u}), FinitePresentation D.f →
    ∀ [Flat D.f] [GeometricallyReduced D.f], IsOpen D.locus

/-- **Stacks Project, Tag 057I.** A geometrically connected fibre in a flat, finitely presented
family with geometrically reduced fibres and a nonempty finite locally free multisection has a
quasi-compact open neighbourhood in the source whose nonempty fibres are geometrically
connected. -/
abbrev Statement057I : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (σ : Z ⟶ X), σ ≫ f = g → ∀ (y : Y),
    FinitePresentation f → ∀ [Flat f] [IsFiniteLocallyFree g], Nonempty (g.fiber y) →
    (∀ y' : Y, GeometricallyReduced (f.fiberToSpecResidueField y')) →
    GeometricallyConnected (f.fiberToSpecResidueField y) →
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ (f.fiberι y ⁻¹ᵁ U = ⊤ ∧
      ∀ y' : Y, Nonempty ((U.ι ≫ f).fiber y') →
        GeometricallyConnected ((U.ι ≫ f).fiberToSpecResidueField y'))

/-- **Stacks Project, Tag 055W.** A geometrically connected open in a fibre of a flat, finitely
presented morphism with geometrically reduced fibres spreads, after an affine elementary étale
base change, to a quasi-compact open with geometrically connected fibres. -/
abbrev Statement055W : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (T : (f.fiber s).Opens),
    FinitePresentation f → ∀ [Flat f] [GeometricallyReduced f]
      [GeometricallyConnected (T.ι ≫ f.fiberToSpecResidueField s)],
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary) (_ : IsAffine U.scheme)
      (V : (pullback f U.toBase).Opens),
      QuasiCompact V.ι ∧ GeometricallyConnected (V.ι ≫ pullback.snd f U.toBase) ∧
      ∀ x : (pullback.snd f U.toBase).fiber U.point,
        ((pullback.snd f U.toBase).fiberι U.point x ∈ V) ↔
          pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point x) ∈
            f.fiberι s '' (T : Set (f.fiber s))

/-- **Stacks Project, Tag 057J.** A geometrically irreducible open in a fibre of a normal,
finitely presented morphism spreads, after an affine elementary étale base change, to a
quasi-compact open with geometrically integral fibres. -/
abbrev Statement057J : Prop :=
  ∀ {Y S : Scheme.{u}} (h : Y ⟶ S) (s : S) (T : (h.fiber s).Opens),
    FinitePresentation h → Scheme.Hom.IsNormal h →
    ∀ [GeometricallyIrreducible (T.ι ≫ h.fiberToSpecResidueField s)],
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary) (_ : IsAffine U.scheme)
      (V : (pullback h U.toBase).Opens),
      QuasiCompact V.ι ∧ GeometricallyIntegral (V.ι ≫ pullback.snd h U.toBase) ∧
      ∀ x : (pullback.snd h U.toBase).fiber U.point,
        ((pullback.snd h U.toBase).fiberι U.point x ∈ V) ↔
          pullback.fst h U.toBase ((pullback.snd h U.toBase).fiberι U.point x) ∈
            h.fiberι s '' (T : Set (h.fiber s))

end AlgebraicGeometry

end
