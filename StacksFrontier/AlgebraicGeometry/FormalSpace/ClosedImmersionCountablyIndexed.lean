module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful

/-!
# Closed immersions into countably indexed affine formal algebraic spaces

Let `S` be a scheme, let `X` be a countably indexed affine formal algebraic space over `S` and
let `f : Y ⟶ X` be a closed immersion of formal algebraic spaces over `S`. **Stacks 0AQI**
asserts two things: that `Y` is again a countably indexed affine formal algebraic space, and
that `f` corresponds to `A ⟶ A/K` for `A` an object of `WAdm^count` — a weakly admissible
topological ring with a countable fundamental system of neighbourhoods of `0`, the subcategory
of Section 0ANA — and `K ⊆ A` a closed ideal.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexedAffine_of_isClosedImmersion`:
  **Stacks 0AQI**, the first conclusion.
* `AlgebraicGeometry.FormalSpace.exists_spfPresentation_continuousHom_of_isClosedImmersion`:
  **Stacks 0AQI**, the part of the second conclusion saying that `f` corresponds to a
  continuous homomorphism of objects of `WAdm^count`.
* `AlgebraicGeometry.FormalSpace.isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion`:
  **Stacks 0AQI**, the remaining part of the second conclusion — that this homomorphism
  presents its target as the quotient of `A` by a closed ideal — under the tautness hypothesis
  discussed below.

## Implementation notes

The first conclusion is the source's argument verbatim. A closed immersion of fppf sheaves is
representable and affine, so the affineness and the countable indexing of the source are the two
parts of **Stacks 0AKP**, `AlgebraicGeometry.isAffineFormalAlgebraicSpace_of_affine` and
`AlgebraicGeometry.isCountablyIndexed_of_affine`. No hypothesis that `Y` is a formal algebraic
space is needed, and none is made: being a closed immersion already forces representability by
algebraic spaces, so the statement is proved for an arbitrary morphism of fppf sheaves into a
countably indexed affine formal algebraic space. That is a generalisation of the source's
statement, not a weakening of it. The step from being a closed immersion to the relative
affineness that Stacks 0AKP asks for is available only privately in
`StacksFrontier/AlgebraicGeometry/FormalSpace/ClosedImmersionMcQuillan.lean`, so it is reproved
here, in the form taking the closed-immersion predicate of Stacks 0ANP rather than its
sheafified-Yoneda reformulation.

The second conclusion splits in two. That `f` corresponds to a continuous homomorphism of
objects of `WAdm^count` combines the first conclusion with **Stacks 0AN1** — the equivalence of
being a countably indexed affine formal algebraic space with being `Spf A` for an object `A` of
`WAdm^count`,
`AlgebraicGeometry.FormalSpace.hasCountableWeakPresentation_of_isCountablyIndexedAffine` —
and with the full faithfulness of `Spf`, **Stacks 0AN0**,
`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`; both source and
target of `f` are identified with formal spectra, and the resulting morphism of formal spectra
is again a closed immersion because being a closed immersion is stable under base change and an
isomorphism square is cartesian.

That the homomorphism `A ⟶ C` so obtained presents `C` as `A/K` for a closed ideal `K` is
**Stacks 0APT** applied to it: `A` is complete with a countable fundamental system of
neighbourhoods of `0` because it is an object of `WAdm^count`, `C` is separated because it is
weakly admissible, the homomorphism has dense image by the dense-image clause of **Stacks 0ANQ**
(`AlgebraicGeometry.FormalSpace.denseRange_of_isClosedImmersion_formalSpectrumMap`), and `K` is the
kernel, closed by continuity. Stacks 0APT needs one further input, the *tautness* of the
homomorphism, which in the source is supplied by the implication (1) ⟹ (3) of **Stacks 0AN5**:
`Spf φ` representable by algebraic spaces implies `φ` taut. This library carries only the converse
direction of Stacks 0AN5 — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalSpace/SpectrumFullyFaithful.lean`, and
`AlgebraicGeometry.FormalSpace.exists_isPullback_formalSpectrumMap_of_factorsThroughStage` for the
step of (3) ⟹ (2) that it does carry — so tautness is carried here as an explicit hypothesis
standing for that absent implication, and the statements that use it are labelled accordingly.
Nothing else of Stacks 0AQI is hypothesised.

## References

* [Stacks Project, Tag 0AQI](https://stacks.math.columbia.edu/tag/0AQI)
* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANQ](https://stacks.math.columbia.edu/tag/0ANQ)
* [Stacks Project, Tag 0APT](https://stacks.math.columbia.edu/tag/0APT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section CountablyIndexed

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A closed immersion of fppf sheaves is representable and affine: a closed immersion of
schemes is affine, and the relative property only has to be compared stage by stage. -/
private theorem relative_isAffineHom_of_isClosedImmersion {X Y : FppfSheaf B S hS} (f : Y ⟶ X)
    (hf : IsClosedImmersion B S hS f) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f := by
  have hle : MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) := by
    intro U V g hg
    change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g) at hg
    show IsAffineHom ((BigFppfOver.toScheme B S hS).map g)
    exact (isClosedImmersion_iff_isAffineHom.mp hg).1
  exact MorphismProperty.relative_monotone
    (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) hle f
    (isClosedImmersionInto_of_isClosedImmersion B S hS f hf)

/-- **Stacks 0AQI**, the first conclusion. The source of a closed immersion of fppf sheaves over
`S` whose target is a countably indexed affine formal algebraic space is again a countably
indexed affine formal algebraic space. -/
@[stacks 0AQI "that Y is a countably indexed affine formal algebraic space"]
theorem isCountablyIndexedAffine_of_isClosedImmersion {X Y : FppfSheaf B S hS}
    (hX : IsCountablyIndexedAffine B S hS X) (f : Y ⟶ X)
    (hf : IsClosedImmersion B S hS f) :
    IsCountablyIndexedAffine B S hS Y :=
  ⟨AlgebraicGeometry.isAffineFormalAlgebraicSpace_of_affine B S hS f hX.1
      (relative_isAffineHom_of_isClosedImmersion B S hS f hf),
    AlgebraicGeometry.isCountablyIndexed_of_affine B S hS f
      (relative_isAffineHom_of_isClosedImmersion B S hS f hf) hX.2⟩

end CountablyIndexed

section Correspondence

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Conjugating a closed immersion of fppf sheaves by isomorphisms of its source and target
leaves a closed immersion: the conjugate is a base change of the original along an isomorphism,
and an isomorphism square is cartesian. -/
private theorem isClosedImmersion_conj_iso {X X' Y Y' : FppfSheaf B S hS} (f : Y ⟶ X)
    (eX : X ≅ X') (eY : Y ≅ Y') (hf : IsClosedImmersion B S hS f) :
    IsClosedImmersion B S hS (eY.inv ≫ f ≫ eX.hom) :=
  isClosedImmersion_of_isPullback B S hS
    (IsPullback.of_horiz_isIso (fst := eY.inv) (snd := eY.inv ≫ f ≫ eX.hom) (f := f)
      (g := eX.inv) ⟨by simp⟩) hf

attribute [local instance] sheaf_hasColimits

/-- **Stacks 0AQI**, the correspondence part of the second conclusion. A closed immersion
`f : Y ⟶ X` of fppf sheaves over `S` whose target is a countably indexed affine formal
algebraic space is, after identifying `X` with `Spf A` and `Y` with `Spf C` for objects `A` and
`C` of `WAdm^count`, the formal spectrum of a continuous homomorphism `A ⟶ C` over `S`, itself
again a closed immersion. -/
@[stacks 0AQI "that f corresponds to a morphism of WAdm^count"]
theorem exists_spfPresentation_continuousHom_of_isClosedImmersion {X Y : FppfSheaf B S hS}
    (hX : IsCountablyIndexedAffine B S hS X) (f : Y ⟶ X)
    (hf : IsClosedImmersion B S hS f) :
    ∃ (P : SpfPresentation B S hS X) (Q : SpfPresentation B S hS Y)
      (hA : TopologicalRing.IsWeaklyAdmissible P.ring),
      (nhds (0 : P.ring)).IsCountablyGenerated ∧
      TopologicalRing.IsWeaklyAdmissible Q.ring ∧
      (nhds (0 : Q.ring)).IsCountablyGenerated ∧
      ∃ (eX : X ≅ formalSpectrum P.system) (eY : Y ≅ formalSpectrum Q.system)
        (g : ContinuousHom P.system Q.system),
        IsClosedImmersion B S hS (formalSpectrumMap hA g) ∧
          f = eY.hom ≫ formalSpectrumMap hA g ≫ eX.inv := by
  obtain ⟨P, hA, hcountA⟩ :=
    hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS X hX
  obtain ⟨Q, hC, hcountC⟩ :=
    hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS Y
      (isCountablyIndexedAffine_of_isClosedImmersion B S hS hX f hf)
  obtain ⟨eX⟩ := P.iso
  obtain ⟨eY⟩ := Q.iso
  obtain ⟨g, hg, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hA hC (eY.inv ≫ f ≫ eX.hom)
  refine ⟨P, Q, hA, hcountA, hC, hcountC, eX, eY, g, ?_, ?_⟩
  · rw [hg]
    exact isClosedImmersion_conj_iso f eX eY hf
  · rw [hg]
    simp

end Correspondence

section Quotient

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- **Stacks 0AQI**, the quotient part of the second conclusion. Let `A` be an object of
`WAdm^count`, that is, a weakly admissible topological ring over `S` with a countable
fundamental system of neighbourhoods of `0`, let `C` be weakly admissible, and let
`g : A ⟶ C` be a continuous homomorphism over `S` whose formal spectrum is a closed immersion.
If `g` is taut, then `K = ker g` is a closed ideal of `A` and `g` identifies `A/K` with `C`
topologically, so the closed immersion is `Spf` of `A ⟶ A/K`.

Tautness is the one hypothesis not proved here: it is the implication (1) ⟹ (3) of
**Stacks 0AN5**, which this library does not carry. Everything else is proved. -/
@[stacks 0AQI "the quotient by a closed ideal, given the tautness of Stacks 0AN5"]
theorem isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hC : TopologicalRing.IsWeaklyAdmissible C)
    (hcount : (nhds (0 : A)).IsCountablyGenerated)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} (g : ContinuousHom D E)
    (hg : IsClosedImmersion B S hS (formalSpectrumMap hA g))
    (htaut : RingHom.IsTaut g.toRingHom) :
    IsClosed (RingHom.ker g.toRingHom : Set A) ∧
      ∃ e : (A ⧸ RingHom.ker g.toRingHom) ≃+* C,
        (∀ a : A, e (Ideal.Quotient.mk (RingHom.ker g.toRingHom) a) = g.toRingHom a) ∧
          IsHomeomorph e := by
  let _ : T2Space A := hA.2.2
  let _ : T2Space C := hC.2.2
  refine ⟨RingHom.isClosed_ker_of_continuous g.toRingHom g.continuous, ?_⟩
  exact RingHom.quotientKerEquiv_of_isTaut_of_denseRange g.toRingHom g.continuous hA.2.1
    hcount htaut (denseRange_of_isClosedImmersion_formalSpectrumMap hA hC g hg)

end Quotient

section Combined

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] sheaf_hasColimits

/-- **Stacks 0AQI** in full, given the implication (1) ⟹ (3) of **Stacks 0AN5** as the
hypothesis `hAN5`. Let `X` be a countably indexed affine formal algebraic space over `S` and
let `f : Y ⟶ X` be a closed immersion of fppf sheaves over `S`. Then `Y` is a countably indexed
affine formal algebraic space, and `f` is `Spf` of a continuous homomorphism `g : A ⟶ C` of
objects of `WAdm^count` whose kernel `K` is a closed ideal of `A` and which identifies `A/K`
with `C` topologically; that is, `f` corresponds to `A ⟶ A/K`.

The hypothesis `hAN5` is exactly the implication of Stacks 0AN5 that a continuous homomorphism
of weakly admissible topological rings over `S` whose formal spectrum is a closed immersion —
hence representable by algebraic spaces — is taut. It is the one input this library does not
carry; the unconditional halves of the lemma are
`AlgebraicGeometry.FormalSpace.isCountablyIndexedAffine_of_isClosedImmersion` and
`AlgebraicGeometry.FormalSpace.exists_spfPresentation_continuousHom_of_isClosedImmersion`. -/
@[stacks 0AQI "given the tautness of Stacks 0AN5"]
theorem isCountablyIndexedAffine_and_exists_closedIdealQuotient_of_isClosedImmersion
    (hAN5 : ∀ {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
      [IsLinearTopology C C] (hA : TopologicalRing.IsWeaklyAdmissible A)
      (_hC : TopologicalRing.IsWeaklyAdmissible C)
      {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} (g : ContinuousHom D E),
      IsClosedImmersion B S hS (formalSpectrumMap hA g) → RingHom.IsTaut g.toRingHom)
    {X Y : FppfSheaf B S hS} (hX : IsCountablyIndexedAffine B S hS X) (f : Y ⟶ X)
    (hf : IsClosedImmersion B S hS f) :
    IsCountablyIndexedAffine B S hS Y ∧
      ∃ (P : SpfPresentation B S hS X) (Q : SpfPresentation B S hS Y)
        (hA : TopologicalRing.IsWeaklyAdmissible P.ring),
        (nhds (0 : P.ring)).IsCountablyGenerated ∧
        TopologicalRing.IsWeaklyAdmissible Q.ring ∧
        ∃ (eX : X ≅ formalSpectrum P.system) (eY : Y ≅ formalSpectrum Q.system)
          (g : ContinuousHom P.system Q.system),
          IsClosed (RingHom.ker g.toRingHom : Set P.ring) ∧
          (∃ e : (P.ring ⧸ RingHom.ker g.toRingHom) ≃+* Q.ring,
            (∀ a : P.ring,
              e (Ideal.Quotient.mk (RingHom.ker g.toRingHom) a) = g.toRingHom a) ∧
            IsHomeomorph e) ∧
          f = eY.hom ≫ formalSpectrumMap hA g ≫ eX.inv := by
  obtain ⟨P, Q, hA, hcountA, hC, -, eX, eY, g, hgci, hfg⟩ :=
    exists_spfPresentation_continuousHom_of_isClosedImmersion hX f hf
  obtain ⟨hker, hquot⟩ :=
    isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion hA hC hcountA g hgci
      (hAN5 hA hC g hgci)
  exact ⟨isCountablyIndexedAffine_of_isClosedImmersion B S hS hX f hf,
    P, Q, hA, hcountA, hC, eX, eY, g, hker, hquot, hfg⟩

end Combined

end AlgebraicGeometry.FormalSpace

end
