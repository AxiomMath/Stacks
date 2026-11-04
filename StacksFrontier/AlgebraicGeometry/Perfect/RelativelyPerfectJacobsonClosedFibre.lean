module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonSpecialization
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Relative perfectness over a ring, from the fibre over a Jacobson-radical ideal

Let `(R, I)` be a ring with an ideal contained in its Jacobson radical, write `S = Spec R` and
`S₀ = Spec (R/I)`, and let `f : X ⟶ S` be proper, flat and locally of finite presentation. Write
`X₀ = S₀ ×_S X`. Stacks 0DJZ says that a pseudo-coherent object `E` of `D(𝒪_X)` whose derived
restriction to `X₀` is `S₀`-perfect is itself `S`-perfect.

This module states that lemma at the scheme level, in the vocabulary the rest of this directory
uses: relative perfectness is `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` of Stacks 0DI0,
and the derived restriction is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` along the projection
`X₀ ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.closedBase`, `closedFibreToBase`, `closedFibreToTotal`: the three
  morphisms of the square, namely `S₀ ⟶ S`, `X₀ ⟶ S₀` and `X₀ ⟶ X`.
* `AlgebraicGeometry.Scheme.Hom.LocallyFiniteTorDimensionFromClosedFibre`: **the Tor clause of
  Stacks 0DJZ, as a predicate on two families of certificates.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre`:
  Stacks 0DJZ with the Tor clause carried.
* `AlgebraicGeometry.Scheme.Hom.exists_specializes_mem_range_closedFibreToTotal`: the
  specialization step of the source's proof, read on the closed fibre of this square.

## The two conjuncts of the conclusion

Relative perfectness (Stacks 0DI0) is the conjunction of pseudo-coherence and locally finite Tor
dimension over `f^{-1}𝒪_S`. The pseudo-coherence conjunct of the conclusion of Stacks 0DJZ is the
hypothesis on `E`. The Tor conjunct is `LocallyFiniteTorDimensionFromClosedFibre`; the
specialization step it consumes is
`AlgebraicGeometry.exists_specializes_mem_range_pullback_snd_quotientMk`.

Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`,
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent`.

## Implementation notes

The family of derived tensor products is a parameter of `IsPerfectRelativeTo`, because part (3)
of Stacks 08CG restricts to an open covering; two families appear here, one on the inverse-image
ringed space of `f` and one on that of the closed-fibre projection `f₀`. They are top-level
binders of both declarations below and are **not** quantified over inside
`LocallyFiniteTorDimensionFromClosedFibre`: quantifying them there would make the carried
hypothesis ask for the bound at every family, including the degenerate
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` at which the
sibling Stacks 0DI5 is false, and so would risk a hypothesis nothing satisfies.

Flatness and local finite presentation of the closed-fibre projection are **not** hypotheses:
both properties are stable under base change, and instance search supplies them from `[Flat f]`
and `[LocallyOfFinitePresentation f]`. Properness of `f` is taken as `IsProper`, the source's own
hypothesis, although only the universal closedness inside it is used.

Everything here lives in one derived-category model: `CategoryTheory.HasDerivedCategory.standard`
is seated as a local instance, and `IsPerfectRelativeTo` for `f`, `IsPerfectRelativeTo` for the
closed-fibre projection, and the derived pullback along `X₀ ⟶ X` all elaborate at
`StrictlyPerfect.OXMod.{u, u}` with certificates at
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}`. No comparison between
two models is needed to state the lemma, and none is written.

## References

* [Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.35.6 (0DI5)](https://stacks.math.columbia.edu/tag/0DI5)
* [Stacks Project, Lemma 37.71.2 (0DJY)](https://stacks.math.columbia.edu/tag/0DJY)
* [Stacks Project, Lemma 76.54.5 (0DL5)](https://stacks.math.columbia.edu/tag/0DL5)
* [Stacks Project, Lemma 15.85.9 (0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
* [Stacks Project, Lemma 20.48.8 (09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (I : Ideal R)

/-- The closed immersion `S₀ = Spec (R/I) ⟶ S = Spec R`. -/
public abbrev closedBase : Spec (CommRingCat.of (R ⧸ I)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The structure morphism `X₀ = S₀ ×_S X ⟶ S₀` of the closed fibre. -/
public abbrev closedFibreToBase :
    pullback (closedBase I) f ⟶ Spec (CommRingCat.of (R ⧸ I)) :=
  pullback.fst _ _

/-- The projection `X₀ = S₀ ×_S X ⟶ X`, along which the derived restriction is taken. -/
public abbrev closedFibreToTotal : pullback (closedBase I) f ⟶ X :=
  pullback.snd _ _

/-- **The specialization step of Stacks 0DJZ, on this square.** For `f` universally closed and
`I` inside the Jacobson radical of `R`, every point of `X` specializes to a point in the image of
`X₀ ⟶ X`.

This is `AlgebraicGeometry.exists_specializes_mem_range_pullback_snd_quotientMk` with the
projection spelled `closedFibreToTotal`; it is restated so that the hypothesis of
`LocallyFiniteTorDimensionFromClosedFibre` below is visibly the same statement. -/
public theorem exists_specializes_mem_range_closedFibreToTotal [UniversallyClosed f]
    (hI : I ≤ (⊥ : Ideal R).jacobson) (x : X) :
    ∃ x₀ : X, x ⤳ x₀ ∧ x₀ ∈ Set.range (closedFibreToTotal f I).base :=
  exists_specializes_mem_range_pullback_snd_quotientMk f hI x

/-- **The Tor clause of Stacks 0DJZ**, as a predicate on the two families of certificates.

Everything the source's proof does after its specialization step: given a pseudo-coherent `E`
whose derived restriction to the closed fibre is `S₀`-perfect, and given that every point of `X`
specializes into the closed fibre, the derived restriction of scalars of `E` along
`f^{-1}𝒪_S ⟶ 𝒪_X` locally has finite Tor dimension.

The specialization conclusion is written out as the third hypothesis rather than derived from
properness, so that the predicate says exactly what remains to be proved once
`exists_specializes_mem_range_closedFibreToTotal` has been applied, and so that it carries no
hypothesis on `f` beyond the two the definition of relative perfectness already needs. -/
public def LocallyFiniteTorDimensionFromClosedFibre [Flat f] [LocallyOfFinitePresentation f]
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).restrict
          U.isOpenEmbedding))
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding)) : Prop :=
  ∀ E : DerivedCategory (OXMod.{u, u} X.toRingedSpace),
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E →
      (closedFibreToBase f I).IsPerfectRelativeTo D₀
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (closedFibreToTotal f I).toLRSHom.toShHom).obj E) →
        (∀ x : X, ∃ x₀ : X, x ⤳ x₀ ∧ x₀ ∈ Set.range (closedFibreToTotal f I).base) →
          RingedSpace.LocallyHasFiniteTorDimension
            (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base) D
            ((derivedScalarRestriction f).obj E)

/-- **Stacks 0DJZ, with the Tor clause carried.** Let `R` be a ring, let `I` be an ideal contained
in the Jacobson radical of `R`, let `f : X ⟶ Spec R` be proper, flat and locally of finite
presentation, and let `X₀ = Spec (R/I) ×_{Spec R} X`. If `E` is a pseudo-coherent object of
`D(𝒪_X)` whose derived restriction to `X₀` is `Spec (R/I)`-perfect, then `E` is
`Spec R`-perfect.

Both conjuncts of the conclusion are supplied: the pseudo-coherence conjunct is the hypothesis
`hE`, and the Tor conjunct is `hTor` applied to the specialization step, which is where
properness and the Jacobson-radical hypothesis are consumed.

Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`,
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent`. -/
public theorem isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (hI : I ≤ (⊥ : Ideal R).jacobson)
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).restrict
          U.isOpenEmbedding))
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (hTor : LocallyFiniteTorDimensionFromClosedFibre f I D D₀)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE₀ : (closedFibreToBase f I).IsPerfectRelativeTo D₀
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (closedFibreToTotal f I).toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo D E :=
  ⟨hE, hTor E hE hE₀ fun x => exists_specializes_mem_range_closedFibreToTotal f I hI x⟩

end AlgebraicGeometry.Scheme.Hom

end
