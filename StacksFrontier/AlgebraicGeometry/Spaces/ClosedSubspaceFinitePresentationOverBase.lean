module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Finite presentation of a closed subspace over a base, against its closed immersion

Let `p : X ⟶ T` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
of finite presentation, and let `i : Z ⟶ X` be a closed immersion.  This file proves that the
composite `Z ⟶ T` is of finite presentation exactly when `i` is.

Both directions are instances of permanence properties already in the library.  The direction
that builds the composite is the composition of morphisms of finite presentation, which is the
conjunction of Stacks 03XQ for the local condition, Stacks 03HG for quasi-compactness and
Stacks 03KQ for quasi-separatedness.  The direction that cancels `p` off the composite is
Stacks 05WT, cancellation of local finite presentation against local finite type, followed by
the observation that for a closed immersion the two remaining conjuncts of finite presentation
are automatic.

This is the geometric half of the dictionary used by Stacks 0D00 to identify the Hilbert functor
of `X/B` with the Quot functor of `𝒪_X/X/B`: a family classified by the Hilbert functor is a
closed subspace `Z ⊆ X_T` of finite presentation over `T`, and the quotient of `𝒪_{X_T}` it
determines is read off from the closed immersion `i`, so the two finiteness conditions have to
be compared.  The module half — finite presentation of `i_*𝒪_Z` as an `𝒪_{X_T}`-module — is
`AlgebraicGeometry.Space.isFinitePresentationOnSite_pushforwardStructureSheaf`
of `StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceQuotientFinitePresentation.lean`.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_of_comp_of_isClosedImmersion`: a closed immersion
  whose composite with a morphism locally of finite type is of finite presentation is itself of
  finite presentation.
* `AlgebraicGeometry.Space.isFinitePresentation_comp_iff_of_isClosedImmersion`: for a closed
  immersion `i : Z ⟶ X` over a morphism `p : X ⟶ T` of finite presentation, `Z ⟶ T` is of finite
  presentation if and only if `i` is.

## Implementation notes

No tag attribute is placed.  The two permanence statements this file combines belong to
Stacks 03XQ and Stacks 05WT, both of Chapter 67, and both are already registered in the library
— the first on `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_comp` and its sibling
`AlgebraicGeometry.Space.isFinitePresentation_comp`, the second deliberately untagged with an
ownership note on `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_comp`.  What is
proved here is their combination at a closed immersion, which is an input to other tags rather
than a clause of either, so it is left untagged as well, following the convention of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceQuotientQuasicoherent.lean`.

The composition direction does not use the closed immersion hypothesis: it is the composition
of morphisms of finite presentation, spelled out as the triple of its three conjuncts rather
than invoked by name, so that this file does not have to import the module carrying the packaged
form.

Statements are given for morphisms of presheaves on the big fppf site of `S` together with
explicit algebraicity hypotheses, which is the form in which the Hilbert functor of Stacks 0CZY
records the structure morphism `Z.ι ≫ pullback.snd` of a family.  The one input stated for the
bundled category of algebraic spaces,
`AlgebraicGeometry.Space.isFinitePresentation_iff_isLocallyOfFinitePresentation`, is applied
through `CategoryTheory.ObjectProperty.homMk`.

## References

* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed immersion whose composite with a morphism locally of finite type is of finite
presentation is itself of finite presentation.**

Local finite presentation of `i` is Stacks 05WT, cancellation of local finite presentation
against local finite type, and the two remaining conjuncts of finite presentation hold for every
closed immersion by
`AlgebraicGeometry.Space.isFinitePresentation_iff_isLocallyOfFinitePresentation`. -/
theorem isFinitePresentation_of_comp_of_isClosedImmersion
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (i : F ⟶ G) (p : G ⟶ H)
    (hi : IsClosedImmersion B S hS i) (hp : IsLocallyOfFiniteType B S hS p)
    (hip : IsFinitePresentation B S hS (i ≫ p)) :
    IsFinitePresentation B S hS i :=
  (isFinitePresentation_iff_isLocallyOfFinitePresentation B S hS
    (ObjectProperty.homMk i : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) hi).mpr
    (isLocallyOfFinitePresentation_of_comp B S hS hF hG hH i p hip.1 hp)

/-- **For a closed immersion over a base morphism of finite presentation, finite presentation of
the composite is finite presentation of the immersion.**  Let `p : X ⟶ T` be a morphism of
algebraic spaces over `S` of finite presentation and let `i : Z ⟶ X` be a closed immersion.
Then `Z ⟶ T` is of finite presentation if and only if `i` is.

The forward direction is
`AlgebraicGeometry.Space.isFinitePresentation_of_comp_of_isClosedImmersion`,
which is Stacks 05WT at a closed immersion; the local finite type of `p` it consumes comes from
local finite presentation of `p` by Stacks 0464.  The backward direction is the composition of
morphisms of finite presentation: Stacks 03XQ for the local condition, Stacks 03HG for
quasi-compactness and Stacks 03KQ for quasi-separatedness.

This is the geometric half of the dictionary of Stacks 0D00 between a family classified by the
Hilbert functor of `X/B` and the quotient of `𝒪_{X_T}` it determines. -/
theorem isFinitePresentation_comp_iff_of_isClosedImmersion
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (i : F ⟶ G) (p : G ⟶ H)
    (hi : IsClosedImmersion B S hS i) (hp : IsFinitePresentation B S hS p) :
    IsFinitePresentation B S hS (i ≫ p) ↔ IsFinitePresentation B S hS i := by
  refine ⟨isFinitePresentation_of_comp_of_isClosedImmersion B S hS hF hG hH i p hi
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hp.1), fun hifp ↦ ?_⟩
  exact ⟨isLocallyOfFinitePresentation_comp B S hS hF hG hH i p hifp.1 hp.1,
    isQuasiCompact_comp B S hS hG hH i p hifp.2.1 hp.2.1,
    isQuasiSeparated_comp B S hS hF hG i p hifp.2.2 hp.2.2⟩

end AlgebraicGeometry.Space

end
