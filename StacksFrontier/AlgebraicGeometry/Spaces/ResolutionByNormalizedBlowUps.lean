module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Regular
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Resolution of singularities by normalized blowups

A two-dimensional Noetherian integral algebraic space `Y` over a scheme `S` *has a resolution
of singularities by normalized blowups* when there is a finite sequence

`Yₙ ⟶ Yₙ₋₁ ⟶ … ⟶ Y₁ ⟶ Y₀ ⟶ Y`

of algebraic spaces over `S` in which every `Yᵢ` is proper over `Y`, the morphism `Y₀ ⟶ Y` is
the normalization of `Y`, each later morphism `Yᵢ ⟶ Yᵢ₋₁` is the normalization of a blowing up
at a closed point, and `Yₙ` is regular.

## Main definitions

* `AlgebraicGeometry.Space.IsNormalizationOfBlowupAtClosedPoint` is the property of a morphism
  of algebraic spaces of being the normalization of the blowing up of its target at a closed
  point.
* `AlgebraicGeometry.Space.NormalizedBlowUpChain` is the sequence above, indexed by its top
  member and by the composite morphism from that member down to `Y`.
* `AlgebraicGeometry.Space.HasResolutionByNormalizedBlowUps` asserts that such a sequence
  exists with regular top member.

## Main results

There are no results in this file; all declarations are definitions.

## Implementation notes

The source displays the sequence as `Yₙ → Xₙ₋₁ → … → Y₁ → Y₀ → Y`; the symbol `Xₙ₋₁` is a
misprint for `Yₙ₋₁`, since clauses (1)–(3) speak only of the spaces `Yᵢ` and of the morphisms
`Yᵢ ⟶ Yᵢ₋₁`.

Finiteness of the sequence is expressed by the inductive type
`AlgebraicGeometry.Space.NormalizedBlowUpChain`, whose base constructor is the normalization
of `Y` and whose step constructor extends a sequence by one normalized blowing up. Each
constructor carries properness of the composite morphism down to `Y`, so clause (1) holds at
every member of the sequence, and the composite itself is an index of the type rather than a
separate family of morphisms.

The members of the sequence are objects of the category of algebraic spaces
`AlgebraicGeometry.Space.AlgebraicSpaces` of Stacks 02X2 rather than presheaves carrying
algebraicity witnesses, so that the morphisms of the sequence compose in that category and
the composite down to `Y` is the evident one; properness and regularity, which are stated for
presheaves, are applied to the underlying presheaf and the underlying morphism.

The normalization of a blowing up at a closed point is
`AlgebraicGeometry.Space.IsNormalizationOfBlowupAtClosedPoint`, the composition of
`AlgebraicGeometry.Space.IsBlowupAtClosedPoint` of Stacks 0BHE with
`AlgebraicGeometry.Space.NormalizationData`; existence of normalization data is the content of
Stacks 07U4, and normalization is unique up to a unique isomorphism over its base, so the
isomorphism identifying the source of the morphism with the normalization is harmless. This
is the notion that Stacks 0BHJ names; it is deliberately left untagged here, that tag being
formalized separately, and this definition should be replaced by that formalization.

Regularity of the last member is the étale-local scheme property
`AlgebraicGeometry.IsRegular` through `AlgebraicGeometry.Space.HasEtaleLocalProperty`, as in
`AlgebraicGeometry.Space.IsResolutionOfSingularities`: an algebraic space is regular when it
admits a surjective étale atlas by a regular scheme.

Two-dimensionality, Noetherianity and integrality of `Y` are standing assumptions of the
source, so they are hypotheses of the predicate which its body does not consume.

## References

* [Stacks Project, Tag 0BHX](https://stacks.math.columbia.edu/tag/0BHX)
* [Stacks Project, Tag 0BHJ](https://stacks.math.columbia.edu/tag/0BHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A morphism `f : X'' ⟶ X` of algebraic spaces over `S` *is the normalization of the blowing
up of `X` at the closed point `x`* when it factors as the normalization of a blowing up of `X`
at `x`, that is, when there are a blowing up `b : X' ⟶ X` of `X` at `x` and normalization data
for `X'` whose normalization morphism followed by `b` is `f`. -/
def IsNormalizationOfBlowupAtClosedPoint {X X'' : AlgebraicSpaces B S hS}
    (x : points B S hS X.obj) (hx : IsClosed ({x} : Set (points B S hS X.obj)))
    (f : X'' ⟶ X) : Prop :=
  ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X),
    IsBlowupAtClosedPoint B S hS x hx b ∧
      ∃ (D : NormalizationData B S hS X'.obj) (e : X''.obj ≅ D.space),
        f.hom = e.hom ≫ D.hom ≫ b.hom

/-- A finite sequence `Yₙ ⟶ … ⟶ Y₀ ⟶ Y` of algebraic spaces over `S` which starts at the
normalization of `Y` and continues through normalizations of blowing ups at closed points,
each member being proper over `Y`. The sequence is indexed by its top member and by the
composite morphism from that member down to `Y`. -/
inductive NormalizedBlowUpChain (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : AlgebraicSpaces B S hS) : (X : AlgebraicSpaces B S hS) → (X ⟶ Y) → Prop where
  /-- The sequence of length zero: a morphism `Y₀ ⟶ Y` which is the normalization of `Y` and
  is proper. -/
  | normalization {Y₀ : AlgebraicSpaces B S hS} (f : Y₀ ⟶ Y)
      (hnorm : ∃ (D : NormalizationData B S hS Y.obj) (e : Y₀.obj ≅ D.space),
        f.hom = e.hom ≫ D.hom)
      (hproper : IsProper B S hS f.hom) :
      NormalizedBlowUpChain B S hS Y Y₀ f
  /-- Extend a sequence with top member `Yᵢ₋₁` by the normalization `Yᵢ ⟶ Yᵢ₋₁` of a blowing
  up of `Yᵢ₋₁` at a closed point, the composite `Yᵢ ⟶ Y` being proper. -/
  | normalizedBlowUp {Yprev Ynext : AlgebraicSpaces B S hS} {f : Yprev ⟶ Y}
      (previous : NormalizedBlowUpChain B S hS Y Yprev f) (g : Ynext ⟶ Yprev)
      (x : points B S hS Yprev.obj)
      (hx : IsClosed ({x} : Set (points B S hS Yprev.obj)))
      (hg : IsNormalizationOfBlowupAtClosedPoint B S hS x hx g)
      (hproper : IsProper B S hS (g ≫ f).hom) :
      NormalizedBlowUpChain B S hS Y Ynext (g ≫ f)

/-- **Stacks 0BHX.** A two-dimensional Noetherian integral algebraic space `Y` over `S` *has a
resolution of singularities by normalized blowups* when the normalization of `Y` can be
followed by finitely many normalizations of blowing ups at closed points, all of them proper
over `Y`, so as to reach a regular algebraic space. -/
@[stacks 0BHX]
abbrev HasResolutionByNormalizedBlowUps (Y : AlgebraicSpaces B S hS)
    (_hYdim : dimension B S hS Y.obj Y.property = 2)
    (_hYnoeth : IsNoetherian B S hS hZ Y.obj)
    (_hYint : IsIntegralSpace B S hS Y.obj) : Prop :=
  ∃ (X : AlgebraicSpaces B S hS) (f : X ⟶ Y),
    NormalizedBlowUpChain B S hS Y X f ∧
      HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsRegular T)

end AlgebraicGeometry.Space

end
