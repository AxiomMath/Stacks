module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernSetup
public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# When the Chern classes of a perfect derived object are defined

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `E` be a perfect object of `D(𝒪_X)`. The Chern classes
of `E` are *defined* when there is an envelope `f : Y ⟶ X` such that `Lf^*E` is isomorphic in
`D(𝒪_Y)` to a locally bounded complex of finite locally free `𝒪_Y`-modules. This file is that
condition, Stacks 0F9E (1).

## Main definitions

* `Stacks.Chow.EnvelopePresentation` — an envelope together with a locally bounded complex of
  finite locally free modules representing the derived pullback.
* `Stacks.Chow.HasDefinedChernClasses` — Stacks 0F9E (1): such a presentation exists.

## Main results

* `Stacks.Chow.hasDefinedChernClasses_iff` unfolds the condition to the bare existence
  statement.

## Implementation notes

The condition is `Nonempty` of a structure rather than an iterated `∃`, because the data of a
presentation — the envelope, the complex, and the isomorphism — is consumed field by field by
every construction that uses it.

The condition is stated for an arbitrary object of `D(𝒪_X)`: it says nothing about perfectness
of `E` and neither does its negation, so nothing is gained by bundling the standing hypothesis
of the source into it, and the criteria of Stacks 0GUE that produce a presentation do not use
perfectness either.

## References

* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StrictlyPerfect

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

/-- An **envelope presentation** of an object `E` of `D(𝒪_X)`: an envelope `f : Y ⟶ X` together
with a locally bounded complex `P` of finite locally free `𝒪_Y`-modules and an isomorphism
`Lf^*E ≅ P` in `D(𝒪_Y)`. -/
structure EnvelopePresentation {X : Scheme.{u}} (E : DerivedCategory X.Modules) where
  /-- The scheme that the object is pulled back to. -/
  Y : Scheme.{u}
  /-- The morphism to the ambient scheme. -/
  f : Y ⟶ X
  /-- The morphism is an envelope: proper and completely decomposed. -/
  envelope : IsEnvelope f
  /-- The complex of finite locally free modules representing the derived pullback. -/
  P : CochainComplex Y.Modules ℤ
  /-- Its terms are finite locally free and vanish outside a finite range of degrees near each
  point. -/
  locallyBounded : IsLocallyBoundedFiniteLocallyFree P
  /-- The complex represents the derived pullback of `E` along the envelope. -/
  representation : Nonempty
    ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj E ≅
      DerivedCategory.Q.obj P)

/-- **Stacks 0F9E (1).** The Chern classes of an object `E` of `D(𝒪_X)` are **defined** when
some envelope `f : Y ⟶ X` has `Lf^*E` isomorphic to a locally bounded complex of finite locally
free `𝒪_Y`-modules. -/
@[stacks 0F9E "clause (1): the condition under which the Chern classes of a perfect object are \
defined"]
def HasDefinedChernClasses {X : Scheme.{u}} (E : DerivedCategory X.Modules) : Prop :=
  Nonempty (EnvelopePresentation E)

/-- The Chern classes of `E` are defined exactly when an envelope, a locally bounded complex of
finite locally free modules on its source, and an isomorphism of that complex with the derived
pullback of `E` exist. -/
theorem hasDefinedChernClasses_iff {X : Scheme.{u}} (E : DerivedCategory X.Modules) :
    HasDefinedChernClasses E ↔
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsEnvelope f) (P : CochainComplex Y.Modules ℤ),
        IsLocallyBoundedFiniteLocallyFree P ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj P) :=
  ⟨fun ⟨H⟩ => ⟨H.Y, H.f, H.envelope, H.P, H.locallyBounded, H.representation⟩,
    fun ⟨Y, f, hf, P, hP, hrep⟩ => ⟨⟨Y, f, hf, P, hP, hrep⟩⟩⟩

end Stacks.Chow

end
