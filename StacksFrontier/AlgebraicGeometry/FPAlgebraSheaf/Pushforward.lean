module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Basic
public import StacksFrontier.AlgebraicGeometry.FPAlgebraSheaf.Predicate
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finitely presented quasi-coherent algebras from affine morphisms

This file produces finitely presented quasi-coherent sheaves of `𝒪_X`-algebras.  Before it,
nothing in the project constructed one: the only statements concluding
`AlgebraicGeometry.Scheme.QuasicoherentAlgebra.IsOfFinitePresentation` or
`Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation` were transport along an isomorphism and
the structure sheaf itself, so the condition had no nontrivial witness.

The construction used is the direct image: for `f : Y ⟶ X` the algebra sheaf `f_* 𝒪_Y` is
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f`, an honest object of `Under X.sheaf`
because a pushforward of a sheaf along a continuous map is a sheaf -- no sheafification is
involved.  Two separate hypotheses on `f` then give the two conditions of [Stacks, Tag 05JS]:

* `f` affine makes `f_* 𝒪_Y` quasi-coherent, which is
  `Stacks.AffineAlgebraEquivalence.isQuasicoherent_pushforwardAlgebra` (half of
  [Stacks, Tag 02KG]);
* `f` locally of finite presentation makes it of finite presentation, which is the theorem
  below.

Together they say that a scheme affine and of finite presentation over `X` presents a finitely
presented quasi-coherent `𝒪_X`-algebra, i.e. that the anti-equivalence of [Stacks, Tag 01SA]
carries finite presentation of a morphism to finite presentation of the corresponding algebra.
Since the repository's relative spectrum
`Stacks.AffineAlgebraEquivalence.affineQuasicoherentEquivalence` is an anti-equivalence, this
is also the only source of such algebras that does not have to be built by hand.

## Main results

* `Stacks.FPAlgebraSheaf.isOfFinitePresentation_pushforwardAlgebra`: **for an affine morphism
  locally of finite presentation, the direct image of the structure sheaf is a finitely
  presented algebra sheaf.**
* `Stacks.FPAlgebraSheaf.isQuasicoherent_and_isOfFinitePresentation_pushforwardAlgebra`: the
  two conditions of [Stacks, Tag 05JS] for such a direct image, in the pair form in which the
  tag asks for them.

## Implementation notes

Affineness of `f` enters twice and for different reasons.  It gives quasi-coherence, and it also
supplies the *affine* open `f ⁻¹ᵁ U` at which finite presentation of the structural ring map is
read off: `AlgebraicGeometry.LocallyOfFinitePresentation` constrains `f.appLE U V e` only for
`U` and `V` affine, and the structural ring map of `f_* 𝒪_Y` over `U` is `f.appLE U (f ⁻¹ᵁ U)
le_rfl`, so `f ⁻¹ᵁ U` has to be affine for the hypothesis to apply at all.  Without affineness
the structural map over an affine `U` is a map to the sections over a possibly non-affine open
and the hypothesis says nothing about it.

The identification of the structural ring map with `f.app U` is definitional:
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f` is `Under.mk ⟨f.c⟩`, so its structure
morphism evaluated at `U` is `f.c.app (op U)`, which is what `AlgebraicGeometry.Scheme.Hom.app`
abbreviates.  Only the rewrite `AlgebraicGeometry.Scheme.Hom.appLE_eq_app` is needed, to turn
`f.appLE U (f ⁻¹ᵁ U) le_rfl` into `f.app U`.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.FPAlgebraSheaf

/-- **For an affine morphism locally of finite presentation, the direct image of the structure
sheaf is an algebra sheaf of finite presentation.**  Over an affine open `U` of the target the
structural ring map of `f_* 𝒪_Y` is `Γ(X, U) ⟶ Γ(Y, f ⁻¹ᵁ U)`; affineness of `f` makes
`f ⁻¹ᵁ U` an affine open, and finite presentation of `f` is exactly the assertion that this map
is of finite presentation. -/
theorem isOfFinitePresentation_pushforwardAlgebra {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] [LocallyOfFinitePresentation f] :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (pushforwardAlgebra f) := by
  intro U hU
  have h := LocallyOfFinitePresentation.finitePresentation_appLE f hU (hU.preimage f) le_rfl
  rwa [Scheme.Hom.appLE_eq_app] at h

/-- **A scheme affine and locally of finite presentation over `X` gives a quasi-coherent
`𝒪_X`-algebra of finite presentation.**  The two conditions are the two conditions imposed on
the members of the directed system of [Stacks, Tag 05JS], in the conjoined form the tag asks
for them in. -/
theorem isQuasicoherent_and_isOfFinitePresentation_pushforwardAlgebra
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] [LocallyOfFinitePresentation f] :
    Scheme.QuasicoherentAlgebra.IsQuasicoherent (pushforwardAlgebra f) ∧
      Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (pushforwardAlgebra f) :=
  ⟨isQuasicoherent_pushforwardAlgebra f, isOfFinitePresentation_pushforwardAlgebra f⟩

end Stacks.FPAlgebraSheaf
