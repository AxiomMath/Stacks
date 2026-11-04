module

public import StacksFrontier.AlgebraicGeometry.FPAlgebraSheaf.Pushforward
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The polynomial algebra sheaf `𝒪_X[x_i]`

The sheaf of polynomial algebras on a scheme `X` is constructed here as an object of
`Under X.sheaf`, together with proofs that it is quasi-coherent and -- for finitely many
variables -- of finite presentation.  It is the first nontrivial finitely presented
quasi-coherent algebra sheaf in the project.

It is *not* built as the sheafification of `U ↦ MvPolynomial n Γ(X, U)`.  That presheaf is not a
sheaf: for a cover of `U` by infinitely many opens, the supports of a compatible family of
polynomials need not have finite union, so the coefficientwise glueing of the family need not be
a polynomial.  (Separatedness does hold, coefficientwise, and glueing holds over a
quasi-compact open, since a finite subcover glues and separatedness extends the result to the
whole cover.  So the presheaf is a sheaf on the quasi-compact opens and only there, which is not
the site.)  Sheafifying it would then leave the sections over an affine open to be computed,
which is the whole difficulty.

Instead the sheaf is the direct image of the structure sheaf of affine `n`-space:
`𝒪_X[x_i] := p_* 𝒪_{𝔸(n; X)}` for `p : 𝔸(n; X) ⟶ X` the projection.  A direct image of a sheaf
is a sheaf, so there is nothing to sheafify, and both conditions come from
`Stacks.FPAlgebraSheaf.isOfFinitePresentation_pushforwardAlgebra`, since Mathlib's
`AlgebraicGeometry.AffineSpace` carries exactly the two instances needed: `p` is affine, and for
`n` finite `p` is locally of finite presentation.

## Main definitions

* `Stacks.FPAlgebraSheaf.polynomialAlgebra X n`: **the polynomial algebra sheaf `𝒪_X[x_i]`,
  `i : n`, as an object of `AlgebraicGeometry.Scheme.QuasicoherentAlgebra X`.**

## Main results

* `Stacks.FPAlgebraSheaf.isQuasicoherent_polynomialAlgebra`: it is quasi-coherent, for any
  index type.
* `Stacks.FPAlgebraSheaf.isOfFinitePresentation_polynomialAlgebra`: **it is of finite
  presentation when there are finitely many variables.**
* `Stacks.FPAlgebraSheaf.sections_polynomialAlgebra`: its sections over an open `U` of `X` are
  the sections of `𝔸(n; X)` over the preimage of `U`.

## Implementation notes

`AlgebraicGeometry.AffineSpace n S` is Mathlib's `pullback (terminal.from S) (terminal.from (Spec
ℤ[n]))`, not a relative spectrum, so no quasi-coherent algebra is needed to define it and the
construction here is not circular.

## Identification of the sections over affine opens

The sections of `polynomialAlgebra X n` over an affine open `U` are identified with
`MvPolynomial n Γ(X, U)` in `StacksFrontier.AlgebraicGeometry.Constructions.AffineSpace`, by
`Stacks.AffineSpace.comparisonApp_bijective`, and `polynomialAlgebra X n` is identified there with
the sheaf associated to `U ↦ MvPolynomial n Γ(X, U)` by `Stacks.AffineSpace.sheafificationIso`.
Nothing in this file depends on the identification; the finite presentation statement is
obtained from finite presentation of the morphism `p`, never from a presentation of the ring of
sections.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.FPAlgebraSheaf

/-- **The polynomial algebra sheaf `𝒪_X[x_i]`, `i : n`**, as a sheaf of commutative
`𝒪_X`-algebras: the direct image of the structure sheaf of affine `n`-space over `X` along the
projection.  A direct image of a sheaf is a sheaf, so this is an object of `Under X.sheaf` with
no sheafification. -/
def polynomialAlgebra (X : Scheme.{u}) (n : Type u) : X.QuasicoherentAlgebra :=
  pushforwardAlgebra (𝔸(n; X) ↘ X)

/-- The sections of the polynomial algebra sheaf over an open `U` of `X` are the sections of
affine `n`-space over the preimage of `U`. -/
theorem sections_polynomialAlgebra (X : Scheme.{u}) (n : Type u) (U : X.Opens) :
    (polynomialAlgebra X n).right.obj.obj (op U) = Γ(𝔸(n; X), (𝔸(n; X) ↘ X) ⁻¹ᵁ U) :=
  rfl

/-- The structural ring map of the polynomial algebra sheaf over an open `U` is the map on
sections induced by the projection from affine `n`-space. -/
theorem hom_app_polynomialAlgebra (X : Scheme.{u}) (n : Type u) (U : X.Opens) :
    (polynomialAlgebra X n).hom.hom.app (op U) = (𝔸(n; X) ↘ X).app U :=
  rfl

/-- **The polynomial algebra sheaf is quasi-coherent.**  The projection from affine `n`-space is
an affine morphism, and a direct image of the structure sheaf along an affine morphism is a
quasi-coherent algebra. -/
theorem isQuasicoherent_polynomialAlgebra (X : Scheme.{u}) (n : Type u) :
    Scheme.QuasicoherentAlgebra.IsQuasicoherent (polynomialAlgebra X n) :=
  isQuasicoherent_pushforwardAlgebra _

/-- **The polynomial algebra sheaf in finitely many variables is of finite presentation.**  The
projection from affine `n`-space is affine and, for `n` finite, locally of finite presentation.
This is the first nontrivial witness in the project to
`AlgebraicGeometry.Scheme.QuasicoherentAlgebra.IsOfFinitePresentation`. -/
theorem isOfFinitePresentation_polynomialAlgebra (X : Scheme.{u}) (n : Type u) [Finite n] :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (polynomialAlgebra X n) :=
  isOfFinitePresentation_pushforwardAlgebra _

/-- **The polynomial algebra sheaf in finitely many variables satisfies both conditions imposed
on the members of the directed system of [Stacks, Tag 05JS].** -/
theorem isQuasicoherent_and_isOfFinitePresentation_polynomialAlgebra
    (X : Scheme.{u}) (n : Type u) [Finite n] :
    Scheme.QuasicoherentAlgebra.IsQuasicoherent (polynomialAlgebra X n) ∧
      Scheme.QuasicoherentAlgebra.IsOfFinitePresentation (polynomialAlgebra X n) :=
  ⟨isQuasicoherent_polynomialAlgebra X n, isOfFinitePresentation_polynomialAlgebra X n⟩

end Stacks.FPAlgebraSheaf
