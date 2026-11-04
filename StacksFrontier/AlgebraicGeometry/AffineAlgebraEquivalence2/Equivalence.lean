module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Faithful
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Full
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over

/-!
# The anti-equivalence of affine schemes and quasi-coherent algebras, up to essential
surjectivity

Let `S` be a scheme. The functor `X ↦ f_* 𝒪_X` from the schemes affine over `S`,
contravariantly, to the quasi-coherent sheaves of commutative `𝒪_S`-algebras is fully faithful;
this file records that, together with the statement that it is an anti-equivalence as soon as it
is essentially surjective.

## Main results

* `fullyFaithfulAffineQuasicoherentPushforwardFunctor`: the functor `X ↦ f_* 𝒪_X` is fully
  faithful.
* `equivalenceOfEssSurj`: an essentially surjective fully faithful functor is an equivalence, so
  the anti-equivalence of Stacks Tag 01SA is exactly what essential surjectivity of
  `affineQuasicoherentPushforwardFunctor` adds to the results of this directory.

## Implementation notes

Fullness is `full_affineQuasicoherentPushforwardFunctor` and faithfulness is
`faithful_affineQuasicoherentPushforwardFunctor`. What remains for essential surjectivity is the
identification `(relativeSpecToBase A)_* 𝒪 ≅ A` of algebra sheaves, for the relative spectrum
`relativeSpec A` constructed in `RelativeSpec.lean`; `relativeSpecAffineOver A` is already an
object of `AffineOver S`.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

/-- The functor `X ↦ f_* 𝒪_X` from the schemes affine over `S` to the quasi-coherent
`𝒪_S`-algebras is fully faithful. -/
public noncomputable def fullyFaithfulAffineQuasicoherentPushforwardFunctor (S : Scheme.{u}) :
    (affineQuasicoherentPushforwardFunctor S).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- If the functor `X ↦ f_* 𝒪_X` is essentially surjective, then it is the anti-equivalence
between the schemes affine over `S` and the quasi-coherent `𝒪_S`-algebras. -/
public noncomputable def equivalenceOfEssSurj (S : Scheme.{u})
    [(affineQuasicoherentPushforwardFunctor S).EssSurj] :
    (AffineOver S)ᵒᵖ ≌ QuasicoherentAlgebra S :=
  have : (affineQuasicoherentPushforwardFunctor S).IsEquivalence := { }
  (affineQuasicoherentPushforwardFunctor S).asEquivalence

/-! ### The identification with pushforward of structure sheaves -/

/-- The value of the functor `X ↦ f_* 𝒪_X` on an object affine over `S`, read in the ambient
category of algebra sheaves, *is* `f_* 𝒪_X`. So the identification of the anti-equivalence with
pushforward of structure sheaves is the identity isomorphism. -/
public theorem pushforwardIso_rfl (S : Scheme.{u}) (X : AffineOver S) :
    (IsQuasicoherentAlgebra S).ι.obj ((affineQuasicoherentPushforwardFunctor S).obj (.op X)) =
      pushforwardAlgebra X.obj.hom :=
  rfl

/-- Under the preceding identification, the functor `X ↦ f_* 𝒪_X` acts on a morphism over `S`
by the canonical contravariant map on pushed-forward structure sheaves. -/
public theorem pushforwardIso_rfl_naturality (S : Scheme.{u}) {X Y : AffineOver S} (f : X ⟶ Y) :
    (IsQuasicoherentAlgebra S).ι.map ((affineQuasicoherentPushforwardFunctor S).map f.op) =
      pushforwardAlgebraMap ((IsAffineHomOver S).ι.map f) :=
  rfl

end Stacks.AffineAlgebraEquivalence

end
