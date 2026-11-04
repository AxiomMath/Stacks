module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleTensorPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteStalkPushforward

/-!
# The canonical map `𝓖 ⊗_ℬ f_*𝓕 ⟶ f_*(f^*𝓖 ⊗_𝒜 𝓕)` for a finite morphism of algebraic spaces

Let `S` be a scheme and `π : X ⟶ Y` a finite morphism of algebraic spaces over `S`. Let `𝒜` be
a sheaf of rings on `X_étale`, `ℬ` a sheaf of rings on `Y_étale`, and `φ : ℬ ⟶ π_*𝒜` a
homomorphism of sheaves of rings; these data are a morphism of ringed topoi

`f = (π, φ) : (Sh(X_étale), 𝒜) ⟶ (Sh(Y_étale), ℬ)`

and Stacks 0DK4 states that for a sheaf of `𝒜`-modules `𝓕` and a sheaf of `ℬ`-modules `𝓖` the
canonical map

`𝓖 ⊗_ℬ f_*𝓕 ⟶ f_*(f^*𝓖 ⊗_𝒜 𝓕)`

is an isomorphism.

The datum `f` and the canonical map are exactly those of Stacks 04G0, which this repository
builds for an arbitrary morphism of algebraic spaces: the two lemmas quantify over the same
`(π, φ)`, in the same direction, and ask about the same adjoint transpose, differing only in
the hypothesis — closed immersion there, finite here — under which it is invertible. So
`AlgebraicGeometry.Space.smallEtaleRingedToposHomOfSharp` and
`AlgebraicGeometry.Space.tensorPushforwardMap` carry both tags, and what this file adds is the
identity that the source's proof of invertibility comes down to after passing to stalks at a
geometric point.

## Main definitions

* `AlgebraicGeometry.Space.tensorBaseChangeCancel`: for a `ℬ`-algebra `𝒜` and an `𝒜`-module
  `𝓕`, the base-change cancellation `(𝒜 ⊗_ℬ 𝓖) ⊗_𝒜 𝓕 = 𝓖 ⊗_ℬ 𝓕`.
* `AlgebraicGeometry.Space.fibreTensorDirectSumEquiv`: the stalk identity of Stacks 0DK4.

## Implementation notes

The stalk identity is pure module theory over the stalk rings, which is how the source's proof
uses it: the stalk of `f_*𝓕` at a geometric point `y` is the sum over the lifts `x₁, …, xₙ` of
`y` of the stalks of `𝓕` (Stacks 0DK3), the stalk of `f^*𝓖` at `xᵢ` is `𝒜_{xᵢ} ⊗_{ℬ_y} 𝓖_y`
(Stacks 04K2, part (4)), and stalks commute with tensor products, so the canonical map becomes
the displayed identity of `ℬ_y`-modules. Its two ingredients are that a tensor product
distributes over a direct sum and that base change cancels against a tensor product over the
base-changed ring.

The source writes the base-changed factor as `𝓖_y ⊗_{ℬ_y} 𝒜_{xᵢ}`, with the ring on the right;
`𝒜_{xᵢ} ⊗_{ℬ_y} 𝓖_y` is written here instead, the same `𝒜_{xᵢ}`-module under the symmetry of
the tensor product over a commutative ring, because that is the order in which the module
structure over the base-changed ring is available. The index set is left arbitrary rather than
finite; for Stacks 0DK4 it is the finite set of lifts of `y`, finite by
`AlgebraicGeometry.Space.finite_geometricLifts`, and for a finite index set the direct sum of
the source's proof and the product of Stacks 0DK3 agree.

Invertibility of the canonical map is not proved here. The source checks it on stalks, using
Stacks 04K5 to know that stalks detect isomorphisms, and the stalk of a direct image along a
finite morphism, which is Stacks 0DK3; that stalk computation is unavailable, since its own
proof reduces to Stacks 03QP for a finite morphism of schemes and that is not in this
repository. `AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isClosedImmersion` is the
invertibility statement for a closed immersion, whose proof instead makes the counit and the
unit of the inverse-image adjunction invertible; for a finite morphism the counit is not
invertible and that route is unavailable too.

## References

* [Stacks Project, Tag 0DK4](https://stacks.math.columbia.edu/tag/0DK4)
* [Stacks Project, Tag 0DK3](https://stacks.math.columbia.edu/tag/0DK3)
* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open TensorProduct DirectSum

universe u v w t

namespace AlgebraicGeometry.Space

/-- **Base change cancels against a tensor product over the base-changed ring.** For a
commutative ring `R`, an `R`-algebra `A`, an `R`-module `G` and an `A`-module `F` whose
`R`-module structure comes from that of `A`, the `A`-module `(A ⊗_R G) ⊗_A F` is `G ⊗_R F`.

This is `TensorProduct.AlgebraTensorModule.cancelBaseChange` read through the symmetry of the
tensor product in each of its two factors. -/
def tensorBaseChangeCancel (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    (G : Type w) [AddCommGroup G] [Module R G]
    (F : Type t) [AddCommGroup F] [Module A F] [Module R F] [IsScalarTower R A F] :
    ((A ⊗[R] G) ⊗[A] F) ≃ₗ[R] (G ⊗[R] F) :=
  ((TensorProduct.comm A (A ⊗[R] G) F).restrictScalars R).trans
    (((TensorProduct.AlgebraTensorModule.cancelBaseChange R A A F G).restrictScalars R).trans
      (TensorProduct.comm R F G))

/-- **The stalk identity of Stacks 0DK4.** Let `R` be a commutative ring, `G` an `R`-module,
`A i` a family of `R`-algebras and `F i` a family of `A i`-modules whose `R`-module structures
come from those of the `A i`. Then

`G ⊗_R (⨁ᵢ F i) = ⨁ᵢ (A i ⊗_R G) ⊗_{A i} F i`.

This is the identity the source's proof of Stacks 0DK4 reduces to at a geometric point `y` of
`Y`: `R` is the stalk `ℬ_y`, `G` is `𝓖_y`, the index set is the set of lifts `x₁, …, xₙ` of
`y` to `X`, `A i` is `𝒜_{xᵢ}` and `F i` is `𝓕_{xᵢ}`. The left side is the stalk at `y` of
`𝓖 ⊗_ℬ f_*𝓕` and the right side is the stalk at `y` of `f_*(f^*𝓖 ⊗_𝒜 𝓕)`.

A tensor product distributes over a direct sum, and each summand is then
`AlgebraicGeometry.Space.tensorBaseChangeCancel`. -/
def fibreTensorDirectSumEquiv (R : Type u) [CommRing R] (ι : Type v) [DecidableEq ι]
    (G : Type w) [AddCommGroup G] [Module R G]
    (A : ι → Type t) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (F : ι → Type t) [∀ i, AddCommGroup (F i)] [∀ i, Module (A i) (F i)]
    [∀ i, Module R (F i)] [∀ i, IsScalarTower R (A i) (F i)] :
    (G ⊗[R] ⨁ i, F i) ≃ₗ[R] ⨁ i, ((A i ⊗[R] G) ⊗[A i] F i) :=
  (TensorProduct.directSumRight R R G F).trans
    (DirectSum.congrLinearEquiv fun i => (tensorBaseChangeCancel R (A i) G (F i)).symm)

end AlgebraicGeometry.Space

end
