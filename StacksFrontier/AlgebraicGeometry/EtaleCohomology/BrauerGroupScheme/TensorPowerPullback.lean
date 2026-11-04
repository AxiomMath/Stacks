module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerEndAlgebra

/-!
# The tensor power of an algebra sheaf under pullback, and the tensor power of a matrix algebra

Let `S` be a scheme. This file supplies the two identifications the proof of [Stacks, Tag 0A2L]
needs in order to read its projector, which lives on a trivialising étale covering, as a section
of the `d`-fold tensor power of an Azumaya `𝒪_S`-algebra:

* pullback commutes with the tensor power, `φ^*(A^{⊗ n}) ≅ (φ^* A)^{⊗ n}`, because the pullback
  of sheaves of algebras is a monoidal functor (`Stacks.EtaleCohomology.BrauerScheme.
  monoidalModulePullback`, the comparison of Tag 01CD);
* a positive tensor power of a matrix algebra is a matrix algebra,
  `Mat_d(𝒪_S)^{⊗ n} ≅ Mat_{d ^ n}(𝒪_S)`.

Composed with the trivialisation `φ_i^* A ≅ Mat_d(𝒪_{U_i})` of the Azumaya condition, the two
give `φ_i^*(A^{⊗ d}) ≅ Mat_{d ^ d}(𝒪_{U_i})`, which is where Saltman's projector
`Matrix.altProj` sits.

## Main definitions

* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowCongr`: the tensor power depends only on
  the isomorphism class of a sheaf of algebras.
* `Stacks.EtaleCohomology.BrauerScheme.algebraPullbackNatTensorPowIso`:
  `φ^*(A^{⊗ n}) ≅ (φ^* A)^{⊗ n}` as sheaves of `𝒪_T`-algebras.
* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowMatrixAlgebraIso`:
  `Mat_d(𝒪_S)^{⊗ (n+1)} ≅ Mat_{d ^ (n+1)}(𝒪_S)` as sheaves of `𝒪_S`-algebras.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.nonempty_natTensorPow_matrixAlgebra_iso_of_pullback`:
  **on a member of a trivialising étale covering of an Azumaya algebra sheaf `A`, the pullback of
  `A^{⊗ (n+1)}` is the matrix algebra of size `d ^ (n+1)`.**

## Implementation notes

The powers of a matrix algebra start at `1`: the zeroth tensor power is the unit algebra sheaf
`𝒪_S`, and identifying that with `Mat_1(𝒪_S)` is the internal endomorphism monoid of the monoidal
unit, which the library does not provide; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.BrauerMonoid`. The pullback
identification has no such restriction, the zeroth case being the unit comparison
`CategoryTheory.Functor.Monoidal.εIso`.

## References

* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

variable {S : Scheme.{u}}

/-- **The tensor power depends only on the isomorphism class**: an isomorphism of sheaves of
algebras induces one of their `n`-fold tensor powers. -/
def natTensorPowCongr {A B : AlgebraSheaf S} (e : A ≅ B) :
    ∀ n : ℕ, Stacks.TensorPowers.natTensorPow A n ≅ Stacks.TensorPowers.natTensorPow B n
  | 0 => Iso.refl _
  | n + 1 => tensorIso (natTensorPowCongr e n) e

/-- **Pullback commutes with the tensor power of a sheaf of algebras**: `φ^*(A^{⊗ n})` is
`(φ^* A)^{⊗ n}`, by the tensorator and the unit comparison of the monoidal functor
`algebraPullback φ`, which are the comparisons of Tag 01CD. -/
def algebraPullbackNatTensorPowIso {T S : Scheme.{u}} (φ : T ⟶ S) (A : AlgebraSheaf S) :
    ∀ n : ℕ, (algebraPullback φ).obj (Stacks.TensorPowers.natTensorPow A n) ≅
      Stacks.TensorPowers.natTensorPow ((algebraPullback φ).obj A) n
  | 0 => (Functor.Monoidal.εIso (algebraPullback φ)).symm
  | n + 1 =>
    (Functor.Monoidal.μIso (algebraPullback φ) (Stacks.TensorPowers.natTensorPow A n) A).symm ≪≫
      tensorIso (algebraPullbackNatTensorPowIso φ A n) (Iso.refl _)

/-- **A positive tensor power of a matrix algebra sheaf is a matrix algebra sheaf**:
`Mat_d(𝒪_S)^{⊗ (n+1)} ≅ Mat_{d ^ (n+1)}(𝒪_S)`, by iterating
`Stacks.EtaleCohomology.BrauerScheme.matrixAlgebraTensorIso`. -/
def natTensorPowMatrixAlgebraIso (S : Scheme.{u}) (d : ℕ) :
    ∀ n : ℕ, Stacks.TensorPowers.natTensorPow (matrixAlgebra S d) (n + 1) ≅
      matrixAlgebra S (d ^ (n + 1))
  | 0 => λ_ (matrixAlgebra S d) ≪≫ eqToIso (congrArg (matrixAlgebra S) (pow_one d).symm)
  | n + 1 =>
    tensorIso (natTensorPowMatrixAlgebraIso S d n) (Iso.refl (matrixAlgebra S d)) ≪≫
      matrixAlgebraTensorIso S (d ^ (n + 1)) d ≪≫
      eqToIso (congrArg (matrixAlgebra S) (pow_succ d (n + 1)).symm)

/-- **On a member of a trivialising étale covering, the pullback of a positive tensor power of an
Azumaya algebra sheaf is a matrix algebra.** This is where the projector of [Stacks, Tag 0A2L]
is read as a section of `A^{⊗ d}`: the trivialisation `φ^* A ≅ Mat_d(𝒪_T)` is carried to the
tensor powers by `algebraPullbackNatTensorPowIso`, and a tensor power of a matrix algebra is a
matrix algebra. -/
theorem nonempty_natTensorPow_matrixAlgebra_iso_of_pullback {T S : Scheme.{u}} (φ : T ⟶ S)
    (A : AlgebraSheaf S) {d : ℕ} (e : (algebraPullback φ).obj A ≅ matrixAlgebra T d) (n : ℕ) :
    Nonempty ((algebraPullback φ).obj (Stacks.TensorPowers.natTensorPow A (n + 1)) ≅
      matrixAlgebra T (d ^ (n + 1))) := by
  refine ⟨algebraPullbackNatTensorPowIso φ A (n + 1) ≪≫ ?_⟩
  refine ?_ ≪≫ natTensorPowMatrixAlgebraIso T d n
  exact natTensorPowCongr e (n + 1)

end Stacks.EtaleCohomology.BrauerScheme

end

end
