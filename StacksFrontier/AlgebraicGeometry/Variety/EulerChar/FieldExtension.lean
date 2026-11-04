module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationFieldExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic

/-!
# The Euler characteristic under extension of the base field

The Euler characteristic of a coherent sheaf on a scheme proper over a field is unchanged by
extension of that field: for a field extension `K/k`, a proper `f : X ⟶ Spec k` and a coherent
`ℱ` on `X`,

`χ(X, ℱ) = χ(X_K, ℱ_K)`,

where `X_K` is the base change and `ℱ_K` its inverse image. This is [Stacks, Tag 08AB]. Here it
is proved from the comparison `Hⁱ(X_K, ℱ_K) ≅ K ⊗_k Hⁱ(X, ℱ)` in every degree, the flat base
change of [Stacks, Tag 02KH] part (2), taken as a hypothesis.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_eq_of_finrank_cohomologyOverField_eq`: two coherent
  sheaves on two schemes proper over two fields have the same Euler characteristic as soon as
  their cohomology has the same dimension in every degree.
* `AlgebraicGeometry.finrank_cohomologyOverField_eq_of_tensorEquiv`: the dimension is unchanged
  by extension of scalars.
* `AlgebraicGeometry.eulerCharacteristic_baseChange_field_of_cohomologyBaseChange`: the
  statement of [Stacks, Tag 08AB], from the degreewise flat base change of
  [Stacks, Tag 02KH] part (2).

## References

* [Stacks Project, Tag 08AB](https://stacks.math.columbia.edu/tag/08AB)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

universe u

/-- **Equal cohomology dimensions give equal Euler characteristics.** Two coherent sheaves on
schemes proper over two fields whose cohomology groups have the same dimension in every degree
have the same Euler characteristic. -/
public theorem eulerCharacteristic_eq_of_finrank_cohomologyOverField_eq (k K : Type u) [Field k]
    [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    [F.IsCoherent] {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of K)) [IsProper f'] (F' : X'.Modules)
    [F'.IsCoherent]
    (h : ∀ n : ℕ, Module.finrank K (cohomologyOverField K f' F' n) =
      Module.finrank k (cohomologyOverField k f F n)) :
    eulerCharacteristic K f' F' = eulerCharacteristic k f F := by
  simp only [eulerCharacteristic_eq_finsum, h]

/-- **Extension of scalars does not change the dimension.** If the degree-`n` cohomology over
the larger field is `K ⊗_k Hⁿ(X, ℱ)`, its dimension over `K` is the dimension of `Hⁿ(X, ℱ)`
over `k`. -/
public theorem finrank_cohomologyOverField_eq_of_tensorEquiv (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules) {X' : Scheme.{u}}
    (f' : X' ⟶ Spec (.of K)) (F' : X'.Modules) (n : ℕ)
    (e : cohomologyOverField K f' F' n ≃ₗ[K] (K ⊗[k] cohomologyOverField k f F n)) :
    Module.finrank K (cohomologyOverField K f' F' n) =
      Module.finrank k (cohomologyOverField k f F n) :=
  e.finrank_eq.trans Module.finrank_baseChange

/-- **[Stacks, Tag 08AB] from the degreewise flat base change of [Stacks, Tag 02KH] part (2).**
Let `K/k` be an extension of fields, `f : X ⟶ Spec k` proper and `ℱ` a coherent sheaf on `X`.
If in every degree the cohomology of the base-changed sheaf on the base-changed scheme is
`K ⊗_k Hⁿ(X, ℱ)`, then the Euler characteristic is unchanged by the base change. -/
public theorem eulerCharacteristic_baseChange_field_of_cohomologyBaseChange (k K : Type u)
    [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent]
    (e : ∀ n : ℕ, Nonempty (cohomologyOverField K (pullback.snd f (specMapAlgebraMap k K))
      ((Scheme.Modules.pullback (pullback.fst f (specMapAlgebraMap k K))).obj F) n ≃ₗ[K]
        (K ⊗[k] cohomologyOverField k f F n))) :
    @eulerCharacteristic K _ (pullback f (specMapAlgebraMap k K))
        (pullback.snd f (specMapAlgebraMap k K)) inferInstance
        ((Scheme.Modules.pullback (pullback.fst f (specMapAlgebraMap k K))).obj F)
        (isCoherent_pullback (pullback.fst f (specMapAlgebraMap k K)) F) =
      eulerCharacteristic k f F :=
  have : ((Scheme.Modules.pullback (pullback.fst f (specMapAlgebraMap k K))).obj F).IsCoherent :=
    isCoherent_pullback (pullback.fst f (specMapAlgebraMap k K)) F
  eulerCharacteristic_eq_of_finrank_cohomologyOverField_eq k K f F
    (pullback.snd f (specMapAlgebraMap k K)) _
    fun n => finrank_cohomologyOverField_eq_of_tensorEquiv k K f F _ _ n (e n).some

end AlgebraicGeometry

end
