module

public import StacksCore.CategoryTheory.GradedObject.GradedVectorSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of the trace map

Let `X` be a nonempty smooth projective scheme over `k`, equidimensional of dimension `d`, in a
cohomology theory given by the data `(D0)`, `(D1)`, `(D2')` of Section 45.14 satisfying the
axioms `(A1)` – `(A7)`. The class of the diagonal decomposes under the Künneth isomorphism of
`(A5)` as
`γ([Δ]) ∈ ⨁_i H^i(X) ⊗_F H^{2d - i}(X)(d)`,
and contracting a linear functional `μ` on `H^{2d - i}(X)(d)` against its degree-`i` component
produces a class `(1 ⊗ μ)(γ([Δ])) ∈ H^i(X)`. This file proves that the resulting map is a linear
isomorphism — the perfect duality between `H^i(X)` and `H^{2d - i}(X)(d)` that the diagonal
class defines — and deduces that the trace map `∫_X = λ` of axiom `(A6)` is unique, since `(A6)`
pins down the value of that isomorphism at `i = 0`.

## Main definitions

* `Stacks.WeilCohomology.coevContract`: contraction of the coevaluation of an exact pairing of
  `F`-modules against a linear functional, `μ ↦ (1 ⊗ μ)(η)`.
* `Stacks.WeilCohomology.coevEquiv`: that contraction as a linear equivalence, inverse to the
  evaluation pairing.
* `Stacks.WeilCohomology.diagonalDuality`: its degree-`i` instance for a dualizable graded
  vector space, the equivalence `(H^{2d - i}(X)(d))^* ≃ H^i(X)` defined by `γ([Δ])`.

## Main results

* `Stacks.WeilCohomology.coevContract_flip_pairingU` and
  `Stacks.WeilCohomology.flip_pairingU_coevContract`: the two triangle identities say exactly
  that contracting the coevaluation and pairing against the evaluation are mutually inverse.
* `Stacks.WeilCohomology.diagonalDuality_symm_apply`: the inverse of the duality defined by
  `γ([Δ])` is the pairing whose perfectness is Tag 0FFV.
* `Stacks.WeilCohomology.traceMap_unique`: **the operative statement of Tag 0FIK.** Two linear
  maps `H^{2d}(X)(d) → F` satisfying the normalisation of axiom `(A6)` are equal.

## The dictionary

The statements are read against a dualizable graded `F`-vector space, which is the shape the
source's own argument produces, so that no cohomology theory has to be constructed:

* `V` is `H^*(X)`, so `V i` is `H^i(X)`;
* `W` is `H^*(X)(d)[2d]`, so `W (-i)` is `H^{2d - i}(X)(d)`, and in particular `W 0` is
  `H^{2d}(X)(d)`, the source of the trace map;
* `ExactPairing V W` is the left-dual structure established by Lemma 45.14.5, Tag 0FIJ: its
  coevaluation is multiplication by `γ([Δ])` and its evaluation is pullback along the diagonal
  followed by `λ`. Consequently `CategoryTheory.GradedObject.Monoidal.coevApply V W i` is the
  degree-`i` Künneth component of `γ([Δ])`, and `coevContract` applied to it is the contraction
  `(1 ⊗ μ)(γ([Δ]))` of the remark.

With that reading, `diagonalDuality V W i` is the map `μ ↦ (1 ⊗ μ)(γ([Δ]))` and its bijectivity
is the remark's perfect duality; the normalisation `(id ⊗ λ) γ([Δ]) = 1` of axiom `(A6)` is the
equation `diagonalDuality V W 0 λ = 1`, so injectivity at `i = 0` is uniqueness of `λ`.

## Implementation notes

Tag 0FFV, already available as
`CategoryTheory.GradedObject.Monoidal.finiteDimensional_and_isPerfPair_of_exactPairing`,
supplies the perfectness of the *evaluation* pairing. The remark attributes the duality to
`γ([Δ])`, that is to the *coevaluation*, and that direction is what is added here: the two
triangle identities, available elementwise as `ModuleCat.expand_X` and `ModuleCat.expand_Y`,
exhibit contraction against the coevaluation and pairing against the evaluation as mutually
inverse linear maps. The reduction from the graded statement to a single degree is
`CategoryTheory.GradedObject.Monoidal.exactPairingApply`.

The hypothesis carried throughout is the left-dual structure, which is the conclusion of Tag
0FIJ and not of this one; the remark itself instructs the reader to combine the proof of that
lemma with Tag 0FFV, so carrying it is what the source does.

## References

* [Stacks Project, Tag 0FIK](https://stacks.math.columbia.edu/tag/0FIK)
* [Stacks Project, Tag 0FIJ](https://stacks.math.columbia.edu/tag/0FIJ)
* [Stacks Project, Tag 0FFV](https://stacks.math.columbia.edu/tag/0FFV)
-/

@[expose] public section

namespace Stacks.WeilCohomology

open CategoryTheory CategoryTheory.GradedObject CategoryTheory.GradedObject.Monoidal
open MonoidalCategory ModuleCat
open scoped TensorProduct

universe uF

section Ungraded

variable {F : Type uF} [Field F] (X Y : ModuleCat.{uF} F) [ExactPairing X Y]

/-- **Contraction of the coevaluation against a linear functional**, `μ ↦ (1 ⊗ μ)(η)`. For the
degree-`i` part of the diagonal class of a Weil cohomology theory this is the map
`μ ↦ (1 ⊗ μ)(γ([Δ]))` of Tag 0FIK. -/
noncomputable def coevContract : (Y →ₗ[F] F) →ₗ[F] X where
  toFun μ := TensorProduct.rid F X (LinearMap.lTensor X μ ((η_ X Y).hom (1 : F)))
  map_add' μ ν := by simp [LinearMap.lTensor_add]
  map_smul' c μ := by simp [LinearMap.lTensor_smul]

/-- Contraction read off a finite expansion of the coevaluation. -/
theorem coevContract_eq_sum (s : Finset (X × Y))
    (hs : ((η_ X Y).hom (1 : F)) = ∑ x ∈ s, x.1 ⊗ₜ[F] x.2) (μ : Y →ₗ[F] F) :
    coevContract X Y μ = ∑ x ∈ s, μ x.2 • x.1 := by
  simp [coevContract, hs]

/-- Contracting the coevaluation against the functional `ε(-, x)` returns `x`: this is the first
triangle identity. -/
theorem coevContract_flip_pairingU (x : X) :
    coevContract X Y ((pairingU X Y).flip x) = x := by
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset ((η_ X Y).hom (1 : F))
  rw [coevContract_eq_sum X Y s hs]
  exact .trans (Finset.sum_congr rfl fun _ _ => rfl) (expand_X X Y s hs x)

/-- Pairing the contraction of the coevaluation against `μ` with the evaluation returns `μ`:
this is the second triangle identity. -/
theorem flip_pairingU_coevContract (μ : Y →ₗ[F] F) :
    (pairingU X Y).flip (coevContract X Y μ) = μ := by
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset ((η_ X Y).hom (1 : F))
  ext y
  have h := congrArg μ (expand_Y X Y s hs y)
  rw [map_sum] at h
  simp only [map_smul, smul_eq_mul, ← pairingU_apply] at h
  rw [LinearMap.flip_apply, coevContract_eq_sum X Y s hs, map_sum, ← h]
  exact Finset.sum_congr rfl fun x _ => by rw [map_smul, smul_eq_mul, mul_comm]

/-- **The duality defined by the coevaluation of an exact pairing of `F`-modules**: contracting
`η` against a functional on `Y` is a linear isomorphism `Y^* ≃ X`, inverse to the evaluation
pairing. -/
noncomputable def coevEquiv : (Y →ₗ[F] F) ≃ₗ[F] X :=
  LinearEquiv.ofLinearMap (coevContract X Y) (pairingU X Y).flip
    (LinearMap.ext fun x => coevContract_flip_pairingU X Y x)
    (LinearMap.ext fun μ => flip_pairingU_coevContract X Y μ)

@[simp] theorem coevEquiv_apply (μ : Y →ₗ[F] F) : coevEquiv X Y μ = coevContract X Y μ := rfl

@[simp] theorem coevEquiv_symm_apply (x : X) :
    (coevEquiv X Y).symm x = (pairingU X Y).flip x := rfl

end Ungraded

section Graded

variable {F : Type uF} [Field F] (V W : GradedObject ℤ (ModuleCat.{uF} F)) [ExactPairing V W]

/-- **Stacks Project, Tag 0FIK.** The class `γ([Δ])` defines a perfect duality between `H^i(X)`
and `H^{2d - i}(X)(d)`: contracting its degree-`i` Künneth component against a linear functional
on `H^{2d - i}(X)(d)` is a linear isomorphism onto `H^i(X)`.

Here `V i` is `H^i(X)`, `W (-i)` is `H^{2d - i}(X)(d)`, and the left-dual structure is the one
Lemma 45.14.5, Tag 0FIJ, produces, whose coevaluation is multiplication by `γ([Δ])`. The
inverse is the pairing of Tag 0FFV, recorded in `diagonalDuality_symm_apply`. -/
@[stacks 0FIK "the perfect duality that `γ([Δ])` defines between `H^i(X)` and `H^{2d-i}(X)(d)`; \
  the left-dual structure of `H^*(X)` produced by Lemma 45.14.5, Tag 0FIJ, is carried as the \
  hypothesis `ExactPairing V W`, as the remark itself directs"]
noncomputable def diagonalDuality (i : ℤ) : (W (-i) →ₗ[F] F) ≃ₗ[F] V i :=
  letI := exactPairingApply V W i
  coevEquiv (V i) (W (-i))

/-- The duality is contraction against the degree-`i` Künneth component of `γ([Δ])`. -/
theorem diagonalDuality_apply (i : ℤ) (μ : W (-i) →ₗ[F] F) :
    diagonalDuality V W i μ =
      TensorProduct.rid F (V i)
        (LinearMap.lTensor (V i) μ ((coevApply V W i).hom (1 : F))) :=
  rfl

/-- The inverse of the duality defined by `γ([Δ])` is the degreewise pairing whose perfectness
is Tag 0FFV. -/
theorem diagonalDuality_symm_apply (i : ℤ) (a : V i) :
    (diagonalDuality V W i).symm a = (gradedPairing V W i).flip a :=
  rfl

/-- Two functionals with the same contraction against `γ([Δ])` are equal. -/
theorem eq_of_diagonalDuality_eq {i : ℤ} {μ ν : W (-i) →ₗ[F] F}
    (h : diagonalDuality V W i μ = diagonalDuality V W i ν) : μ = ν :=
  (diagonalDuality V W i).injective h

/-- **Stacks Project, Tag 0FIK.** The trace map is unique: an `F`-linear map
`λ : H^{2d}(X)(d) → F` satisfying the normalisation `(id ⊗ λ) γ([Δ]) = 1` of axiom `(A6)` is
determined by that equation, because contraction of `γ([Δ])` against a functional is injective
in degree `0`. This is what licenses the notation `∫_X` for it. -/
@[stacks 0FIK "uniqueness of the trace map `∫_X = λ` of axiom (A6), the remark's conclusion; \
  the normalisation `(id ⊗ λ) γ([Δ]) = 1` is axiom (A6) and the left-dual structure is Lemma \
  45.14.5, Tag 0FIJ"]
theorem traceMap_unique (one : V 0) {lam lam' : W 0 →ₗ[F] F}
    (hlam : diagonalDuality V W 0 lam = one) (hlam' : diagonalDuality V W 0 lam' = one) :
    lam = lam' :=
  eq_of_diagonalDuality_eq V W (hlam.trans hlam'.symm)

end Graded

end Stacks.WeilCohomology

end
