module

public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Unramified.Field

/-!
# A finite separable extension with connected tensor square is trivial

Let `k` be a field and `K/k` a finite separable extension. If the spectrum of `K ⊗[k] K` is a
connected space then `K = k`, in the sense that `algebraMap k K` is bijective, equivalently
`Module.finrank k K = 1`.

Separability is what makes this work: for `K/k` purely inseparable of positive degree the
spectrum of `K ⊗[k] K` is a single point, hence connected, while `K ≠ k`. Finiteness is also
needed: `k(t) ⊗[k] k(t)` is a domain, so its spectrum is connected.

## Main results

* `Stacks.SeparableSelfTensor.isField_of_connectedSpace`: `K ⊗[k] K` is a field.
* `Stacks.SeparableSelfTensor.finrank_eq_one_of_connectedSpace`: `Module.finrank k K = 1`.
* `Stacks.SeparableSelfTensor.bijective_algebraMap_of_connectedSpace`:
  `algebraMap k K` is bijective.

## Implementation notes

`K ⊗[k] K` is reduced because `K/k` is separable, hence formally étale, and a formally
unramified algebra over a field is reduced
(`Algebra.FormallyUnramified.isReduced_of_field`). It is Artinian because it is a
finite-dimensional `k`-algebra, so its spectrum is finite and discrete. A discrete connected
nonempty space is a point, and a reduced ring whose spectrum is a point is a field
(`PrimeSpectrum.subsingleton_iff_isField_of_isReduced`).

The degree is then forced by the multiplication map `Algebra.TensorProduct.lmul'`, which is a
surjection of `k`-algebras `K ⊗[k] K → K` and is injective because its source is a field; so
`[K : k]² = [K : k]`.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.SeparableSelfTensor

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
  [Algebra.IsSeparable k K]

/-- **The tensor square of a finite separable extension with connected spectrum is a field.**
Reducedness comes from separability and the dimension-zero Artinian spectrum is discrete, so a
connected spectrum is a single point. -/
theorem isField_of_connectedSpace (h : ConnectedSpace (PrimeSpectrum (K ⊗[k] K))) :
    IsField (K ⊗[k] K) := by
  have hnt : Nontrivial (K ⊗[k] K) := Module.FaithfullyFlat.lTensor_nontrivial k K K
  have : Algebra.FormallyEtale k K := .of_isSeparable k K
  let : Algebra K (K ⊗[k] K) := Algebra.TensorProduct.leftAlgebra
  have hred : IsReduced (K ⊗[k] K) :=
    Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[k] K)
  have : IsArtinianRing (K ⊗[k] K) := IsArtinianRing.of_finite k (K ⊗[k] K)
  refine PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp ⟨fun a b => ?_⟩
  have := h.toPreconnectedSpace
  have huniv : ({a} : Set (PrimeSpectrum (K ⊗[k] K))) = Set.univ :=
    (isClopen_discrete _).eq_univ ⟨a, rfl⟩
  exact (huniv.symm ▸ Set.mem_univ b : b ∈ ({a} : Set (PrimeSpectrum (K ⊗[k] K)))).symm

/-- **A finite separable extension whose tensor square has connected spectrum is trivial.**
Multiplication `K ⊗[k] K → K` is a surjection out of a field, hence an isomorphism, so
`[K : k]² = [K : k]`. -/
theorem finrank_eq_one_of_connectedSpace (h : ConnectedSpace (PrimeSpectrum (K ⊗[k] K))) :
    Module.finrank k K = 1 := by
  let : Field (K ⊗[k] K) := (isField_of_connectedSpace k K h).toField
  let φ : K ⊗[k] K →ₐ[k] K := Algebra.TensorProduct.lmul' k
  have hsurj : Function.Surjective φ := fun x => ⟨x ⊗ₜ[k] 1, by simp [φ]⟩
  have hdim : Module.finrank k (K ⊗[k] K) = Module.finrank k K :=
    (AlgEquiv.ofBijective φ ⟨RingHom.injective φ.toRingHom, hsurj⟩).toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct] at hdim
  have hp : 0 < Module.finrank k K := Module.finrank_pos
  nlinarith

/-- **A finite separable extension whose tensor square has connected spectrum is trivial**,
stated as bijectivity of the structure map. -/
theorem bijective_algebraMap_of_connectedSpace
    (h : ConnectedSpace (PrimeSpectrum (K ⊗[k] K))) : Function.Bijective (algebraMap k K) :=
  Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (finrank_eq_one_of_connectedSpace k K h)

end Stacks.SeparableSelfTensor

end
