module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric reducedness is detected at the minimal primes

Let `k` be a field and let `S` be a reduced `k`-algebra. If the localization `S_𝔭` is
geometrically reduced over `k` for every minimal prime `𝔭` of `S`, then `S` itself is
geometrically reduced over `k`. Geometric reducedness is Mathlib's
`Algebra.IsGeometricallyReduced`, and `S_𝔭` is `Localization.AtPrime 𝔭`.

## Main results

* `Algebra.IsGeometricallyReduced.of_forall_minimalPrimes`: a reduced algebra over a field whose
  localizations at the minimal primes are geometrically reduced is geometrically reduced.
* `Stacks.GeometricallyReduced.MinimalPrimes.solution`: the same statement.

## References

* [Stacks 07K2](https://stacks.math.columbia.edu/tag/07K2)
-/

@[expose] public section

universe u v

namespace Stacks.GeometricallyReduced.MinimalPrimes

open TensorProduct

section Free

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {κ : Type*} [DecidableEq κ]

/-- The identification `N ⊗[R] X ≃ (κ →₀ X)` attached to a basis of the `R`-module `N` indexed
by `κ`. -/
private noncomputable def finsuppOfBasis (b : Module.Basis κ R N) (X : Type*) [AddCommGroup X]
    [Module R X] : N ⊗[R] X ≃ₗ[R] (κ →₀ X) :=
  (TensorProduct.congr b.repr (LinearEquiv.refl R X)).trans (TensorProduct.finsuppScalarLeft R X κ)

/-- The identification `finsuppOfBasis b` is natural in the second variable: it turns
`LinearMap.lTensor N g` into `Finsupp.mapRange g`. -/
private theorem finsuppOfBasis_lTensor (b : Module.Basis κ R N) {X Y : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] (g : X →ₗ[R] Y) (z : N ⊗[R] X) :
    finsuppOfBasis b Y (LinearMap.lTensor N g z)
      = Finsupp.mapRange.linearMap g (finsuppOfBasis b X z) := by
  induction z with
  | tmul n x => ext j; simp [finsuppOfBasis]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The canonical map out of a base change of a product is the product of the base changes of the
projections. -/
private theorem piRightHom_eq_pi_lTensor_proj {ι : Type*} (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    TensorProduct.piRightHom R R N M
      = LinearMap.pi fun i ↦ LinearMap.lTensor N (LinearMap.proj i) :=
  TensorProduct.ext' fun n f ↦ funext fun i ↦ by simp

/-- For a free `R`-module `N`, the canonical map `N ⊗[R] (∀ i, M i) → ∀ i, N ⊗[R] M i` is
injective. -/
private theorem piRightHom_injective [Module.Free R N] {ι : Type*} (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    Function.Injective (TensorProduct.piRightHom R R N M) := by
  classical
  set b := Module.Free.chooseBasis R N
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  refine (finsuppOfBasis b _).map_eq_zero_iff.mp (Finsupp.ext fun j ↦ funext fun i ↦ ?_)
  have h : LinearMap.lTensor N (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i) z = 0 := by
    simpa [piRightHom_eq_pi_lTensor_proj] using congrFun hz i
  simpa [h] using (DFunLike.congr_fun (finsuppOfBasis_lTensor b (LinearMap.proj i) z) j).symm

/-- Base change along a free module preserves injectivity of a product of linear maps: if `N` is a
free `R`-module and the family `f i : X →ₗ[R] Y i` has injective product, then the induced map
`N ⊗[R] X → ∀ i, N ⊗[R] Y i` is injective. -/
@[sga "3 VIB 11.7" "special case"]
private theorem injective_pi_lTensor_of_free [Module.Free R N] {X : Type*} [AddCommGroup X]
    [Module R X] {ι : Type*} {Y : ι → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)]
    (f : ∀ i, X →ₗ[R] Y i) (hf : Function.Injective (LinearMap.pi f)) :
    Function.Injective (LinearMap.pi fun i ↦ LinearMap.lTensor N (f i)) := by
  have h : (LinearMap.pi fun i ↦ LinearMap.lTensor N (f i))
      = TensorProduct.piRightHom R R N Y ∘ₗ LinearMap.lTensor N (LinearMap.pi f) :=
    TensorProduct.ext' fun n x ↦ funext fun i ↦ by simp
  simpa [h] using (piRightHom_injective Y).comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)

end Free

/-- Reducedness of a base change `K ⊗[k] X` follows from reducedness of the base changes
`K ⊗[k] Y i` along a family of `k`-algebra maps `g i : X →ₐ[k] Y i` whose product is injective,
for a field `k`. -/
private theorem isReduced_tensorProduct_of_injective_pi {k K X : Type*} {ι : Type*}
    {Y : ι → Type*} [Field k] [CommRing K] [Algebra k K] [CommRing X] [Algebra k X]
    [∀ i, CommRing (Y i)] [∀ i, Algebra k (Y i)] (g : ∀ i, X →ₐ[k] Y i)
    (hg : Function.Injective fun (x : X) i ↦ g i x) (hY : ∀ i, IsReduced (K ⊗[k] Y i)) :
    IsReduced (K ⊗[k] X) :=
  isReduced_of_injective (AlgHom.pi fun i ↦ Algebra.TensorProduct.map (AlgHom.id k K) (g i))
    (injective_pi_lTensor_of_free (fun i ↦ (g i).toLinearMap) hg)

/-- Let `k` be a field and let `S` be a reduced `k`-algebra whose localization at
every minimal prime is geometrically reduced over `k`. Then `S` is geometrically reduced. -/
public theorem solution {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [IsReduced S]
    (H : ∀ (p : Ideal S) [p.IsPrime], p ∈ minimalPrimes S →
      Algebra.IsGeometricallyReduced k (Localization.AtPrime p)) :
    Algebra.IsGeometricallyReduced k S := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  have hp (p : minimalPrimes S) : (p : Ideal S).IsPrime := p.2.1.1
  exact isReduced_tensorProduct_of_injective_pi
    (Y := fun p : minimalPrimes S ↦ Localization.AtPrime (p : Ideal S))
    (fun p ↦ IsScalarTower.toAlgHom k S (Localization.AtPrime (p : Ideal S)))
    (fun x y hxy ↦ localizationProdMap_injective S (funext fun p ↦ by simpa using congrFun hxy p))
    fun p ↦ have := H (p : Ideal S) p.2
      inferInstance

end Stacks.GeometricallyReduced.MinimalPrimes

@[expose] public section

/-- Let `k` be a field and let `S` be a reduced `k`-algebra such that the localization
`Localization.AtPrime p` is geometrically reduced over `k` for every minimal prime `p` of `S`. Then
`S` is geometrically reduced over `k`. -/
@[stacks 07K2 "Stated with Mathlib's `Algebra.IsGeometricallyReduced` in place of the source's
  Definition 030S, the two being equivalent by Lemma 030V, and with the concrete localization
  `Localization.AtPrime p` for the source's `S_𝔭`."]
public theorem Algebra.IsGeometricallyReduced.of_forall_minimalPrimes {k : Type u} {S : Type v}
    [Field k] [CommRing S] [Algebra k S] [IsReduced S]
    (H : ∀ (p : Ideal S) [p.IsPrime], p ∈ minimalPrimes S →
      Algebra.IsGeometricallyReduced k (Localization.AtPrime p)) :
    Algebra.IsGeometricallyReduced k S :=
  Stacks.GeometricallyReduced.MinimalPrimes.solution H

end
