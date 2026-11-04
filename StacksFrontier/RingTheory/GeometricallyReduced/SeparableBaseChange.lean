module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Unramified.Field
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Base change of a reduced algebra along a separable extension

If `K/F` is a separable algebraic field extension and `T` is a reduced `F`-algebra, then
`K ⊗[F] T` is reduced. Reducedness of a tensor product is also shown to be invariant under ring
isomorphisms and to descend along an injection of either tensor factor.

## Main results

In the namespace `Stacks.GeometricallyReduced.SeparableBaseChange`:

* `isReduced_tensorProduct_of_injective_left`, `isReduced_tensorProduct_of_injective_right`:
  reducedness of a tensor product descends along an injection of either factor, the other factor
  being flat.
* `isReduced_tensorProduct_of_forall_fg_intermediateField`: `L ⊗[k] S` is reduced if `F ⊗[k] S`
  is reduced for every finitely generated subextension `F` of `L/k`.
* `isReduced_tensorProduct_of_finiteDimensional`: base change of a reduced algebra along a finite
  separable extension is reduced.
* `isReduced_tensorProduct_of_isSeparable`: base change of a reduced algebra along a separable
  algebraic extension is reduced.

In the root namespace:

* `isReduced_congr`: reducedness is invariant under a ring isomorphism.

## References

* [Stacks Project, Tag 030U](https://stacks.math.columbia.edu/tag/030U)
* [Stacks Project, Tag 00I3](https://stacks.math.columbia.edu/tag/00I3)
-/

open scoped TensorProduct

namespace Stacks.GeometricallyReduced.SeparableBaseChange

/-- Reducedness is invariant under a ring isomorphism. -/
public theorem _root_.isReduced_congr {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : IsReduced R ↔ IsReduced S :=
  ⟨fun _ => isReduced_of_injective e.symm e.symm.injective,
    fun _ => isReduced_of_injective e e.injective⟩

/-- `A ⊗[R] B` is reduced if and only if `B ⊗[R] A` is reduced. -/
private theorem isReduced_tensorProduct_comm {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] : IsReduced (A ⊗[R] B) ↔ IsReduced (B ⊗[R] A) :=
  isReduced_congr (Algebra.TensorProduct.comm R A B).toRingEquiv

/-- Reducedness of a base change `B ⊗[R] S` descends along an injection `A →ₐ[R] B` of the left
factor, provided `S` is flat over `R`. -/
public theorem isReduced_tensorProduct_of_injective_left {R S A B : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (hf : Function.Injective f) (h : IsReduced (B ⊗[R] S)) :
    IsReduced (A ⊗[R] S) :=
  have := h
  isReduced_of_injective (Algebra.TensorProduct.map f (AlgHom.id R S))
    (Module.Flat.rTensor_preserves_injective_linearMap _ hf)

/-- Reducedness of a base change `A ⊗[R] B` descends along an injection `S →ₐ[R] B` of the right
factor, provided `A` is flat over `R`. -/
public theorem isReduced_tensorProduct_of_injective_right {R A S B : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] [CommRing S] [CommRing B] [Algebra R S]
    [Algebra R B] (f : S →ₐ[R] B) (hf : Function.Injective f) (h : IsReduced (A ⊗[R] B)) :
    IsReduced (A ⊗[R] S) :=
  have := h
  isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id R A) f)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)

/-- If `F ⊗[k] S` is reduced for every finitely generated subextension `F` of a field extension
`L/k`, then `L ⊗[k] S` is reduced. -/
public theorem isReduced_tensorProduct_of_forall_fg_intermediateField
    {k L S : Type*} [Field k] [Field L] [Algebra k L] [CommRing S] [Algebra k S]
    (H : ∀ F : IntermediateField k L, F.FG → IsReduced (↥F ⊗[k] S)) :
    IsReduced (L ⊗[k] S) := by
  rw [isReduced_tensorProduct_comm]
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB ↦ ?_
  obtain ⟨s, rfl⟩ := hB
  have hle : Algebra.adjoin k (s : Set L) ≤ (IntermediateField.adjoin k (s : Set L)).toSubalgebra :=
    IntermediateField.algebra_adjoin_le_adjoin k _
  refine isReduced_tensorProduct_of_injective_right (Subalgebra.inclusion hle)
    (Subalgebra.inclusion_injective hle) ?_
  rw [isReduced_tensorProduct_comm]
  exact H _ ⟨s, rfl⟩

/-- Base change of a reduced Noetherian algebra along a finite separable field extension is
reduced. -/
@[ega "0 23.1.7" "partial",
  ega "IV 4.3.5" "special case",
  ega "IV 4.3.6" "special case",
  ega "IV 6.7.6" "special case"]
public theorem isReduced_tensorProduct_of_isNoetherianRing_of_finiteDimensional
    {F B C : Type*} [Field F] [Field B] [Algebra F B] [Algebra.IsSeparable F B]
    [FiniteDimensional F B] [CommRing C] [Algebra F C] [IsReduced C] [IsNoetherianRing C] :
    IsReduced (B ⊗[F] C) := by
  classical
  have : ∀ q : minimalPrimes C, (q : Ideal C).IsPrime := fun q ↦ q.2.1.1
  have : Fintype (minimalPrimes C) := (minimalPrimes.finite_of_isNoetherianRing C).fintype
  set L : minimalPrimes C → Type _ := fun q ↦ Localization.AtPrime (q : Ideal C)
  have hfac : ∀ q, IsReduced (B ⊗[F] L q) := fun q ↦ by
    let _ : Field (L q) := (minimal_prime_reduced_localization_isField C _ q.2).toField
    have : Algebra.FormallyUnramified F B := Algebra.FormallyUnramified.of_isSeparable F B
    rw [isReduced_tensorProduct_comm]
    exact Algebra.FormallyUnramified.isReduced_of_field (L q) _
  refine isReduced_tensorProduct_of_injective_right
    ((Algebra.ofId C (∀ q, L q)).restrictScalars F)
    (fun x y hxy ↦ localizationProdMap_injective C
      (funext fun q ↦ by simpa using congrFun hxy q)) ?_
  exact (isReduced_congr (Algebra.TensorProduct.piRight F F B L).toRingEquiv).2 inferInstance

/-- Base change of a reduced algebra along a finite separable field extension is reduced. -/
@[ega "0 23.1.7" "partial",
  ega "IV 4.3.5" "special case",
  ega "IV 4.3.6" "special case",
  ega "IV 6.7.6" "special case"]
public theorem isReduced_tensorProduct_of_finiteDimensional
    {F B T : Type*} [Field F] [Field B] [Algebra F B] [Algebra.IsSeparable F B]
    [FiniteDimensional F B] [CommRing T] [Algebra F T] [IsReduced T] :
    IsReduced (B ⊗[F] T) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun C hC ↦ ?_
  have : Algebra.FiniteType F ↥C := (Subalgebra.fg_iff_finiteType C).mp hC
  have : IsNoetherianRing ↥C := Algebra.FiniteType.isNoetherianRing F ↥C
  have : IsReduced ↥C := isReduced_of_injective C.val Subtype.val_injective
  exact isReduced_tensorProduct_of_isNoetherianRing_of_finiteDimensional

/-- Base change of a reduced algebra along a separable algebraic field extension is reduced. -/
@[ega "0 23.1.7" "partial",
  ega "IV 4.3.5" "special case",
  ega "IV 4.3.6" "special case",
  ega "IV 6.7.6" "special case"]
public theorem isReduced_tensorProduct_of_isSeparable
    {F K T : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsSeparable F K]
    [CommRing T] [Algebra F T] [IsReduced T] :
    IsReduced (K ⊗[F] T) := by
  refine isReduced_tensorProduct_of_forall_fg_intermediateField fun M hM ↦ ?_
  obtain ⟨s, rfl⟩ := hM
  have : FiniteDimensional F ↥(IntermediateField.adjoin F (s : Set K)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  exact isReduced_tensorProduct_of_finiteDimensional

end Stacks.GeometricallyReduced.SeparableBaseChange
