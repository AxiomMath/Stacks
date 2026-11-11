module

import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reducedness of tensor products over a field

Let `k` be a field. The tensor product `R ⊗[k] S` of a reduced `k`-algebra `R` with a
geometrically reduced `k`-algebra `S` is reduced, and so is `K ⊗[k] S` for a reduced `k`-algebra
`S` and a field extension `K/k` which is separable or separably generated. Over a perfect field
every reduced algebra is geometrically reduced, so any two reduced algebras have reduced tensor
product.

## Main results

* `Algebra.IsGeometricallyReduced.isReduced_tensorProduct`: the tensor product of a reduced
  `k`-algebra with a geometrically reduced `k`-algebra is reduced.
* `Algebra.IsGeometricallyReduced.of_perfectField`: over a perfect field every reduced algebra is
  geometrically reduced.
* `PerfectField.isReduced_tensorProduct`: over a perfect field the tensor product of two reduced
  algebras is reduced.
* `Algebra.IsGeometricallyReduced.of_isSeparable`: a separable algebraic extension is
  geometrically reduced.
* `Stacks.GeometricallyReduced.Separability.isGeometricallyReduced_of_isSeparablyGenerated`: a
  separably generated field extension is geometrically reduced.
* `Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated`: for a reduced
  `k`-algebra `S` and a separable, or separably generated, field extension `K/k`, the ring
  `K ⊗[k] S` is reduced.
* `isField_tensorProduct_of_isSeparableExtension_of_isPurelyInseparable` (in the namespace
  `Stacks.GeometricallyReduced.Separability`): the base change of a separable extension to a
  purely inseparable one is a field.

## References

* [Stacks Project, Tag 034N](https://stacks.math.columbia.edu/tag/034N)
* [Stacks Project, Tag 030U](https://stacks.math.columbia.edu/tag/030U)
* [Stacks Project, Tag 00I4](https://stacks.math.columbia.edu/tag/00I4)
-/

@[expose] public section

universe u v w

/-! ### Tensor products with a geometrically reduced algebra -/

namespace Stacks.GeometricallyReduced.TensorReduced

open TensorProduct

/-- A reduced `k`-algebra `R` embeds into the product, over the minimal primes `p` of `R`, of the
fraction fields of the domains `R ⧸ p`. -/
private theorem exists_injective_pi_fractionRing_quotient_minimalPrimes (k : Type*)
    [CommSemiring k] (R : Type*) [CommRing R] [Algebra k R] [IsReduced R] :
    ∃ φ : R →ₐ[k] ∀ p : minimalPrimes R, FractionRing (R ⧸ (p : Ideal R)),
      Function.Injective φ := by
  refine ⟨AlgHom.pi fun p ↦ (IsScalarTower.toAlgHom k (R ⧸ (p : Ideal R)) _).comp
    (Ideal.Quotient.mkₐ k (p : Ideal R)), (injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_⟩
  have hmem : a ∈ sInf (minimalPrimes R) :=
    Ideal.mem_sInf.mpr fun q hq ↦ Ideal.Quotient.eq_zero_iff_mem.mp
      (FaithfulSMul.algebraMap_injective (R ⧸ q) (FractionRing (R ⧸ q))
        (by simpa using congrFun ha ⟨q, hq⟩))
  simpa [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced] using hmem

/-- A reduced Noetherian `k`-algebra `R` in the universe of `k` has reduced base change along a
`k`-algebra `S` all of whose base changes to the field extensions of `k` in that universe are
reduced. -/
private theorem isReduced_tensorProduct_of_isNoetherianRing (k : Type u) [Field k] (S : Type v)
    [CommRing S] [Algebra k S] (hS : ∀ (L : Type u) [Field L] [Algebra k L], IsReduced (L ⊗[k] S))
    (R : Type u) [CommRing R] [Algebra k R] [IsReduced R] [IsNoetherianRing R] :
    IsReduced (S ⊗[k] R) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_injective_pi_fractionRing_quotient_minimalPrimes k R
  have : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  have hp : ∀ p : minimalPrimes R, (p : Ideal R).IsPrime := fun p ↦ IsMinimalPrime.isPrime p.2
  have hfactors : ∀ p : minimalPrimes R, IsReduced (S ⊗[k] FractionRing (R ⧸ (p : Ideal R))) :=
    fun p ↦ isReduced_tensorProduct_comm.mp (hS _)
  have : IsReduced (S ⊗[k] ∀ p : minimalPrimes R, FractionRing (R ⧸ (p : Ideal R))) :=
    isReduced_of_injective (Algebra.TensorProduct.piRight k k S _) (AlgEquiv.injective _)
  exact SeparableBaseChange.isReduced_tensorProduct_of_injective_right φ hφ ‹_›

/-- For a field `k`, the tensor product of a reduced `k`-algebra `R` with a geometrically reduced
`k`-algebra `S` is reduced. -/
public theorem solution
    (k : Type u) (R : Type v) (S : Type w) [Field k] [CommRing R] [Algebra k R] [IsReduced R]
    [CommRing S] [Algebra k S] [Algebra.IsGeometricallyReduced k S] :
    IsReduced (R ⊗[k] S) := by
  have hS : ∀ (L : Type u) [Field L] [Algebra k L], IsReduced (L ⊗[k] S) :=
    ((Algebra.isGeometricallyReduced_tfae k (ringExpChar k) S
      (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)).out 6 5).mp
      ‹Algebra.IsGeometricallyReduced k S›
  refine isReduced_tensorProduct_comm.mp
    (IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB ↦ ?_)
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    ((Subalgebra.fg_iff_finiteType B).mp hB)
  have e := Ideal.quotientKerAlgEquivOfSurjective hf
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : IsReduced (MvPolynomial (Fin n) k ⧸ RingHom.ker f) := isReduced_of_injective e e.injective
  have : IsReduced (S ⊗[k] (MvPolynomial (Fin n) k ⧸ RingHom.ker f)) :=
    isReduced_tensorProduct_of_isNoetherianRing k S hS _
  exact SeparableBaseChange.isReduced_tensorProduct_of_injective_right e.symm.toAlgHom
    e.symm.injective ‹_›

end Stacks.GeometricallyReduced.TensorReduced

@[expose] public section

open TensorProduct

/-- The tensor product of a reduced `k`-algebra `R` with a geometrically reduced `k`-algebra `S`
is reduced. -/
@[stacks 034N "Stated with Mathlib's `Algebra.IsGeometricallyReduced` in place of the source's
  Definition 030S, the two being equivalent by Lemma 030V; as an instance, since both hypotheses
  are classes."]
public instance Algebra.IsGeometricallyReduced.isReduced_tensorProduct
    (k R S : Type*) [Field k] [CommRing R] [Algebra k R] [IsReduced R]
    [CommRing S] [Algebra k S] [Algebra.IsGeometricallyReduced k S] :
    IsReduced (R ⊗[k] S) := Stacks.GeometricallyReduced.TensorReduced.solution k R S

/-! ### Reduced algebras over a perfect field -/

/-- Over a perfect field `k`, every reduced `k`-algebra is geometrically reduced. -/
@[stacks 00I4 "Clause (1): over a perfect field `k` every reduced `k`-algebra is geometrically
  reduced, stated with Mathlib's `Algebra.IsGeometricallyReduced` (equivalent to the source's
  Definition 030S by Lemma 030V); the source's form, reducedness of `K ⊗[k] S` for every field
  extension `K/k`, is `PerfectField.isReduced_tensorProduct_field`."]
public theorem Algebra.IsGeometricallyReduced.of_perfectField (k S : Type*) [Field k]
    [PerfectField k] [CommRing S] [Algebra k S] [IsReduced S] :
    Algebra.IsGeometricallyReduced k S := by
  have : IsPerfectClosure (algebraMap k k) (ringExpChar k) :=
    IsPRadical.of_id (K := k) (p := ringExpChar k)
  refine ((Algebra.isGeometricallyReduced_tfae k (ringExpChar k) S k
    (AlgebraicClosure k)).out 3 6).mp ?_
  exact isReduced_of_injective (Algebra.TensorProduct.lid k S) (AlgEquiv.injective _)

/-- Over a perfect field `k`, the tensor product of two reduced `k`-algebras is reduced. -/
@[stacks 00I4 "Clause (2): over a perfect field `k` the tensor product `R ⊗[k] S` of two reduced
  `k`-algebras is reduced."]
public theorem PerfectField.isReduced_tensorProduct (k R S : Type*) [Field k] [PerfectField k]
    [CommRing R] [Algebra k R] [IsReduced R] [CommRing S] [Algebra k S] [IsReduced S] :
    IsReduced (R ⊗[k] S) :=
  have := Algebra.IsGeometricallyReduced.of_perfectField k S
  inferInstance

/-- Over a perfect field `k`, a reduced `k`-algebra `S` is geometrically reduced in the sense of
Definition 030S: `K ⊗[k] S` is reduced for every field extension `K/k`. -/
@[stacks 00I4 "Clause (1) in the source's Definition 030S of geometric reducedness: over a perfect
  field `k`, for a reduced `k`-algebra `S`, the ring `K ⊗[k] S` is reduced for every field extension
  `K/k`."]
public theorem PerfectField.isReduced_tensorProduct_field (k S : Type*) [Field k] [PerfectField k]
    [CommRing S] [Algebra k S] [IsReduced S] (K : Type*) [Field K] [Algebra k K] :
    IsReduced (K ⊗[k] S) :=
  PerfectField.isReduced_tensorProduct k K S

end

/-! ### Base change along a separable or separably generated extension -/

namespace Stacks.GeometricallyReduced.Separability

open TensorProduct

/-- Let `k → F → A` with `F` a field and `A` geometrically reduced over `F`. If `F ⊗[k] S` is
reduced, then so is `A ⊗[k] S`. -/
private theorem isReduced_tensorProduct_of_isGeometricallyReduced (k F A S : Type*) [Field k]
    [Field F] [CommRing A] [CommRing S] [Algebra k F] [Algebra k A] [Algebra F A]
    [IsScalarTower k F A] [Algebra k S] [Algebra.IsGeometricallyReduced F A]
    (h : IsReduced (F ⊗[k] S)) : IsReduced (A ⊗[k] S) :=
  have := h
  have : IsReduced (A ⊗[F] (F ⊗[k] S)) := isReduced_tensorProduct_comm.mp inferInstance
  isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange k F A A S).symm
    (AlgEquiv.injective _)

/-- A separable algebraic extension of finite type is geometrically reduced. -/
@[ega "IV 6.7.6" "special case"]
private theorem isGeometricallyReduced_of_essFiniteType (F K : Type*) [Field F] [Field K]
    [Algebra F K] [Algebra.IsSeparable F K] [Algebra.EssFiniteType F K] :
    Algebra.IsGeometricallyReduced F K := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  have : Algebra.FormallyUnramified F K := Algebra.FormallyUnramified.of_isSeparable F K
  exact Algebra.FormallyUnramified.isReduced_of_field (AlgebraicClosure F) _

/-- A separable algebraic extension is geometrically reduced. -/
public theorem _root_.Algebra.IsGeometricallyReduced.of_isSeparable (F K : Type*) [Field F]
    [Field K] [Algebra F K] [Algebra.IsSeparable F K] : Algebra.IsGeometricallyReduced F K :=
  Stacks.FormallySmooth.SeparableTFAE.isGeometricallyReduced_of_forall_essFiniteType F K fun K' =>
    isGeometricallyReduced_of_essFiniteType F K'

/-- A separably generated field extension is geometrically reduced. -/
public theorem isGeometricallyReduced_of_isSeparablyGenerated (k : Type u) (K : Type v) [Field k]
    [Field K] [Algebra k K] [Algebra.IsSeparablyGenerated k K] :
    Algebra.IsGeometricallyReduced k K := by
  obtain ⟨s, hs, hsep⟩ :=
    Algebra.IsSeparablyGenerated.isSeparable (k := k) (K := K)
  have := Algebra.IsGeometricallyReduced.of_isSeparable (IntermediateField.adjoin k s) K
  have := Stacks.GeometricallyReduced.TestFields.isReduced_tensorProduct_fractionRing_mvPolynomial
    k (s : Type v) (AlgebraicClosure k)
  have e : FractionRing (MvPolynomial (s : Type v) k) ≃ₐ[k] IntermediateField.adjoin k s :=
    hs.1.aevalEquivField.trans (IntermediateField.equivOfEq (by rw [Subtype.range_coe]))
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact isReduced_tensorProduct_comm.mp (isReduced_tensorProduct_of_isGeometricallyReduced k
    (IntermediateField.adjoin k s) K (AlgebraicClosure k)
    (isReduced_of_injective (Algebra.TensorProduct.congr e.symm AlgEquiv.refl)
      (AlgEquiv.injective _)))

/-- For a field `k`, a reduced `k`-algebra `S` and a field extension `K/k` which is separable or
separably generated, the ring `K ⊗[k] S` is reduced. -/
public theorem solution
    {k K S : Type*} [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] [IsReduced S]
    (hK : Algebra.IsSeparableExtension k K ∨ Algebra.IsSeparablyGenerated k K) :
    IsReduced (K ⊗[k] S) :=
  have : Algebra.IsGeometricallyReduced k K := hK.elim
    (fun h => have := h;
      Stacks.FormallySmooth.SeparableTFAE.isGeometricallyReduced_of_isSeparableExtension k K)
    (fun h => have := h; isGeometricallyReduced_of_isSeparablyGenerated k K)
  isReduced_tensorProduct_comm.mp inferInstance

end Stacks.GeometricallyReduced.Separability

@[expose] public section

open TensorProduct

/-- Let `k` be a field, let `S` be a reduced `k`-algebra and let `K/k` be a field extension which
is either separable or separably generated. Then `K ⊗[k] S` is reduced. -/
@[stacks 030U "Stated with the two notions of Definition 030O as a disjunctive hypothesis, as in
  the source: separably generated implies separable is Lemma 030X, whose proof uses this lemma.",
  ega "0 23.1.7" "partial",
  ega "IV 4.3.5" "more general",
  ega "IV 4.3.6" "special case"]
public theorem Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated
    {k K S : Type*} [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] [IsReduced S]
    (hK : Algebra.IsSeparableExtension k K ∨ Algebra.IsSeparablyGenerated k K) :
    IsReduced (K ⊗[k] S) := Stacks.GeometricallyReduced.Separability.solution hK

namespace Stacks.GeometricallyReduced.Separability

/-- **The base change of a separable extension to a purely inseparable one is a field.** For `K/k`
separable and `k'/k` purely inseparable, `k' ⊗[k] K` is a field. -/
@[ega "IV 4.3.5" "special case"]
public theorem isField_tensorProduct_of_isSeparableExtension_of_isPurelyInseparable
    (k K k' : Type*) [Field k] [Field K] [Field k'] [Algebra k K] [Algebra k k']
    [Algebra.IsSeparableExtension k K] [IsPurelyInseparable k k'] : IsField (k' ⊗[k] K) := by
  have : IsReduced (K ⊗[k] k') :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated
      (Or.inl ‹Algebra.IsSeparableExtension k K›)
  have hsub : Subsingleton (PrimeSpectrum (K ⊗[k] k')) :=
    ⟨fun _ _ => (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k k' K).injective
      (Subsingleton.elim _ _)⟩
  exact MulEquiv.isField (PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp hsub)
    (Algebra.TensorProduct.comm k k' K).toRingEquiv.toMulEquiv

end Stacks.GeometricallyReduced.Separability

end
