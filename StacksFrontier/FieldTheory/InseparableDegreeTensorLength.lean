module

public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.FieldTheory.SeparableAlgebraic.TensorProduct
public import StacksFrontier.RingTheory.TensorProduct.LocalAlgebra
public import StacksCore.Tactic.StacksAttribute

/-!
# The length of a local factor of a finite field extension tensored with an algebraically
closed field

Let `L/k` be a finite field extension and let `K/k` be algebraically closed. The ring
`K \otimes_k L` is artinian, and every one of its local factors has length the inseparable
degree `[L : k]_i`. Equivalently: the separable part of `L/k` splits the tensor product into
`[L : k]_s` local factors, indexed by the embeddings of the separable closure of `k` in `L`
into `K`, and each factor is a local ring whose length is the remaining, purely inseparable,
part of the degree.

## Main results

* `Field.length_atPrime_algClosedTensor_eq_finInsepDegree` — the length of the localization of
  `K \otimes_k L` at a prime is `[L : k]_i`.
* `Field.length_atPrime_tensorAlgClosed_eq_finInsepDegree` — the same with the factors of the
  tensor product in the other order.

## Implementation notes

The length is taken over the localization itself, so it is the length of the local artinian
ring `(K \otimes_k L)_\mathfrak p` as a module over itself; it is finite, so it is read as a
natural number.

The proof passes to `F = separableClosure k L`. An embedding `L \to K` is produced from the
prime, which makes `K` an `F`-algebra; the comparison map `K \otimes_k L \to K \otimes_F L`
is then a localization at that prime, by
`Algebra.TensorProduct.exists_isLocalization_mapOfCompatibleSMul_of_isSeparable`. Since `L/F`
is purely inseparable, `K \otimes_F L` is local with residue field `K`, so its length over
itself is its `K`-dimension, which is `[L : F] = [L : k]_i`.

Tag `0F3D` is formalized as `AlgebraicGeometry.flatQuasiFiniteWeight_isWeighting`; it
computes the weighting of a flat locally quasi-finite morphism and does not supply this
field-theoretic length, so the results here are independent of it and can be cited directly.
The first paragraph of the proof of Stacks tag `0H5P` is exactly such a consumer: the equality
`[\kappa(x) : \kappa(s)]_i = \text{length}((k \otimes_{\kappa(s)} \kappa(x))_\mathfrak p)`
for `k` an algebraic closure is the one step that proof reduces its base-change compatibility
to.

## References

* [Stacks Project, Lemma 030K](https://stacks.math.columbia.edu/tag/030K)
* [Stacks Project, Lemma 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
-/

@[expose] public section

open scoped TensorProduct

universe u

/-- Isomorphic rings have the same length over themselves. -/
theorem Module.length_self_eq_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso e.idealComapOrderIso.symm]

/-- A nontrivial commutative ring with exactly one prime ideal is local. -/
private lemma isLocalRing_of_existsUnique_isPrime {R : Type u} [CommRing R]
    (h : ∃! P : Ideal R, P.IsPrime) : IsLocalRing R := by
  obtain ⟨P, hP, huniq⟩ := h
  have : Nontrivial R :=
    ⟨⟨0, 1, fun e => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ P.zero_mem (e ▸ isUnit_one))⟩⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := R)
  exact IsLocalRing.of_unique_max_ideal
    ⟨m, hm, fun n hn => ((huniq m hm.isPrime).trans (huniq n hn.isPrime).symm).symm⟩

namespace Field

/-- Let `L/k` be finite and let `K/k` be algebraically closed. Then every prime of `K ⊗_k L` is
the kernel of a `K`-algebra map `K ⊗_k L → K`. -/
private theorem exists_algHom_ker_eq_of_isAlgClosed
    (k L K : Type u) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
    [Module.Finite k L] [IsAlgClosed K] (t : Ideal (K ⊗[k] L)) [t.IsPrime] :
    ∃ τ : K ⊗[k] L →ₐ[K] K, RingHom.ker τ = t := by
  have : Module.Finite K (K ⊗[k] L) := Module.Finite.base_change k K L
  have : IsArtinianRing (K ⊗[k] L) := IsArtinianRing.of_finite K _
  have : t.IsMaximal := IsArtinianRing.isMaximal_of_isPrime t
  have : Field ((K ⊗[k] L) ⧸ t) := Ideal.Quotient.field t
  have : Module.Finite K ((K ⊗[k] L) ⧸ t) :=
    Module.Finite.of_surjective ((Algebra.linearMap (K ⊗[k] L) _).restrictScalars K)
      Ideal.Quotient.mk_surjective
  have : Algebra.IsIntegral K ((K ⊗[k] L) ⧸ t) := Algebra.IsIntegral.of_finite K _
  have hbij : Function.Bijective (algebraMap K ((K ⊗[k] L) ⧸ t)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨(AlgEquiv.ofBijective (Algebra.ofId K _) hbij).symm.toAlgHom.comp
    (Ideal.Quotient.mkₐ K t), ?_⟩
  ext r
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- Let `F/k` be separable algebraic and let `K`, `L` be `F`-algebras with `K ⊗_F L` local. If
`t` is the prime of `K ⊗_k L` under the maximal ideal of `K ⊗_F L`, then the localization of
`K ⊗_k L` at `t` has the same length as `K ⊗_F L`. -/
private theorem length_atPrime_eq_length_tensor_of_isSeparable
    {k F K L : Type u} [Field k] [Field F] [CommRing K] [CommRing L] [Algebra k F]
    [Algebra.IsSeparable k F] [Algebra k K] [Algebra k L] [Algebra F K] [Algebra F L]
    [IsScalarTower k F K] [IsScalarTower k F L] [IsLocalRing (K ⊗[F] L)]
    (t : Ideal (K ⊗[k] L)) [t.IsPrime]
    (ht : Ideal.comap (Algebra.TensorProduct.mapOfCompatibleSMul F k F K L)
      (IsLocalRing.maximalIdeal (K ⊗[F] L)) = t) :
    Module.length (Localization.AtPrime t) (Localization.AtPrime t) =
      Module.length (K ⊗[F] L) (K ⊗[F] L) := by
  let : Algebra (K ⊗[k] L) (K ⊗[F] L) :=
    (Algebra.TensorProduct.mapOfCompatibleSMul F k F K L).toRingHom.toAlgebra
  obtain ⟨M, hM⟩ :=
    Algebra.TensorProduct.exists_isLocalization_mapOfCompatibleSMul_of_isSeparable k F K L
  have key : ∀ r, IsUnit (algebraMap (K ⊗[k] L) (K ⊗[F] L) r) ↔ r ∈ t.primeCompl := by
    intro r
    rw [← IsLocalRing.notMem_maximalIdeal, Ideal.mem_primeCompl_iff, ← ht]
    rfl
  have hle : M ≤ t.primeCompl := fun s hs => (key s).1 (IsLocalization.map_units _ ⟨s, hs⟩)
  have : IsLocalization t.primeCompl (K ⊗[F] L) :=
    IsLocalization.of_le M t.primeCompl hle fun r hr => (key r).2 hr
  exact Module.length_self_eq_of_ringEquiv
    (IsLocalization.algEquiv t.primeCompl (Localization.AtPrime t) (K ⊗[F] L)).toRingEquiv

/-- Let `L/F` be purely inseparable and `ψ : L → K` an `F`-embedding. The kernel of the induced
map `K ⊗_F L → K` is the maximal ideal of `K ⊗_F L`. -/
private lemma ker_tensorLift_eq_maximalIdeal_of_isPurelyInseparable
    {F L K : Type u} [Field F] [Field L] [Field K] [Algebra F L] [Algebra F K]
    [hpi : IsPurelyInseparable F L] [IsLocalRing (K ⊗[F] L)] (ψ : L →ₐ[F] K) :
    RingHom.ker (Algebra.TensorProduct.lift (AlgHom.id F K) ψ
      (fun _ _ => Commute.all _ _)).toRingHom = IsLocalRing.maximalIdeal (K ⊗[F] L) := by
  obtain ⟨P, _, huniq⟩ :=
    tensorField_isPurelyInseparable_unique_prime (K := F) (L := K) (M := L) (Or.inl hpi)
  rw [huniq _ (RingHom.ker_isPrime _), huniq _ (IsLocalRing.maximalIdeal.isMaximal _).isPrime]

/-- Let `L/F` be finite and purely inseparable, and let `K` be a field into which `L` embeds over
`F`. Then `K ⊗_F L` has length `[L : F]` over itself. -/
private theorem length_tensor_eq_finrank_of_isPurelyInseparable
    {F L K : Type u} [Field F] [Field L] [Field K] [Algebra F L] [Algebra F K]
    [Module.Finite F L] [hpi : IsPurelyInseparable F L] (ψ : L →ₐ[F] K) :
    Module.length (K ⊗[F] L) (K ⊗[F] L) = Module.finrank F L := by
  have : IsLocalRing (K ⊗[F] L) :=
    isLocalRing_of_existsUnique_isPrime (tensorField_isPurelyInseparable_unique_prime (Or.inl hpi))
  let χ : (K ⊗[F] L) →ₐ[F] K :=
    Algebra.TensorProduct.lift (AlgHom.id F K) ψ (fun _ _ => Commute.all _ _)
  have hχker : RingHom.ker χ.toRingHom = IsLocalRing.maximalIdeal (K ⊗[F] L) :=
    ker_tensorLift_eq_maximalIdeal_of_isPurelyInseparable _
  -- the residue field of `K ⊗_F L` is `K`, so its length over itself is its `K`-dimension
  have : IsLocalHom (algebraMap K (K ⊗[F] L)) :=
    ⟨fun a ha => by
      rcases eq_or_ne a 0 with rfl | h
      · simp only [map_zero] at ha
        exact (not_isUnit_zero ha).elim
      · exact h.isUnit⟩
  have hχK : ∀ a : K, χ (algebraMap K (K ⊗[F] L) a) = a := by
    intro a
    change χ (a ⊗ₜ[F] (1 : L)) = a
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have hsurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField (K ⊗[F] L))) := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := K ⊗[F] L) z
    refine ⟨IsLocalRing.residue K (χ x), ?_⟩
    rw [IsLocalRing.ResidueField.algebraMap_residue, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ← hχker]
    change χ _ = 0
    rw [map_sub, hχK]
    simp
  have hresone : Module.length (IsLocalRing.ResidueField K)
      (IsLocalRing.ResidueField (K ⊗[F] L)) = 1 := by
    rw [Module.length_eq_finrank,
      ← (AlgEquiv.ofBijective (Algebra.ofId (IsLocalRing.ResidueField K)
        (IsLocalRing.ResidueField (K ⊗[F] L)))
          ⟨RingHom.injective _, hsurj⟩).toLinearEquiv.finrank_eq,
      Module.finrank_self]
    rfl
  have : Module.Finite K (K ⊗[F] L) := Module.Finite.base_change F K L
  have hlen : Module.length K (K ⊗[F] L) =
      Module.length (K ⊗[F] L) (K ⊗[F] L) *
        Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField (K ⊗[F] L)) :=
    IsLocalRing.length_restrictScalars K (K ⊗[F] L) (K ⊗[F] L)
  rw [hresone, mul_one, Module.length_eq_finrank, Module.finrank_baseChange] at hlen
  exact hlen.symm

/-- Let `L/k` be finite and let `K/k` be algebraically closed. Then every local factor of
`K ⊗_k L` has length the inseparable degree of `L/k`. -/
theorem length_atPrime_algClosedTensor_eq_finInsepDegree
    (k L K : Type u) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
    [Module.Finite k L] [IsAlgClosed K] (t : Ideal (K ⊗[k] L)) [t.IsPrime] :
    (Module.length (Localization.AtPrime t) (Localization.AtPrime t)).toNat =
      Field.finInsepDegree k L := by
  obtain ⟨τ, hτker⟩ := exists_algHom_ker_eq_of_isAlgClosed k L K t
  let ψ : L →ₐ[k] K := (τ.restrictScalars k).comp Algebra.TensorProduct.includeRight
  -- the separable closure of `k` in `L`, and the `F`-algebra structure it induces on `K`
  let F := separableClosure k L
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  have : Algebra.IsSeparable k F := separableClosure.isSeparable k L
  have hpi : IsPurelyInseparable F L := separableClosure.isPurelyInseparable k L
  have : Module.Finite F L := Module.Finite.of_restrictScalars_finite k F L
  let algFK : Algebra F K := (ψ.comp F.val).toRingHom.toAlgebra
  have : IsScalarTower k F K := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap k K a = ψ (F.val (algebraMap k F a))
    rw [show F.val (algebraMap k F a) = algebraMap k L a from rfl, ψ.commutes])
  have : IsLocalRing (K ⊗[F] L) :=
    isLocalRing_of_existsUnique_isPrime (tensorField_isPurelyInseparable_unique_prime (Or.inl hpi))
  -- the augmentation `K ⊗_F L → K`, whose kernel is the maximal ideal
  let ψF : L →ₐ[F] K := { ψ.toRingHom with commutes' := fun _ => rfl }
  let χ : (K ⊗[F] L) →ₐ[F] K :=
    Algebra.TensorProduct.lift (AlgHom.id F K) ψF (fun _ _ => Commute.all _ _)
  have hχker : RingHom.ker χ.toRingHom = IsLocalRing.maximalIdeal (K ⊗[F] L) :=
    ker_tensorLift_eq_maximalIdeal_of_isPurelyInseparable _
  have hcomp : ∀ r : K ⊗[k] L,
      χ (Algebra.TensorProduct.mapOfCompatibleSMul F k F K L r) = τ r := by
    intro r
    induction r with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul a b =>
      have h : (a ⊗ₜ[k] b : K ⊗[k] L) =
          algebraMap K (K ⊗[k] L) a * Algebra.TensorProduct.includeRight b := by
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      rw [Algebra.TensorProduct.mapOfCompatibleSMul_tmul, h, map_mul, τ.commutes]
      rfl
  have ht : Ideal.comap (Algebra.TensorProduct.mapOfCompatibleSMul F k F K L)
      (IsLocalRing.maximalIdeal (K ⊗[F] L)) = t := by
    rw [← hχker, ← hτker]
    ext r
    change χ (Algebra.TensorProduct.mapOfCompatibleSMul F k F K L r) = 0 ↔ τ r = 0
    rw [hcomp]
  rw [length_atPrime_eq_length_tensor_of_isSeparable t ht,
    length_tensor_eq_finrank_of_isPurelyInseparable ψF]
  simp only [ENat.toNat_natCast]
  rfl

/-- Let `L/k` be finite and let `K/k` be algebraically closed. Then every local factor of
`L ⊗_k K` has length the inseparable degree of `L/k`. -/
theorem length_atPrime_tensorAlgClosed_eq_finInsepDegree
    (k L K : Type u) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
    [Module.Finite k L] [IsAlgClosed K] (t : Ideal (L ⊗[k] K)) [t.IsPrime] :
    (Module.length (Localization.AtPrime t) (Localization.AtPrime t)).toNat =
      Field.finInsepDegree k L := by
  let ec : (L ⊗[k] K) ≃+* (K ⊗[k] L) := (Algebra.TensorProduct.comm k L K).toRingEquiv
  let t' : Ideal (K ⊗[k] L) := Ideal.comap ec.symm.toRingHom t
  have : t'.IsPrime := Ideal.comap_isPrime _ _
  have h : t = Ideal.comap ec.toRingHom t' := by
    ext z
    simp [t']
  rw [Module.length_self_eq_of_ringEquiv (Localization.localRingEquiv t t' ec h)]
  exact length_atPrime_algClosedTensor_eq_finInsepDegree k L K t'

end Field

end
