module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.FieldTheory.InseparableDegreeTensorLength
public import StacksFrontier.RingTheory.Length.Finiteness
public import StacksFrontier.RingTheory.Length.FlatLocalHom

/-!
# The inseparable degree of a residue field extension under base change

Let `L/k` be a finite field extension, let `k'/k` be any field extension, and let `t` be a prime
of `k' \otimes_k L`. The quotient of `k' \otimes_k L` by `t` is a finite field extension `L'/k'`,
and the two inseparable degrees are related by

`[L : k]_i = length((k' \otimes_k L)_t) \cdot [L' : k']_i`.

Geometrically `k = \kappa(s)`, `k' = \kappa(s')`, `L = \kappa(x)` and `L' = \kappa(x')` for a point
`x` of a scheme over `s` and a point `x'` of its base change to `s'`; this is the displayed
equation in the first paragraph of the proof of Stacks tag `0H5P`.

## Main results

* `Field.length_atPrime_mul_finInsepDegree_eq_finInsepDegree`: the displayed equation, with the
  residue field at `t` presented abstractly as a surjection `k' \otimes_k L \to L'` of
  `k'`-algebras with kernel `t`.

## References

* [Stacks Project, Lemma 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Lemma 030K](https://stacks.math.columbia.edu/tag/030K)
-/

@[expose] public section

open scoped TensorProduct

universe u

/-- For an ideal `I` of `R`, the length of `R ⧸ I` as an `R`-module is its length as a module
over the ring `R ⧸ I`: the two lattices of submodules coincide. -/
private lemma length_quotient_eq_length_self {R : Type u} [CommRing R] (I : Ideal R) :
    Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) := by
  unfold Module.length
  congr 1
  exact (Order.krullDim_eq_of_orderIso (submoduleOrderIsoOfScalarTower I (M := R ⧸ I))).symm

/-- A ring isomorphism identifies the localization at a prime `n` with the localization at its
contraction, hence their lengths over themselves. -/
private lemma length_atPrime_comap_eq {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (n : Ideal S) [n.IsPrime] :
    Module.length (Localization.AtPrime (Ideal.comap (e : R →+* S) n))
        (Localization.AtPrime (Ideal.comap (e : R →+* S) n)) =
      Module.length (Localization.AtPrime n) (Localization.AtPrime n) :=
  Module.length_self_eq_of_ringEquiv (Localization.localRingEquiv _ n e rfl)

/-- The ring homomorphism from `R ⧸ I` to `R_P ⧸ I R_P` induced by `R → R_P`. -/
private noncomputable def quotLocalizationMap {R : Type u} [CommRing R] (I P : Ideal R)
    [P.IsPrime] :
    (R ⧸ I) →+*
      (Localization.AtPrime P ⧸ Ideal.map (algebraMap R (Localization.AtPrime P)) I) :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization.AtPrime P)) I)).comp
      (algebraMap R (Localization.AtPrime P)))
    fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)

/-- Localization commutes with quotients: if `q` is a prime of `R ⧸ I` whose preimage in `R` is
the prime `P`, then the localization of `R ⧸ I` at `q` is the quotient of `R_P` by `I R_P`. -/
private noncomputable def quotLocalizationEquiv {R : Type u} [CommRing R] (I P : Ideal R)
    [P.IsPrime] (q : Ideal (R ⧸ I)) [q.IsPrime]
    (hq : Ideal.comap (Ideal.Quotient.mk I) q = P) :
    Localization.AtPrime q ≃+*
      (Localization.AtPrime P ⧸ Ideal.map (algebraMap R (Localization.AtPrime P)) I) := by
  letI : Algebra (R ⧸ I)
      (Localization.AtPrime P ⧸ Ideal.map (algebraMap R (Localization.AtPrime P)) I) :=
    (quotLocalizationMap I P).toAlgebra
  have hmem : ∀ x : R, Ideal.Quotient.mk I x ∈ q ↔ x ∈ P := by
    intro x
    rw [← hq]
    exact Iff.rfl
  haveI : IsLocalization q.primeCompl
      (Localization.AtPrime P ⧸ Ideal.map (algebraMap R (Localization.AtPrime P)) I) := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro y
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y.1
      have hxP : x ∉ P := fun hp => y.2 (hx ▸ (hmem x).mpr hp)
      rw [show (y : R ⧸ I) = Ideal.Quotient.mk I x from hx.symm]
      exact (IsLocalization.map_units (Localization.AtPrime P)
        (⟨x, hxP⟩ : P.primeCompl)).map
        (Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization.AtPrime P)) I))
    · intro z
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl v
      have hsq : Ideal.Quotient.mk I (s : R) ∉ q := fun hh => s.2 ((hmem _).mp hh)
      refine ⟨⟨Ideal.Quotient.mk I a, ⟨Ideal.Quotient.mk I (s : R), hsq⟩⟩, ?_⟩
      change Ideal.Quotient.mk _ (IsLocalization.mk' (Localization.AtPrime P) a s) *
          Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime P) (s : R)) =
        Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime P) a)
      rw [← map_mul, IsLocalization.mk'_spec]
    · intro u w h
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
      replace h : Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization.AtPrime P)) I)
          (algebraMap R (Localization.AtPrime P) x) =
        Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime P) y) := h
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← map_sub,
        IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl] at h
      obtain ⟨m, hm, hmI⟩ := h
      refine ⟨⟨Ideal.Quotient.mk I m, fun hh => hm ((hmem m).mp hh)⟩, ?_⟩
      change Ideal.Quotient.mk I m * Ideal.Quotient.mk I x =
        Ideal.Quotient.mk I m * Ideal.Quotient.mk I y
      rw [← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
        ← mul_sub]
      exact hmI
  exact (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) _).toRingEquiv

/-- Multiplicativity of length along the flat local homomorphism `C_t → D_P`. Here `C → D` is
flat, `P` is a prime of `D` contracting to the prime `t` of `C`, and `q` is the prime of `D ⧸ tD`
cut out by `P`; the quotient `D_P ⧸ t D_P` is the localization of `D ⧸ tD` at `q`. -/
private lemma length_atPrime_mul_length_atPrime_quotient (C D : Type u) [CommRing C] [CommRing D]
    [Algebra C D] [Module.Flat C D] (t : Ideal C) [t.IsPrime] (P : Ideal D) [P.IsPrime]
    (hP : Ideal.comap (algebraMap C D) P = t)
    (q : Ideal (D ⧸ Ideal.map (algebraMap C D) t)) [q.IsPrime]
    (hq : Ideal.comap (Ideal.Quotient.mk (Ideal.map (algebraMap C D) t)) q = P) :
    Module.length (Localization.AtPrime t) (Localization.AtPrime t) *
        Module.length (Localization.AtPrime q) (Localization.AtPrime q) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) := by
  let : Algebra (Localization.AtPrime t) (Localization.AtPrime P) :=
    (Localization.localRingHom t P (algebraMap C D) hP.symm).toAlgebra
  have halg : algebraMap (Localization.AtPrime t) (Localization.AtPrime P) =
      Localization.localRingHom t P (algebraMap C D) hP.symm := rfl
  have : IsLocalHom (algebraMap (Localization.AtPrime t) (Localization.AtPrime P)) := by
    rw [halg]
    exact Localization.isLocalHom_localRingHom t P (algebraMap C D) hP.symm
  have : Module.Flat (Localization.AtPrime t) (Localization.AtPrime P) := by
    rw [← RingHom.flat_algebraMap_iff, halg]
    exact (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat C D›).localRingHom P t hP.symm
  have hcomp : (Localization.localRingHom t P (algebraMap C D) hP.symm).comp
      (algebraMap C (Localization.AtPrime t)) =
      (algebraMap D (Localization.AtPrime P)).comp (algebraMap C D) :=
    RingHom.ext fun x => Localization.localRingHom_to_map t P (algebraMap C D) hP.symm x
  have hext : extendedMaximalIdeal (Localization.AtPrime t) (Localization.AtPrime P) =
      Ideal.map (algebraMap D (Localization.AtPrime P)) (Ideal.map (algebraMap C D) t) := by
    show Ideal.map (algebraMap (Localization.AtPrime t) (Localization.AtPrime P))
        (IsLocalRing.maximalIdeal (Localization.AtPrime t)) = _
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map, halg, hcomp]
  have hrid : Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⊗[Localization.AtPrime t] Localization.AtPrime t) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) :=
    (Algebra.TensorProduct.rid (Localization.AtPrime t) (Localization.AtPrime P)
      (Localization.AtPrime P)).toLinearEquiv.length_eq
  have hquot : Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸
        extendedMaximalIdeal (Localization.AtPrime t) (Localization.AtPrime P)) =
      Module.length (Localization.AtPrime q) (Localization.AtPrime q) := by
    rw [hext, length_quotient_eq_length_self]
    exact (Module.length_self_eq_of_ringEquiv
      (quotLocalizationEquiv (Ideal.map (algebraMap C D) t) P q hq)).symm
  rw [← hquot, ← hrid]
  exact length_baseChange_eq_length_mul_length_quotient _ _ _

/-- Cancelling the base change: `(k' ⊗[k] L) ⊗[k'] K` is isomorphic to `K ⊗[k] L`. -/
private noncomputable def tensorCancelBaseChangeRingEquiv (k k' L K : Type u) [Field k]
    [Field k'] [Field L] [Field K] [Algebra k k'] [Algebra k L] [Algebra k K] [Algebra k' K]
    [IsScalarTower k k' K] :
    ((k' ⊗[k] L) ⊗[k'] K) ≃+* (K ⊗[k] L) :=
  (Algebra.TensorProduct.comm k' (k' ⊗[k] L) K).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange k k' K K L).toRingEquiv

/-- The fibre of the base change: if `φ : k' ⊗[k] L → L'` is a surjection of `k'`-algebras with
kernel `t`, then `L' ⊗[k'] K` is isomorphic to the quotient of `(k' ⊗[k] L) ⊗[k'] K` by the ideal
generated by `t`. -/
private noncomputable def quotientTensorRingEquiv (k k' L K L' : Type u) [Field k] [Field k']
    [Field L] [Field K] [Field L'] [Algebra k k'] [Algebra k L] [Algebra k' K] [Algebra k' L']
    (t : Ideal (k' ⊗[k] L)) (φ : (k' ⊗[k] L) →ₐ[k'] L') (hsurj : Function.Surjective φ)
    (hker : RingHom.ker φ = t) :
    (L' ⊗[k'] K) ≃+*
      (((k' ⊗[k] L) ⊗[k'] K) ⧸
        Ideal.map (algebraMap (k' ⊗[k] L) ((k' ⊗[k] L) ⊗[k'] K)) t) :=
  (Algebra.TensorProduct.congr
      ((Ideal.quotientEquivAlgOfEq k' hker.symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective hsurj)).symm
      (AlgEquiv.refl : K ≃ₐ[k'] K)).toRingEquiv.trans
    (Algebra.TensorProduct.quotientTensorEquiv (R := k') k' K (k' ⊗[k] L) t).toRingEquiv

/-- The numerical form of the base-change formula: if every local factor of `D` has length `b`
and the local factor of `D ⧸ tD` at `q` has length `a`, then `length(C_t) * a = b`. -/
private lemma length_atPrime_mul_toNat_eq (C D : Type u) [CommRing C] [CommRing D]
    [Algebra C D] [Module.Flat C D] (t : Ideal C) [t.IsPrime] (ht : t.IsMaximal)
    (q : Ideal (D ⧸ Ideal.map (algebraMap C D) t)) [q.IsPrime] (a b : ℕ)
    (hqa : (Module.length (Localization.AtPrime q) (Localization.AtPrime q)).toNat = a)
    (hb : ∀ (P : Ideal D) [P.IsPrime],
      (Module.length (Localization.AtPrime P) (Localization.AtPrime P)).toNat = b) :
    (Module.length (Localization.AtPrime t) (Localization.AtPrime t)).toNat * a = b := by
  have hPp : (Ideal.comap (Ideal.Quotient.mk (Ideal.map (algebraMap C D) t)) q).IsPrime :=
    Ideal.comap_isPrime _ _
  have hle : t ≤ Ideal.comap (algebraMap C D)
      (Ideal.comap (Ideal.Quotient.mk (Ideal.map (algebraMap C D) t)) q) := by
    intro x hx
    show Ideal.Quotient.mk (Ideal.map (algebraMap C D) t) (algebraMap C D x) ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)]
    exact Ideal.zero_mem _
  have hcomap : Ideal.comap (algebraMap C D)
      (Ideal.comap (Ideal.Quotient.mk (Ideal.map (algebraMap C D) t)) q) = t :=
    (ht.eq_of_le (Ideal.comap_isPrime (algebraMap C D) _).ne_top hle).symm
  have h := congrArg ENat.toNat
    (length_atPrime_mul_length_atPrime_quotient C D t _ hcomap q rfl)
  have hb' := hb (Ideal.comap (Ideal.Quotient.mk (Ideal.map (algebraMap C D) t)) q)
  rwa [ENat.toNat_mul, hqa, hb'] at h

/-- The base-change formula for the inseparable degree, with the two base changes presented
abstractly by the ring isomorphisms `eD` and `eE`. -/
private lemma length_atPrime_mul_finInsepDegree_of_ringEquivs
    (k k' L K L' : Type u) [Field k] [Field k'] [Field L] [Field K] [Field L']
    [Algebra k k'] [Algebra k L] [Algebra k K] [Algebra k' K] [Algebra k' L']
    [Module.Finite k L] [Module.Finite k' L'] [IsAlgClosed K]
    (t : Ideal (k' ⊗[k] L)) [t.IsPrime]
    (D : Type u) [CommRing D] [Algebra (k' ⊗[k] L) D] [Module.Flat (k' ⊗[k] L) D]
    (eD : D ≃+* (K ⊗[k] L))
    (eE : (L' ⊗[k'] K) ≃+* (D ⧸ Ideal.map (algebraMap (k' ⊗[k] L) D) t)) :
    (Module.length (Localization.AtPrime t) (Localization.AtPrime t)).toNat *
        Field.finInsepDegree k' L' = Field.finInsepDegree k L := by
  have : Module.Finite k' (k' ⊗[k] L) := Module.Finite.base_change k k' L
  have : IsArtinianRing (k' ⊗[k] L) := IsArtinianRing.of_finite k' _
  have htmax : t.IsMaximal := IsArtinianRing.isMaximal_of_isPrime t
  -- a prime `q'` of `L' ⊗[k'] K`, transported to a prime of `D ⧸ tD` along `eE`
  have : Module.Finite K (K ⊗[k'] L') := Module.Finite.base_change k' K L'
  have : Nontrivial (K ⊗[k'] L') :=
    Module.nontrivial_of_finrank_pos (R := K) (by
      rw [Module.finrank_baseChange]
      exact Module.finrank_pos)
  have : Nontrivial (L' ⊗[k'] K) :=
    (Algebra.TensorProduct.comm k' L' K).toRingEquiv.toRingHom.domain_nontrivial
  obtain ⟨q', hq'⟩ := Ideal.exists_maximal (L' ⊗[k'] K)
  have := hq'.isPrime
  refine length_atPrime_mul_toNat_eq (k' ⊗[k] L) D t htmax
    (Ideal.comap (eE.symm : (D ⧸ Ideal.map (algebraMap (k' ⊗[k] L) D) t) →+*
      (L' ⊗[k'] K)) q') _ _ ?_ ?_
  · rw [length_atPrime_comap_eq eE.symm q']
    exact Field.length_atPrime_tensorAlgClosed_eq_finInsepDegree k' L' K q'
  · intro P hP
    rw [← length_atPrime_comap_eq eD.symm P]
    exact Field.length_atPrime_algClosedTensor_eq_finInsepDegree k L K _

namespace Field

/-- **Stacks 0H5P, first paragraph.** Let `L/k` be a finite field extension, let `k'/k` be a field
extension and let `t` be a prime of `k' ⊗[k] L`. Present the residue field at `t` as a surjection
`φ : k' ⊗[k] L → L'` of `k'`-algebras with kernel `t`. Then the length of `(k' ⊗[k] L)_t` times
the inseparable degree of `L'/k'` is the inseparable degree of `L/k`. -/
theorem length_atPrime_mul_finInsepDegree_eq_finInsepDegree
    (k k' L : Type u) [Field k] [Field k'] [Field L] [Algebra k k'] [Algebra k L]
    [Module.Finite k L] (t : Ideal (k' ⊗[k] L)) [t.IsPrime]
    (L' : Type u) [Field L'] [Algebra k' L']
    (φ : (k' ⊗[k] L) →+* L')
    (hsurj : Function.Surjective φ) (hker : RingHom.ker φ = t)
    (hφ : ∀ a : k', φ (algebraMap k' (k' ⊗[k] L) a) = algebraMap k' L' a) :
    (Module.length (Localization.AtPrime t) (Localization.AtPrime t)).toNat *
        Field.finInsepDegree k' L' = Field.finInsepDegree k L := by
  let φ' : (k' ⊗[k] L) →ₐ[k'] L' := { φ with commutes' := hφ }
  have hsurj' : Function.Surjective φ' := hsurj
  have hker' : RingHom.ker φ' = t := by
    rw [← hker]
    ext x
    exact Iff.rfl
  have : Module.Finite k' (k' ⊗[k] L) := Module.Finite.base_change k k' L
  have : Module.Finite k' L' := Module.Finite.of_surjective φ'.toLinearMap hsurj'
  exact length_atPrime_mul_finInsepDegree_of_ringEquivs k k' L (AlgebraicClosure k') L' t
    ((k' ⊗[k] L) ⊗[k'] AlgebraicClosure k')
    (tensorCancelBaseChangeRingEquiv k k' L (AlgebraicClosure k'))
    (quotientTensorRingEquiv k k' L (AlgebraicClosure k') L' t φ' hsurj' hker')

end Field

end
