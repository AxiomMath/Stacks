module

import Mathlib.RingTheory.ZariskisMainTheorem

public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.RingTheory.Artinian.FiniteType

@[expose] public section

/-!
# Quasi-finiteness of a base change

Let `R → S` be a ring map of finite type, let `R → R'` be any ring map and set
`S' = R' ⊗[R] S`. For a prime `𝔮'` of `S'` with image `𝔮` in `Spec S`, the map `R' → S'` is
quasi-finite at `𝔮'` if and only if `R → S` is quasi-finite at `𝔮`. Equivalently, the locus where
`R' → S'` is quasi-finite is the inverse image of the locus where `R → S` is quasi-finite under the
canonical map `Spec(S') → Spec(S)`.

If moreover `Spec(R') → Spec(R)` is surjective, then `R → S` is quasi-finite if and only if
`R' → S'` is: one direction is `Algebra.QuasiFinite.baseChange`, and the other follows from the
equivalence above by choosing, for each prime `𝔭` of `R`, a prime of `R'` over it.

## Main results

* `Algebra.quasiFiniteAt_baseChange_iff`: `R' → S'` is quasi-finite at `𝔮'` if and only if
  `R → S` is quasi-finite at the image `𝔮` of `𝔮'` in `Spec S`.

## References

* [StacksProject 00PP](https://stacks.math.columbia.edu/tag/00PP)
* [StacksProject 00PJ](https://stacks.math.columbia.edu/tag/00PJ)
* [StacksProject 00P4](https://stacks.math.columbia.edu/tag/00P4)
* [StacksProject 00PL](https://stacks.math.columbia.edu/tag/00PL)

## Tags

quasi-finite ring map, base change, tensor product, fibre, finite type algebra
-/

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Stacks.QuasiFinite.BaseChangeInvariance

/-- Let `k` be an artinian ring and `S` a `k`-algebra of finite type. Then `S` is `k`-quasi-finite
at a prime `𝔮` if and only if `Spec S` has dimension `0` at `𝔮`. -/
private lemma quasiFiniteAt_iff_localKrullDim_eq_zero (k S : Type*) [CommRing k]
    [IsArtinianRing k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (𝔮 : Ideal S)
    [𝔮.IsPrime] :
    Algebra.QuasiFiniteAt k 𝔮 ↔
      TopologicalSpace.localKrullDim (PrimeSpectrum S) ⟨𝔮, ‹_›⟩ = 0 := by
  have h : IsOpen {(⟨𝔮, ‹_›⟩ : PrimeSpectrum S)} ↔
      topologicalKrullDimAt (PrimeSpectrum S) ⟨𝔮, ‹_›⟩ = 0 :=
    (PrimeSpectrum.isOpen_singleton_tfae_and_exists_algEquiv_prod_of_finiteType
      k 𝔮 (Localization.AtPrime 𝔮)).1.out 1 4
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, ← h]
  exact ⟨fun _ ↦ (Algebra.QuasiFiniteAt.isClopen_singleton (R := k) ⟨𝔮, ‹_›⟩).isOpen,
    fun h ↦ Algebra.QuasiFiniteAt.of_isOpen_singleton ⟨𝔮, ‹_›⟩ h⟩

/-- Let `k → K` be a field extension, let `F` be a `k`-algebra of finite type and let `T` be the
base change of `F` to `K`, presented as a pushout square. Then `T` is `K`-quasi-finite at a prime
`Q` if and only if `F` is `k`-quasi-finite at the prime `Q ∩ F` below it. -/
private lemma quasiFiniteAt_iff_comap_of_isPushout (k K F T : Type*) [Field k] [Field K]
    [CommRing F] [CommRing T] [Algebra k K] [Algebra k F] [Algebra k T] [Algebra K T]
    [Algebra F T] [IsScalarTower k K T] [IsScalarTower k F T] [Algebra.IsPushout k K F T]
    [Algebra.FiniteType k F] (Q : Ideal T) [Q.IsPrime] :
    Algebra.QuasiFiniteAt K Q ↔ Algebra.QuasiFiniteAt k (Q.comap (algebraMap F T)) := by
  have : Algebra.FiniteType K T :=
    .of_surjective (Algebra.IsPushout.equiv k K F T).toAlgHom
      (Algebra.IsPushout.equiv k K F T).surjective
  rw [quasiFiniteAt_iff_localKrullDim_eq_zero K T Q,
    quasiFiniteAt_iff_localKrullDim_eq_zero k F (Q.comap (algebraMap F T)),
    ← Algebra.IsPushout.localKrullDim_comap_eq k K F T ⟨Q, ‹_›⟩]
  rfl

/-- Quasi-finiteness at a prime is transported by an isomorphism of algebras. -/
private lemma quasiFiniteAt_comap_algEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (p : Ideal A) [p.IsPrime] [Algebra.QuasiFiniteAt R p]
    (e : B ≃ₐ[R] A) : Algebra.QuasiFiniteAt R (p.comap e.toAlgHom.toRingHom) :=
  Algebra.QuasiFiniteAt.of_surjectiveOnStalks p e.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective e.symm.surjective) _ (by ext; simp)

/-- Let `R → S` be of finite type and `R → R'` any ring map. Then `R' → R' ⊗[R] S` is
quasi-finite at a prime `𝔮'` if and only if `R → S` is quasi-finite at the image `𝔮` of `𝔮'` in
`Spec S`. -/
public theorem solution {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (R' : Type*) [CommRing R'] [Algebra R R']
    (𝔮 : Ideal S) [𝔮.IsPrime] (𝔮' : Ideal (R' ⊗[R] S)) [𝔮'.IsPrime]
    (h : 𝔮 = 𝔮'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    Algebra.QuasiFiniteAt R' 𝔮' ↔ Algebra.QuasiFiniteAt R 𝔮 := by
  refine ⟨fun hqf ↦ ?_, fun hqf ↦ Algebra.QuasiFiniteAt.baseChange 𝔮 𝔮' h⟩
  let 𝔭' : Ideal R' := 𝔮'.under R'
  have : 𝔮'.LiesOver 𝔭' := ⟨rfl⟩
  let 𝔭 : Ideal R := 𝔭'.under R
  have : 𝔭'.LiesOver 𝔭 := ⟨rfl⟩
  have : 𝔮.LiesOver 𝔭 := ⟨by
    rw [h]
    change 𝔭 = Ideal.under R (Ideal.under S 𝔮')
    rw [Ideal.under_under, show 𝔭 = Ideal.under R (Ideal.under R' 𝔮') from rfl,
      Ideal.under_under]⟩
  let := Localization.AtPrime.algebraOfLiesOver 𝔭 𝔭'
  let e : 𝔭'.Fiber (R' ⊗[R] S) ≃ₐ[𝔭'.ResidueField]
      𝔭'.ResidueField ⊗[𝔭.ResidueField] (𝔭.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  let iso := PrimeSpectrum.primesOverOrderIsoFiber R' (R' ⊗[R] S) 𝔭'
  let Q' : Ideal (𝔭'.Fiber (R' ⊗[R] S)) := (iso ⟨𝔮', ‹_›, ‹_›⟩).asIdeal
  have hQ' : 𝔮' = Q'.comap Algebra.TensorProduct.includeRight.toRingHom :=
    congr($(iso.symm_apply_apply ⟨𝔮', ‹_›, ‹_›⟩).1).symm
  have : Algebra.QuasiFiniteAt 𝔭'.ResidueField Q' := .baseChange 𝔮' Q' hQ'
  have hQ := (quasiFiniteAt_iff_comap_of_isPushout 𝔭.ResidueField 𝔭'.ResidueField (𝔭.Fiber S)
    (𝔭'.ResidueField ⊗[𝔭.ResidueField] (𝔭.Fiber S)) _).mp
      (quasiFiniteAt_comap_algEquiv (R := 𝔭'.ResidueField) (A := 𝔭'.Fiber (R' ⊗[R] S))
        (B := 𝔭'.ResidueField ⊗[𝔭.ResidueField] (𝔭.Fiber S)) Q' e.symm)
  obtain ⟨Q, _, hQqf, hQc⟩ : ∃ (Q : Ideal (𝔭.Fiber S)) (_ : Q.IsPrime),
      Algebra.QuasiFiniteAt 𝔭.ResidueField Q ∧
        Q.comap Algebra.TensorProduct.includeRight.toRingHom = 𝔮 := by
    refine ⟨_, inferInstance, hQ, ?_⟩
    conv_rhs => rw [h, hQ']
    simp only [Ideal.comap_comap]
    congr 1
    ext s
    simp [e, Algebra.TensorProduct.right_algebraMap_apply]
  exact Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField 𝔭 𝔮 Q hQc

end Stacks.QuasiFinite.BaseChangeInvariance

open TensorProduct

@[expose] public section

/-- Let `R → S` be a ring map of finite type, let `R → R'` be any ring map and set
`S' = R' ⊗[R] S`. Let `𝔮'` be a prime of `S'` and let `𝔮` be its image under the canonical map
`Spec(S') → Spec(S)`. Then `R' → S'` is quasi-finite at `𝔮'` if and only if `R → S` is
quasi-finite at `𝔮`; equivalently, the quasi-finite locus of `Spec(S')` is the inverse image of the
quasi-finite locus of `Spec(S)`. -/
@[stacks 00PP "(1). The canonical map `Spec(S') → Spec(S)` is
`PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom`, so the source's equality of
subsets of `Spec(S')` is this equivalence quantified over `𝔮'`. Quasi-finiteness at a prime
(Definition 00PL) is `Algebra.QuasiFiniteAt`, the source's notion under the finite type
hypothesis. The `←` direction is `Algebra.QuasiFiniteAt.baseChange`; `→` is the new content.
Part (3) is `Algebra.QuasiFinite.baseChange`, tagged 00PP upstream; see the module docstring for
part (2)."]
public theorem Algebra.quasiFiniteAt_baseChange_iff {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (R' : Type*) [CommRing R'] [Algebra R R']
    (𝔮 : Ideal S) [𝔮.IsPrime] (𝔮' : Ideal (R' ⊗[R] S)) [𝔮'.IsPrime]
    (h : 𝔮 = 𝔮'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    Algebra.QuasiFiniteAt R' 𝔮' ↔ Algebra.QuasiFiniteAt R 𝔮 :=
  Stacks.QuasiFinite.BaseChangeInvariance.solution (S := S) R' 𝔮 𝔮' h

end
