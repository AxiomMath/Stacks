module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.FiniteFieldCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.KummerProcyclicAbsoluteGalois

/-!
# Fields with Kummer data have cohomological dimension at most one

Let `ℓ` be a prime and `K` a field with primitive `ℓ ^ e`-th roots of unity for every `e`, an
element `π` which is not an `ℓ`-th power and such that every nonzero element of `K` is
`π ^ i * b ^ ℓ`, and all of whose finite separable extensions have `ℓ`-power degree. Then the
absolute Galois group of `K` is `ℤ_ℓ`
(`Stacks.GaloisCohomology.hasPrimeBase_gal_of_kummer`), so `H^q_ét(Spec K, 𝓕) = 0` for every
torsion abelian sheaf `𝓕` and every `q ≥ 2` (Stacks 03R8 part (2) read through Stacks 03QU).

The hypotheses are intrinsic to `K`; they are transported to the residue field of `Spec K` at
the geometric point used by the comparison of étale and Galois cohomology.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_spec_of_kummer`: the vanishing.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Module

universe u

namespace AlgebraicGeometry

open Stacks.Torsion

attribute [local instance] GeometricPoint.residueFieldAlgebra

/-- **Kummer data give cohomological dimension at most one.** Let `ℓ` be a prime and `K` a field
containing primitive `ℓ ^ e`-th roots of unity for all `e`, with an element `π` which is not an
`ℓ`-th power, such that every nonzero element of `K` is `π ^ i * b ^ ℓ`, and such that every
finite separable extension of `K` has `ℓ`-power degree. Then `H^q_ét(Spec K, 𝓕) = 0` for every
torsion abelian sheaf `𝓕` on the small étale site of `Spec K` and every `q ≥ 2`. -/
theorem subsingleton_sheafH_spec_of_kummer (K : Type u) [Field K] {ℓ : ℕ} (hℓ : ℓ.Prime) {π : K}
    (hζ : ∀ e : ℕ, ∃ ζ : K, IsPrimitiveRoot ζ (ℓ ^ e)) (hπ : ∀ y : K, y ^ ℓ ≠ π)
    (hgen : ∀ a : K, a ≠ 0 → ∃ (i : ℕ) (b : K), a = π ^ i * b ^ ℓ)
    (hdeg : ∀ (M : Type u) [Field M] [Algebra K M] [FiniteDimensional K M]
      [Algebra.IsSeparable K M], ∃ k, finrank K M = ℓ ^ k)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : torsionSheafProperty (Spec (.of K)).smallEtaleTopology F) (q : ℕ) (hq : 2 ≤ q) :
    letI := hasExt_smallEtaleSheaf_objectUniverse (Spec (.of K))
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) := by
  let := hasExt_smallEtaleSheaf_objectUniverse (Spec (.of K))
  let B := BigEtaleSite.containing (Spec (.of K))
  have hK : B.Contains (Spec (.of K)) := BigEtaleSite.contains_containing _
  let sbar := GeometricPoint.ofAlgebraicClosure K
  refine (subsingleton_smallEtaleSheafH_iff_isZero_continuousGroupCohomology B K hK sbar F q).2 ?_
  set κ := (Spec (CommRingCat.of K)).residueField (sbar.hom default)
  let e : K ≃+* κ := residueFieldSpecRingEquiv K (sbar.hom default)
  let : Algebra K κ := e.toRingHom.toAlgebra
  let eA : K ≃ₐ[K] κ := AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)
  have : Module.Finite K κ := Module.Finite.equiv eA.toLinearEquiv
  have hfinκ : finrank K κ = 1 := by rw [← eA.toLinearEquiv.finrank_eq, finrank_self]
  have : Algebra.IsSeparable K κ := Algebra.IsSeparable.of_algHom K K eA.symm.toAlgHom
  have hbase : Stacks.GroupCohomology.HasPrimeBase (GeometricPoint.absoluteGaloisGroup sbar) := by
    refine Stacks.GaloisCohomology.hasPrimeBase_gal_of_kummer (F := κ) hℓ (π := e π)
      (fun n => ?_) (fun y hy => ?_) (fun a ha => ?_) (fun M hM => ?_)
    · obtain ⟨ζ, hζn⟩ := hζ n
      exact ⟨e ζ, hζn.map_of_injective e.injective⟩
    · apply hπ (e.symm y)
      rw [← map_pow, hy, RingEquiv.symm_apply_apply]
    · obtain ⟨i, b, hab⟩ := hgen (e.symm a) (by simpa using ha)
      refine ⟨i, e b, ?_⟩
      rw [← map_pow, ← map_pow, ← map_mul, ← hab, RingEquiv.apply_symm_apply]
    · let : Algebra K M := ((algebraMap κ M).comp e.toRingHom).toAlgebra
      have : IsScalarTower K κ M := .of_algebraMap_eq' rfl
      have : Module.Finite K M := Module.Finite.trans κ M
      have : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K κ M
      obtain ⟨k, hk⟩ := hdeg M
      exact ⟨k, by rw [← hk, ← Module.finrank_mul_finrank K κ M, hfinκ, one_mul]⟩
  refine Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_torsion hbase q hq _ ?_
  exact fun m => isOfFinAddOrder_iff_nsmul_eq_zero.1
    (isAddTorsion_etaleContinuousGModuleEquivalence_functor_obj B K hK sbar _
      ((SmallEtale.torsionSheafProperty_toEtaleSite_iff B (Spec (.of K)) hK F).2 hF) m)

end AlgebraicGeometry

end
