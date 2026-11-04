module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.Etale.ResidueFieldColimit
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite

/-!
# A discrete valuation ring with separably closed residue field, as a union of finite étale ones

Let `A` be a discrete valuation ring. Applying Stacks 09E0 to a separable closure of the residue
field of `A` gives a local ring `A'` which is a directed union of finite étale local
`A`-subalgebras and whose residue field is a separable closure of that of `A`. This file shows
that `A'` is a discrete valuation ring, that `A → A'` is injective, and that a uniformizer of `A`
stays a uniformizer of `A'`. This is the first step of the proof of Stacks 09ET.

## Main results

* `IsDiscreteValuationRing.exists_finiteEtale_directed_isSepClosure`: the statement above.
-/

@[expose] public section

open IsLocalRing

universe u

namespace IsDiscreteValuationRing

/-- A discrete valuation ring `A` has an extension `A → A'` of discrete valuation rings which is a
directed union of finite étale local `A`-subalgebras, in which a uniformizer of `A` stays a
uniformizer, and whose residue field is a separable closure of the residue field of `A`. -/
theorem exists_finiteEtale_directed_isSepClosure (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra A A') (_ : IsLocalHom (algebraMap A A')) (𝒮 : Set (Subalgebra A A')),
      DirectedOn (· ≤ ·) 𝒮 ∧
      (∀ x : A', ∃ S ∈ 𝒮, x ∈ S) ∧
      (∀ S ∈ 𝒮, Module.Finite A S ∧ Algebra.Etale A S ∧ IsLocalRing S) ∧
      Function.Injective (algebraMap A A') ∧
      (∀ ϖ : A, Irreducible ϖ → Irreducible (algebraMap A A' ϖ)) ∧
      IsSepClosure (ResidueField A) (ResidueField A') := by
  obtain ⟨A', _, _, _, _, 𝒮, hdir, hcov, h𝒮, ⟨e⟩⟩ :=
    IsLocalRing.exists_finiteEtale_directed_residueField_algEquiv A
      (SeparableClosure (ResidueField A))
  have hsub : ∀ S ∈ 𝒮, ∃ _ : IsLocalRing S, IsLocalHom (algebraMap A S) ∧
      Algebra.EssFiniteType A S ∧ Algebra.FormallyUnramified A S ∧ Module.Flat A S := by
    intro S hS
    obtain ⟨_, _, _⟩ := h𝒮 S hS
    exact ⟨inferInstance, ⟨fun a ha => isUnit_of_map_unit (algebraMap A A') a (ha.map S.val)⟩,
      inferInstance, inferInstance, inferInstance⟩
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨hdom, hdvr, hirr⟩ := of_forall_mem_subalgebra 𝒮 hcov hsub hϖ
  refine ⟨A', inferInstance, hdom, hdvr, inferInstance, inferInstance, 𝒮, hdir, hcov, h𝒮,
    fun a b hab => ?_,
    fun _ h => (of_forall_mem_subalgebra 𝒮 hcov hsub h).2.2, ?_⟩
  · rw [← sub_eq_zero, ← map_sub] at hab
    by_contra hne
    obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible (sub_ne_zero.mpr hne) hϖ
    rw [hu, map_mul, map_pow] at hab
    exact pow_ne_zero n hirr.ne_zero
      (((u.isUnit.map (algebraMap A A')).mul_right_eq_zero).mp hab)
  · exact ⟨IsSepClosed.of_ringEquiv e.toRingEquiv, AlgEquiv.Algebra.isSeparable e.symm⟩

end IsDiscreteValuationRing
