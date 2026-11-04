module

public import StacksFrontier.RingTheory.Rig.RigEtaleLocus

/-!
# Étaleness off `V(I)` is invariant under isomorphism

Let `A → B` and `A₁ → B₁` be ring maps and let `α : A ≃ A₁`, `β : B ≃ B₁` be ring isomorphisms
compatible with them. If `Spec B₁ → Spec A₁` is étale over the complement of `V(α(I))`, then
`Spec B → Spec A` is étale over the complement of `V(I)`.

This moves the hypothesis of part (1) of Stacks 0ALQ between two presentations of the same
morphism of affine schemes, for instance between a ring map `φ : A → A'` and the map
`Γ(Spec A, 𝒪) → Γ(Spec A', 𝒪)` it induces on global sections.

## Main results

* `Rig.IsEtaleOutside.of_ringEquiv`: the transport.

## References

* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
-/

@[expose] public section

universe u u₁ v v₁

namespace Rig

/-- **Étaleness off `V(I)` transports along an isomorphism of ring maps.** -/
theorem IsEtaleOutside.of_ringEquiv {A : Type u} {A₁ : Type u₁} {B : Type v} {B₁ : Type v₁}
    [CommRing A] [CommRing A₁] [CommRing B] [CommRing B₁] [Algebra A B] [Algebra A₁ B₁]
    (α : A ≃+* A₁) (β : B ≃+* B₁)
    (hcomm : ∀ a : A, β (algebraMap A B a) = algebraMap A₁ B₁ (α a)) {I : Ideal A}
    (h : IsEtaleOutside (I.map (α : A →+* A₁)) B₁) : IsEtaleOutside I B := by
  rw [isEtaleOutside_iff] at h ⊢
  intro q hq hqI
  set q₁ : Ideal B₁ := q.map (β : B →+* B₁) with hq₁def
  have hq₁ : q₁.IsPrime := Ideal.map_isPrime_of_equiv β
  have hmem : ∀ b : B, β b ∈ q₁ ↔ b ∈ q := fun b ↦ by
    rw [hq₁def, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]
  have hnot : ¬ I.map (α : A →+* A₁) ≤ q₁.comap (algebraMap A₁ B₁) := fun hle ↦ hqI fun a ha ↦ by
    rw [Ideal.mem_comap, ← hmem, hcomm]
    exact hle (Ideal.mem_map_of_mem _ ha)
  let : Algebra A A₁ := (α : A →+* A₁).toAlgebra
  let : Algebra A B₁ := ((algebraMap A₁ B₁).comp (α : A →+* A₁)).toAlgebra
  have : IsScalarTower A A₁ B₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FormallyEtale A A₁ :=
    Algebra.FormallyEtale.of_equiv ({ α with commutes' := fun _ ↦ rfl } : A ≃ₐ[A] A₁)
  have : IsScalarTower A A₁ (Localization.AtPrime q₁) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      rw [IsScalarTower.algebraMap_apply A B₁ (Localization.AtPrime q₁),
        IsScalarTower.algebraMap_apply A₁ B₁ (Localization.AtPrime q₁)]
      rfl
  have : Algebra.FormallyEtale A₁ (Localization.AtPrime q₁) := h q₁ hq₁ hnot
  have : Algebra.FormallyEtale A (Localization.AtPrime q₁) :=
    Algebra.FormallyEtale.comp A A₁ (Localization.AtPrime q₁)
  let βA : B ≃ₐ[A] B₁ := { β with commutes' := hcomm }
  have H : Submonoid.map βA q.primeCompl = q₁.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact fun hx ↦ hy ((hmem y).mp hx)
    · exact fun hx ↦ ⟨β.symm x, fun hy ↦ hx (by simpa using (hmem _).mpr hy),
        β.apply_symm_apply x⟩
  exact Algebra.FormallyEtale.of_equiv
    (IsLocalization.algEquivOfAlgEquiv (Localization.AtPrime q) (Localization.AtPrime q₁)
      βA H).symm

end Rig

end
