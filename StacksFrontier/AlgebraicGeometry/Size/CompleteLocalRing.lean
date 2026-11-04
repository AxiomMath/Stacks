module

public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison
public import StacksFrontier.RingTheory.CohenRing

/-!
# Complete Noetherian local rings and the big fppf site

Let `Λ` be a Noetherian local ring, Hausdorff for its maximal-ideal-adic topology (for instance
complete, such as a Cohen ring), with a surjection `Λ → k` onto a field. Then
`#Λ ≤ (max ℵ₀ #k) ^ ℵ₀`: `Λ` embeds into the product of the quotients `Λ/𝔪ⁿ`, each of finite
length and so of cardinality at most `max ℵ₀ #k`. The cutoff of a big fppf site is a strong limit
cardinal, so `Spec Λ` lies in every big fppf site containing `Spec k`.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_spec_of_isHausdorff`: `Spec Λ` lies in every big fppf
  site containing `Spec k`.
* `AlgebraicGeometry.module_finite_of_surjective_algebraMap`: `k` is a finite `Λ`-module.
* `AlgebraicGeometry.flat_of_charZero` and `AlgebraicGeometry.flat_of_isCohenRing`: every
  morphism from the spectrum of a domain of characteristic zero, for instance a Cohen ring, to the
  spectrum of the integers is flat.
* `AlgebraicGeometry.locallyOfFiniteType_and_quasiCompact_spec_map_of_surjective`:
  `Spec k ⟶ Spec Λ` is locally of finite type and quasi-compact.
-/

@[expose] public section

open CategoryTheory IsLocalRing Cardinal

universe u

namespace AlgebraicGeometry

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The quotient of a Noetherian local ring by a power of its maximal ideal has finite length. -/
theorem isFiniteLength_quotient_maximalIdeal_pow [IsLocalRing Λ] [IsNoetherianRing Λ] (n : ℕ) :
    IsFiniteLength Λ (Λ ⧸ maximalIdeal Λ ^ n) := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  suffices IsArtinianRing (Λ ⧸ maximalIdeal Λ ^ n) from
    ⟨isNoetherian_quotient _,
      isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := maximalIdeal Λ ^ n))⟩
  have : Ring.KrullDimLE 0 (Λ ⧸ maximalIdeal Λ ^ n) := Ring.KrullDimLE.mk₀ fun P hP => by
    set f := Ideal.Quotient.mk (maximalIdeal Λ ^ n)
    have hle : maximalIdeal Λ ^ n ≤ P.comap f := fun x hx => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact P.zero_mem
    have hm : maximalIdeal Λ ≤ P.comap f := (Ideal.IsPrime.comap f).le_of_pow_le hle
    have hmax : (P.comap f).IsMaximal := by
      rw [le_antisymm (le_maximalIdeal (Ideal.IsPrime.comap f).ne_top) hm]
      exact maximalIdeal.isMaximal Λ
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective f Ideal.Quotient.mk_surjective hmax with
      h | h <;> rw [Ideal.map_comap_of_surjective f Ideal.Quotient.mk_surjective] at h
    · exact absurd h hP.ne_top
    · exact h
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- **A Noetherian local ring, Hausdorff for the maximal-ideal-adic topology, with residue field
`k` has at most `(max ℵ₀ #k) ^ ℵ₀` elements.** It embeds into the product of its quotients by the
powers of its maximal ideal, each of finite length. -/
theorem mk_le_max_aleph0_pow_aleph0 [IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsHausdorff (maximalIdeal Λ) Λ] (hsurj : Function.Surjective (algebraMap Λ k)) :
    #Λ ≤ (max ℵ₀ #k) ^ ℵ₀ := by
  have hres : #(ResidueField Λ) = #k :=
    Cardinal.mk_congr ((Ideal.quotEquivOfEq (IsLocalRing.ker_eq_maximalIdeal _ hsurj).symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)).toEquiv
  have hi : Function.Injective
      (fun x : Λ => fun n : ℕ => Ideal.Quotient.mk (maximalIdeal Λ ^ n) x) := by
    intro x y h
    refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal Λ) (x - y) fun n => ?_)
    simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using Ideal.Quotient.eq.mp (congrFun h n)
  calc #Λ ≤ #(∀ n : ℕ, Λ ⧸ maximalIdeal Λ ^ n) := mk_le_of_injective hi
    _ = Cardinal.prod (fun n : ℕ => #(Λ ⧸ maximalIdeal Λ ^ n)) := mk_pi _
    _ ≤ Cardinal.prod (fun _ : ℕ => max ℵ₀ #k) := prod_le_prod _ _ fun n =>
      hres ▸ Cardinal.mk_le_max_residueField_of_isFiniteLength
        (isFiniteLength_quotient_maximalIdeal_pow n)
    _ = (max ℵ₀ #k) ^ ℵ₀ := by simp

/-- **The spectrum of a complete Noetherian local ring with residue field `k` lies in every big
fppf site containing `Spec k`.** Its cardinality is at most `(max ℵ₀ #k) ^ ℵ₀`, which is below the
cutoff since the cutoff is a strong limit cardinal above `ℵ₀` and `#k`. -/
theorem BigFppfSite.contains_spec_of_isHausdorff (B : BigFppfSite.{u}) [IsLocalRing Λ]
    [IsNoetherianRing Λ] [IsHausdorff (maximalIdeal Λ) Λ]
    (hsurj : Function.Surjective (algebraMap Λ k)) (hk : B.Contains (Spec (.of k))) :
    B.Contains (Spec (.of Λ)) := by
  refine BigFppfSite.contains_spec_of_mk_lt_cutoff B
    ((mk_le_max_aleph0_pow_aleph0 hsurj).trans_lt ?_)
  calc (max ℵ₀ #k) ^ ℵ₀ ≤ (2 ^ max ℵ₀ #k) ^ ℵ₀ :=
        Cardinal.power_le_power_right (Cardinal.cantor _).le
    _ = 2 ^ max ℵ₀ #k := by
      rw [← Cardinal.power_mul,
        Cardinal.mul_eq_left (le_max_left _ _) (le_max_left _ _) aleph0_ne_zero]
    _ < B.cutoff := B.cutoff_isStrongPrelimit
      (max_lt B.aleph0_lt_cutoff (BigFppfSite.mk_lt_cutoff_of_contains_spec B hk))

/-- A field which is a quotient of `Λ` is a finite `Λ`-module. -/
theorem module_finite_of_surjective_algebraMap (hsurj : Function.Surjective (algebraMap Λ k)) :
    Module.Finite Λ k :=
  Module.Finite.of_surjective (Algebra.linearMap Λ k) hsurj

/-- **The closed point of the spectrum of a local ring with residue field `k`**: the morphism
`Spec k ⟶ Spec Λ` of a surjection `Λ → k` is locally of finite type and quasi-compact, being a
closed immersion. -/
theorem locallyOfFiniteType_and_quasiCompact_spec_map_of_surjective
    (hsurj : Function.Surjective (algebraMap Λ k)) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ 𝟙 (Spec (.of Λ))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ 𝟙 (Spec (.of Λ))) := by
  rw [Category.comp_id]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap Λ k))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  exact ⟨inferInstance, inferInstance⟩

/-- A Cohen ring has characteristic zero: its uniformizer is a prime number `p`, which is neither
zero nor a unit. -/
theorem charZero_of_isCohenRing [IsDomain Λ] [hΛ : IsCohenRing Λ] : CharZero Λ := by
  obtain ⟨p, hp, hm⟩ := hΛ.exists_prime_maximalIdeal_eq_span
  have hpm : (p : Λ) ∈ maximalIdeal Λ := hm ▸ Ideal.subset_span rfl
  have hp0 : (p : Λ) ≠ 0 := by
    intro h0
    have : maximalIdeal Λ = ⊥ := by rw [hm, h0, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_a_field Λ this
  rcases CharP.char_is_prime_or_zero Λ (ringChar Λ) with hq | hq
  · exfalso
    have : Fact (ringChar Λ).Prime := ⟨hq⟩
    by_cases hpq : ringChar Λ = p
    · subst hpq
      exact hp0 (CharP.cast_eq_zero Λ _)
    · have hne : (p : ZMod (ringChar Λ)) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 h)
      have hunit : IsUnit (p : Λ) := by
        simpa using (Ne.isUnit hne).map (ZMod.castHom (dvd_refl (ringChar Λ)) Λ)
      exact (mem_maximalIdeal _).1 hpm hunit
  · have : CharP Λ 0 := hq ▸ ringChar.charP Λ
    exact CharP.charP_to_charZero Λ

/-- **The spectrum of a domain of characteristic zero is flat over the integers**: such a ring is
torsion-free over `ℤ`, hence flat. -/
theorem flat_of_charZero [IsDomain Λ] [CharZero Λ]
    (f : Spec (.of Λ) ⟶ Spec (.of (ULift.{u} ℤ))) : Flat f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [Flat.SpecMap_iff]
  have hφ : φ.hom = (Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom := by
    ext x
    exact RingHom.congr_fun (Subsingleton.elim
      (φ.hom.comp ULift.ringEquiv.symm.toRingHom) (Int.castRingHom Λ)) x.down
  rw [hφ]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective ULift.ringEquiv.bijective)
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ Λ))

/-- **The spectrum of a Cohen ring is flat over the integers**: a Cohen ring is a domain of
characteristic zero, hence torsion-free over `ℤ`, hence flat. -/
theorem flat_of_isCohenRing [IsDomain Λ] [IsCohenRing Λ]
    (f : Spec (.of Λ) ⟶ Spec (.of (ULift.{u} ℤ))) : Flat f :=
  have := charZero_of_isCohenRing (Λ := Λ)
  flat_of_charZero f

end AlgebraicGeometry

end
