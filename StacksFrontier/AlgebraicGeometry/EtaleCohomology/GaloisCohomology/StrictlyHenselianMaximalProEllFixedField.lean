module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.KummerProcyclicAbsoluteGalois
public import StacksFrontier.RingTheory.DiscreteValuationRing.StrictlyHenselianKummerUnits
public import StacksFrontier.FieldTheory.Galois.SeparableClosureGaloisGroup

/-!
# The fixed field of a maximal pro-`ℓ` subgroup over a strictly henselian discrete valuation ring

Let `B` be a strictly henselian discrete valuation ring with uniformizer `ϖ` and fraction field
`K`, let `ℓ` be a prime invertible in `B`, let `Kˢᵉᵖ` be a separable closure of `K` and `H` a
maximal pro-`ℓ` subgroup of `Gal(Kˢᵉᵖ/K)` with fixed field `L`. Then `L` carries the Kummer data
of `Stacks.GaloisCohomology.hasPrimeBase_gal_of_kummer` with `π = ϖ`:

* `L` contains a primitive `ℓ ^ e`-th root of unity for every `e` (Hensel's lemma in `B`);
* `ϖ` is not an `ℓ`-th power in `L`: a root would lie in a finite subextension `K'` of `L / K`,
  whose degree is prime to `ℓ` (`IsMaximalProPSubgroup.not_dvd_index`), and taking norms to `K`
  is impossible;
* every nonzero element of `L` is `ϖ ^ i * b ^ ℓ`: it lies in such a `K'`, whose integral
  closure is a strictly henselian discrete valuation ring with units `ℓ`-divisible;
* every finite separable extension of `L` has `ℓ`-power degree, `Gal(Kˢᵉᵖ/L) ≅ H` being pro-`ℓ`.

## Main results

* `AlgebraicGeometry.StrictlyHenselianKummer.not_dvd_finrank_of_le_fixedField`: finite
  subextensions of `L / K` have degree prime to `ℓ`.
* `AlgebraicGeometry.StrictlyHenselianKummer.fixedField_kummerData`: the four properties.

## References

* J.-P. Serre, *Cohomologie galoisienne*, II §3.3.
-/

@[expose] public section

open IntermediateField Module

universe u

namespace AlgebraicGeometry.StrictlyHenselianKummer

/-- **An open subgroup of a pro-`ℓ` profinite group has `ℓ`-power index.** -/
theorem exists_index_eq_pow_of_isProPGroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : IsProPGroup ℓ G) (U : OpenSubgroup G) : ∃ k, (U : Subgroup G).index = ℓ ^ k := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨N, hNU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one U.isOpen' U.one_mem
  have : Finite (G ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (hG N)
  have hdvd : (U : Subgroup G).index ∣ ℓ ^ m := by
    rw [← hm]
    exact Subgroup.index_dvd_of_le (fun x hx => hNU hx)
  exact ((Nat.dvd_prime_pow hℓ).1 hdvd).imp fun _ h => h.2

/-- **Being pro-`ℓ` is invariant under continuous isomorphisms.** -/
theorem isProPGroup_of_continuousMulEquiv {G G' : Type*} [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] {ℓ : ℕ} (φ : G ≃ₜ* G') (hG' : IsProPGroup ℓ G') :
    IsProPGroup ℓ G := by
  intro N
  let N' : OpenNormalSubgroup G' :=
    { toSubgroup := N.toSubgroup.comap φ.symm.toMulEquiv.toMonoidHom
      isOpen' := N.isOpen'.preimage φ.symm.continuous
      isNormal' := inferInstance }
  intro g
  induction g using QuotientGroup.induction_on with
  | H x =>
  obtain ⟨k, hk⟩ := hG' N' (φ x : G' ⧸ N'.toSubgroup)
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk ⊢
  have : φ.symm (φ x ^ ℓ ^ k) ∈ N.toSubgroup := hk
  rwa [map_pow, ContinuousMulEquiv.symm_apply_apply] at this

variable {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [StrictlyHenselianLocalRing B]
  (K Ksep : Type u) [Field K] [Algebra B K] [IsFractionRing B K] [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep] {ℓ : ℕ} {H : Subgroup Gal(Ksep/K)}

/-- **Finite subextensions of the fixed field of a maximal pro-`ℓ` subgroup have degree prime to
`ℓ`.** -/
theorem not_dvd_finrank_of_le_fixedField (hℓ : ℓ.Prime) (hH : IsMaximalProPSubgroup ℓ H)
    (K' : IntermediateField K Ksep) [FiniteDimensional K K'] (hK' : K' ≤ fixedField H) :
    ¬ ℓ ∣ finrank K K' := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  exact hH.not_dvd_index ((InfiniteGalois.isOpen_iff_finite K').2 inferInstance)
    ((IntermediateField.le_iff_le H K').1 hK')

omit [StrictlyHenselianLocalRing B] in
/-- **The uniformizer is not an `ℓ`-th power in a finite subextension of the fixed field.** -/
theorem not_exists_pow_eq_of_le_fixedField (hℓ : ℓ.Prime) (hH : IsMaximalProPSubgroup ℓ H)
    {ϖ : B} (hϖ : Irreducible ϖ) (K' : IntermediateField K Ksep) [FiniteDimensional K K']
    (hK' : K' ≤ fixedField H) :
    ¬ ∃ y : K', y ^ ℓ = algebraMap K K' (algebraMap B K ϖ) :=
  Stacks.StrictlyHenselianKummer.not_exists_pow_eq_of_not_dvd_finrank hϖ hℓ.ne_zero K'
    (not_dvd_finrank_of_le_fixedField K Ksep hℓ hH K' hK')

/-- **The absolute Galois group of the fixed field of a maximal pro-`ℓ` subgroup is pro-`ℓ`.** -/
theorem isProPGroup_gal_fixedField (hH : IsMaximalProPSubgroup ℓ H) :
    IsProPGroup ℓ Gal(Ksep/fixedField H) :=
  isProPGroup_of_continuousMulEquiv
    (InfiniteGalois.fixedFieldGalContinuousMulEquiv ⟨H, hH.prop.1⟩) hH.prop.2

/-- **Finite separable extensions of the fixed field of a maximal pro-`ℓ` subgroup have `ℓ`-power
degree.** -/
theorem exists_finrank_eq_pow_of_fixedField (hℓ : ℓ.Prime) (hH : IsMaximalProPSubgroup ℓ H)
    (M : Type u) [Field M] [Algebra (fixedField H) M] [FiniteDimensional (fixedField H) M]
    [Algebra.IsSeparable (fixedField H) M] : ∃ k, finrank (fixedField H) M = ℓ ^ k := by
  have : IsGalois (fixedField H) Ksep := IsGalois.tower_top_of_isGalois K (fixedField H) Ksep
  have : IsSepClosed Ksep := IsSepClosure.sep_closed K
  let f : M →ₐ[fixedField H] Ksep := IsSepClosed.lift
  let M' : IntermediateField (fixedField H) Ksep := f.fieldRange
  have hdegM : finrank (fixedField H) M = finrank (fixedField H) M' :=
    (AlgEquiv.ofInjectiveField f).toLinearEquiv.finrank_eq
  have : FiniteDimensional (fixedField H) M' :=
    Module.Finite.equiv (AlgEquiv.ofInjectiveField f).toLinearEquiv
  obtain ⟨k, hk⟩ := exists_index_eq_pow_of_isProPGroup hℓ (isProPGroup_gal_fixedField K Ksep hH)
    { toSubgroup := M'.fixingSubgroup
      isOpen' := (InfiniteGalois.isOpen_iff_finite M').2 inferInstance }
  refine ⟨k, ?_⟩
  rw [hdegM, IntermediateField.finrank_eq_fixingSubgroup_index]
  exact hk

/-- Every element of the fixed field lies in a finite subextension of `L / K` inside it. -/
private theorem exists_finite_le_fixedField_inclusion_eq (x : fixedField H) :
    ∃ (K' : IntermediateField K Ksep) (_ : FiniteDimensional K K') (h : K' ≤ fixedField H)
      (x' : K'), inclusion h x' = x :=
  ⟨K⟮(x : Ksep)⟯, adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _),
    adjoin_simple_le_iff.2 x.2, ⟨x, mem_adjoin_simple_self K _⟩, rfl⟩

/-- **Every nonzero element of the fixed field of a maximal pro-`ℓ` subgroup is a power of the
uniformizer times an `ℓ`-th power.** -/
theorem exists_eq_pow_mul_pow_of_fixedField (hℓ : ℓ.Prime) (hℓB : IsUnit (ℓ : B))
    (hH : IsMaximalProPSubgroup ℓ H) {ϖ : B} (hϖ : Irreducible ϖ) (a : fixedField H) (ha : a ≠ 0) :
    ∃ (i : ℕ) (b : fixedField H),
      a = algebraMap K (fixedField H) (algebraMap B K ϖ) ^ i * b ^ ℓ := by
  obtain ⟨K', _, hle, a, rfl⟩ := exists_finite_le_fixedField_inclusion_eq K Ksep a
  let : Algebra B K' := ((algebraMap K K').comp (algebraMap B K)).toAlgebra
  have : IsScalarTower B K K' := .of_algebraMap_eq' rfl
  obtain ⟨i, b, hab⟩ := Stacks.StrictlyHenselianKummer.exists_eq_pow_mul_pow hϖ hℓ hℓB K'
    (not_exists_pow_eq_of_le_fixedField K Ksep hℓ hH hϖ K' hle) a (by rintro rfl; simp at ha)
  exact ⟨i, inclusion hle b, by simp [hab]⟩

/-- **Kummer data on the fixed field of a maximal pro-`ℓ` subgroup** of the absolute Galois group
of the fraction field of a strictly henselian discrete valuation ring, `ℓ` being invertible. -/
theorem fixedField_kummerData (hℓ : ℓ.Prime) (hℓB : IsUnit (ℓ : B))
    (hH : IsMaximalProPSubgroup ℓ H) {ϖ : B} (hϖ : Irreducible ϖ) :
    (∀ e : ℕ, ∃ ζ : fixedField H, IsPrimitiveRoot ζ (ℓ ^ e)) ∧
    (∀ y : fixedField H, y ^ ℓ ≠ algebraMap K (fixedField H) (algebraMap B K ϖ)) ∧
    (∀ a : fixedField H, a ≠ 0 → ∃ (i : ℕ) (b : fixedField H),
      a = algebraMap K (fixedField H) (algebraMap B K ϖ) ^ i * b ^ ℓ) ∧
    (∀ (M : Type u) [Field M] [Algebra (fixedField H) M] [FiniteDimensional (fixedField H) M]
      [Algebra.IsSeparable (fixedField H) M], ∃ k, finrank (fixedField H) M = ℓ ^ k) := by
  refine ⟨fun e => ?_, fun y hy => ?_, exists_eq_pow_mul_pow_of_fixedField K Ksep hℓ hℓB hH hϖ,
    fun M _ _ _ _ => exists_finrank_eq_pow_of_fixedField K Ksep hℓ hH M⟩
  · have hinj : Function.Injective ((algebraMap K (fixedField H)).comp (algebraMap B K)) :=
      (algebraMap K _).injective.comp (IsFractionRing.injective B K)
    obtain ⟨ζ, hζ⟩ := Stacks.StrictlyHenselianKummer.exists_isPrimitiveRoot B
      (m := ℓ ^ e) (by exact_mod_cast hℓB.pow e)
    exact ⟨_, hζ.map_of_injective hinj⟩
  · obtain ⟨K', _, hle, y, rfl⟩ := exists_finite_le_fixedField_inclusion_eq K Ksep y
    exact not_exists_pow_eq_of_le_fixedField K Ksep hℓ hH hϖ K' hle
      ⟨y, (inclusion hle).injective (by simpa using hy)⟩

end AlgebraicGeometry.StrictlyHenselianKummer

end
