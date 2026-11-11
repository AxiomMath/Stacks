module

public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalization

/-!
# All homogeneous parts of the localization `B[1/ψ f]` of the truncation algebra

Let `A` be an `ℕ`-graded ring, `B = ⨁_{d ≥ 0} A_{≥ d}` its truncation algebra and `f ∈ A_d` with
`d > 0`, `g = ψ(f) ∈ B_d`. The localization `B[1/g]` is `ℤ`-graded: its degree `m'` part
`(B[1/g])_{m'}` consists of the fractions `b / gᵏ` with `b ∈ B_{m' + kd}`. Stacks, Section 0EKF,
states the equality of homogeneous parts

  `(B[1/g])_{m'} = ⨁_{m ≥ m'} (A[1/f])_m`

for every `m'`, where `(A[1/f])_m` consists of the fractions `a / fᵏ` with `a ∈ A_{m + kd}`. The
case `m' = 0` is `Stacks.Truncation.isInternal_awayGrading`. Here we prove it for every integer
`m'`, through the ring map `B[1/g] → A[1/f]`, `b / gᵏ ↦ b / fᵏ` (forgetting the degree of `b`):
it is injective on `(B[1/g])_{m'}`, and carries it onto the sum of the `(A[1/f])_m`, `m ≥ m'`.

## Main definitions

* `Stacks.Truncation.locToLocalization`: the ring map `B[1/ψ f] → A[1/f]`.
* `Stacks.Truncation.locPiece`: the degree `m'` part `(B[1/ψ f])_{m'}`.
* `Stacks.Truncation.awayPieceInt`: the degree `m` part `(A[1/f])_m`, for `m ∈ ℤ`.

## Main results

* `Stacks.Truncation.locToLocalization_injOn_locPiece` and
  `Stacks.Truncation.map_locPiece_eq_iSup_awayPieceInt`: the equality of homogeneous parts.

## References

* [Stacks Project, Tag 0EKF](https://stacks.math.columbia.edu/tag/0EKF)
-/

@[expose] public noncomputable section

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

namespace Stacks.Truncation

universe u

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {f : A}

/-- The ring map `B[1/ψ f] → A[1/f]`, `b / (ψ f)ᵏ ↦ b / fᵏ`, induced by forgetting the degree. -/
def locToLocalization : Localization.Away (psi 𝒜 f) →+* Localization.Away f :=
  Localization.awayLift ((algebraMap A (Localization.Away f)).comp (forgetDegree 𝒜)) (psi 𝒜 f)
    (isUnit_iff_exists_inv.mpr ⟨awayFrac f 1 1, comp_psi_mul_awayFrac 𝒜⟩)

/-- `b / (ψ f)ᵏ ↦ b / fᵏ`. -/
theorem locToLocalization_mk (b : TruncationRing 𝒜) (k : ℕ) :
    locToLocalization 𝒜 (Localization.mk b ⟨psi 𝒜 f ^ k, k, rfl⟩) =
      awayFrac f k (forgetDegree 𝒜 b) := by
  rw [locToLocalization, Localization.awayLift_mk _ _ _ _ (comp_psi_mul_awayFrac 𝒜) k,
    RingHom.comp_apply, ← awayFrac_zero_eq_algebraMap, awayFrac_one_one_pow, awayFrac_mul,
    mul_one, zero_add]

variable {𝒜 d}

omit [CommRing A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
private theorem mem_of_eq {R : Type*} {S : Type*} [SetLike S R] (𝒢 : ℕ → S) {i j : ℕ}
    (h : i = j) {a : R} (ha : a ∈ 𝒢 i) : a ∈ 𝒢 j :=
  h ▸ ha

/-- For `d > 0` every integer `m` is `n - kd` for some natural numbers `k` and `n`. -/
theorem exists_natCast_eq_add_mul (hd : 0 < d) (m : ℤ) :
    ∃ k n : ℕ, (n : ℤ) = m + k * d := by
  refine ⟨m.natAbs, (m + m.natAbs * d).toNat, Int.toNat_of_nonneg ?_⟩
  have h1 : -m ≤ (m.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact neg_le_abs m
  have h2 : (m.natAbs : ℤ) ≤ m.natAbs * d := by
    have : (1 : ℤ) ≤ d := by exact_mod_cast hd
    nlinarith [Int.natCast_nonneg m.natAbs]
  linarith

private theorem powers_mk_mul (s : TruncationRing 𝒜) (k l : ℕ) :
    (⟨s ^ k, k, rfl⟩ : Submonoid.powers s) * ⟨s ^ l, l, rfl⟩ = ⟨s ^ (k + l), k + l, rfl⟩ :=
  Subtype.ext (pow_add s k l).symm

variable (𝒜 d)

/-- The degree `m` part `(A[1/f])_m` of `A[1/f]`, for an integer `m`: the fractions `a / fᵏ` with
`a` homogeneous of degree `n = m + kd`. -/
def awayPieceInt (hf : f ∈ 𝒜 d) (hd : 0 < d) (m : ℤ) : AddSubgroup (Localization.Away f) where
  carrier := {z | ∃ (k n : ℕ) (a : A), (n : ℤ) = m + k * d ∧ a ∈ 𝒜 n ∧ z = awayFrac f k a}
  add_mem' := by
    rintro _ _ ⟨k, n, a, hn, ha, rfl⟩ ⟨l, n', b, hn', hb, rfl⟩
    refine ⟨k + l, k * d + n', f ^ k * b + f ^ l * a, by push_cast; linarith,
      add_mem ?_ ?_, awayFrac_add f k l a b⟩
    · simpa only [smul_eq_mul] using SetLike.mul_mem_graded (SetLike.pow_mem_graded k hf) hb
    · refine mem_of_eq 𝒜 ?_ (SetLike.mul_mem_graded (SetLike.pow_mem_graded l hf) ha)
      rw [smul_eq_mul]
      zify
      linarith
  zero_mem' := by
    obtain ⟨k, n, hn⟩ := exists_natCast_eq_add_mul hd m
    exact ⟨k, n, 0, hn, zero_mem _, (awayFrac_zero f k).symm⟩
  neg_mem' := by
    rintro _ ⟨k, n, a, hn, ha, rfl⟩
    exact ⟨k, n, -a, hn, neg_mem ha, awayFrac_neg f k a⟩

/-- The degree `m'` part `(B[1/ψ f])_{m'}` of `B[1/ψ f]`, for an integer `m'`: the fractions
`b / (ψ f)ᵏ` with `b ∈ B_n`, `n = m' + kd`. -/
def locPiece (hf : f ∈ 𝒜 d) (hd : 0 < d) (m : ℤ) :
    AddSubgroup (Localization.Away (psi 𝒜 f)) where
  carrier := {z | ∃ (k n : ℕ) (b : TruncationRing 𝒜), (n : ℤ) = m + k * d ∧ b ∈ grading 𝒜 n ∧
    z = Localization.mk b (⟨psi 𝒜 f ^ k, k, rfl⟩ : Submonoid.powers (psi 𝒜 f))}
  add_mem' := by
    rintro _ _ ⟨k, n, a, hn, ha, rfl⟩ ⟨l, n', b, hn', hb, rfl⟩
    refine ⟨k + l, k * d + n', psi 𝒜 f ^ k * b + psi 𝒜 f ^ l * a, by push_cast; linarith,
      add_mem (SetLike.mul_mem_graded (psi_pow_mem_grading 𝒜 d hf k) hb) ?_, ?_⟩
    · refine mem_of_eq (grading 𝒜) ?_ (SetLike.mul_mem_graded (psi_pow_mem_grading 𝒜 d hf l) ha)
      zify
      linarith
    · rw [Localization.add_mk, powers_mk_mul]
  zero_mem' := by
    obtain ⟨k, n, hn⟩ := exists_natCast_eq_add_mul hd m
    exact ⟨k, n, 0, hn, zero_mem _, (Localization.mk_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨k, n, a, hn, ha, rfl⟩
    exact ⟨k, n, -a, hn, neg_mem ha, Localization.neg_mk _ _⟩

variable {𝒜 d}

/-- **The map `B[1/ψ f] → A[1/f]` is injective on `(B[1/ψ f])_{m'}`.** -/
theorem locToLocalization_injOn_locPiece (hf : f ∈ 𝒜 d) (hd : 0 < d) (m : ℤ)
    {z : Localization.Away (psi 𝒜 f)} (hz : z ∈ locPiece 𝒜 d hf hd m)
    (h0 : locToLocalization 𝒜 z = 0) : z = 0 := by
  obtain ⟨k, n, b, -, hb, rfl⟩ := hz
  obtain ⟨c, hc, rfl⟩ := exists_eq_degElt 𝒜 hb
  rw [locToLocalization_mk, forgetDegree_degElt, awayFrac_eq_zero_iff] at h0
  obtain ⟨N, hN⟩ := h0
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨psi 𝒜 f ^ N, N, rfl⟩, ?_⟩
  change psi 𝒜 f ^ N * degElt 𝒜 n c hc = 0
  rw [psi_pow_eq_degElt 𝒜 d hf N, degElt_mul, degElt_congr 𝒜 rfl hN _ (zero_mem _), degElt_zero]

/-- **`(B[1/g])_{m'} = ⨁_{m ≥ m'} (A[1/f])_m`** (Stacks, Section 0EKF), for `f ∈ A_d`, `d > 0`,
`g = ψ(f)` and any integer `m'`: the map `B[1/g] → A[1/f]`, injective on `(B[1/g])_{m'}` by
`locToLocalization_injOn_locPiece`, carries `(B[1/g])_{m'}` onto the sum of the homogeneous parts
`(A[1/f])_m` with `m ≥ m'`. -/
@[stacks 0EKF "the equality of homogeneous parts (B[1/g])_{m'} = ⨁_{m ≥ m'} (A[1/f])_m, \
g = ψ(f), for every m'"]
theorem map_locPiece_eq_iSup_awayPieceInt (hf : f ∈ 𝒜 d) (hd : 0 < d) (m' : ℤ) :
    (locPiece 𝒜 d hf hd m').map (locToLocalization 𝒜).toAddMonoidHom =
      ⨆ (m : ℤ) (_ : m' ≤ m), awayPieceInt 𝒜 d hf hd m := by
  classical
  refine le_antisymm ?_ (iSup₂_le fun m hm => ?_)
  · rintro _ ⟨z, ⟨k, n, b, hn, hb, rfl⟩, rfl⟩
    obtain ⟨c, hc, rfl⟩ := exists_eq_degElt 𝒜 hb
    change locToLocalization 𝒜 _ ∈ _
    rw [locToLocalization_mk, forgetDegree_degElt, ← DirectSum.sum_support_decompose 𝒜 c,
      ← awayFrac_sum]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    rcases Nat.lt_or_ge j n with hj | hj
    · have h0 : (DirectSum.decompose 𝒜 c j : A) = 0 := by
        rw [← GradedRing.proj_apply]
        exact (mem_truncation_iff 𝒜).mp hc j hj
      rw [h0, awayFrac_zero]
      exact zero_mem _
    · refine AddSubgroup.mem_iSup_of_mem ((j : ℤ) - k * d) ?_
      refine AddSubgroup.mem_iSup_of_mem (by omega) ?_
      exact ⟨k, j, _, by ring, (DirectSum.decompose 𝒜 c j).2, rfl⟩
  · rintro _ ⟨k, n, a, hn, ha, rfl⟩
    obtain ⟨K, N, hN⟩ := exists_natCast_eq_add_mul hd m'
    -- the numerator `f ^ (K + k) * a` has degree `(K + k) d + n ≥ m' + (K + k) d`
    have hdeg : ((m' + (K + k : ℕ) * d).toNat : ℤ) = m' + (K + k : ℕ) * d := by
      refine Int.toNat_of_nonneg ?_
      push_cast
      nlinarith [Int.natCast_nonneg N, Int.natCast_nonneg k, Int.natCast_nonneg d]
    set e := (m' + (K + k : ℕ) * d).toNat with he
    have hle : (e : ℤ) ≤ ((K * d + n : ℕ) : ℤ) := by
      rw [hdeg]
      push_cast
      linarith
    have hmem : f ^ K * a ∈ truncation 𝒜 e := by
      refine mem_truncation_of_mem 𝒜 ?_ (SetLike.mul_mem_graded (SetLike.pow_mem_graded K hf) ha)
      rw [smul_eq_mul]
      exact_mod_cast hle
    refine ⟨Localization.mk (degElt 𝒜 e (f ^ K * a) hmem) ⟨psi 𝒜 f ^ (k + K), k + K, rfl⟩,
      ⟨k + K, e, _, by rw [hdeg]; push_cast; ring, degElt_mem_grading 𝒜 e _ hmem, rfl⟩, ?_⟩
    change locToLocalization 𝒜 _ = _
    rw [locToLocalization_mk, forgetDegree_degElt, ← awayFrac_shift]

/-! ### Compatibility with further localization

For `f ∈ A_d`, `f' ∈ A_{d'}` the standard open `D₊(f f')` lies in `D₊(f)`, and the localization
maps `B[1/ψ f] → B[1/ψ(f f')]`, `A[1/f] → A[1/(f f')]` commute with the maps
`B[1/ψ f] → A[1/f]` and carry `(B[1/ψ f])_{m'}` into `(B[1/ψ(f f')])_{m'}` and `(A[1/f])_m` into
`(A[1/(f f')])_m`: the identification `(B[1/g])_{m'} = ⨁_{m ≥ m'} (A[1/f])_m` is compatible with
further localization. -/

section FurtherLocalization

variable (𝒜) (f f' : A)

/-- `ψ f` becomes a unit in `B[1/ψ(f f')]`. -/
theorem isUnit_algebraMap_psi :
    IsUnit (algebraMap (TruncationRing 𝒜) (Localization.Away (psi 𝒜 (f * f'))) (psi 𝒜 f)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (psi 𝒜 (f * f')))
    (psi 𝒜 (f * f'))
  have e : algebraMap (TruncationRing 𝒜) (Localization.Away (psi 𝒜 (f * f'))) (psi 𝒜 (f * f')) =
      algebraMap _ _ (psi 𝒜 f) * algebraMap _ _ (psi 𝒜 f') := by
    rw [← map_mul, ← map_mul]
  rw [e] at h
  exact isUnit_of_mul_isUnit_left h

/-- `f` becomes a unit in `A[1/(f f')]`. -/
theorem isUnit_algebraMap_left :
    IsUnit (algebraMap A (Localization.Away (f * f')) f) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f * f')) (f * f')
  have e : algebraMap A (Localization.Away (f * f')) (f * f') =
      algebraMap _ _ f * algebraMap _ _ f' := by
    rw [← map_mul]
  rw [e] at h
  exact isUnit_of_mul_isUnit_left h

/-- The localization map `B[1/ψ f] → B[1/ψ(f f')]`. -/
def locRestrict : Localization.Away (psi 𝒜 f) →+* Localization.Away (psi 𝒜 (f * f')) :=
  Localization.awayLift (algebraMap _ _) (psi 𝒜 f) (isUnit_algebraMap_psi 𝒜 f f')

/-- The localization map `A[1/f] → A[1/(f f')]`. -/
def awayRestrict : Localization.Away f →+* Localization.Away (f * f') :=
  Localization.awayLift (algebraMap _ _) f (isUnit_algebraMap_left f f')

theorem locRestrict_algebraMap (b : TruncationRing 𝒜) :
    locRestrict 𝒜 f f' (algebraMap _ _ b) = algebraMap _ _ b :=
  IsLocalization.Away.lift_eq _ (isUnit_algebraMap_psi 𝒜 f f') b

theorem awayRestrict_algebraMap (a : A) :
    awayRestrict f f' (algebraMap _ _ a) = algebraMap _ _ a :=
  IsLocalization.Away.lift_eq _ (isUnit_algebraMap_left f f') a

theorem locToLocalization_algebraMap (b : TruncationRing 𝒜) :
    locToLocalization 𝒜 (f := f) (algebraMap _ _ b) = algebraMap _ _ (forgetDegree 𝒜 b) :=
  (IsLocalization.Away.lift_eq _
    (isUnit_iff_exists_inv.mpr ⟨awayFrac f 1 1, comp_psi_mul_awayFrac 𝒜⟩) b).trans
    (RingHom.comp_apply _ _ _)

/-- **The maps `B[1/ψ f] → A[1/f]` commute with further localization.** -/
@[stacks 0EKF "the identification (B[1/g])_{m'} = ⨁_{m ≥ m'} (A[1/f])_m is compatible with \
further localization: the comparison maps commute with D₊(f f') ⊆ D₊(f)"]
theorem locToLocalization_comp_locRestrict :
    (locToLocalization 𝒜 (f := f * f')).comp (locRestrict 𝒜 f f') =
      (awayRestrict f f').comp (locToLocalization 𝒜 (f := f)) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (psi 𝒜 f)) (RingHom.ext fun b => ?_)
  simp only [RingHom.comp_apply, locRestrict_algebraMap, locToLocalization_algebraMap,
    awayRestrict_algebraMap]

variable {𝒜} {d' : ℕ}

/-- `locRestrict` on fractions: `b / (ψ f)ᵏ ↦ (ψ f')ᵏ b / (ψ(f f'))ᵏ`. -/
theorem locRestrict_mk (b : TruncationRing 𝒜) (k : ℕ) :
    locRestrict 𝒜 f f' (Localization.mk b (⟨psi 𝒜 f ^ k, k, rfl⟩ : Submonoid.powers _)) =
      Localization.mk (psi 𝒜 f' ^ k * b)
        (⟨psi 𝒜 (f * f') ^ k, k, rfl⟩ : Submonoid.powers _) := by
  symm
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  have hs := IsLocalization.mk'_spec (Localization.Away (psi 𝒜 f)) b
    (⟨psi 𝒜 f ^ k, k, rfl⟩ : Submonoid.powers (psi 𝒜 f))
  rw [← Localization.mk_eq_mk'] at hs
  have h2 := congrArg (locRestrict 𝒜 f f') hs
  rw [map_mul (locRestrict 𝒜 f f'), locRestrict_algebraMap, locRestrict_algebraMap] at h2
  have e : algebraMap (TruncationRing 𝒜) (Localization.Away (psi 𝒜 (f * f')))
      (psi 𝒜 (f * f') ^ k) = algebraMap _ _ (psi 𝒜 f ^ k) * algebraMap _ _ (psi 𝒜 f' ^ k) := by
    rw [← map_mul, ← mul_pow, ← map_mul]
  change _ = _ * algebraMap _ _ (psi 𝒜 (f * f') ^ k)
  rw [e, ← mul_assoc, h2, map_mul (algebraMap _ _)]
  exact mul_comm _ _

/-- `awayRestrict` on fractions: `a / fᵏ ↦ f'ᵏ a / (f f')ᵏ`. -/
theorem awayRestrict_awayFrac (k : ℕ) (a : A) :
    awayRestrict f f' (awayFrac f k a) = awayFrac (f * f') k (f' ^ k * a) := by
  symm
  rw [awayFrac, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  have hs := IsLocalization.mk'_spec (Localization.Away f) a
    (⟨f ^ k, k, rfl⟩ : Submonoid.powers f)
  rw [← Localization.mk_eq_mk'] at hs
  have h2 := congrArg (awayRestrict f f') hs
  rw [map_mul, awayRestrict_algebraMap, awayRestrict_algebraMap] at h2
  have e : algebraMap A (Localization.Away (f * f')) ((f * f') ^ k) =
      algebraMap _ _ (f ^ k) * algebraMap _ _ (f' ^ k) := by
    rw [← map_mul, ← mul_pow]
  change _ = awayRestrict f f' (awayFrac f k a) * algebraMap _ _ ((f * f') ^ k)
  rw [e, ← mul_assoc, awayFrac, h2, map_mul (algebraMap _ _)]
  exact mul_comm _ _

/-- **`B[1/ψ f] → B[1/ψ(f f')]` carries `(B[1/ψ f])_{m'}` into `(B[1/ψ(f f')])_{m'}`.** -/
@[stacks 0EKF "the localization B[1/ψ f] → B[1/ψ(f f')] preserves the homogeneous parts \
(B[1/g])_{m'}"]
theorem map_locPiece_le (hf : f ∈ 𝒜 d) (hf' : f' ∈ 𝒜 d') (hd : 0 < d) (m : ℤ) :
    (locPiece 𝒜 d hf hd m).map (locRestrict 𝒜 f f').toAddMonoidHom ≤
      locPiece 𝒜 (d + d') (SetLike.mul_mem_graded hf hf') (by omega) m := by
  rintro _ ⟨_, ⟨k, n, b, hn, hb, rfl⟩, rfl⟩
  refine ⟨k, k * d' + n, psi 𝒜 f' ^ k * b, by push_cast; linarith,
    SetLike.mul_mem_graded (psi_pow_mem_grading 𝒜 d' hf' k) hb, ?_⟩
  exact locRestrict_mk f f' b k

/-- **`A[1/f] → A[1/(f f')]` carries `(A[1/f])_m` into `(A[1/(f f')])_m`.** -/
@[stacks 0EKF "the localization A[1/f] → A[1/(f f')] preserves the homogeneous parts \
(A[1/f])_m"]
theorem map_awayPieceInt_le (hf : f ∈ 𝒜 d) (hf' : f' ∈ 𝒜 d') (hd : 0 < d) (m : ℤ) :
    (awayPieceInt 𝒜 d hf hd m).map (awayRestrict f f').toAddMonoidHom ≤
      awayPieceInt 𝒜 (d + d') (SetLike.mul_mem_graded hf hf') (by omega) m := by
  rintro _ ⟨_, ⟨k, n, a, hn, ha, rfl⟩, rfl⟩
  refine ⟨k, k * d' + n, f' ^ k * a, by push_cast; linarith, ?_, ?_⟩
  · simpa only [smul_eq_mul] using SetLike.mul_mem_graded (SetLike.pow_mem_graded k hf') ha
  · exact awayRestrict_awayFrac f f' k a

end FurtherLocalization

end Stacks.Truncation

end
