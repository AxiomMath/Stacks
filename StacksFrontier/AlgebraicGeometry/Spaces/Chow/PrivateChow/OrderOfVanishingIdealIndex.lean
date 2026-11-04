module

public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing

/-!
# The order of vanishing of a fraction as an index of ideals

Let `R` be a Noetherian ring of Krull dimension at most one and `Q(R)` its total ring of
fractions. For a unit `c ∈ Q(R)` and an ideal `J ⊆ R` containing a nonzerodivisor with
`c J ⊆ R`, write `c J` for the ideal `{y ∈ R : y = c x, x ∈ J}`. Then

`length(R / c J) - length(R / J) = ord_R(c)`.

Writing `c = a / b` with nonzerodivisors `a, b`, the two ideals `a J` and `b (c J)` agree, and
`length(R / x I) = length(R / I) + ord_R(x)` for a nonzerodivisor `x` (the exact sequence
`R / I → R / x I → R / (x) → 0` of `Ideal.exact_mulQuot_quotOfMul`).

This is the local computation behind the comparison of the order of vanishing of a meromorphic
section with the lengths of the cokernels of its denominator ideal.

## Main results

* `Ring.length_quotient_smul_eq_add_ord`: `length(R / x I) = length(R / I) + ord_R(x)`.
* `Ring.toNat_length_quotient_sub_toNat_length_quotient_eq_ordTotalFracInt`: the displayed
  formula.
-/

@[expose] public section

open scoped nonZeroDivisors Pointwise

namespace Ring

variable {R : Type*} [CommRing R]

/-- For a nonzerodivisor `x` and an ideal `I`, `length(R / x I) = length(R / I) + ord_R(x)`. -/
theorem length_quotient_smul_eq_add_ord {x : R} (hx : x ∈ R⁰) (I : Ideal R) :
    Module.length R (R ⧸ x • I) = Module.length R (R ⧸ I) + Ring.ord R x :=
  Module.length_eq_add_of_exact (Ideal.mulQuot x I) (Ideal.quotOfMul x I)
    (Ideal.mulQuot_injective I hx) (Ideal.quotOfMul_surjective I) (Ideal.exact_mulQuot_quotOfMul I)

variable (R) [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [Nontrivial R]
variable {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]

omit [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [Nontrivial R] in
/-- An element of `R` whose image in the total ring of fractions is a unit is a
nonzerodivisor. -/
theorem mem_nonZeroDivisors_of_isUnit_algebraMap {a : R} (ha : IsUnit (algebraMap R K a)) :
    a ∈ R⁰ := by
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
  have h : algebraMap R K x * algebraMap R K a = 0 := by rw [← map_mul, hx, map_zero]
  exact IsFractionRing.injective R K (ha.mul_left_eq_zero.1 h ▸ (map_zero _).symm)

/-- **The order of vanishing as an index of ideals.** Let `c` be a unit of the total ring of
fractions of `R`, let `J ⊆ R` be an ideal containing a nonzerodivisor with `c J ⊆ R`, and let
`J'` be the ideal `c J`. Then `length(R / J') - length(R / J) = ord_R(c)`. -/
theorem toNat_length_quotient_sub_toNat_length_quotient_eq_ordTotalFracInt (c : K)
    (hc : IsUnit c) (J J' : Ideal R) (hJ : ∃ r ∈ J, r ∈ R⁰)
    (hcJ : ∀ x ∈ J, ∃ y : R, algebraMap R K y = c * algebraMap R K x)
    (hJ' : ∀ y : R, y ∈ J' ↔ ∃ x ∈ J, algebraMap R K y = c * algebraMap R K x) :
    ((Module.length R (R ⧸ J')).toNat : ℤ) - ((Module.length R (R ⧸ J)).toNat : ℤ) =
      Ring.ordTotalFracInt R c hc := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ c
  have hspec : IsLocalization.mk' K a b * algebraMap R K (b : R) = algebraMap R K a :=
    IsLocalization.mk'_spec K a b
  have ha : a ∈ R⁰ := mem_nonZeroDivisors_of_isUnit_algebraMap R
    (hspec ▸ hc.mul (IsLocalization.map_units K b))
  have hrel : ∀ (x y : R), algebraMap R K y = IsLocalization.mk' K a b * algebraMap R K x ↔
      (b : R) * y = a * x := fun x y => by
    refine ⟨fun h => IsFractionRing.injective R K ?_, fun h => ?_⟩
    · rw [map_mul, map_mul, h, ← hspec]
      ring
    · refine (IsLocalization.map_units K b).mul_left_inj.1 ?_
      rw [mul_comm (algebraMap R K y), ← map_mul, h, map_mul, ← hspec]
      ring
  have hsmul : (b : R) • J' = a • J := by
    ext z
    simp only [Submodule.mem_smul_pointwise_iff_exists, smul_eq_mul]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := (hJ' y).1 hy
      exact ⟨x, hx, ((hrel x y).1 hxy).symm⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy⟩ := hcJ x hx
      exact ⟨y, (hJ' y).2 ⟨x, hx, hy⟩, (hrel x y).1 hy⟩
  have h₁ := length_quotient_smul_eq_add_ord b.2 J'
  have h₂ := length_quotient_smul_eq_add_ord ha J
  rw [hsmul] at h₁
  obtain ⟨r, hrJ, hr⟩ := hJ
  have hle : Ideal.span {r} ≤ J := (Ideal.span_singleton_le_iff_mem J).2 hrJ
  have hJfin : Module.length R (R ⧸ J) ≠ ⊤ := ne_top_of_le_ne_top (Ring.ord_ne_top hr)
    (Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle))
  have hord : Ring.ordTotalFracInt R (IsLocalization.mk' K a b) hc =
      ((Ring.ord R a).toNat : ℤ) - ((Ring.ord R (b : R)).toNat : ℤ) :=
    Ring.ordTotalFracInt_mk' R ⟨a, ha⟩ b hc
  rw [hord]
  have hafin := Ring.ord_ne_top ha
  have hsum : Module.length R (R ⧸ J') + Ring.ord R b ≠ ⊤ := by
    rw [← h₁, h₂]
    exact WithTop.add_ne_top.2 ⟨hJfin, hafin⟩
  have key : (Module.length R (R ⧸ J')).toNat + (Ring.ord R b).toNat =
      (Module.length R (R ⧸ J)).toNat + (Ring.ord R a).toNat := by
    rw [← ENat.toNat_add (WithTop.add_ne_top.1 hsum).1 (Ring.ord_ne_top b.2),
      ← ENat.toNat_add hJfin hafin, ← h₁, h₂]
  omega

end Ring

namespace Ring

/-- **The order of vanishing of a fraction read at a localization, as an index of extended
ideals.** Let `A` be a ring with a total ring of fractions `K_A`, let `O` be a localization of `A`
at a submonoid `M`, Noetherian of dimension at most one, with total ring of fractions `K_O`, and
let `φ : K_A → K_O` be compatible with `A → O`. Let `c ∈ K_A` with `φ c` a unit, let
`I = {a : a c ∈ A}` and `J' = {a c : a ∈ I}`, and assume `I` contains an element whose image in
`O` is a nonzerodivisor. Then `length(O / J' O) - length(O / I O) = ord_O(φ c)`. -/
theorem toNat_length_quotient_map_sub_eq_ordTotalFracInt {A : Type*} [CommRing A]
    {K_A : Type*} [CommRing K_A] [Algebra A K_A]
    (O : Type*) [CommRing O] [IsNoetherianRing O] [Ring.KrullDimLE 1 O] [Nontrivial O]
    [Algebra A O] (M : Submonoid A) [IsLocalization M O]
    {K_O : Type*} [CommRing K_O] [Algebra O K_O] [IsFractionRing O K_O]
    (φ : K_A →+* K_O) (hφ : ∀ a : A, φ (algebraMap A K_A a) = algebraMap O K_O (algebraMap A O a))
    (c : K_A) (hc : IsUnit (φ c)) (I J' : Ideal A)
    (hI : ∀ a, a ∈ I ↔ ∃ y : A, algebraMap A K_A y = algebraMap A K_A a * c)
    (hJ' : ∀ y, y ∈ J' ↔ ∃ a ∈ I, algebraMap A K_A y = algebraMap A K_A a * c)
    (hq : ∃ q ∈ I, algebraMap A O q ∈ O⁰) :
    ((Module.length O (O ⧸ J'.map (algebraMap A O))).toNat : ℤ) -
        ((Module.length O (O ⧸ I.map (algebraMap A O))).toNat : ℤ) =
      Ring.ordTotalFracInt O (φ c) hc := by
  have hunit : ∀ s : M, IsUnit (algebraMap A O s) := IsLocalization.map_units O
  have htw : ∀ s : M, algebraMap O K_O (algebraMap A O s) *
      algebraMap O K_O ((hunit s).unit⁻¹ : Oˣ) = 1 := fun s => by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have hrel : ∀ a y : A, algebraMap A K_A y = algebraMap A K_A a * c →
      algebraMap O K_O (algebraMap A O y) = φ c * algebraMap O K_O (algebraMap A O a) := by
    intro a y h
    rw [← hφ, ← hφ, h, map_mul, mul_comm]
  refine toNat_length_quotient_sub_toNat_length_quotient_eq_ordTotalFracInt O (φ c) hc
    (I.map (algebraMap A O)) (J'.map (algebraMap A O)) ?_ ?_ ?_
  · obtain ⟨q, hqI, hq⟩ := hq
    exact ⟨_, Ideal.mem_map_of_mem _ hqI, hq⟩
  · intro x hx
    obtain ⟨⟨⟨a, ha⟩, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M O).1 hx
    obtain ⟨y, hy⟩ := (hI a).1 ha
    refine ⟨(hunit s).unit⁻¹ * algebraMap A O y, ?_⟩
    have hs' := congrArg (algebraMap O K_O) hs
    rw [map_mul] at hs' ⊢
    linear_combination (algebraMap O K_O ((hunit s).unit⁻¹ : Oˣ)) * hrel a y hy -
      φ c * algebraMap O K_O ((hunit s).unit⁻¹ : Oˣ) * hs' + φ c * algebraMap O K_O x * htw s
  · refine fun y => ⟨fun hy => ?_, ?_⟩
    · obtain ⟨⟨⟨y₀, hy₀⟩, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M O).1 hy
      obtain ⟨a, ha, hya⟩ := (hJ' y₀).1 hy₀
      refine ⟨(hunit s).unit⁻¹ * algebraMap A O a,
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩
      have hs' := congrArg (algebraMap O K_O) hs
      rw [map_mul] at hs' ⊢
      linear_combination (algebraMap O K_O ((hunit s).unit⁻¹ : Oˣ)) * hs' +
        (algebraMap O K_O ((hunit s).unit⁻¹ : Oˣ)) * hrel a y₀ hya - algebraMap O K_O y * htw s
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨⟨⟨a, ha⟩, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M O).1 hx
      obtain ⟨y₀, hy₀⟩ := (hI a).1 ha
      have : y * algebraMap A O s = algebraMap A O y₀ := by
        refine IsFractionRing.injective O K_O ?_
        have hs' := congrArg (algebraMap O K_O) hs
        rw [map_mul] at hs' ⊢
        linear_combination (algebraMap O K_O (algebraMap A O s)) * hxy + φ c * hs' - hrel a y₀ hy₀
      exact (IsLocalization.mem_map_algebraMap_iff M O).2 ⟨⟨⟨y₀, (hJ' y₀).2 ⟨a, ha, hy₀⟩⟩, s⟩, this⟩

end Ring
