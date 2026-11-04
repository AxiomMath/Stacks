module

import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.LinearCombination
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic finite presentation

Stacks 00FG: an inclusion of domains of finite type becomes finitely presented after
localizing the source and target at suitable nonzero elements, stated with the canonical map
`Localization.awayMapMul f g : R_f → S_{fg}`.

The proof proceeds by induction on a finite generating set. In the one-generator case,
a nonzero relation of least degree becomes monic after inverting its leading coefficient;
clearing denominators shows that it generates the localized kernel. The gluing step
combines the localizations along a tower.
-/

@[expose] public section

section LocalizationMap

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The composite ring homomorphism `R → S → S_{fg}`, where
`S_{fg} = Localization.Away (algebraMap R S f * g)`. This is the homomorphism through which
the localization `R_f` will receive its map. -/
noncomputable def GenericFinitePresentation.baseMap (f : R) (g : S) :
    R →+* Localization.Away (algebraMap R S f * g) :=
  (algebraMap S (Localization.Away (algebraMap R S f * g))).comp (algebraMap R S)

open GenericFinitePresentation

/-- If `algebraMap R S f * g` is a unit in a tower `R → S → T`, then so is the image of `f`. -/
private theorem isUnit_algebraMap_of_isUnit_mul {T : Type*} [CommSemiring T] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] (f : R) (g : S)
    (h : IsUnit (algebraMap S T (algebraMap R S f * g))) : IsUnit (algebraMap R T f) := by
  rw [map_mul, ← IsScalarTower.algebraMap_apply] at h
  exact isUnit_of_mul_isUnit_left h

/-- The image of `f` in `S_{fg}` is a unit: indeed `fg = (algebraMap R S f) * g` is a
unit in `S_{fg}` by construction, and `algebraMap R S f` divides it. -/
theorem GenericFinitePresentation.isUnit_baseMap (f : R) (g : S) : IsUnit (baseMap f g f) :=
  isUnit_algebraMap_of_isUnit_mul f g (IsLocalization.Away.algebraMap_isUnit _)

/-- The canonical ring homomorphism `R_f → S_{fg}` obtained from the structure map
`R → S → S_{fg}` by the universal property of the localization `R_f = Localization.Away
f` (using that `f` is invertible in `S_{fg}`). -/
@[ega "0 1.6.2" "special case"]
noncomputable def Localization.awayMapMul (f : R) (g : S) :
    Localization.Away f →+* Localization.Away (algebraMap R S f * g) :=
  IsLocalization.Away.lift f (isUnit_baseMap f g)

/-- `awayMapMul f g` extends the structure map `R → S[1/(fg)]`. -/
@[simp]
theorem Localization.awayMapMul_algebraMap (f : R) (g : S) (x : R) :
    awayMapMul f g (algebraMap R (Localization.Away f) x) =
      algebraMap R (Localization.Away (algebraMap R S f * g)) x := by
  rw [awayMapMul, IsLocalization.Away.lift_eq, baseMap, RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply]

/-- Composing `awayMapMul` with the localization map gives the structure map. -/
theorem Localization.awayMapMul_comp_algebraMap (f : R) (g : S) :
    (awayMapMul f g).comp (algebraMap R (Localization.Away f)) =
      algebraMap R (Localization.Away (algebraMap R S f * g)) :=
  RingHom.ext (awayMapMul_algebraMap f g)

/-- The algebra structure given by `awayMapMul` makes `R → R[1/f] → S[1/(fg)]` a tower. -/
theorem Localization.isScalarTower_awayMapMul (f : R) (g : S) :
    letI := (awayMapMul f g).toAlgebra
    IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f * g)) :=
  let := (awayMapMul f g).toAlgebra
  IsScalarTower.of_algebraMap_eq' (awayMapMul_comp_algebraMap f g).symm

end LocalizationMap

section GenericFinitePresentation

open Localization

section OneGenerator

/-- Evaluating at the image of `b` commutes with mapping the coefficients along a tower. -/
private theorem aeval_map_algebraMap_eq {A B Af Bf : Type*} [CommRing A] [CommRing B]
    [CommRing Af] [CommRing Bf] [Algebra A B] [Algebra B Bf] [Algebra A Af] [Algebra Af Bf]
    [Algebra A Bf] [IsScalarTower A Af Bf] [IsScalarTower A B Bf] (b : B) (p : Polynomial A) :
    Polynomial.aeval (algebraMap B Bf b) (p.map (algebraMap A Af)) =
      algebraMap B Bf (Polynomial.aeval b p) := by
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply]

/-- **Descent along the localization.** An element of the kernel of the localized
evaluation map `Polynomial A_f → B_f`, `X ↦ b₀`, comes — after multiplication by a power of
`f` — from an element of the kernel `𝔮` of `Polynomial A → B`, `X ↦ b₀`. -/
theorem exists_aeval_eq_zero_map_eq_pow_smul {A B Bf : Type*}
    [CommRing A] [CommRing B] [CommRing Bf]
    [Algebra A B] [Algebra B Bf] [Algebra A Bf] [IsScalarTower A B Bf] {b₀ : B}
    (f : A) (hf : algebraMap A B f ∈ nonZeroDivisors B)
    [IsLocalization.Away (algebraMap A B f) Bf]
    [Algebra (Localization.Away f) Bf] [IsScalarTower A (Localization.Away f) Bf]
    (P : Polynomial (Localization.Away f))
    (hP : Polynomial.aeval (algebraMap B Bf b₀) P = 0) :
    ∃ (P' : Polynomial A) (k : ℕ),
      Polynomial.aeval b₀ P' = 0 ∧
      P'.map (algebraMap A (Localization.Away f)) =
        (algebraMap A (Localization.Away f) f) ^ k • P := by
  set Af := Localization.Away f with hAf
  set β : Bf := algebraMap B Bf b₀ with hβ
  have hBinj : Function.Injective (algebraMap B Bf) :=
    IsLocalization.injective Bf (M := Submonoid.powers (algebraMap A B f)) <|
      Submonoid.powers_le.mpr hf
  obtain ⟨P', k, hPeq⟩ : ∃ (P' : Polynomial A) (k : ℕ),
      P'.map (algebraMap A Af) = (algebraMap A Af f) ^ k • P := by
    obtain ⟨c, hcmem, hc⟩ :=
      IsLocalization.integerNormalization_spec (Submonoid.powers f) (S := Af) P
    obtain ⟨k, hk⟩ := hcmem
    refine ⟨IsLocalization.integerNormalization (Submonoid.powers f) P, k, ?_⟩
    rw [hc, algebra_compatible_smul Af c P, ← hk, map_pow]
  refine ⟨P', k, ?_, hPeq⟩
  apply hBinj; rw [map_zero]
  rw [← aeval_map_algebraMap_eq (Af := Af) b₀ P', hPeq, map_smul, hP, smul_zero]

/-- For a suitable nonzero `f : A` the kernel of the localized evaluation map
`Polynomial A_f → B_f`, `X ↦ b`, is finitely generated: take `f` to be the leading
coefficient of a nonzero element of `𝔮 = ker (Polynomial A → B, X ↦ b)` of minimal degree,
or `f = 1` when `𝔮 = 0`. The target `B_f` may be any localization of `B` at the image of `f`,
with a compatible `A_f`-algebra structure. -/
theorem exists_ne_zero_fg_ker_aeval_away {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (hinj : Function.Injective (algebraMap A B)) (b : B) :
    ∃ f : A, f ≠ 0 ∧
      ∀ (Bf : Type*) [CommRing Bf] [Algebra B Bf] [Algebra A Bf] [IsScalarTower A B Bf]
        [IsLocalization.Away (algebraMap A B f) Bf]
        [Algebra (Localization.Away f) Bf] [IsScalarTower A (Localization.Away f) Bf],
        (RingHom.ker (Polynomial.aeval (algebraMap B Bf b)
          : Polynomial (Localization.Away f) →ₐ[Localization.Away f] Bf).toRingHom).FG := by
  have : IsDomain A := hinj.isDomain (algebraMap A B)
  classical
  set q := RingHom.ker (Polynomial.aeval b : Polynomial A →ₐ[A] B).toRingHom with hq
  by_cases hqbot : ∀ p ∈ q, p = 0
  · -- 𝔮 = 0: take f = 1, kernel is ⊥
    refine ⟨1, one_ne_zero, ?_⟩
    intro Bf _ _ _ _ _ _ _
    rw [show (RingHom.ker (Polynomial.aeval
        (algebraMap B Bf b)
        : Polynomial (Localization.Away (1 : A)) →ₐ[Localization.Away (1 : A)] _).toRingHom)
          = ⊥ from ?_]
    · exact Submodule.fg_bot
    · rw [eq_bot_iff]
      intro P hP
      rw [RingHom.mem_ker] at hP
      obtain ⟨P', k, hP'0, hP'eq⟩ := exists_aeval_eq_zero_map_eq_pow_smul (1 : A)
        (by rw [map_one]; exact one_mem _) P hP
      have hmem : P' ∈ q := by rw [hq, RingHom.mem_ker]; exact hP'0
      have hP'z : P' = 0 := hqbot P' hmem
      rw [hP'z, Polynomial.map_zero] at hP'eq
      simp only [map_one, one_pow, one_smul] at hP'eq
      simpa using hP'eq.symm
  · -- 𝔮 ≠ 0: pick a minimal-degree nonzero element
    push Not at hqbot
    have hex : ∃ n, ∃ p ∈ q, p ≠ 0 ∧ p.natDegree = n := by
      obtain ⟨p, hp, hp0⟩ := hqbot; exact ⟨p.natDegree, p, hp, hp0, rfl⟩
    obtain ⟨h, hhq, hh0, hhd⟩ := Nat.find_spec hex
    have hmin : ∀ p ∈ q, p ≠ 0 → h.natDegree ≤ p.natDegree := by
      intro p hp hp0; rw [hhd]; by_contra hlt; push Not at hlt
      exact Nat.find_min hex hlt ⟨p, hp, hp0, rfl⟩
    -- now run the monic-division argument
    set f := h.leadingCoeff with hf
    have hfne : f ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hh0
    refine ⟨f, hfne, ?_⟩
    intro Bf _ _ _ _ _ _ _
    set Af := Localization.Away f with hAf
    set β : Bf := algebraMap B Bf b with hβ
    have hfle := Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hfne)
    have hAfinj : Function.Injective (algebraMap A Af) := IsLocalization.injective Af hfle
    have : IsDomain Af := IsLocalization.isDomain_localization hfle
    set H : Polynomial Af := h.map (algebraMap A Af) with hH
    have hHlead : H.leadingCoeff = algebraMap A Af f := by
      rw [hH, Polynomial.leadingCoeff, Polynomial.natDegree_map_eq_of_injective hAfinj,
        Polynomial.coeff_map, ← Polynomial.leadingCoeff, ← hf]
    have hHleadUnit : IsUnit H.leadingCoeff := by
      rw [hHlead]; exact IsLocalization.Away.algebraMap_isUnit f
    have haevalbh : Polynomial.aeval b h = 0 := by rwa [hq, RingHom.mem_ker] at hhq
    have hHker : Polynomial.aeval β H = 0 := by
      rw [hH, hβ, aeval_map_algebraMap_eq b h, haevalbh, map_zero]
    have hHdeg : H.natDegree = h.natDegree := by
      rw [hH, Polynomial.natDegree_map_eq_of_injective hAfinj]
    set Hm : Polynomial Af := Polynomial.C (↑hHleadUnit.unit⁻¹ : Af) * H with hHm
    have hHmMonic : Hm.Monic := by
      rw [hHm, Polynomial.Monic, Polynomial.leadingCoeff_C_mul_of_isUnit (Units.isUnit _)]; simp
    have hH0 : H ≠ 0 := by
      intro hc; rw [hc, Polynomial.leadingCoeff_zero] at hHleadUnit; simp at hHleadUnit
    have hHmdeg : Hm.natDegree = h.natDegree := by
      rw [hHm, Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr (Units.ne_zero _)) hH0,
        Polynomial.natDegree_C, zero_add, hHdeg]
    have hHmker : Polynomial.aeval β Hm = 0 := by rw [hHm, map_mul, hHker, mul_zero]
    have hspaneq : Ideal.span ({H} : Set (Polynomial Af)) = Ideal.span {Hm} := by
      rw [hHm]
      apply le_antisymm
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
        refine ⟨Polynomial.C (↑hHleadUnit.unit : Af), ?_⟩
        rw [mul_right_comm, ← Polynomial.C_mul]; simp
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
        exact ⟨Polynomial.C (↑hHleadUnit.unit⁻¹ : Af), by ring⟩
    rw [show (RingHom.ker (Polynomial.aeval β : Polynomial Af →ₐ[Af] Bf).toRingHom)
        = Ideal.span {H} from ?_]
    · exact ⟨{H}, by rw [Finset.coe_singleton]⟩
    apply le_antisymm
    · intro P hP
      rw [RingHom.mem_ker] at hP
      rw [hspaneq, Ideal.mem_span_singleton]
      have hdecomp := Polynomial.modByMonic_add_div P Hm
      set rem := P %ₘ Hm with hrem
      have hremeq : rem = P - Hm * (P /ₘ Hm) := by rw [hrem]; linear_combination hdecomp
      have hremker : Polynomial.aeval β rem = 0 := by
        rwa [hremeq, map_sub, map_mul, hHmker, zero_mul, sub_zero]
      obtain ⟨rem', k, hrem'0, hrem'eq⟩ := exists_aeval_eq_zero_map_eq_pow_smul f
        (mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr hfne)) rem hremker
      have hrem'q : rem' ∈ q := by rw [hq, RingHom.mem_ker]; exact hrem'0
      have hwunit : IsUnit (algebraMap A Af f) := IsLocalization.Away.algebraMap_isUnit f
      have hrem'z : rem' = 0 := by
        by_contra hne
        have hle := hmin rem' hrem'q hne
        have hdeg' : rem'.natDegree = rem.natDegree := by
          have h1 : (rem'.map (algebraMap A Af)).natDegree = rem'.natDegree :=
            Polynomial.natDegree_map_eq_of_injective hAfinj rem'
          rw [hrem'eq, Polynomial.smul_eq_C_mul] at h1
          rcases eq_or_ne rem 0 with hr | hr
          · rw [hr] at h1 ⊢
            simp only [mul_zero, Polynomial.natDegree_zero] at h1 ⊢
            omega
          · rw [Polynomial.natDegree_mul
              (Polynomial.C_ne_zero.mpr (pow_ne_zero k hwunit.ne_zero)) hr,
              Polynomial.natDegree_C, zero_add] at h1
            omega
        have hrne : rem ≠ 0 := by
          intro hr0; apply hne
          have hz : rem'.map (algebraMap A Af) = 0 := by rw [hrem'eq, hr0, smul_zero]
          exact (Polynomial.map_eq_zero_iff hAfinj).mp hz
        have hdlt : rem.natDegree < Hm.natDegree :=
          Polynomial.natDegree_lt_natDegree hrne (Polynomial.degree_modByMonic_lt P hHmMonic)
        rw [hHmdeg] at hdlt
        omega
      have hremz : rem = 0 := by
        rw [hrem'z, Polynomial.map_zero] at hrem'eq
        have hh := hrem'eq.symm
        rw [smul_eq_zero] at hh
        rcases hh with h1 | h1
        · exact absurd h1 (pow_ne_zero k hwunit.ne_zero)
        · exact h1
      refine ⟨P /ₘ Hm, ?_⟩
      rw [hremz, zero_add] at hdecomp
      exact hdecomp.symm
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      exact hHker

/-- An inclusion of domains generated by one element admits nonzero `f, g` such that
`A[1/f] → B[1/(fg)]` is of finite presentation. The localized evaluation map is surjective
and has finitely generated kernel. -/
theorem exists_ne_zero_finitePresentation_localizedMap_of_adjoin_singleton_eq_top {A B : Type*}
    [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (hinj : Function.Injective (algebraMap A B))
    {b : B} (hgen : Algebra.adjoin A ({b} : Set B) = ⊤) :
    ∃ (f : A) (g : B), f ≠ 0 ∧ g ≠ 0 ∧ (awayMapMul f g).FinitePresentation := by
  have : IsDomain A := hinj.isDomain (algebraMap A B)
  classical
  obtain ⟨f, hf, hfg⟩ := exists_ne_zero_fg_ker_aeval_away (A := A) (B := B) hinj b
  refine ⟨f, 1, hf, one_ne_zero, ?_⟩
  rw [RingHom.FinitePresentation]
  let : Algebra (Localization.Away f) (Localization.Away (algebraMap A B f * 1)) :=
    (awayMapMul f 1).toAlgebra
  set Af := Localization.Away f with hAf
  set Bf := Localization.Away (algebraMap A B f * 1) with hBf
  set β : Bf := algebraMap B Bf b with hβ
  have : IsScalarTower A Af Bf := isScalarTower_awayMapMul f 1
  have : IsLocalization.Away (algebraMap A B f) Bf := by
    simpa only [mul_one] using
      (inferInstance : IsLocalization.Away (algebraMap A B f * 1) Bf)
  -- surjectivity of the localized evaluation map
  have hsurj : Function.Surjective
      (Polynomial.aeval β : Polynomial Af → Bf) := by
    have hbsurj : Function.Surjective (Polynomial.aeval b : Polynomial A → B) := by
      have hr : (Polynomial.aeval b : Polynomial A →ₐ[A] B).range = ⊤ := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact hgen
      rw [← AlgHom.range_eq_top]; exact hr
    have hImB : ∀ y : B,
        algebraMap B Bf y ∈ (Polynomial.aeval β : Polynomial Af →ₐ[Af] Bf).range := by
      intro y
      obtain ⟨p, rfl⟩ := hbsurj y
      exact (AlgHom.mem_range _).mpr ⟨p.map (algebraMap A Af), aeval_map_algebraMap_eq b p⟩
    have huAf : IsUnit (algebraMap A Af f) := IsLocalization.Away.algebraMap_isUnit f
    rw [← AlgHom.range_eq_top, Algebra.eq_top_iff]
    intro z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (algebraMap A B f * 1) z
    have hukey : algebraMap B Bf (algebraMap A B f * 1) =
        algebraMap Af Bf (algebraMap A Af f) := by
      rw [map_mul, map_one, mul_one, ← IsScalarTower.algebraMap_apply A B Bf,
        IsScalarTower.algebraMap_apply A Af Bf]
    have hinvmem : (algebraMap Af Bf) (↑huAf.unit⁻¹) ∈
        (Polynomial.aeval β : Polynomial Af →ₐ[Af] Bf).range :=
      Subalgebra.algebraMap_mem _ _
    have hamem : algebraMap B Bf a ∈
        (Polynomial.aeval β : Polynomial Af →ₐ[Af] Bf).range := hImB a
    have hunit : algebraMap Af Bf (algebraMap A Af f) * algebraMap Af Bf (↑huAf.unit⁻¹) = 1 := by
      rw [← map_mul, huAf.mul_val_inv, map_one]
    have haz : z * (algebraMap Af Bf (algebraMap A Af f)) ^ n = algebraMap B Bf a := by
      rw [← hukey]; exact ha
    have hinvn : (algebraMap Af Bf (algebraMap A Af f)) ^ n *
        (algebraMap Af Bf (↑huAf.unit⁻¹)) ^ n = 1 := by
      rw [← mul_pow, hunit, one_pow]
    have hz : z = algebraMap B Bf a * (algebraMap Af Bf (↑huAf.unit⁻¹)) ^ n := by
      rw [← haz, mul_assoc, hinvn, mul_one]
    rw [hz]
    exact mul_mem hamem (pow_mem hinvmem n)
  -- finite presentation via surjection from the (finitely presented) polynomial ring
  have hpoly : Algebra.FinitePresentation Af (Polynomial Af) :=
    Algebra.FinitePresentation.polynomial _ _
  exact Algebra.FinitePresentation.of_surjective
    (f := (Polynomial.aeval β : Polynomial Af →ₐ[Af] Bf)) hsurj (hfg Bf)

end OneGenerator

/-- If `D` is an algebra over `A_f` and `C`, compatibly with the maps from `A`, then `D` is
a tower over `A_f → C`. -/
private theorem isScalarTower_of_away {A Af C D : Type*} [CommRing A] [CommRing Af]
    [CommRing C] [CommRing D] [Algebra A Af] (f : A) [IsLocalization.Away f Af] [Algebra A C]
    [Algebra A D] [Algebra Af C] [Algebra Af D] [Algebra C D] [IsScalarTower A Af C]
    [IsScalarTower A Af D] [IsScalarTower A C D] : IsScalarTower Af C D := by
  refine .of_algebraMap_eq' ?_
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  rw [← IsScalarTower.algebraMap_eq A Af D, RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq A Af C, ← IsScalarTower.algebraMap_eq A C D]

/-- **Transitivity of finite presentation along a tower.** This packages the composition
step that Stacks 00FG leaves "to the reader": finite presentation composes
(`Algebra.FinitePresentation.trans`). Combined with the fact that the structural localization
maps `R_f → R_{ff'}` are themselves of finite presentation
(`IsLocalization.Away.finitePresentation`),
this is what lets the two inductive reductions `A_f → A'_{fg}` and `A'_{fgf'} → B_{fgf'g'}` be
glued into a single `A_F → B_{F·G}` of finite presentation. -/
@[ega "IV 1.4.1"]
private theorem generic_fp_trans {A C E : Type*}
    [CommRing A] [CommRing C] [CommRing E]
    [Algebra A C] [Algebra C E] [Algebra A E] [IsScalarTower A C E]
    (hAC : Algebra.FinitePresentation A C) (hCE : Algebra.FinitePresentation C E) :
    Algebra.FinitePresentation A E :=
  Algebra.FinitePresentation.trans A C E

/-- **Source localization preserves finite presentation.** If `R → T` is of finite
presentation and `S` is a localization of `R` at a multiplicative set `M`, then the induced
`S → T` is of finite presentation (here `T` is already an `S`-algebra, e.g. `M` invertible in
`T`). This is the universe-polymorphic ingredient that lets us localize the *source* of a
finite-presentation map, which the standard `of_isLocalizationAway` (extending the target)
does not provide. It is proved by base change: `S ⊗[R] T` is of finite presentation over `S`
(`Algebra.FinitePresentation.baseChange`) and is isomorphic to `T`
(`IsLocalization.algebraLid`). -/
private theorem fp_localization_source {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid R) [IsLocalization M S]
    [Algebra.FinitePresentation R T] : Algebra.FinitePresentation S T := by
  have hbc : Algebra.FinitePresentation S (TensorProduct R S T) :=
    Algebra.FinitePresentation.baseChange S
  exact hbc.equiv (IsLocalization.algebraLid M S T)

/-- **Gluing step (localization tower).** Abstract form of the inductive gluing in Stacks
00FG. Given a tower of commutative rings `A → A' → B` with `A' → B` injective and `B` having
no zero divisors, suppose:
* the map `A → A'` admits a generic finite-presentation localization, i.e. there are
  nonzero `f₀ : A`, `g₀ : A'` with `A_{f₀} → A'_{f₀ g₀}` of finite presentation, and
* the map `A' → B` admits a generic finite-presentation localization, i.e. there are
  nonzero `f₁ : A'`, `g₁ : B` with `A'_{f₁} → B_{f₁ g₁}` of finite presentation.

Then `A → B` admits a generic finite-presentation localization: there exist nonzero
`F : A`, `G : B` with `A_F → B_{F G}` of finite presentation.

An iterated `Localization.Away` is a single `Localization.Away` at a product
(`IsLocalization.Away.mul`), so the two finite-presentation legs `A_F → C` and `C → B_{FG}`
compose by `generic_fp_trans` once the intermediate ring `C` is identified as the
appropriate common localization. -/
theorem exists_finitePresentation_localizedMap_trans {A A' B : Type*}
    [CommRing A] [CommRing A'] [CommRing B]
    [NoZeroDivisors B]
    [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    (hinjA'B : Function.Injective (algebraMap A' B))
    (hAA' : ∃ (f : A) (g : A'), f ≠ 0 ∧ g ≠ 0 ∧ (awayMapMul f g).FinitePresentation)
    (hA'B : ∃ (f : A') (g : B), f ≠ 0 ∧ g ≠ 0 ∧ (awayMapMul f g).FinitePresentation) :
    ∃ (f : A) (g : B), f ≠ 0 ∧ g ≠ 0 ∧ (awayMapMul f g).FinitePresentation := by
  classical
  obtain ⟨f₀, g₀, hf₀, hg₀, hAA'fp⟩ := hAA'
  obtain ⟨f₁, g₁, hf₁, hg₁, hA'Bfp⟩ := hA'B
  set c₀ : A' := algebraMap A A' f₀ * g₀ with hc₀
  set c₁ : B := algebraMap A' B f₁ * g₁ with hc₁
  set G : B := algebraMap A' B g₀ * algebraMap A' B f₁ * g₁ with hG
  refine ⟨f₀, G, hf₀, ?_, ?_⟩
  · -- G ≠ 0
    have h1 : algebraMap A' B g₀ ≠ 0 := fun h => hg₀ (hinjA'B (by rw [h, map_zero]))
    have h2 : algebraMap A' B f₁ ≠ 0 := fun h => hf₁ (hinjA'B (by rw [h, map_zero]))
    rw [hG]
    exact mul_ne_zero (mul_ne_zero h1 h2) hg₁
  -- main finite-presentation goal
  rw [RingHom.FinitePresentation]
  let algBD : Algebra (Localization.Away f₀)
      (Localization.Away (algebraMap A B f₀ * G)) := (awayMapMul f₀ G).toAlgebra
  let algAfA'c : Algebra (Localization.Away f₀) (Localization.Away c₀) :=
    (awayMapMul f₀ g₀).toAlgebra
  let algA'fBc : Algebra (Localization.Away f₁) (Localization.Away c₁) :=
    (awayMapMul f₁ g₁).toAlgebra
  -- the middle ring `C = A'_{c₀ f₁}` (localization of `A'_{c₀}` at the image of `f₁`)
  set C := Localization.Away (algebraMap A' (Localization.Away c₀) f₁) with hCdef
  -- the auxiliary target ring `BD' = (B_{c₁})` localized at the image of `c₀`
  set BD' := Localization.Away (algebraMap B (Localization.Away c₁) (algebraMap A' B c₀))
    with hBD'
  ------------------------------------------------------------------
  -- Leg 1: `Algebra.FinitePresentation A_{f₀} C`
  ------------------------------------------------------------------
  have hAfA'c : Algebra.FinitePresentation (Localization.Away f₀) (Localization.Away c₀) := by
    have := hAA'fp; rw [RingHom.FinitePresentation] at this; convert this using 2
  have leg1 : Algebra.FinitePresentation (Localization.Away f₀) C := by
    have : Algebra.FinitePresentation (Localization.Away f₀) (Localization.Away c₀) := hAfA'c
    have : IsScalarTower (Localization.Away f₀) (Localization.Away c₀) C := inferInstance
    exact Algebra.FinitePresentation.of_isLocalizationAway
      (S := Localization.Away c₀) (algebraMap A' (Localization.Away c₀) f₁)
  ------------------------------------------------------------------
  -- Leg 2: `Algebra.FinitePresentation C BD'`
  ------------------------------------------------------------------
  have hA'fBc : Algebra.FinitePresentation (Localization.Away f₁) (Localization.Away c₁) := by
    have := hA'Bfp; rw [RingHom.FinitePresentation] at this; convert this using 2
  have legTarget : Algebra.FinitePresentation (Localization.Away f₁) BD' := by
    have : Algebra.FinitePresentation (Localization.Away f₁) (Localization.Away c₁) := hA'fBc
    have : IsScalarTower (Localization.Away f₁) (Localization.Away c₁) BD' := inferInstance
    exact Algebra.FinitePresentation.of_isLocalizationAway
      (S := Localization.Away c₁) (algebraMap B (Localization.Away c₁) (algebraMap A' B c₀))
  -- `Localization.Away f₁ → C` (since `f₁` is a unit in `C`)
  have hf₁unitC : IsUnit (algebraMap A' C f₁) := by
    have : IsUnit (algebraMap (Localization.Away c₀) C
        (algebraMap A' (Localization.Away c₀) f₁)) := IsLocalization.Away.algebraMap_isUnit _
    rwa [← IsScalarTower.algebraMap_apply A' (Localization.Away c₀) C f₁] at this
  let algAwayf₁C : Algebra (Localization.Away f₁) C :=
    (Localization.awayLift (algebraMap A' C) f₁ hf₁unitC).toAlgebra
  have towerA'Awayf₁C : IsScalarTower A' (Localization.Away f₁) C :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp f₁ hf₁unitC).symm
  -- `C` is the localization of `A'_{f₁}` at the image of `c₀`
  have : IsLocalization (Submonoid.powers (algebraMap A' (Localization.Away f₁) c₀)) C := by
    have := IsLocalization.Away.commutes (R := A') (Localization.Away f₁) (Localization.Away c₀) C
      f₁ c₀
    exact this
  -- `C` is the localization of `A'` at `f₁ * c₀`
  have hCaway : IsLocalization.Away (f₁ * c₀) C :=
    IsLocalization.Away.mul (R := A') (Localization.Away c₀) C c₀ f₁
  -- units in `BD'`
  have hc₀unitBD' : IsUnit (algebraMap A' BD' c₀) := by
    have h1 : IsUnit (algebraMap (Localization.Away c₁) BD'
        (algebraMap B (Localization.Away c₁) (algebraMap A' B c₀))) :=
      IsLocalization.Away.algebraMap_isUnit _
    rw [← IsScalarTower.algebraMap_apply B (Localization.Away c₁) BD',
      ← IsScalarTower.algebraMap_apply A' B BD'] at h1
    exact h1
  have hc₁unitBD' : IsUnit (algebraMap B BD' c₁) := by
    have h2 : IsUnit (algebraMap (Localization.Away c₁) BD'
        (algebraMap B (Localization.Away c₁) c₁)) :=
      (IsLocalization.Away.algebraMap_isUnit c₁).map (algebraMap (Localization.Away c₁) BD')
    rwa [← IsScalarTower.algebraMap_apply B (Localization.Away c₁) BD' c₁] at h2
  have hf₁unitBD' : IsUnit (algebraMap A' BD' f₁) := by
    exact isUnit_algebraMap_of_isUnit_mul (R := A') f₁ g₁ hc₁unitBD'
  have hunitCBD' : IsUnit (algebraMap A' BD' (f₁ * c₀)) := by
    simp only [map_mul]; exact hf₁unitBD'.mul hc₀unitBD'
  let algCBD' : Algebra C BD' :=
    (IsLocalization.Away.lift (R := A') (S := C) (P := BD') (f₁ * c₀) hunitCBD').toAlgebra
  have hCBD'comp : (algebraMap C BD').comp (algebraMap A' C) = algebraMap A' BD' :=
    IsLocalization.Away.lift_comp (f₁ * c₀) hunitCBD'
  have towerA'CBD' : IsScalarTower A' C BD' :=
    IsScalarTower.of_algebraMap_eq' hCBD'comp.symm
  have towerA'Awayf₁Bc₁ : IsScalarTower A' (Localization.Away f₁) (Localization.Away c₁) :=
    isScalarTower_awayMapMul f₁ g₁
  have hAwayf₁BD'comp : algebraMap A' BD'
      = (algebraMap (Localization.Away f₁) BD').comp (algebraMap A' (Localization.Away f₁)) := by
    rw [IsScalarTower.algebraMap_eq A' (Localization.Away c₁) BD',
      IsScalarTower.algebraMap_eq A' (Localization.Away f₁) (Localization.Away c₁),
      IsScalarTower.algebraMap_eq (Localization.Away f₁) (Localization.Away c₁) BD',
      ← RingHom.comp_assoc]
  have towerA'Awayf₁BD' : IsScalarTower A' (Localization.Away f₁) BD' :=
    IsScalarTower.of_algebraMap_eq' hAwayf₁BD'comp
  have towerAwayf₁CBD' : IsScalarTower (Localization.Away f₁) C BD' :=
    isScalarTower_of_away f₁
  have leg2 : Algebra.FinitePresentation C BD' := by
    have : Algebra.FinitePresentation (Localization.Away f₁) BD' := legTarget
    exact fp_localization_source (R := Localization.Away f₁) (S := C) (T := BD')
      (Submonoid.powers (algebraMap A' (Localization.Away f₁) c₀))
  ------------------------------------------------------------------
  -- Glue: `A_{f₀} → C → BD'` and transport `BD' ≃ BD` to get the goal.
  ------------------------------------------------------------------
  -- `f₀` is a unit in `BD'` (its image `algebraMap A B f₀` divides `c₀ = ... f₀ * g₀`)
  have hf₀unitBD' : IsUnit (algebraMap A BD' f₀) := by
    exact isUnit_algebraMap_of_isUnit_mul (R := A) f₀ g₀ hc₀unitBD'
  -- algebra `A_{f₀} → BD'` via the universal property (lift inverting `f₀`)
  let algAfBD' : Algebra (Localization.Away f₀) BD' :=
    (Localization.awayLift (algebraMap A BD') f₀ hf₀unitBD').toAlgebra
  have hAfBD'comp : (algebraMap (Localization.Away f₀) BD').comp
      (algebraMap A (Localization.Away f₀)) = algebraMap A BD' :=
    IsLocalization.Away.lift_comp f₀ hf₀unitBD'
  have towerAAfBD' : IsScalarTower A (Localization.Away f₀) BD' :=
    IsScalarTower.of_algebraMap_eq' hAfBD'comp.symm
  -- tower `A → A_{f₀} → C`
  have towerAAfC : IsScalarTower A (Localization.Away f₀) C := by
    have : IsScalarTower A (Localization.Away f₀) (Localization.Away c₀) :=
      isScalarTower_awayMapMul f₀ g₀
    refine .of_algebraMap_eq fun a => ?_
    rw [IsScalarTower.algebraMap_apply (Localization.Away f₀) (Localization.Away c₀) C,
      ← IsScalarTower.algebraMap_apply A (Localization.Away f₀) (Localization.Away c₀),
      ← IsScalarTower.algebraMap_apply A (Localization.Away c₀) C]
  -- tower `A → C → BD'`
  have towerAA'C : IsScalarTower A A' C := inferInstance
  have towerAA'BD' : IsScalarTower A A' BD' := inferInstance
  have towerACBD' : IsScalarTower A C BD' := by
    have hc : algebraMap A BD' = (algebraMap C BD').comp (algebraMap A C) := by
      rw [IsScalarTower.algebraMap_eq A A' C, ← RingHom.comp_assoc, hCBD'comp,
        ← IsScalarTower.algebraMap_eq A A' BD']
    exact IsScalarTower.of_algebraMap_eq' hc
  -- tower `A_{f₀} → C → BD'`
  have towerAfCBD' : IsScalarTower (Localization.Away f₀) C BD' :=
    isScalarTower_of_away f₀
  have legAll : Algebra.FinitePresentation (Localization.Away f₀) BD' :=
    generic_fp_trans (A := Localization.Away f₀) (C := C) (E := BD') leg1 leg2
  -- identify the target denominator: `algebraMap A B f₀ * G = algebraMap A' B c₀ * c₁`
  have hDident : algebraMap A B f₀ * G = algebraMap A' B c₀ * c₁ := by
    rw [hG, hc₀, hc₁, map_mul, IsScalarTower.algebraMap_apply A A' B f₀]
    ring
  -- `BD` and `BD'` are both localizations of `B` at `algebraMap A B f₀ * G`
  have hBDawayBD' : IsLocalization.Away (algebraMap A' B c₀ * c₁) BD' :=
    IsLocalization.Away.mul (R := B) (Localization.Away c₁) BD' c₁ (algebraMap A' B c₀)
  have hBDaway' : IsLocalization.Away (algebraMap A B f₀ * G) BD' := by
    rw [hDident]; exact hBDawayBD'
  -- the `B`-algebra isomorphism `BD' ≃ₐ[B] BD`
  let eB : BD' ≃ₐ[B] Localization.Away (algebraMap A B f₀ * G) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap A B f₀ * G)) BD'
      (Localization.Away (algebraMap A B f₀ * G))
  -- promote to an `A_{f₀}`-algebra isomorphism
  have towerAAfBD : IsScalarTower A (Localization.Away f₀)
      (Localization.Away (algebraMap A B f₀ * G)) := isScalarTower_awayMapMul f₀ G
  have heBcomm : ∀ x : Localization.Away f₀,
      eB (algebraMap (Localization.Away f₀) BD' x)
        = algebraMap (Localization.Away f₀) (Localization.Away (algebraMap A B f₀ * G)) x := by
    intro x
    have key : (eB.toAlgHom.toRingHom.comp
        (algebraMap (Localization.Away f₀) BD')).comp (algebraMap A (Localization.Away f₀))
        = (algebraMap (Localization.Away f₀)
            (Localization.Away (algebraMap A B f₀ * G))).comp
            (algebraMap A (Localization.Away f₀)) := by
      rw [← IsScalarTower.algebraMap_eq A (Localization.Away f₀)
            (Localization.Away (algebraMap A B f₀ * G))]
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A (Localization.Away f₀) BD']
      ext a
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        AlgEquiv.coe_toAlgHom]
      rw [IsScalarTower.algebraMap_apply A B BD' a,
        IsScalarTower.algebraMap_apply A B (Localization.Away (algebraMap A B f₀ * G)) a]
      exact eB.commutes _
    have := IsLocalization.ringHom_ext (Submonoid.powers f₀) key
    exact RingHom.congr_fun this x
  let eAf : BD' ≃ₐ[Localization.Away f₀] Localization.Away (algebraMap A B f₀ * G) :=
    AlgEquiv.ofRingEquiv (f := eB.toRingEquiv) heBcomm
  exact legAll.equiv eAf

/-- Strong induction on the number of generators: remove a generator, apply induction
to the intermediate subalgebra, and glue with the one-generator case. -/
private theorem exists_ne_zero_finitePresentation_localizedMap_of_card :
    ∀ (n : ℕ) {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
      [Algebra A B], Function.Injective (algebraMap A B) →
      ∀ s : Finset B, s.card = n → Algebra.adjoin A (↑s : Set B) = ⊤ →
      ∃ (f : A) (g : B), f ≠ 0 ∧ g ≠ 0 ∧ (awayMapMul f g).FinitePresentation := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro A B _ _ _ _ hinj s hcard hgen
    have : IsDomain A := hinj.isDomain (algebraMap A B)
    classical
    by_cases hle : n ≤ 1
    · -- base case: at most one generator. Reduce to a single-generator adjoin and apply
      -- the one-generator case. If `s` is empty, the single generator is `0`.
      -- Need: `∃ b, Algebra.adjoin A ({b} : Set B) = ⊤`.
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
      · -- s.card = 0, so s = ∅
        rw [h0] at hcard
        rw [Finset.card_eq_zero] at hcard
        subst hcard
        rw [Finset.coe_empty] at hgen
        have hgen0 : Algebra.adjoin A ({(0 : B)} : Set B) = ⊤ := by
          rw [eq_top_iff, ← hgen]
          exact Algebra.adjoin_mono (Set.empty_subset _)
        exact exists_ne_zero_finitePresentation_localizedMap_of_adjoin_singleton_eq_top hinj hgen0
      · -- s.card = 1, so s = {b}
        rw [h1] at hcard
        rw [Finset.card_eq_one] at hcard
        obtain ⟨b, rfl⟩ := hcard
        rw [Finset.coe_singleton] at hgen
        exact exists_ne_zero_finitePresentation_localizedMap_of_adjoin_singleton_eq_top hinj hgen
    · -- inductive step: pick `b ∈ s`, set `A' = Algebra.adjoin A ↑(s.erase b)`.
      push Not at hle
      have hne : s.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨b, hb⟩ := hne
      -- `A'` as an intermediate domain `A ⊆ A' ⊆ B`.
      set A' := Algebra.adjoin A (↑(s.erase b) : Set B) with hA'def
      -- `B` is generated over `A'` by the single element `b`.
      have hgenA'B : Algebra.adjoin A' ({b} : Set B) = ⊤ := by
        apply Subalgebra.restrictScalars_injective A
        rw [Algebra.restrictScalars_adjoin, Subalgebra.restrictScalars_top,
          Algebra.adjoin_union, hA'def, Algebra.adjoin_eq, ← hgen, ← Algebra.adjoin_union]
        congr 1
        rw [Finset.coe_erase]
        ext x
        simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
        grind
      -- The induction hypothesis applies to `A ⊆ A'` with the generating set `s.erase b`
      -- (lifted to `A'`), which has cardinality `< n`.
      have hinjA'B : Function.Injective (algebraMap A' B) := by
        rw [Subalgebra.algebraMap_eq]
        exact Subtype.coe_injective
      have hAA' : ∃ (f : A) (g : A'), f ≠ 0 ∧ g ≠ 0 ∧ (awayMapMul f g).FinitePresentation := by
        have hinjAA' : Function.Injective (algebraMap A A') := by
          have hcomp : (algebraMap A' B) ∘ (algebraMap A A') = algebraMap A B := by
            ext x; rw [Function.comp_apply, ← IsScalarTower.algebraMap_apply]
          have hci : Function.Injective ((algebraMap A' B) ∘ (algebraMap A A')) := by
            rw [hcomp]; exact hinj
          exact Function.Injective.of_comp hci
        set T : Finset A' := (s.erase b).subtype (· ∈ A') with hTdef
        have hTcoe : (↑T : Set A') = Subtype.val ⁻¹' (↑(s.erase b) : Set B) := by
          rw [hTdef]; ext x; simp only [Finset.mem_coe, Finset.mem_subtype, Finset.mem_erase,
            Set.mem_preimage, Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
          tauto
        have hTgen : Algebra.adjoin A (↑T : Set A') = ⊤ := by
          rw [hTcoe]
          exact Algebra.adjoin_adjoin_coe_preimage
        have hTcard : T.card < n := by
          have h1 : T.card ≤ (s.erase b).card := by
            rw [hTdef, Finset.card_subtype]; exact Finset.card_filter_le _ _
          have h2 : (s.erase b).card = s.card - 1 := Finset.card_erase_of_mem hb
          omega
        exact IH T.card hTcard (A := A) (B := A') hinjAA' T rfl hTgen
      -- The base case applies to `A' ⊆ B`.
      have hA'B : ∃ (f : A') (g : B), f ≠ 0 ∧ g ≠ 0 ∧ (awayMapMul f g).FinitePresentation :=
        exists_ne_zero_finitePresentation_localizedMap_of_adjoin_singleton_eq_top hinjA'B hgenA'B
      -- Glue.
      exact exists_finitePresentation_localizedMap_trans hinjA'B hAA' hA'B

/-- A finite generating set for an inclusion of domains yields a generic
finite-presentation localization. -/
theorem exists_ne_zero_finitePresentation_localizedMap_of_adjoin_eq_top {A B : Type*}
    [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) (s : Finset B)
    (hs : Algebra.adjoin A (s : Set B) = ⊤) :
    ∃ (f : A) (g : B), f ≠ 0 ∧ g ≠ 0 ∧ (awayMapMul f g).FinitePresentation :=
  exists_ne_zero_finitePresentation_localizedMap_of_card s.card hinj s rfl hs

/-- **Generic finite presentation.** An inclusion of domains of finite type admits nonzero
`f ∈ R` and `g ∈ S` such that `R[1/f] → S[1/(fg)]` is of finite presentation.
The domain hypothesis on `R` follows from injectivity. -/
@[stacks 00FG]
theorem GenericFinitePresentation.generic_finite_presentation
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.FiniteType R S] (hinj : Function.Injective (algebraMap R S)) :
    ∃ (f : R) (g : S), f ≠ 0 ∧ g ≠ 0 ∧ (awayMapMul f g).FinitePresentation := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  exact exists_ne_zero_finitePresentation_localizedMap_of_adjoin_eq_top hinj s hs

end GenericFinitePresentation
