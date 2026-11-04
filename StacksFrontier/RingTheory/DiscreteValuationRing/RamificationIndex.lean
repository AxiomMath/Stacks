module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.RingTheory.Ideal.Over.HeightOne
public import StacksFrontier.RingTheory.KrullAkizuki
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ramification index and residue degree of extensions of discrete valuation rings

Let `A ⊂ B` be an extension of discrete valuation rings, that is an injective local ring map, with
fraction fields `K ⊂ L`. The ramification index of `B` over `A` is the integer `e ≥ 1` with
`m_A B = m_B ^ e`; equivalently `e = v_B(π_A)` for a uniformizer `π_A` of `A`. If `K` has
characteristic `p > 0` and `L / K` is purely inseparable, then `e` is a power of `p`.

If moreover `L / K` is finite, then the residue field extension `κ_A ⊂ κ_B` is finite as well, and
its degree `f`, the *residue degree*, satisfies `e * f ≤ [L : K]`. Both `e` and `f` are
multiplicative in towers `A ⊂ B ⊂ C` of discrete valuation rings.

## Main definitions

* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx`: the ramification index of the
  maximal ideal of `A` in `B`.

## Main results

* `Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_ramificationIdx`: the
  `B`-valuation of the image of a
  uniformizer of `A` is the ramification index.
* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_eq_prime_pow_of_purelyInseparable`:
  for a purely inseparable
  extension in characteristic `p`, the ramification index is a power of `p`.
* `Stacks.DiscreteValuationRing.Ramification.map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx`:
  `m_A B = m_B ^ e`.
* `Stacks.DiscreteValuationRing.Ramification.one_le_ramificationIdx`: the ramification index is at
  least `1`.
* `IsDiscreteValuationRing.residueField_finite_and_ramificationIdx_mul_residueDegree_le_finrank`:
  for a finite extension `L / K` the residue field extension is finite and `e * f ≤ [L : K]`.
* `IsDiscreteValuationRing.ramificationIdx_and_inertiaDeg_tower`: the ramification index and the
  residue degree are multiplicative in a tower of discrete valuation rings.

## Implementation notes

The residue degree is `Ideal.inertiaDeg`, the dimension of the larger residue field over the
smaller one; for tag 09E5 it is spelled directly as that `Module.finrank`. Abstract fraction fields
and compatible scalar towers express the induced inclusion of fraction fields.

## References

* [Stacks Project, Tag 09E6](https://stacks.math.columbia.edu/tag/09E6)
* [Stacks Project, Tag 09E5](https://stacks.math.columbia.edu/tag/09E5)
* [Stacks Project, Tag 0BRL](https://stacks.math.columbia.edu/tag/0BRL)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Stacks.DiscreteValuationRing.Ramification

/-- The ramification index of `B` over `A`: the ramification index of the maximal ideal of `B`
over the maximal ideal of `A`. -/
@[sga "7 VIII 7.3.5"]
noncomputable def ramificationIdx (A B : Type*)
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] : ℕ :=
  Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)

/-- The ramification index of `B` over `A` is the ramification index of the maximal ideal of `A`
in the maximal ideal of `B`. -/
theorem ramificationIdx_def (A B : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] : ramificationIdx A B =
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B) := rfl

/-- For an extension of discrete valuation rings `A → B` and any uniformizer `π_A` of `A`, the
`B`-valuation of the image of `π_A` equals the ramification index of `B` over `A`. -/
theorem addVal_algebraMap_eq_ramificationIdx (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [FaithfulSMul A B] (πA : A) (hπA : Irreducible πA) :
    IsDiscreteValuationRing.addVal B (algebraMap A B πA) = (ramificationIdx A B : ℕ∞) := by
  rw [ramificationIdx_def]
  set f := algebraMap A B
  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr hπA.ne_zero) hπB
  have hval : IsDiscreteValuationRing.addVal B (f πA) = (n : ℕ∞) :=
    IsDiscreteValuationRing.addVal_def (f πA) u hπB n hn
  rw [hval]
  congr 1
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer πA).mp hπA,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB]
  symm
  apply Ideal.ramificationIdx'_spec <;>
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
      Ideal.span_singleton_le_span_singleton]
  · exact hn ▸ Dvd.intro_left _ rfl
  · intro hdvd
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hval, hπB.addVal_pow] at hdvd
    exact n.not_succ_le_self (by exact_mod_cast hdvd)

/-- **Stacks 09E6**.
Let `A ⊂ B` be an extension of discrete valuation rings inducing the field extension `K ⊂ L`. If
`K` has characteristic `p` with `p` prime and `L / K` is purely inseparable, then the ramification
index `e` of `B` over `A` is a power of `p`: there is `m ≥ 0` with `e = p ^ m`. -/
@[stacks 09E6]
theorem ramificationIdx_eq_prime_pow_of_purelyInseparable (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] (K L : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] (p : ℕ) (hp : p.Prime) [CharP K p]
    [IsPurelyInseparable K L] : ∃ m : ℕ, ramificationIdx A B = p ^ m := by
  have : ExpChar K p := .prime hp
  obtain ⟨πA, hπA⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B
  set f := algebraMap A B
  set E := ramificationIdx A B
  have hval : IsDiscreteValuationRing.addVal B (f πA) = (E : ℕ∞) :=
    addVal_algebraMap_eq_ramificationIdx A B πA hπA
  have hinjBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hdvdA (a : A) (ha : a ≠ 0) : ∃ k : ℕ,
      IsDiscreteValuationRing.addVal B (f a) = ((k * E : ℕ) : ℕ∞) := by
    obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπA
    refine ⟨k, ?_⟩
    obtain ⟨w, hw⟩ := u.isUnit.map f
    rw [hk, map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, ← hw,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, hval]
    push_cast
    simp [nsmul_eq_mul]
  obtain ⟨m, hmem⟩ := IsPurelyInseparable.pow_mem K p (algebraMap B L πB)
  have hEdvd : E ∣ p ^ m := by
    set q := p ^ m
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨a₁, a₂, ha₂mem, hdiv⟩ := IsFractionRing.div_surjective (A := A) c
    have ha₂ne : a₂ ≠ 0 := nonZeroDivisors.ne_zero ha₂mem
    have hfa₂ne : f a₂ ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr ha₂ne
    have htowerAKL (x : A) : algebraMap K L (algebraMap A K x) = algebraMap A L x :=
      (IsScalarTower.algebraMap_apply A K L x).symm
    have htowerABL (x : A) : algebraMap A L x = algebraMap B L (f x) :=
      IsScalarTower.algebraMap_apply A B L x
    have hkey : algebraMap A L a₁ / algebraMap A L a₂ = algebraMap B L (πB ^ q) := by
      rw [← htowerAKL, ← htowerAKL, ← map_div₀, hdiv, hc, map_pow]
    have ha₂L : algebraMap A L a₂ ≠ 0 := by
      rw [htowerABL]
      exact (map_ne_zero_iff _ hinjBL).mpr hfa₂ne
    have hcross := (div_eq_iff ha₂L).mp hkey
    rw [htowerABL, htowerABL, ← map_mul] at hcross
    have hBeq : f a₁ = πB ^ q * f a₂ := hinjBL hcross
    have ha₁ne : a₁ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hBeq
      exact mul_ne_zero (pow_ne_zero _ hπB.ne_zero) hfa₂ne hBeq.symm
    have hvalEq := congrArg (IsDiscreteValuationRing.addVal B) hBeq
    rw [IsDiscreteValuationRing.addVal_mul, hπB.addVal_pow] at hvalEq
    obtain ⟨k₁, hk₁⟩ := hdvdA a₁ ha₁ne
    obtain ⟨k₂, hk₂⟩ := hdvdA a₂ ha₂ne
    rw [hk₁, hk₂] at hvalEq
    have hnat : k₁ * E = q + k₂ * E := by exact_mod_cast hvalEq
    refine ⟨k₁ - k₂, ?_⟩
    rw [Nat.mul_sub, Nat.mul_comm E k₁, Nat.mul_comm E k₂]
    omega
  exact ((Nat.dvd_prime_pow hp).mp hEdvd).imp fun _ => And.right

/-- For an extension of discrete valuation rings `A → B` with ramification index `e`, the image of
the maximal ideal of `A` generates the `e`-th power of the maximal ideal of `B`. -/
theorem map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx (A B : Type*) [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [FaithfulSMul A B] :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B)
      = IsLocalRing.maximalIdeal B ^ ramificationIdx A B := by
  obtain ⟨πA, hπA⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B
  set E := ramificationIdx A B
  have hval : IsDiscreteValuationRing.addVal B (algebraMap A B πA) = (E : ℕ∞) :=
    addVal_algebraMap_eq_ramificationIdx A B πA hπA
  have hvalB : IsDiscreteValuationRing.addVal B (πB ^ E) = (E : ℕ∞) :=
    hπB.addVal_pow E
  have hassoc : Associated (algebraMap A B πA) (πB ^ E) :=
    (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mp (hval.trans hvalB.symm)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer πA).mp hπA,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow]
  exact Ideal.span_singleton_eq_span_singleton.mpr hassoc

/-- The ramification index of an extension of discrete valuation rings is at least `1`. -/
theorem one_le_ramificationIdx (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [FaithfulSMul A B]
    [IsLocalHom (algebraMap A B)] : 1 ≤ ramificationIdx A B := by
  obtain ⟨πA, hπA⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hne : IsDiscreteValuationRing.addVal B (algebraMap A B πA) ≠ 0 := fun h0 =>
    hπA.not_isUnit (isUnit_of_map_unit _ πA (IsDiscreteValuationRing.addVal_eq_zero_iff.mp h0))
  rw [addVal_algebraMap_eq_ramificationIdx A B πA hπA] at hne
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)

end Stacks.DiscreteValuationRing.Ramification

namespace IsDiscreteValuationRing

open Pointwise

/-- Let `A → B` be an injective local map of discrete valuation rings, with compatible fraction
fields `K → L`. If `L / K` is finite, then the residue-field extension is finite and its degree,
multiplied by the ramification index of `B / A`, is at most `[L : K]`. -/
@[stacks 09E5]
theorem residueField_finite_and_ramificationIdx_mul_residueDegree_le_finrank
    (A B K L : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Module.Finite K L] :
    Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) ∧
      (IsLocalRing.maximalIdeal B).ramificationIdx A *
          Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) ≤
        Module.finrank K L := by
  have h031F := Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient
    A B K L (IsLocalRing.maximalIdeal A)
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  let I := mA.map (algebraMap A B)
  have hI : I ≤ mB := by
    simpa [I, mA, mB] using IsLocalRing.map_maximalIdeal_le (algebraMap A B)
  let _ : Module.Finite (A ⧸ mA) (B ⧸ I) := h031F.2.2.2
  have hfinAI : Module.Finite A (B ⧸ I) := Module.Finite.trans (A ⧸ mA) _
  have hfinAB : Module.Finite A (IsLocalRing.ResidueField B) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ A hI).toLinearMap
      (Ideal.Quotient.factor_surjective hI)
  have hfin : Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    Module.Finite.of_restrictScalars_finite A _ _
  refine ⟨hfin, ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmA : mA = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  let f : B →ₗ[A] L := (IsScalarTower.toAlgHom A B L).toLinearMap
  have hideal : (π • ⊤ : Submodule A B) = Submodule.restrictScalars A I := by
    show (π • ⊤ : Submodule A B) =
      Submodule.restrictScalars A (mA.map (algebraMap A B))
    rw [hmA, Ideal.map_span, Set.image_singleton]
    ext b
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
      Submodule.restrictScalars_mem, Ideal.mem_span_singleton, true_and]
    constructor <;> rintro ⟨c, rfl⟩ <;> exact ⟨c, by rw [Algebra.smul_def]⟩
  have hlen_le : Module.length A (B ⧸ I) ≤ Module.finrank K L := by
    have he := (QuotSMulTop.congr π
      (LinearEquiv.ofInjective f (IsFractionRing.injective B L)).symm).length_eq
    let e := (Submodule.quotEquivOfEq _ _ hideal).trans
      (Submodule.Quotient.restrictScalarsEquiv A I)
    rw [← e.length_eq, ← he]
    refine (length_quotient_smul_le_finrank_mul A K (LinearMap.range f) hπ.ne_zero).trans ?_
    rw [← hmA, ← pow_one mA,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal A 1, Nat.cast_one, mul_one]
  have hmap : I = mB ^ Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B := by
    simpa [I, mA, mB] using
      Stacks.DiscreteValuationRing.Ramification.map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx
        A B
  have hlenB : Module.length B (B ⧸ I) =
      (Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B : ℕ∞) := by
    rw [hmap, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  have hlenA := IsLocalRing.length_restrictScalars A B (B ⧸ I)
  rw [hlenB, Module.length_eq_finrank] at hlenA
  have heq : Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B =
      mB.ramificationIdx A :=
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (IsDiscreteValuationRing.not_a_field A)
  rwa [hlenA, ← Nat.cast_mul, ENat.natCast_le_natCast, heq] at hlen_le

/-- Ramification indices and residue degrees multiply in a tower of extensions
of discrete valuation rings. -/
@[stacks 0BRL]
theorem ramificationIdx_and_inertiaDeg_tower
    (A B C : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [FaithfulSMul A B] [FaithfulSMul B C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] :
    (IsLocalRing.maximalIdeal C).ramificationIdx A =
        (IsLocalRing.maximalIdeal B).ramificationIdx A *
          (IsLocalRing.maximalIdeal C).ramificationIdx B ∧
      (IsLocalRing.maximalIdeal C).inertiaDeg A =
        (IsLocalRing.maximalIdeal B).inertiaDeg A *
          (IsLocalRing.maximalIdeal C).inertiaDeg B := by
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm
  have : (IsLocalRing.maximalIdeal C).LiesOver (IsLocalRing.maximalIdeal B) :=
    (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap B C)).symm
  have : Module.Flat B C := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    exact (Module.isTorsionFree_iff_algebraMap_injective (R := B) (A := C)).2
      (FaithfulSMul.algebraMap_injective B C)
  exact ⟨Ideal.ramificationIdx_tower (R := A) (S := B) (T := C)
      (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal C),
    Ideal.inertiaDeg_tower (R := A) (S := B) (T := C)
      (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal C)⟩

/-- Localizing a surjective ring map `f : R →+* S` at a prime `q` of `S` gives a surjection of the
localization of `R` at the contraction `q.comap f` onto the localization of `S` at `q`. -/
theorem localRingHom_surjective_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (q : Ideal S) [q.IsPrime] :
    Function.Surjective (Localization.localRingHom (q.comap f) q f rfl) := by
  intro z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl z
  obtain ⟨a', rfl⟩ := hf a
  obtain ⟨s', hs'⟩ := hf s.val
  have hs : s' ∈ (q.comap f).primeCompl := by
    show f s' ∉ q
    rw [hs']
    exact s.property
  refine ⟨IsLocalization.mk' (Localization.AtPrime (q.comap f)) a' ⟨s', hs⟩, ?_⟩
  rw [Localization.localRingHom_mk']
  congr 1
  exact Subtype.ext hs'

end IsDiscreteValuationRing
