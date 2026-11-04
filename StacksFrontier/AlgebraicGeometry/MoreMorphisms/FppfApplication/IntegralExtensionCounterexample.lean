module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Data.Nat.Prime.Int
public import StacksFrontier.RingTheory.SqZero

/-!
# A surjective integral morphism over a non-retrocompact open that does not extend

This file sets up the counterexample showing that [Stacks, Tag 0CNX] is false for a general open
subscheme, so that the hypothesis `[QuasiCompact U.ι]` in
`AlgebraicGeometry.exists_integral_surjective_extension` cannot be dropped.

## The construction

The base ring is `Base = ∏ (n : ℕ), ℤ`, with the elements `twos = (2, 2, 2, …)`, the standard
idempotents `idem n`, and `pows = (1, 2, 4, 8, …)`; the base scheme is `Sch = Spec Base` and the
open subscheme is
`Uo = Df ⊔ Wo` where `Df = D twos` and `Wo = ⨆ n, D (idem n)`.
This `Uo` is not quasi-compact — `not_isCompact_Uo` — because the points `pt n` (the `n`-th
coordinate even) lie in `De n` and in no other member of that cover; hence `Uo.ι` is not a
quasi-compact morphism, i.e. `Uo` is not retrocompact in `Sch` (`not_quasiCompact_Uo`).

Over `Sch` sits the affine scheme `Aff = Spec (Sq Base)` of the square-zero extension
`Sq Base = Base ⊕ Base`, with structure morphism `toSch`, which is integral and surjective. The
counterexample is the scheme over `Uo` glued from the part of `Aff` over `Df` and the part of
`Aff` over `Wo`, identified over the overlap by `psi`, the endomorphism scaling the square-zero
ideal by `pows`. Geometrically this is the relative spectrum of `𝒪 ⊕ ℐ` for the invertible ideal
sheaf `ℐ` on `Uo` that is `𝒪` on `Df` and `2 ^ n • ℤ` on `D (idem n)`: the gluing cocycle is
`pows`, which is a non-unit globally but invertible on the overlap because
`pows * ovl n = ovl n ^ (n + 1)` with `ovl n = twos * idem n` (`pows_mul_ovl`).

## Main results

* `Stacks.IntegralExtensionCounterexample.not_quasiCompact_Uo`: the open subscheme of the
  counterexample is not retrocompact.
* `Stacks.IntegralExtensionCounterexample.le_of_eq_scale_pows`: over the `n`-th overlap, the
  generator of the square-zero ideal is `2 ^ N` times a `pows`-twisted section only when `n ≤ N`,
  because the twist contributes a factor `2 ^ n` on the `n`-th coordinate and `2 ^ n` must then
  divide `2 ^ N`. Over `Df` the sections of a hypothetical extension are a localization, so a
  single `N` would have to work for every `n`; taking `n = N + 1` gives the contradiction.

The gluing, and the comparison with a hypothetical extension, are in the companion module
`IntegralExtensionCounterexampleChase`.

## References

* [Stacks Project, Tag 0CNX](https://stacks.math.columbia.edu/tag/0CNX)
-/

@[expose] public section

namespace Stacks.IntegralExtensionCounterexample

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open Stacks.SqZero Stacks.ModuleQuadraticExtension

universe u

noncomputable section

/-- The base ring of the counterexample: the product of countably many copies of `ℤ`. -/
abbrev Rcat : CommRingCat.{u} := CommRingCat.of (ℕ → ULift.{u} ℤ)

/-- The carrier of the base ring. -/
abbrev Base : Type u := Rcat.{u}

/-- The affine base scheme of the counterexample. -/
abbrev Sch : Scheme.{u} := Spec Rcat.{u}

/-- The `n`-th coordinate of the base ring, as a ring map to `ℤ`. -/
def ev (n : ℕ) : Base.{u} →+* ℤ :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom.comp (Pi.evalRingHom _ n)

/-- The element `(2, 2, 2, …)` of the base ring. -/
def twos : Base.{u} := fun _ ↦ 2

/-- The `n`-th standard idempotent of the base ring. -/
def idem (n : ℕ) : Base.{u} := fun m ↦ if m = n then 1 else 0

/-- The element `(1, 2, 4, 8, …)` of the base ring. -/
def pows : Base.{u} := fun n ↦ 2 ^ n

/-- The `n`-th coordinate map sends `r` to its `n`-th component. -/
lemma ev_apply (n : ℕ) (r : Base.{u}) : ev n r = (r n).down := rfl

/-- Powers in the base ring are computed componentwise. -/
lemma base_pow_apply (r : Base.{u}) (k n : ℕ) : (r ^ k) n = (r n) ^ k := rfl

/-- Every coordinate of `twos` is `2`. -/
@[simp] lemma ev_twos (n : ℕ) : ev.{u} n twos = 2 := rfl

/-- The `n`-th coordinate of `pows` is `2 ^ n`. -/
@[simp] lemma ev_pows (n : ℕ) : ev.{u} n pows = 2 ^ n := by
  rw [ev_apply]; simp [pows]

/-- The `n`-th coordinate of `idem n` is `1`. -/
@[simp] lemma ev_idem_self (n : ℕ) : ev.{u} n (idem n) = 1 := by
  rw [ev_apply]; simp [idem]

/-- The `m`-th coordinate of `idem n` is `0` for `m ≠ n`. -/
lemma ev_idem_of_ne {m n : ℕ} (h : m ≠ n) : ev.{u} m (idem n) = 0 := by
  rw [ev_apply]; simp [idem, h]

/-- Multiplied by `idem n`, the element `pows` agrees with `twos ^ n`. -/
lemma pows_mul_idem (n : ℕ) : pows.{u} * idem n = twos ^ n * idem n := by
  funext m
  by_cases h : m = n
  · subst h
    show pows.{u} m * idem m m = (twos.{u} ^ m) m * idem m m
    simp [pows, idem, twos, base_pow_apply]
  · show pows.{u} m * idem n m = (twos.{u} ^ n) m * idem n m
    simp [idem, h]

/-- The basic open of a section of the base ring, as an open of the base scheme. -/
def D (r : Base.{u}) : Sch.{u}.Opens := PrimeSpectrum.basicOpen r

/-- A point lies in `D r` if and only if `r` is not in its prime ideal. -/
lemma mem_D {r : Base.{u}} {x : ↥Sch.{u}} :
    x ∈ D.{u} r ↔ r ∉ (show PrimeSpectrum Base.{u} from x).asIdeal := Iff.rfl

/-- The basic open of a product is the intersection of the basic opens. -/
lemma D_mul (a b : Base.{u}) : D.{u} (a * b) = D.{u} a ⊓ D.{u} b :=
  PrimeSpectrum.basicOpen_mul a b

/-- The ideal `(2)` of `ℤ`, as a point of `Spec ℤ`. -/
def primeTwo : PrimeSpectrum ℤ :=
  ⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two⟩

/-- The point of the base scheme at which the `n`-th coordinate is even. -/
def pt (n : ℕ) : ↥Sch.{u} := PrimeSpectrum.comap (ev n) primeTwo

/-- An element lies in the prime ideal of `pt n` if and only if its `n`-th coordinate is even. -/
lemma mem_pt {n : ℕ} {s : Base.{u}} :
    s ∈ (show PrimeSpectrum Base.{u} from pt.{u} n).asIdeal ↔ (2 : ℤ) ∣ ev n s :=
  Ideal.mem_span_singleton

/-- The basic open on which `(2, 2, …)` is invertible. -/
def Df : Sch.{u}.Opens := D twos

/-- The basic open on which the `n`-th idempotent is invertible. -/
def De (n : ℕ) : Sch.{u}.Opens := D (idem n)

/-- The union of the `De n`: a non-quasi-compact open of the base scheme. -/
def Wo : Sch.{u}.Opens := ⨆ n, De n

/-- The open subscheme of the counterexample. -/
def Uo : Sch.{u}.Opens := Df ⊔ Wo

/-- The point `pt n` lies in `De n`. -/
lemma pt_mem_De (n : ℕ) : pt.{u} n ∈ De.{u} n := by
  rw [De, mem_D, mem_pt]
  simp

/-- The point `pt n` does not lie in `Df`. -/
lemma pt_notMem_Df (n : ℕ) : pt.{u} n ∉ Df.{u} := by
  rw [Df, mem_D, mem_pt]
  simp

/-- The point `pt n` does not lie in `De m` for `m ≠ n`. -/
lemma pt_notMem_De {m n : ℕ} (h : m ≠ n) : pt.{u} n ∉ De.{u} m := by
  rw [De, mem_D, mem_pt, ev_idem_of_ne (Ne.symm h)]
  simp

/-- Each `De n` is contained in `Uo`. -/
lemma De_le_Uo (n : ℕ) : De.{u} n ≤ Uo.{u} := le_sup_right.trans' (le_iSup De.{u} n)

/-- The open `Uo` is not quasi-compact. -/
lemma not_isCompact_Uo : ¬ IsCompact (Uo.{u} : Set ↥Sch.{u}) := by
  intro hc
  set c : Option ℕ → Set ↥Sch.{u} := fun i ↦ match i with
    | none => (Df.{u} : Set ↥Sch.{u})
    | some n => (De.{u} n : Set ↥Sch.{u}) with hcdef
  have hsub : (Uo.{u} : Set ↥Sch.{u}) ⊆ ⋃ i, c i := by
    intro x hx
    rcases (by simpa [Uo] using hx : x ∈ (Df.{u} : Set ↥Sch.{u}) ∨ x ∈ (Wo.{u} : Set ↥Sch.{u}))
      with h | h
    · exact Set.mem_iUnion.mpr ⟨none, h⟩
    · obtain ⟨n, hn⟩ := Opens.mem_iSup.mp h
      exact Set.mem_iUnion.mpr ⟨some n, hn⟩
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover c
    (fun i ↦ by cases i <;> exact Opens.isOpen _) hsub
  have hfin : {n : ℕ | (some n : Option ℕ) ∈ t}.Finite :=
    Set.Finite.preimage (Option.some_injective ℕ).injOn t.finite_toSet
  obtain ⟨n, hn⟩ := hfin.infinite_compl.nonempty
  obtain ⟨i, hi, hmem'⟩ := Set.mem_iUnion₂.mp (ht (De_le_Uo n (pt_mem_De n)))
  cases i with
  | none => exact pt_notMem_Df n hmem'
  | some m =>
      by_cases hmn : m = n
      · exact hn (by subst hmn; exact hi)
      · exact pt_notMem_De hmn hmem'

/-- The inclusion of `Uo` into the base scheme is not quasi-compact. -/
lemma not_quasiCompact_Uo : ¬ QuasiCompact Uo.{u}.ι := by
  intro h
  refine not_isCompact_Uo ?_
  rw [isCompact_iff_compactSpace]
  exact QuasiCompact.compactSpace_of_compactSpace Uo.{u}.ι

/-- The product of the two generators of the `n`-th overlap. -/
def ovl (n : ℕ) : Base.{u} := twos * idem n

/-- The identity `pows * ovl n = ovl n ^ (n + 1)`. -/
lemma pows_mul_ovl (n : ℕ) : pows.{u} * ovl n = ovl.{u} n ^ (n + 1) := by
  have hi : IsIdempotentElem (idem.{u} n) := by
    funext m
    change idem n m * idem n m = idem n m
    by_cases h : m = n <;> simp [idem, h]
  calc pows.{u} * ovl n = twos * (pows * idem n) := by rw [ovl]; ring
    _ = ovl.{u} n ^ (n + 1) := by
      rw [pows_mul_idem, ovl, mul_pow, hi.pow_succ_eq]; ring

/-- The `n`-th coordinate of `ovl n` is `2`. -/
@[simp] lemma ev_ovl (n : ℕ) : ev.{u} n (ovl n) = 2 := by
  rw [ovl, map_mul, ev_twos, ev_idem_self, mul_one]

/-- The intersection of `Df` and `De n` is `D (ovl n)`. -/
lemma Df_inf_De (n : ℕ) : Df.{u} ⊓ De.{u} n = D.{u} (ovl n) := (D_mul twos (idem n)).symm

/-- Each `De n` is contained in `Wo`. -/
lemma De_le_Wo (n : ℕ) : De.{u} n ≤ Wo.{u} := le_iSup De.{u} n

/-- The intersection of `Df` and `Wo` is the union of the `D (ovl n)`. -/
lemma Df_inf_Wo : Df.{u} ⊓ Wo.{u} = ⨆ n, D.{u} (ovl n) := by
  rw [Wo, inf_iSup_eq]
  exact iSup_congr fun n ↦ Df_inf_De n

/-- The element `pows` is invertible on `D (ovl n)`: `D (ovl n) ≤ D pows`. -/
lemma D_ovl_le_D_pows (n : ℕ) : D.{u} (ovl n) ≤ D.{u} pows := by
  intro x hx
  rw [mem_D] at hx ⊢
  intro hp
  exact hx (((show PrimeSpectrum Base.{u} from x).2.pow_mem_iff_mem (n + 1)
    (Nat.succ_pos n)).mp (pows_mul_ovl n ▸ Ideal.mul_mem_right _ _ hp))

/-- The element `pows` is invertible on the overlap `Df ⊓ Wo`. -/
lemma Df_inf_Wo_le_D_pows : Df.{u} ⊓ Wo.{u} ≤ D.{u} pows := by
  rw [Df_inf_Wo]
  exact iSup_le D_ovl_le_D_pows

/-- Over the `n`-th overlap, the generator of the square-zero ideal is `2 ^ N` times a section
twisted by `(1, 2, 4, …)` only if `n ≤ N`. -/
lemma le_of_eq_scale_pows {n N : ℕ} (L : Type u) [CommRing L] [Algebra (Sq Base.{u}) L]
    [IsLocalization.Away (algebraMap Base.{u} (Sq Base.{u}) (ovl n)) L] (y : Sq Base.{u})
    (hy : algebraMap (Sq Base.{u}) L (Ext.mk (zeroDatum Base.{u}) 0 (twos ^ N))
        = algebraMap (Sq Base.{u}) L (scale pows.{u} y)) :
    n ≤ N := by
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers
    (algebraMap Base.{u} (Sq Base.{u}) (ovl n))) hy
  obtain ⟨k, hk⟩ := c.2
  rw [← hk] at hc
  have hsnd := congrArg Ext.snd hc
  simp only [Stacks.SqZero.algebraMap_pow_eq, Stacks.SqZero.snd_mul, Ext.fst_mk, Ext.snd_mk,
    Stacks.SqZero.snd_scale, smul_eq_mul, mul_zero, add_zero, zero_mul] at hsnd
  have harith := congrArg (ev.{u} n) hsnd
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, ev_ovl, ev_twos, ev_pows] at harith
  have h2 : ((2 : ℤ) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hdvd : (2 : ℤ) ^ n ∣ 2 ^ N := by
    refine ⟨ev.{u} n y.snd, ?_⟩
    have := mul_left_cancel₀ h2 (by linarith [harith] : (2:ℤ) ^ k * 2 ^ N
      = 2 ^ k * (2 ^ n * ev.{u} n y.snd))
    linarith [this]
  have hdvdN : (2 : ℕ) ^ n ∣ 2 ^ N := by
    rw [← Int.natCast_dvd_natCast]
    push_cast
    exact hdvd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvdN

/-- The square-zero extension of the base ring, as a commutative ring object. -/
abbrev Ecat : CommRingCat.{u} := CommRingCat.of (Sq Base.{u})

/-- The affine scheme that is integral and surjective over the base scheme. -/
abbrev Aff : Scheme.{u} := Spec Ecat.{u}

/-- The structure morphism of `Aff` over the base scheme. -/
def toSch : Aff.{u} ⟶ Sch.{u} :=
  Spec.map (CommRingCat.ofHom (algebraMap Base.{u} (Sq Base.{u})))

/-- Scaling the square-zero ideal by `(1, 2, 4, …)`, as an endomorphism of `Aff` over `Sch`. -/
def psi : Aff.{u} ⟶ Aff.{u} :=
  Spec.map (CommRingCat.ofHom (scale pows.{u} : Sq Base.{u} →ₐ[Base.{u}] Sq Base.{u}).toRingHom)

/-- The endomorphism `psi` is a morphism over the base scheme. -/
lemma psi_comp_toSch : psi.{u} ≫ toSch.{u} = toSch.{u} := by
  rw [psi, toSch, ← Spec.map_comp]
  congr 1

/-- The structure morphism `toSch` is integral. -/
instance isIntegralHom_toSch : IsIntegralHom toSch.{u} :=
  Stacks.SqZero.isIntegralHom_specMap_algebraMap Rcat.{u}

/-- The structure morphism `toSch` is surjective. -/
instance surjective_toSch : Surjective toSch.{u} :=
  Stacks.SqZero.surjective_specMap_algebraMap Rcat.{u}

end

end Stacks.IntegralExtensionCounterexample
