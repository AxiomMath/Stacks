module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.NormalSymbol
public import StacksFrontier.RingTheory.Length.FiniteModification

/-!
# Tame symbols and a finite modification

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring and let `A ⊆ B` be a finite ring
extension with `B / A` annihilated by a power of `𝔪` and with `𝔪` not an associated prime of
`B`. Stacks 0EAT asserts

`∂_A(a, b) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(∂_{B_𝔮}(a, b))`,

the product being over the maximal ideals of `B`.

In this development the tame symbol is carried as data — `Stacks.Chow.RegularTameSymbol`, the
four conditions Stacks 0EAL, 0EAM, 0EAN and 0EAP, which is how Stacks 0EAH presents it — and, as
that type's docstring records, the source gives a recipe producing such a datum but does not claim
the datum is unique. What is proved here is that **the right-hand side is itself a tame symbol on
`A`**: `Stacks.Chow.normPushforward`, whose value is the displayed product by construction
(`Stacks.Chow.normPushforward_apply`).

That is the whole of Stacks 0EAT available at this spelling, and the reason is exact rather than
a matter of taste. Once the right-hand side is known to be a term of `RegularTameSymbol A`, the
displayed equation for an *arbitrary* `symbA : RegularTameSymbol A` says that two terms of that
type agree — that is, it is a uniqueness statement for `RegularTameSymbol A`, which is precisely
what the source declines to assert and what this development therefore does not have. A consumer
that wants the equation must either supply the symbol on `A` as `normPushforward` itself, which
makes it `normPushforward_apply`, or prove uniqueness first.

The whole content is the verification of the two conditions that mention a length. Stacks 0EAM
asks for `∂_A(b, b) = (-1) ^ length_A(A/bA)` and Stacks 0EAN for `∂_A(u, b) = ū ^ length_A(A/bA)`;
on the right-hand side the corresponding exponents are `length_{B_𝔮}(B_𝔮/bB_𝔮)`, and the norm of
an element of `κ(𝔪)` is its `[κ(𝔮) : κ(𝔪)]`-th power, so what is needed is

`length_A(A/bA) = ∑_𝔮 [κ(𝔮) : κ(𝔪)] length_{B_𝔮}(B_𝔮/bB_𝔮)`,

which is `Stacks.Length.ord_eq_sum_finrank_mul_ord`. Bimultiplicativity (Stacks 0EAL) and the
Steinberg relation (Stacks 0EAP) are inherited factor by factor.

## Main definitions

* `Stacks.Chow.toExtensionNonZeroDivisor` — a nonzerodivisor of `A` as a nonzerodivisor of `B_𝔮`.
* `Stacks.Chow.normProd` — the right-hand side of Stacks 0EAT.
* `Stacks.Chow.normPushforward`, `Stacks.Chow.normPushforwardOfModuleFinite` — Stacks 0EAT: the
  right-hand side is a tame symbol on `A`.

## Main results

* `Stacks.Chow.mem_nonZeroDivisors_algebraMap` — a nonzerodivisor of `A` stays a nonzerodivisor
  in `B`.
* `Stacks.Chow.normPushforward_apply` — the product formula of Stacks 0EAT.
* `Stacks.Chow.not_isAssociatedPrime_maximalIdeal_self`, `Stacks.Chow.normPushforwardSelf` — the
  hypothesis class is inhabited: a one-dimensional Noetherian normal local domain satisfies every
  hypothesis for the identity extension `A ⊆ A`.
* `Stacks.Chow.normPushforwardSelfDvr` — the same at a discrete valuation ring, where every
  hypothesis is an instance.

## Implementation notes

`Fintype (MaximalSpectrum B)` and the locality of `A → B_𝔮` are carried as instance hypotheses,
as in the source's formula, and both are discharged by
`Stacks.Length.finite_maximalSpectrum` and `Stacks.Length.isLocalHom_algebraMap_localization`;
`Stacks.Chow.normPushforwardOfModuleFinite` is the resulting form with no instance hypothesis
left. The residue degree `[κ(𝔮) : κ(𝔪)]` is spelled `Module.finrank`, which is what
`Algebra.norm_algebraMap` computes the norm of an element of `κ(𝔪)` with.

## References

* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Stacks.Chow

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]

omit [Module.Finite A B] in
/-- **A nonzerodivisor of `A` stays a nonzerodivisor in `B`** when `𝔪` is not an associated
prime of `B`: the kernel of multiplication by it is supported at `𝔪`. -/
theorem mem_nonZeroDivisors_algebraMap (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    {a : A} (ha : a ∈ nonZeroDivisors A) : algebraMap A B a ∈ nonZeroDivisors B := by
  have hreg : IsSMulRegular B a := Stacks.Length.isSMulRegular_of_not_isAssociatedPrime hass ha
  have key : ∀ x : B, x * algebraMap A B a = 0 → x = 0 := by
    intro x hx
    refine hreg (?_ : a • x = a • (0 : B))
    rw [smul_zero, Algebra.smul_def, mul_comm (algebraMap A B a) x]
    exact hx
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

/-- **A nonzerodivisor of `A` as a nonzerodivisor of `B_𝔮`.** It is a nonzerodivisor of `B` by
`Stacks.Chow.mem_nonZeroDivisors_algebraMap`, and a nonzerodivisor stays one in a localization. -/
def toExtensionNonZeroDivisor (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (q : MaximalSpectrum B) (a : nonZeroDivisors A) :
    nonZeroDivisors (Localization.AtPrime q.asIdeal) :=
  ⟨algebraMap A (Localization.AtPrime q.asIdeal) (a : A), by
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q.asIdeal)]
    exact IsLocalization.nonZeroDivisors_le_comap (M := q.asIdeal.primeCompl)
      (S := Localization.AtPrime q.asIdeal) (mem_nonZeroDivisors_algebraMap hass a.2)⟩

omit [Module.Finite A B] in
/-- The underlying element of `toExtensionNonZeroDivisor hass q a` is the image of `a` in
`B_𝔮`. -/
@[simp]
theorem toExtensionNonZeroDivisor_val (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (q : MaximalSpectrum B) (a : nonZeroDivisors A) :
    (toExtensionNonZeroDivisor hass q a : Localization.AtPrime q.asIdeal) =
      algebraMap A (Localization.AtPrime q.asIdeal) (a : A) := rfl

omit [Module.Finite A B] in
/-- `toExtensionNonZeroDivisor hass q` is multiplicative. -/
theorem toExtensionNonZeroDivisor_mul (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (q : MaximalSpectrum B) (a a' : nonZeroDivisors A) :
    toExtensionNonZeroDivisor hass q (a * a') =
      toExtensionNonZeroDivisor hass q a * toExtensionNonZeroDivisor hass q a' :=
  Subtype.ext (by simp [Submonoid.coe_mul])

variable [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B] in
/-- The residue-field norm of the image of a unit of `κ(𝔪)` is its `[κ(𝔮) : κ(𝔪)]`-th power. -/
theorem units_map_norm_algebraMap_residueField (q : MaximalSpectrum B)
    (x : (ResidueField A)ˣ) :
    Units.map (Algebra.norm (ResidueField A) :
        ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
      (Units.map (algebraMap (ResidueField A)
        (ResidueField (Localization.AtPrime q.asIdeal))).toMonoidHom x) =
      x ^ Module.finrank (ResidueField A)
        (ResidueField (Localization.AtPrime q.asIdeal)) := by
  refine Units.ext ?_
  simp only [Units.coe_map, Units.val_pow_eq_pow_val]
  exact Algebra.norm_algebraMap _

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B] in
/-- The residue-field norm of `-1` is `(-1) ^ [κ(𝔮) : κ(𝔪)]`. -/
theorem units_map_norm_neg_one (q : MaximalSpectrum B) :
    Units.map (Algebra.norm (ResidueField A) :
        ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
      (-1 : (ResidueField (Localization.AtPrime q.asIdeal))ˣ) =
      (-1 : (ResidueField A)ˣ) ^ Module.finrank (ResidueField A)
        (ResidueField (Localization.AtPrime q.asIdeal)) := by
  rw [show (-1 : (ResidueField (Localization.AtPrime q.asIdeal))ˣ) =
    Units.map (algebraMap (ResidueField A)
      (ResidueField (Localization.AtPrime q.asIdeal))).toMonoidHom
      (-1 : (ResidueField A)ˣ) from Units.ext (by simp)]
  exact units_map_norm_algebraMap_residueField q (-1)

variable [Fintype (MaximalSpectrum B)]
  (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
  (symb : ∀ q : MaximalSpectrum B, RegularTameSymbol (Localization.AtPrime q.asIdeal))

/-- **The right-hand side of Stacks 0EAT**: the product over the maximal ideals of `B` of the
residue-field norms of the given symbols on the localizations. -/
noncomputable def normProd (a b : nonZeroDivisors A) : (ResidueField A)ˣ :=
  ∏ q : MaximalSpectrum B,
    Units.map (Algebra.norm (ResidueField A) :
        ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
      (symb q (toExtensionNonZeroDivisor hass q a) (toExtensionNonZeroDivisor hass q b))

omit [Module.Finite A B] in
/-- `normProd hass symb a b` is the product over the maximal ideals `𝔮` of `B` of the
residue-field norms of `symb 𝔮` evaluated at the images of `a` and `b` in `B_𝔮`. -/
theorem normProd_eq (a b : nonZeroDivisors A) :
    normProd hass symb a b =
      ∏ q : MaximalSpectrum B,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (symb q (toExtensionNonZeroDivisor hass q a)
            (toExtensionNonZeroDivisor hass q b)) := rfl

omit [Module.Finite A B] in
/-- `normProd hass symb` is multiplicative in its first argument. -/
theorem normProd_mul_left (a a' b : nonZeroDivisors A) :
    normProd hass symb (a * a') b = normProd hass symb a b * normProd hass symb a' b := by
  rw [normProd_eq, normProd_eq, normProd_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [toExtensionNonZeroDivisor_mul, (symb q).map_mul_left, map_mul]

omit [Module.Finite A B] in
/-- `normProd hass symb` is multiplicative in its second argument. -/
theorem normProd_mul_right (a b b' : nonZeroDivisors A) :
    normProd hass symb a (b * b') = normProd hass symb a b * normProd hass symb a b' := by
  rw [normProd_eq, normProd_eq, normProd_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [toExtensionNonZeroDivisor_mul, (symb q).map_mul_right, map_mul]

omit [Module.Finite A B] in
/-- `normProd hass symb` satisfies the Steinberg relation: if `c = b - a`, then
`normProd a c * normProd b b = normProd b c * normProd a b`. -/
theorem normProd_steinberg (a b c : nonZeroDivisors A) (hc : (c : A) = (b : A) - (a : A)) :
    normProd hass symb a c * normProd hass symb b b =
      normProd hass symb b c * normProd hass symb a b := by
  have hcq : ∀ q : MaximalSpectrum B,
      (toExtensionNonZeroDivisor hass q c : Localization.AtPrime q.asIdeal) =
        (toExtensionNonZeroDivisor hass q b : Localization.AtPrime q.asIdeal) -
          (toExtensionNonZeroDivisor hass q a : Localization.AtPrime q.asIdeal) := by
    intro q
    simp only [toExtensionNonZeroDivisor_val, hc, map_sub]
  rw [normProd_eq, normProd_eq, normProd_eq, normProd_eq, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [← map_mul, ← map_mul, (symb q).steinberg _ _ _ (hcq q)]

variable (hinj : Function.Injective (algebraMap A B))
  (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
    LinearMap.range (Algebra.linearMap A B))

include hass hinj hquot in
/-- The exponent identity behind Stacks 0EAM and 0EAN for the norm product: the length of
`A / bA` is the sum over the maximal ideals of `B` of the residue degree times the length of
`B_𝔮 / bB_𝔮`. -/
theorem ord_toNat_eq_sum_finrank_mul_ord_toNat {a : A} (ha : a ∈ nonZeroDivisors A) :
    (Ring.ord A a).toNat =
      ∑ q : MaximalSpectrum B,
        Module.finrank (ResidueField A) (ResidueField (Localization.AtPrime q.asIdeal)) *
          (Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap A (Localization.AtPrime q.asIdeal) a)).toNat := by
  have hid := Stacks.Length.ord_eq_sum_finrank_mul_ord hinj hquot hass ha
  have htop : Ring.ord A a ≠ ⊤ := Ring.ord_ne_top ha
  have hpos : ∀ q : MaximalSpectrum B,
      Module.finrank (ResidueField A)
        (ResidueField (Localization.AtPrime q.asIdeal)) ≠ 0 := by
    intro q
    have := Stacks.Length.finite_residueField A q
    exact Module.finrank_pos.ne'
  have hne : ∀ q : MaximalSpectrum B,
      Ring.ord (Localization.AtPrime q.asIdeal)
        (algebraMap A (Localization.AtPrime q.asIdeal) a) ≠ ⊤ := by
    intro q
    have hterm : (Module.finrank (ResidueField A)
          (ResidueField (Localization.AtPrime q.asIdeal)) : ℕ∞) *
        Ring.ord (Localization.AtPrime q.asIdeal)
          (algebraMap A (Localization.AtPrime q.asIdeal) a) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (hid ▸ htop) ?_
      exact Finset.single_le_sum
        (f := fun q' : MaximalSpectrum B =>
          (Module.finrank (ResidueField A)
            (ResidueField (Localization.AtPrime q'.asIdeal)) : ℕ∞) *
          Ring.ord (Localization.AtPrime q'.asIdeal)
            (algebraMap A (Localization.AtPrime q'.asIdeal) a))
        (fun _ _ => zero_le) (Finset.mem_univ q)
    intro hq
    rw [hq, ENat.mul_top (by exact_mod_cast hpos q)] at hterm
    exact hterm rfl
  have key : ((Ring.ord A a).toNat : ℕ∞) =
      ((∑ q : MaximalSpectrum B,
        Module.finrank (ResidueField A) (ResidueField (Localization.AtPrime q.asIdeal)) *
          (Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap A (Localization.AtPrime q.asIdeal) a)).toNat : ℕ) : ℕ∞) := by
    rw [ENat.natCast_toNat htop, hid, Nat.cast_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [Nat.cast_mul, ENat.natCast_toNat (hne q)]
  exact_mod_cast key

/-- `normProd hass symb a b` is `c ^ ord_A(b)` once each local factor is `c` to the power
`[κ(𝔮) : κ(𝔪)] * ord_{B_𝔮}(b)`. -/
private theorem normProd_eq_pow_of_forall
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (a b : nonZeroDivisors A) (c : (ResidueField A)ˣ)
    (h : ∀ q : MaximalSpectrum B,
      Units.map (Algebra.norm (ResidueField A) :
          ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
        (symb q (toExtensionNonZeroDivisor hass q a) (toExtensionNonZeroDivisor hass q b)) =
      c ^ (Module.finrank (ResidueField A) (ResidueField (Localization.AtPrime q.asIdeal)) *
        (Ring.ord (Localization.AtPrime q.asIdeal)
          (algebraMap A (Localization.AtPrime q.asIdeal) b)).toNat)) :
    normProd hass symb a b = c ^ (Ring.ord A (b : A)).toNat := by
  rw [normProd_eq, ord_toNat_eq_sum_finrank_mul_ord_toNat hass hinj hquot b.2,
    ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun q _ => h q

include hinj hquot in
/-- **Stacks 0EAM for the norm product.** -/
theorem normProd_self (b : nonZeroDivisors A) :
    normProd hass symb b b = (-1) ^ (Ring.ord A (b : A)).toNat := by
  refine normProd_eq_pow_of_forall hass symb hinj hquot b b (-1) fun q => ?_
  rw [(symb q).self, map_pow, units_map_norm_neg_one q, ← pow_mul]
  rfl

include hinj hquot in
/-- **Stacks 0EAN for the norm product.** -/
theorem normProd_unit_left (a b : nonZeroDivisors A) (u : Aˣ) (hu : (a : A) = u) :
    normProd hass symb a b =
      Units.map (residue A).toMonoidHom u ^ (Ring.ord A (b : A)).toNat := by
  refine normProd_eq_pow_of_forall hass symb hinj hquot a b _ fun q => ?_
  have hres : Units.map (residue (Localization.AtPrime q.asIdeal)).toMonoidHom
      (Units.map (algebraMap A (Localization.AtPrime q.asIdeal)).toMonoidHom u) =
      Units.map (algebraMap (ResidueField A)
        (ResidueField (Localization.AtPrime q.asIdeal))).toMonoidHom
        (Units.map (residue A).toMonoidHom u) := Units.ext (by simp)
  rw [(symb q).unit_left _ _ (Units.map (algebraMap A (Localization.AtPrime q.asIdeal)).toMonoidHom
    u) (by simp [hu]), map_pow, hres,
    units_map_norm_algebraMap_residueField q (Units.map (residue A).toMonoidHom u), ← pow_mul]
  rfl

/-- **Stacks 0EAT.** For a one-dimensional Noetherian local ring `A` and a finite ring extension
`A ⊆ B` with `B / A` annihilated by a power of `𝔪` and `𝔪` not an associated prime of `B`, the
product over the maximal ideals `𝔮` of `B` of the residue-field norms of a family of tame symbols
`∂_{B_𝔮}` is a tame symbol on `A`:

`∂_A(a, b) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(∂_{B_𝔮}(a, b))`.

Bimultiplicativity (Stacks 0EAL) and the Steinberg relation (Stacks 0EAP) are inherited factor by
factor; the diagonal condition (Stacks 0EAM) and the unit condition (Stacks 0EAN) hold because
`length_A(A/bA) = ∑_𝔮 [κ(𝔮) : κ(𝔪)] length_{B_𝔮}(B_𝔮/bB_𝔮)`. -/
noncomputable def normPushforward : RegularTameSymbol A where
  toFun := normProd hass symb
  map_mul_left := normProd_mul_left hass symb
  map_mul_right := normProd_mul_right hass symb
  self := normProd_self hass symb hinj hquot
  unit_left := normProd_unit_left hass symb hinj hquot
  steinberg := normProd_steinberg hass symb

/-- The value of `normPushforward hass symb hinj hquot` at `(a, b)` is the product over the maximal
ideals `𝔮` of `B` of the residue-field norms of `symb 𝔮` at the images of `a` and `b` in `B_𝔮`. -/
@[simp]
theorem normPushforward_apply (a b : nonZeroDivisors A) :
    normPushforward hass symb hinj hquot a b =
      ∏ q : MaximalSpectrum B,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (symb q (toExtensionNonZeroDivisor hass q a)
            (toExtensionNonZeroDivisor hass q b)) := rfl

end Stacks.Chow

namespace Stacks.Chow

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]

/-- **Stacks 0EAT with every instance hypothesis discharged.** A finite algebra over a local
ring has finitely many maximal ideals and is local at each of them, by
`Stacks.Length.finite_maximalSpectrum` and
`Stacks.Length.isLocalHom_algebraMap_localization`. -/
noncomputable def normPushforwardOfModuleFinite
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (symb : ∀ q : MaximalSpectrum B, RegularTameSymbol (Localization.AtPrime q.asIdeal))
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B)) :
    RegularTameSymbol A :=
  letI := Stacks.Length.finite_maximalSpectrum (A := A) (B := B)
  letI := Fintype.ofFinite (MaximalSpectrum B)
  letI : ∀ q : MaximalSpectrum B,
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := fun q =>
    Stacks.Length.isLocalHom_algebraMap_localization q
  normPushforward hass symb hinj hquot

end Stacks.Chow

namespace Stacks.Chow

/-- **The maximal ideal of a one-dimensional Noetherian local domain is not an associated prime
of the ring itself.** The annihilator of a nonzero element of a domain is zero, and the maximal
ideal of a local ring is zero only for a field; so the hypotheses of Stacks 0EAT are satisfied by
the identity extension `A ⊆ A`. -/
theorem not_isAssociatedPrime_maximalIdeal_self {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsDomain A] (hA : ¬ IsField A) :
    ¬ IsAssociatedPrime (maximalIdeal A) A := by
  intro h
  obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp h
  by_cases hx0 : x = 0
  · subst hx0
    refine hprime.ne_top ?_
    rw [hx, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  · refine hA (isField_iff_maximalIdeal_eq.mpr ?_)
    rw [hx, eq_bot_iff]
    intro r hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at hr
    exact Ideal.mem_bot.mpr ((mul_eq_zero.mp hr).resolve_right hx0)

/-- **The maximal ideal of a one-dimensional Noetherian local domain that is not a field has
height one.** It contains a nonzero element, which is a nonzerodivisor. -/
theorem height_maximalIdeal_eq_one_of_not_isField {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A] [IsDomain A] (hA : ¬ IsField A) :
    (maximalIdeal A).height = 1 := by
  obtain ⟨a, ham, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := maximalIdeal A) fun h => hA (isField_iff_maximalIdeal_eq.mpr h)
  exact Stacks.Length.height_maximalIdeal_eq_one (mem_nonZeroDivisors_of_ne_zero ha0) ham

/-- **Non-vacuity of Stacks 0EAT.** A one-dimensional Noetherian normal local domain is a
discrete valuation ring, so each of its localizations at a maximal ideal carries the tame symbol
`Stacks.Chow.dvrRegularTameSymbol`; and the identity extension `A ⊆ A` satisfies the remaining
hypotheses — it is injective, its cokernel is zero, and `𝔪` is not an associated prime of a
domain. So the hypothesis class of `Stacks.Chow.normPushforwardOfModuleFinite` is inhabited, and
the construction returns a tame symbol on `A`. -/
noncomputable def normPushforwardSelf (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A] [IsDomain A] [IsIntegrallyClosed A]
    (hA : ¬ IsField A) : RegularTameSymbol A := by
  refine normPushforwardOfModuleFinite (B := A)
    (not_isAssociatedPrime_maximalIdeal_self hA) (fun q => ?_) (fun x y h => h) ⟨0, by simp⟩
  letI : IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) :=
    isDiscreteValuationRing_localization_of_height_eq_one q.asIdeal
      (by rw [eq_maximalIdeal q.isMaximal]
          exact height_maximalIdeal_eq_one_of_not_isField hA)
  exact dvrRegularTameSymbol (Classical.choose_spec
    (IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q.asIdeal)))

/-- **Non-vacuity of Stacks 0EAT at a discrete valuation ring**, where every hypothesis is an
instance: a discrete valuation ring is a Noetherian local domain of Krull dimension at most one,
is integrally closed, and is not a field. -/
noncomputable def normPushforwardSelfDvr (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] : RegularTameSymbol A :=
  normPushforwardSelf A (IsDiscreteValuationRing.not_isField A)

end Stacks.Chow

end
