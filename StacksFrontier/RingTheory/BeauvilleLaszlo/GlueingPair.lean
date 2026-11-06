module

public import StacksFrontier.RingTheory.AdicCompletion.PrincipalFiltration
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion.ScalarExtension
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.ShortExact
public import StacksFrontier.RingTheory.BeauvilleLaszlo.Covering

@[expose] public section

/-!
# Glueing pairs

Let `R` be a commutative ring, let `f : R`, and let `R → R'` be a ring map inducing
isomorphisms `R/fⁿR → R'/fⁿR'` for every `n > 0`. Associated with this data is the sequence
of `R`-modules
`0 → R → R' ⊕ R_f → R'_f → 0`,
whose right-hand map is the difference of the two canonical localization maps. When this
sequence is exact one calls `(R → R', f)` a *glueing pair*; `(R, f)` is a glueing pair when
`(R → R^∧, f)` is one, for `R^∧` the `(f)`-adic completion.

## Main definitions

* `beauvilleLaszloSequence` (Stacks 0F1Q): the sequence `0 → R → R' ⊕ R_f → R'_f → 0`,
  as a `ShortComplex` of additive groups.
* `adicCompletionBeauvilleLaszloSequence` (Stacks 0BNQ): its specialization
  `0 → R → R^∧ ⊕ R_f → (R^∧)_f → 0` to the `(f)`-adic completion.
* `powerTorsion`, `modulePowerTorsion`: the `f`-power torsion `R[f^∞]` and `M[f^∞]`.
* `quotientPowMap`, `powerTorsionMap`: the maps `R/fⁿR → R'/fⁿR'` and `R[f^∞] → R'[f^∞]`
  induced by `R → R'`.

## Main results

* `beauvilleLaszloSequence_exactness_iff_powerTorsionMap` (Stacks 0BNR): the sequence is
  always exact on the right; it is exact on the left, resp. in the middle, exactly when
  `R[f^∞] → R'[f^∞]` is injective, resp. surjective. Hence `(R → R', f)` is a glueing pair
  if and only if `R[f^∞] → R'[f^∞]` is bijective.
* `adicCompletion_isRegular_and_isGlueingPair` (Stacks 0BNS): a nonzerodivisor `f` stays a
  nonzerodivisor in `R^∧`, so `(R, f)` is a glueing pair.
* `adicCompletion_isGlueingPair_of_flat` (Stacks 0BNT): if `R → R^∧` is flat — in particular
  if `R` is Noetherian — then `R[fⁿ] → R^∧[fⁿ]` is an isomorphism and `(R, f)` is a glueing
  pair.
* `adicCompletion_torsionMap_not_bijective_examples` (Stacks 0BNU): two rings
  `k[f, T₁, T₂, …]/(fT₁, fT₂ - T₁, …)` and `k[f, T₁, T₂, …]/(fT₁, f²T₂, …)` for which
  `R[f^∞] → R^∧[f^∞]` fails to be injective, resp. surjective; so `(R, f)` need not be a
  glueing pair.
* `exists_nonflat_adicCompletion_prod_localizationAway` (Stacks 0BNP): consequently
  `R → R^∧ ⊕ R_f` is not in general flat, so faithfully flat descent is unavailable and the
  Beauville--Laszlo theorem is not a special case of it.

## Implementation notes

The four-term sequence, including the zero objects at its ends, is represented by Mathlib's
`ShortComplex AddCommGrpCat`; its objects are universe-lifted so that `R` and `R'` may live in
independent universes. Exactness of the sequence is therefore `ShortComplex.ShortExact`, and
the elementwise criteria of Stacks 0BNR are transported across the lift. The standing
hypothesis on `R → R'` is carried as bijectivity of `quotientPowMap f n φ` for all `n > 0`
rather than as an abstract isomorphism, which is what makes the completion case a direct
instance via `quotient_pow_equiv_adicCompletion`.

`powerTorsion` is the `M = R` case of `modulePowerTorsion`, so there is a single provider of
the notion of `f`-power torsion; both are `abbrev`s for `Submodule.torsion'` over
`Submonoid.powers f`.

The counterexamples of Stacks 0BNU are presented over `MvPolynomial (Option ℕ) k`, with the
distinguished variable `X none` playing the role of `f`; the required nonvanishing is detected
by explicit test homomorphisms into a shift module over `Polynomial k` and into truncated
polynomial rings.

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0F1Q](https://stacks.math.columbia.edu/tag/0F1Q)
* [Stacks Project, Tag 0BNQ](https://stacks.math.columbia.edu/tag/0BNQ)
* [Stacks Project, Tag 0BNR](https://stacks.math.columbia.edu/tag/0BNR)
* [Stacks Project, Tag 0BNS](https://stacks.math.columbia.edu/tag/0BNS)
* [Stacks Project, Tag 0BNT](https://stacks.math.columbia.edu/tag/0BNT)
* [Stacks Project, Tag 0BNU](https://stacks.math.columbia.edu/tag/0BNU)
* [Stacks Project, Tag 0BNP](https://stacks.math.columbia.edu/tag/0BNP)
-/

namespace BeauvilleLaszlo
section

open CategoryTheory


universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The diagonal map `R → S ⊕ Rₑ` in the Beauville--Laszlo gluing sequence. -/
public def toBaseChangeAndAway (f : R) (φ : R →+* S) :
    R →+ S × Localization.Away f where
  toFun r := (φ r, algebraMap R (Localization.Away f) r)
  map_zero' := by simp
  map_add' _ _ := by simp

/-- The map `toBaseChangeAndAway f φ` sends `r` to `(φ r, r / 1)`. -/
@[simp]
public theorem toBaseChangeAndAway_apply (f : R) (φ : R →+* S) (r : R) :
    toBaseChangeAndAway f φ r = (φ r, algebraMap R (Localization.Away f) r) := rfl

/-- The difference of the two canonical maps `S ⊕ Rₑ → Sₓ`, where
`Sₓ = S[(φ f)⁻¹]`. -/
public noncomputable def awayDifference (f : R) (φ : R →+* S) :
    S × Localization.Away f →+ Localization.Away (φ f) where
  toFun x := algebraMap S (Localization.Away (φ f)) x.1 - Localization.awayMap φ f x.2
  map_zero' := by simp
  map_add' x y := by
    change algebraMap S (Localization.Away (φ f)) (x.1 + y.1) -
        Localization.awayMap φ f (x.2 + y.2) = _
    rw [map_add, map_add]
    abel

/-- The map `awayDifference f φ` sends `(s, a)` to the difference of the images of `s` and `a`
in `Sₓ`. -/
@[simp]
public theorem awayDifference_apply (f : R) (φ : R →+* S)
    (x : S × Localization.Away f) :
    awayDifference f φ x =
      algebraMap S (Localization.Away (φ f)) x.1 - Localization.awayMap φ f x.2 := rfl

/-- The canonical sequence
`0 → R → S ⊕ Rₑ → Sₓ → 0`, whose right-hand map is the difference of the
two canonical localization maps. -/
@[stacks 0F1Q]
public noncomputable def beauvilleLaszloSequence (f : R) (φ : R →+* S) :
    ShortComplex AddCommGrpCat.{max u v} :=
  let d : AddCommGrpCat.of (ULift.{max u v} R) ⟶
      AddCommGrpCat.of (ULift.{max u v} (S × Localization.Away f)) :=
    AddCommGrpCat.ofHom <|
      AddEquiv.ulift.symm.toAddMonoidHom.comp <|
        (toBaseChangeAndAway f φ).comp AddEquiv.ulift.toAddMonoidHom
  let e : AddCommGrpCat.of (ULift.{max u v} (S × Localization.Away f)) ⟶
      AddCommGrpCat.of (ULift.{max u v} (Localization.Away (φ f))) :=
    AddCommGrpCat.ofHom <|
      AddEquiv.ulift.symm.toAddMonoidHom.comp <|
        (awayDifference f φ).comp AddEquiv.ulift.toAddMonoidHom
  ShortComplex.mk d e
    (by
      ext r
      rcases r with ⟨r⟩
      simp [d, e, toBaseChangeAndAway, awayDifference, Localization.awayMap,
        IsLocalization.Away.map, IsLocalization.map_eq])

end

section

open CategoryTheory


universe u

/-- The canonical sequence `0 → R → R̂ ⊕ Rₑ → R̂ₑ → 0`, where `R̂` is the
completion of `R` along the principal ideal generated by `f`. -/
@[stacks 0BNQ]
public noncomputable abbrev adicCompletionBeauvilleLaszloSequence
    (R : Type u) [CommRing R] (f : R) : ShortComplex AddCommGrpCat.{u} :=
  beauvilleLaszloSequence f
    (algebraMap R (AdicCompletion (Ideal.span {f}) R))

end

section

open CategoryTheory


universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The submodule `M[f^∞]` of a module `M`, consisting of the elements annihilated by some
power of `f`. -/
public abbrev modulePowerTorsion {R : Type*} [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (f : R) : Submodule R M :=
  Submodule.torsion' R M (Submonoid.powers f)

/-- The submodule `R[f^∞]` consisting of elements annihilated by some power of `f`; the
case `M = R` of `modulePowerTorsion`. -/
public abbrev powerTorsion (f : R) : Submodule R R :=
  modulePowerTorsion R f

/-- The canonical map `R / f^n R → S / (φ f)^n S`. -/
public def quotientPowMap (f : R) (n : ℕ) (φ : R →+* S) :
    (R ⧸ (Ideal.span {f}) ^ n) →+* (S ⧸ (Ideal.span {φ f}) ^ n) :=
  Ideal.quotientMap ((Ideal.span {φ f}) ^ n) φ (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span]
    simp)

/-- The map `quotientPowMap f n φ` sends the class of `r` to the class of `φ r`. -/
@[simp]
public theorem quotientPowMap_mk (f : R) (n : ℕ) (φ : R →+* S) (r : R) :
    quotientPowMap f n φ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (φ r) := rfl

/-- A ring homomorphism restricts to the canonical additive map
`R[f^∞] → S[(φ f)^∞]`. -/
public def powerTorsionMap (f : R) (φ : R →+* S) :
    powerTorsion f →+ powerTorsion (φ f) where
  toFun x := ⟨φ x, by
    obtain ⟨⟨a, ⟨n, rfl⟩⟩, ha⟩ := x.property
    refine ⟨⟨φ (f ^ n), ⟨n, (map_pow φ f n).symm⟩⟩, ?_⟩
    change φ (f ^ n) * φ (x : R) = 0
    change (f ^ n) * (x : R) = 0 at ha
    rw [← map_mul, ha, map_zero]⟩
  map_zero' := Subtype.ext (φ.map_zero)
  map_add' x y := Subtype.ext (φ.map_add (x : R) (y : R))

/-- The map `powerTorsionMap f φ` acts as `φ` on underlying elements. -/
@[simp]
public theorem powerTorsionMap_apply (f : R) (φ : R →+* S) (x : powerTorsion f) :
    (powerTorsionMap f φ x : S) = φ x := by
  simp [powerTorsionMap]

end

section

open CategoryTheory

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

private theorem mem_powerTorsion_iff (f r : R) :
    r ∈ powerTorsion f ↔ algebraMap R (Localization.Away f) r = 0 :=
  (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) r).symm

private theorem awayMap_algebraMap (f : R) (φ : R →+* S) (r : R) :
    Localization.awayMap φ f (algebraMap R (Localization.Away f) r) =
      algebraMap S (Localization.Away (φ f)) (φ r) := by
  simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]

private theorem exists_sub_eq_pow_mul (f : R) (φ : R →+* S)
    (hφ : ∀ n : ℕ, 0 < n → Function.Surjective (quotientPowMap f n φ))
    (n : ℕ) (x : S) : ∃ r : R, ∃ s : S, x - φ r = (φ f) ^ n * s := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact ⟨0, x, by simp⟩
  obtain ⟨r, hr⟩ := hφ n hn (Ideal.Quotient.mk _ x)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hx : x - φ r ∈ (Ideal.span {φ f}) ^ n := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, ← quotientPowMap_mk, hr, sub_self]
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  exact ⟨r, hx⟩

private theorem pow_dvd_of_map_pow_dvd (f : R) (φ : R →+* S)
    (hφ : ∀ n : ℕ, 0 < n → Function.Injective (quotientPowMap f n φ))
    (n : ℕ) (r : R) (hr : (φ f) ^ n ∣ φ r) : f ^ n ∣ r := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hz : Ideal.Quotient.mk ((Ideal.span {φ f}) ^ n) (φ r) = 0 := by
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have : Ideal.Quotient.mk ((Ideal.span {f}) ^ n) r = 0 :=
    hφ n hn (by simpa using hz)
  simpa only [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] using this

private theorem toBaseChangeAndAway_injective_iff (f : R) (φ : R →+* S) :
    Function.Injective (toBaseChangeAndAway f φ) ↔
      Function.Injective (powerTorsionMap f φ) := by
  rw [injective_iff_map_eq_zero, injective_iff_map_eq_zero]
  constructor
  · intro h r hr
    apply Subtype.ext
    apply h r
    exact Prod.ext (congrArg Subtype.val hr)
      ((mem_powerTorsion_iff f r).mp r.property)
  · intro h r hr
    have ht : r ∈ powerTorsion f :=
      (mem_powerTorsion_iff f r).mpr (congrArg Prod.snd hr)
    exact congrArg Subtype.val (h ⟨r, ht⟩ (Subtype.ext (congrArg Prod.fst hr)))

private theorem awayDifference_surjective (f : R) (φ : R →+* S)
    (hφ : ∀ n : ℕ, 0 < n → Function.Surjective (quotientPowMap f n φ)) :
    Function.Surjective (awayDifference f φ) := by
  intro x
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (φ f) x
  obtain ⟨r, s, hs⟩ := exists_sub_eq_pow_mul f φ hφ n a
  let y := IsLocalization.mk' (Localization.Away f) r
    (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  have hy : y * algebraMap R (Localization.Away f) f ^ n =
      algebraMap R (Localization.Away f) r := by
    simpa only [map_pow] using IsLocalization.mk'_spec (Localization.Away f) r
      (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  have hy' := congrArg (Localization.awayMap φ f) hy
  simp only [map_mul, map_pow, awayMap_algebraMap] at hy'
  refine ⟨(s, -y), ?_⟩
  apply ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ f))
    (φ f)).pow n).mul_right_cancel
  simp only [awayDifference_apply, map_neg, sub_neg_eq_add, add_mul, hy', ha]
  have hs' := congrArg (algebraMap S (Localization.Away (φ f))) hs
  simp only [map_sub, map_mul, map_pow] at hs'
  linear_combination -hs'

private theorem awayDifference_exact_iff (f : R) (φ : R →+* S)
    (hφ : ∀ n : ℕ, 0 < n → Function.Injective (quotientPowMap f n φ)) :
    (∀ p, awayDifference f φ p = 0 → ∃ r, toBaseChangeAndAway f φ r = p) ↔
      Function.Surjective (powerTorsionMap f φ) := by
  constructor
  · intro h x
    obtain ⟨r, hr⟩ := h (x, 0) (by
      simp only [awayDifference_apply, map_zero, sub_zero]
      exact (mem_powerTorsion_iff (φ f) x).mp x.property)
    refine ⟨⟨r, (mem_powerTorsion_iff f r).mpr (congrArg Prod.snd hr)⟩, ?_⟩
    exact Subtype.ext (congrArg Prod.fst hr)
  · intro h p hp
    obtain ⟨x, y⟩ := p
    have lift (t : S) (ht : t ∈ powerTorsion (φ f)) :
        ∃ z : R, φ z = t ∧ algebraMap R (Localization.Away f) z = 0 := by
      obtain ⟨z, hz⟩ := h ⟨t, ht⟩
      exact ⟨z, congrArg Subtype.val hz, (mem_powerTorsion_iff f z).mp z.property⟩
    have hxy : algebraMap S (Localization.Away (φ f)) x =
        Localization.awayMap φ f y := sub_eq_zero.mp hp
    obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj f y
    have hr' := congrArg (Localization.awayMap φ f) hr
    simp only [map_mul, map_pow, awayMap_algebraMap] at hr'
    have ht : (φ f) ^ n * x - φ r ∈ powerTorsion (φ f) := by
      rw [mem_powerTorsion_iff, map_sub, map_mul, map_pow, hxy, mul_comm, hr',
        sub_self]
    obtain ⟨z, hzφ, hz0⟩ := lift _ ht
    have hrz : φ (r + z) = (φ f) ^ n * x := by
      rw [map_add, hzφ]
      ring
    obtain ⟨w, hw⟩ := pow_dvd_of_map_pow_dvd f φ hφ n (r + z) ⟨x, hrz⟩
    have hyw : y = algebraMap R (Localization.Away f) w := by
      apply ((IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away f) f).pow n).mul_right_cancel
      rw [hr, mul_comm, ← map_pow, ← map_mul, ← hw, map_add, hz0, add_zero]
    have ht' : x - φ w ∈ powerTorsion (φ f) := by
      rw [mem_powerTorsion_iff, map_sub, hxy, hyw, awayMap_algebraMap, sub_self]
    obtain ⟨z', hzφ', hz0'⟩ := lift _ ht'
    refine ⟨w + z', Prod.ext ?_ ?_⟩
    · show φ (w + z') = x
      rw [map_add, hzφ']
      ring
    · show algebraMap R (Localization.Away f) (w + z') = y
      rw [map_add, hz0', add_zero, hyw]

private theorem beauvilleLaszloSequence_epi_iff (f : R) (φ : R →+* S) :
    Epi (beauvilleLaszloSequence f φ).g ↔ Function.Surjective (awayDifference f φ) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  constructor
  · intro h x
    obtain ⟨r, hr⟩ := h (ULift.up x)
    exact ⟨r.down, congrArg ULift.down hr⟩
  · intro h x
    obtain ⟨r, hr⟩ := h x.down
    exact ⟨ULift.up r, congrArg ULift.up hr⟩

private theorem beauvilleLaszloSequence_mono_iff (f : R) (φ : R →+* S) :
    Mono (beauvilleLaszloSequence f φ).f ↔
      Function.Injective (toBaseChangeAndAway f φ) := by
  rw [AddCommGrpCat.mono_iff_injective]
  constructor
  · intro h x y hxy
    exact congrArg ULift.down (h (congrArg ULift.up hxy))
  · intro h x y hxy
    exact ULift.ext (h (congrArg ULift.down hxy))

private theorem beauvilleLaszloSequence_exact_iff (f : R) (φ : R →+* S) :
    (beauvilleLaszloSequence f φ).Exact ↔
      ∀ p, awayDifference f φ p = 0 → ∃ r, toBaseChangeAndAway f φ r = p := by
  rw [ShortComplex.ab_exact_iff]
  constructor
  · intro h p hp
    obtain ⟨r, hr⟩ := h (ULift.up p) (congrArg ULift.up hp)
    exact ⟨r.down, congrArg ULift.down hr⟩
  · intro h p hp
    obtain ⟨r, hr⟩ := h p.down (congrArg ULift.down hp)
    exact ⟨ULift.up r, congrArg ULift.up hr⟩

private theorem beauvilleLaszloSequence_exactness (f : R) (φ : R →+* S)
    (hφ : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n φ)) :
    Epi (beauvilleLaszloSequence f φ).g ∧
      (Mono (beauvilleLaszloSequence f φ).f ↔
        Function.Injective (powerTorsionMap f φ)) ∧
      ((beauvilleLaszloSequence f φ).Exact ↔
        Function.Surjective (powerTorsionMap f φ)) ∧
      ((beauvilleLaszloSequence f φ).ShortExact ↔
        Function.Bijective (powerTorsionMap f φ)) := by
  have he : Epi (beauvilleLaszloSequence f φ).g :=
    (beauvilleLaszloSequence_epi_iff f φ).mpr
      (awayDifference_surjective f φ fun n hn ↦ (hφ n hn).2)
  have hm := (beauvilleLaszloSequence_mono_iff f φ).trans
    (toBaseChangeAndAway_injective_iff f φ)
  have hx := (beauvilleLaszloSequence_exact_iff f φ).trans
    (awayDifference_exact_iff f φ fun n hn ↦ (hφ n hn).1)
  exact ⟨he, hm, hx, fun h ↦ ⟨hm.mp h.mono_f, hx.mp h.exact⟩,
    fun h ↦ ShortComplex.ShortExact.mk' (hx.mpr h.2) (hm.mpr h.1) he⟩

/-- `R → R^∧` is an isomorphism modulo every power of `f`. -/
private theorem quotientPowMap_adicCompletion_bijective_aux {R : Type*} [CommRing R]
    (f : R) (n : ℕ) : Function.Bijective
      (quotientPowMap f n
        (algebraMap R (AdicCompletion (Ideal.span {f}) R))) := by
  obtain ⟨e, he⟩ := quotient_pow_equiv_adicCompletion f n
  have hmap : quotientPowMap f n
      (algebraMap R (AdicCompletion (Ideal.span {f}) R)) = e.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    show quotientPowMap f n
      (algebraMap R (AdicCompletion (Ideal.span {f}) R))
        (Ideal.Quotient.mk _ r) = e (Ideal.Quotient.mk _ r)
    rw [quotientPowMap_mk, he]
  rw [hmap]
  exact e.bijective

/-- If `R → S` is an isomorphism modulo every positive power of `f`, the
Beauville--Laszlo sequence is always exact on the right; its left and middle
exactness are equivalent to injectivity and surjectivity on `f`-power torsion.
Consequently it is short exact precisely when that map is bijective. The same
criterion specializes to the `(f)`-adic completion of `R`. -/
@[stacks 0BNR]
public theorem beauvilleLaszloSequence_exactness_iff_powerTorsionMap
    (f : R) (φ : R →+* S)
    (hφ : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n φ)) :
    Epi (beauvilleLaszloSequence f φ).g ∧
      (Mono (beauvilleLaszloSequence f φ).f ↔
        Function.Injective (powerTorsionMap f φ)) ∧
      ((beauvilleLaszloSequence f φ).Exact ↔
        Function.Surjective (powerTorsionMap f φ)) ∧
      ((beauvilleLaszloSequence f φ).ShortExact ↔
        Function.Bijective (powerTorsionMap f φ)) ∧
      ((beauvilleLaszloSequence f
          (algebraMap R (AdicCompletion (Ideal.span {f}) R))).ShortExact ↔
        Function.Bijective (powerTorsionMap f
          (algebraMap R (AdicCompletion (Ideal.span {f}) R)))) := by
  obtain ⟨he, hm, hx, hs⟩ := beauvilleLaszloSequence_exactness f φ hφ
  refine ⟨he, hm, hx, hs, ?_⟩
  apply (beauvilleLaszloSequence_exactness f
    (algebraMap R (AdicCompletion (Ideal.span {f}) R)) ?_).2.2.2
  exact fun n _ ↦ quotientPowMap_adicCompletion_bijective_aux f n

end

section






open CategoryTheory

end

section



open CategoryTheory


/-- A nonzerodivisor of `R` stays a nonzerodivisor in the `(f)`-adic completion of `R`. -/
public theorem isSMulRegular_algebraMap_adicCompletion {R : Type*} [CommRing R]
    {I : Ideal R} {f : R} (hI : I = Ideal.span {f}) (hf : IsSMulRegular R f) :
    IsSMulRegular (AdicCompletion I R) (algebraMap R (AdicCompletion I R) f) := by
  refine IsSMulRegular.of_right_eq_zero_of_smul fun z hz ↦ ?_
  rw [smul_eq_mul] at hz
  ext n
  obtain ⟨a, ha⟩ :=
    Submodule.Quotient.mk_surjective (I ^ (n + 1) • ⊤ : Submodule R R) (z.val (n + 1))
  have hmk : (algebraMap R (AdicCompletion I R) f).val (n + 1) =
      Submodule.Quotient.mk (p := (I ^ (n + 1) • ⊤ : Submodule R R)) f := rfl
  have hdvd : a ∈ Ideal.span {f ^ n} := by
    have hzero : (algebraMap R (AdicCompletion I R) f * z).val (n + 1) = 0 := by
      rw [hz]
      rfl
    rw [AdicCompletion.val_mul, hmk, ← ha] at hzero
    rw [← Module.mul_mem_span_pow_succ_iff hf, ← Module.pow_smul_top_eq_span_pow hI,
      ← Submodule.Quotient.mk_eq_zero]
    simpa using hzero
  have hval : z.val n = Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) a := by
    rw [← z.2 (Nat.le_succ n), ← ha]
    exact Submodule.factor_mk _ _
  have ha0 : Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) a = 0 := by
    rwa [Submodule.Quotient.mk_eq_zero, Module.pow_smul_top_eq_span_pow hI]
  rw [hval, ha0]
  rfl

/-- If `f` acts injectively on `M`, then `M` has no nonzero `f`-power torsion. -/
public lemma powerTorsion_subsingleton {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {f : R}
    (hf : IsSMulRegular M f) : Subsingleton (modulePowerTorsion M f) := by
  have h0 (x : modulePowerTorsion M f) : (x : M) = 0 := by
    obtain ⟨⟨_, ⟨n, rfl⟩⟩, hx⟩ := x.property
    change f ^ n • (x : M) = 0 at hx
    exact hf.pow n (by simpa using hx)
  exact ⟨fun x y ↦ Subtype.ext ((h0 x).trans (h0 y).symm)⟩

/-- The canonical map `R / fⁿR → R^∧ / fⁿR^∧` to the `(f)`-adic completion is bijective. -/
public lemma quotientPowMap_adicCompletion_bijective {R : Type*} [CommRing R]
    (f : R) (n : ℕ) : Function.Bijective
      (quotientPowMap f n
        (algebraMap R (AdicCompletion (Ideal.span {f}) R))) := by
  exact quotientPowMap_adicCompletion_bijective_aux f n

/-- A nonzerodivisor `f` remains a nonzerodivisor in the `(f)`-adic completion, and the
canonical Beauville--Laszlo sequence is short exact; equivalently, `(R, f)` is a glueing pair. -/
@[stacks 0BNS]
public theorem adicCompletion_isRegular_and_isGlueingPair {R : Type*} [CommRing R] (f : R) (hf :
  IsRegular f) :
    IsRegular (algebraMap R (AdicCompletion (Ideal.span {f}) R) f) ∧
      (beauvilleLaszloSequence f
        (algebraMap R (AdicCompletion (Ideal.span {f}) R))).ShortExact := by
  let Rhat := AdicCompletion (Ideal.span {f}) R
  have hregHat : IsSMulRegular Rhat (algebraMap R Rhat f) :=
    isSMulRegular_algebraMap_adicCompletion rfl hf.left
  refine ⟨(Commute.isRegular_iff (Commute.all _)).2 hregHat, ?_⟩
  have hquot : ∀ n : ℕ, 0 < n → Function.Bijective
      (quotientPowMap f n (algebraMap R Rhat)) :=
    fun n _ ↦ quotientPowMap_adicCompletion_bijective f n
  rw [(beauvilleLaszloSequence_exactness_iff_powerTorsionMap f
    (algebraMap R Rhat) hquot).2.2.2.1]
  have hs := powerTorsion_subsingleton (M := R) (f := f) hf.left
  have ht := powerTorsion_subsingleton (M := Rhat) hregHat
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩

end

section

open scoped TensorProduct

end

section

open scoped TensorProduct
open CategoryTheory

universe u

/-- If the `(f)`-adic completion of `R` is flat over `R`, then tensoring the exact sequence
given by multiplication by `f ^ n` remains exact for every positive `n`, the canonical map on
`f ^ n`-torsion is an isomorphism, and `(R, f)` is a glueing pair. These conclusions hold in
particular when `R` is Noetherian. -/
@[stacks 0BNT]
public theorem adicCompletion_isGlueingPair_of_flat {R : Type u} [CommRing R] (f : R) :
    let P : Prop :=
      (∀ n : ℕ, 0 < n →
        let T := Submodule.torsionBy R R (f ^ n)
        let a : T ⊗[R] AdicCompletion (Ideal.span {f}) R →ₗ[R]
            AdicCompletion (Ideal.span {f}) R :=
          (TensorProduct.lid R (AdicCompletion (Ideal.span {f}) R)).toLinearMap.comp
            (TensorProduct.map T.subtype
              (LinearMap.id (R := R) (M := AdicCompletion (Ideal.span {f}) R)))
        let b : AdicCompletion (Ideal.span {f}) R →ₗ[R]
            AdicCompletion (Ideal.span {f}) R :=
          (LinearMap.lsmul R (AdicCompletion (Ideal.span {f}) R)) (f ^ n)
        Function.Injective a ∧ Function.Exact a b ∧
          Function.Injective
            (fun x : T => algebraMap R (AdicCompletion (Ideal.span {f}) R) x.1) ∧
          Set.range (fun x : T => algebraMap R (AdicCompletion (Ideal.span {f}) R) x.1) =
            (Submodule.torsionBy (AdicCompletion (Ideal.span {f}) R)
              (AdicCompletion (Ideal.span {f}) R)
              ((algebraMap R (AdicCompletion (Ideal.span {f}) R) f) ^ n) :
                Set (AdicCompletion (Ideal.span {f}) R))) ∧
      Function.Injective (fun r : R =>
        (algebraMap R (AdicCompletion (Ideal.span {f}) R) r,
          algebraMap R (Localization.Away f) r)) ∧
      Function.Exact
        (fun r : R => (algebraMap R (AdicCompletion (Ideal.span {f}) R) r,
          algebraMap R (Localization.Away f) r))
        (fun x : AdicCompletion (Ideal.span {f}) R × Localization.Away f =>
          algebraMap (AdicCompletion (Ideal.span {f}) R)
              (Localization.Away
                (algebraMap R (AdicCompletion (Ideal.span {f}) R) f)) x.1 -
            Localization.awayMap
              (algebraMap R (AdicCompletion (Ideal.span {f}) R)) f x.2) ∧
      Function.Surjective
        (fun x : AdicCompletion (Ideal.span {f}) R × Localization.Away f =>
          algebraMap (AdicCompletion (Ideal.span {f}) R)
              (Localization.Away
                (algebraMap R (AdicCompletion (Ideal.span {f}) R) f)) x.1 -
            Localization.awayMap
              (algebraMap R (AdicCompletion (Ideal.span {f}) R)) f x.2)
    (Module.Flat R (AdicCompletion (Ideal.span {f}) R) → P) ∧
      (∀ [IsNoetherianRing R], P) := by
  let S := AdicCompletion (Ideal.span {f}) R
  let φ : R →+* S := algebraMap R S
  have core (hflat : Module.Flat R S) :
      (∀ n : ℕ, 0 < n →
        let T := Submodule.torsionBy R R (f ^ n)
        let a : T ⊗[R] S →ₗ[R] S :=
          (TensorProduct.lid R S).toLinearMap.comp
            (TensorProduct.map T.subtype (LinearMap.id (R := R) (M := S)))
        let b : S →ₗ[R] S := (LinearMap.lsmul R S) (f ^ n)
        Function.Injective a ∧ Function.Exact a b ∧
          Function.Injective (fun x : T => φ x.1) ∧
          Set.range (fun x : T => φ x.1) =
            (Submodule.torsionBy S S ((φ f) ^ n) : Set S)) ∧
      Function.Injective (fun r : R => (φ r, algebraMap R (Localization.Away f) r)) ∧
      Function.Exact
        (fun r : R => (φ r, algebraMap R (Localization.Away f) r))
        (fun x : S × Localization.Away f =>
          algebraMap S (Localization.Away (φ f)) x.1 - Localization.awayMap φ f x.2) ∧
      Function.Surjective
        (fun x : S × Localization.Away f =>
          algebraMap S (Localization.Away (φ f)) x.1 - Localization.awayMap φ f x.2) := by
    let : Module.Flat R S := hflat
    have fixed : ∀ n : ℕ, 0 < n →
        let T := Submodule.torsionBy R R (f ^ n)
        let a : T ⊗[R] S →ₗ[R] S :=
          (TensorProduct.lid R S).toLinearMap.comp
            (TensorProduct.map T.subtype (LinearMap.id (R := R) (M := S)))
        let b : S →ₗ[R] S := (LinearMap.lsmul R S) (f ^ n)
        Function.Injective a ∧ Function.Exact a b ∧
          Function.Injective (fun x : T => φ x.1) ∧
          Set.range (fun x : T => φ x.1) =
            (Submodule.torsionBy S S ((φ f) ^ n) : Set S) := by
      intro n hn
      let g : R →ₗ[R] R := (LinearMap.lsmul R R) (f ^ n)
      let T := Submodule.torsionBy R R (f ^ n)
      let a : T ⊗[R] S →ₗ[R] S :=
        (TensorProduct.lid R S).toLinearMap.comp
          (TensorProduct.map T.subtype (LinearMap.id (R := R) (M := S)))
      let b : S →ₗ[R] S := (LinearMap.lsmul R S) (f ^ n)
      have hT : T = LinearMap.ker g := rfl
      have hxT (x : T) : f ^ n * x.1 = 0 := by
        simpa [smul_eq_mul] using Submodule.smul_coe_torsionBy (f ^ n) x
      have hainj : Function.Injective a := by
        have h := Module.Flat.rTensor_preserves_injective_linearMap (M := S) T.subtype
          Subtype.val_injective
        apply (TensorProduct.lid R S).injective.comp
        intro x y hxy
        apply h
        have heq : TensorProduct.map T.subtype (LinearMap.id (R := R) (M := S)) =
            T.subtype.rTensor S := by
          ext
          simp
        simpa [a, heq] using hxy
      have hex0 : Function.Exact (T.subtype.rTensor S) (g.rTensor S) := by
        apply Module.Flat.rTensor_exact S
        rw [hT]
        exact LinearMap.exact_subtype_ker_map g
      have hcommA : ∀ z, a z = TensorProduct.lid R S ((T.subtype.rTensor S) z) := by
        intro z
        rfl
      have hcommB : ∀ z, b (TensorProduct.lid R S z) =
          TensorProduct.lid R S ((g.rTensor S) z) := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => simp [b, g, smul_smul, mul_comm]
        | add x y hx hy => simp [hx, hy]
      have hex : Function.Exact a b := by
        intro x
        constructor
        · intro hx
          let y := (TensorProduct.lid R S).symm x
          have hy : (g.rTensor S) y = 0 := by
            apply (TensorProduct.lid R S).injective
            rw [← hcommB]
            simpa [y] using hx
          obtain ⟨z, hz⟩ := hex0 y |>.mp hy
          refine ⟨z, ?_⟩
          rw [hcommA, hz]
          simp [y]
        · rintro ⟨z, rfl⟩
          rw [hcommA, hcommB]
          have hz := congrFun hex0.comp_eq_zero z
          simpa using congrArg (TensorProduct.lid R S) hz
      have hM : ∀ x : T, ∃ k : ℕ, ∀ r ∈ (Ideal.span {f}) ^ k, r • x = 0 := by
        intro x
        refine ⟨n, ?_⟩
        intro r hr
        rw [Ideal.span_singleton_pow] at hr
        obtain ⟨c, rfl⟩ := (Ideal.mem_span_singleton).mp hr
        apply Subtype.ext
        show (f ^ n * c) * x.1 = 0
        rw [mul_comm (f ^ n) c, mul_assoc, hxT x, mul_zero]
      have hmk :=
        (_root_.tensorProduct_mk_bijective_of_ideal_power_torsion.{u, u, u}
          R (Ideal.span {f}) T hM).2 (Submodule.fg_span_singleton f)
      have hcanon : ∀ x : T,
          a (TensorProduct.mk R T S x 1) = φ x.1 := by
        intro x
        show x.1 • (1 : S) = algebraMap R S x.1
        simp [Algebra.smul_def]
      refine ⟨hainj, hex, ?_, ?_⟩
      · intro x y hxy
        apply hmk.1
        apply hainj
        rw [hcanon, hcanon]
        exact hxy
      · ext s
        constructor
        · rintro ⟨x, rfl⟩
          show φ x.1 ∈ Submodule.torsionBy S S ((φ f) ^ n)
          rw [Submodule.mem_torsionBy_iff]
          show (φ f) ^ n * φ x.1 = 0
          rw [← map_pow, ← map_mul]
          rw [hxT x, map_zero]
        · intro hs
          change s ∈ Submodule.torsionBy S S ((φ f) ^ n) at hs
          rw [Submodule.mem_torsionBy_iff] at hs
          have hbs : b s = 0 := by
            simpa [b, φ, Algebra.smul_def] using hs
          obtain ⟨z, hz⟩ := hex s |>.mp hbs
          obtain ⟨x, rfl⟩ := hmk.2 z
          exact ⟨x, by rw [← hz]; exact (hcanon x).symm⟩
    have hpower : Function.Bijective (powerTorsionMap f φ) := by
      constructor
      · intro x y hxy
        obtain ⟨⟨_, ⟨i, rfl⟩⟩, hxi⟩ := x.property
        obtain ⟨⟨_, ⟨j, rfl⟩⟩, hyj⟩ := y.property
        change f ^ i * x.1 = 0 at hxi
        change f ^ j * y.1 = 0 at hyj
        let n := i + j + 1
        let tx : Submodule.torsionBy R R (f ^ n) := ⟨x.1, by
          rw [Submodule.mem_torsionBy_iff]
          show f ^ n * x.1 = 0
          rw [show n = (j + 1) + i by omega, pow_add, mul_assoc, hxi, mul_zero]⟩
        let ty : Submodule.torsionBy R R (f ^ n) := ⟨y.1, by
          rw [Submodule.mem_torsionBy_iff]
          show f ^ n * y.1 = 0
          rw [show n = (i + 1) + j by omega, pow_add, mul_assoc, hyj, mul_zero]⟩
        have hn : 0 < n := by omega
        have hi := (fixed n hn).2.2.1
        apply Subtype.ext
        have ht : tx = ty := hi (by
          show φ tx.1 = φ ty.1
          exact congrArg Subtype.val hxy)
        exact congrArg (fun z => z.1) ht
      · intro y
        obtain ⟨⟨_, ⟨n, rfl⟩⟩, hyn⟩ := y.property
        change (φ f) ^ n * y.1 = 0 at hyn
        have hs : (y.1 : S) ∈ Submodule.torsionBy S S ((φ f) ^ (n + 1)) := by
          rw [Submodule.mem_torsionBy_iff]
          show (φ f) ^ (n + 1) * y.1 = 0
          rw [pow_succ, mul_assoc, mul_comm (φ f) y.1, ← mul_assoc, hyn, zero_mul]
        have hs' : y.1 ∈ Set.range (fun x : Submodule.torsionBy R R (f ^ (n + 1)) => φ x.1) := by
          rw [(fixed (n + 1) (by omega)).2.2.2]
          exact hs
        obtain ⟨x, hx⟩ := hs'
        refine ⟨⟨x.1, ?_⟩, Subtype.ext hx⟩
        refine ⟨⟨f ^ (n + 1), ⟨n + 1, rfl⟩⟩, ?_⟩
        show f ^ (n + 1) * x.1 = 0
        simpa [smul_eq_mul] using Submodule.smul_coe_torsionBy (f ^ (n + 1)) x
    have hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n φ) :=
      fun n _ ↦ quotientPowMap_adicCompletion_bijective_aux f n
    have hshort : (beauvilleLaszloSequence f φ).ShortExact :=
      ((beauvilleLaszloSequence_exactness_iff_powerTorsionMap f φ hquot).2.2.2.2).2
        hpower
    refine ⟨fixed, ?_, ?_, ?_⟩
    · exact (beauvilleLaszloSequence_mono_iff f φ).mp hshort.mono_f
    · intro x
      constructor
      · intro hx
        exact (beauvilleLaszloSequence_exact_iff f φ).mp hshort.exact x hx
      · rintro ⟨y, rfl⟩
        simp [φ, IsLocalization.Away.map, Localization.awayMap, IsLocalization.map_eq]
    · exact (beauvilleLaszloSequence_epi_iff f φ).mp hshort.epi_g
  refine ⟨?_, ?_⟩
  · intro h
    simpa [S, φ] using core h
  · intro _
    simpa [S, φ] using core (AdicCompletion.flat_of_isNoetherian (Ideal.span {f}))

end

section

open scoped BigOperators

end

section

open scoped BigOperators


variable (k : Type*) [Field k]

private def shift : (ℕ → k) →ₗ[k] (ℕ → k) where
  toFun v n := v (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[instance_reducible]
private noncomputable def polyModule : Module (Polynomial k) (ℕ → k) :=
  Module.compHom (ℕ → k)
    (Polynomial.aeval (R := k) (A := Module.End k (ℕ → k)) (shift k)).toRingHom

private noncomputable local instance : Module (Polynomial k) (ℕ → k) := polyModule k
private noncomputable local instance : Module (Polynomial k)ᵐᵒᵖ (ℕ → k) :=
  Module.compHom _ ((RingHom.id (Polynomial k)).fromOpposite mul_comm)
private local instance : IsCentralScalar (Polynomial k) (ℕ → k) :=
  ⟨fun _ _ ↦ rfl⟩

private lemma shift_single (n : ℕ) :
    shift k (Pi.single (n + 1) 1) = Pi.single n 1 := by
  ext i
  simp [shift, Pi.single_apply]

private lemma shift_single_zero : shift k (Pi.single 0 1) = 0 := by
  ext i
  simp [shift]

private noncomputable def testHom :
    MvPolynomial (Option ℕ) k →+*
      TrivSqZeroExt (Polynomial k) (ℕ → k) :=
  MvPolynomial.eval₂Hom
    ((TrivSqZeroExt.inlHom (Polynomial k) (ℕ → k)).comp Polynomial.C)
    fun
    | none => TrivSqZeroExt.inl Polynomial.X
    | some n => TrivSqZeroExt.inr (Pi.single n 1)

private lemma testHom_F_mul_T_zero :
    testHom k (MvPolynomial.X none * MvPolynomial.X (some 0)) = 0 := by
  apply TrivSqZeroExt.ext
  · simp [testHom]
  · simp only [testHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr,
      MulOpposite.op_zero, TrivSqZeroExt.snd_inl, smul_zero, add_zero, TrivSqZeroExt.snd_zero]
    show (Polynomial.aeval (shift k) Polynomial.X) (Pi.single 0 1) = 0
    simpa using shift_single_zero k

private lemma testHom_rel (n : ℕ) :
    testHom k (MvPolynomial.X none * MvPolynomial.X (some (n + 1)) -
      MvPolynomial.X (some n)) = 0 := by
  apply TrivSqZeroExt.ext
  · simp [testHom]
  · simp only [testHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr, MulOpposite.op_zero, TrivSqZeroExt.snd_inl,
      smul_zero, add_zero, TrivSqZeroExt.snd_zero]
    show (Polynomial.aeval (shift k) Polynomial.X) (Pi.single (n + 1) 1) - Pi.single n 1 = 0
    simp [shift_single]

private lemma testHom_T_zero_ne : testHom k (MvPolynomial.X (some 0)) ≠ 0 := by
  intro h
  have h' := congrArg (TrivSqZeroExt.snd (R := Polynomial k) (M := ℕ → k)) h
  simpa [testHom, Pi.single_apply] using congrFun h' 0

private lemma firstIdeal_le_ker :
    Ideal.span ({MvPolynomial.X none * MvPolynomial.X (some 0)} ∪
      Set.range (fun n : ℕ ↦ MvPolynomial.X none * MvPolynomial.X (some (n + 1)) -
        MvPolynomial.X (some n))) ≤ RingHom.ker (testHom k) := by
  apply Ideal.span_le.2
  rintro p (rfl | ⟨n, rfl⟩)
  exacts [testHom_F_mul_T_zero k, testHom_rel k n]

private lemma first_T_zero_ne :
    Ideal.Quotient.mk
      (Ideal.span ({MvPolynomial.X none * MvPolynomial.X (some 0)} ∪
        Set.range (fun n : ℕ ↦ MvPolynomial.X none * MvPolynomial.X (some (n + 1)) -
          MvPolynomial.X (some n))))
      (MvPolynomial.X (some 0) : MvPolynomial (Option ℕ) k) ≠ 0 := fun h ↦
  testHom_T_zero_ne k (firstIdeal_le_ker k (Ideal.Quotient.eq_zero_iff_mem.mp h))

private lemma first_relation (n : ℕ) :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let T : ℕ → P := fun i ↦ MvPolynomial.X (some i)
    let I := Ideal.span ({F * T 0} ∪ Set.range (fun i ↦ F * T (i + 1) - T i))
    let q : P →+* P ⧸ I := Ideal.Quotient.mk I
    q F * q (T (n + 1)) = q (T n) := by
  dsimp
  rw [← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_union_right _ ⟨n, rfl⟩)

private lemma first_annihilates :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let T : ℕ → P := fun i ↦ MvPolynomial.X (some i)
    let I := Ideal.span ({F * T 0} ∪ Set.range (fun i ↦ F * T (i + 1) - T i))
    let q : P →+* P ⧸ I := Ideal.Quotient.mk I
    q F * q (T 0) = 0 := by
  dsimp
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_union_left _ (Set.mem_singleton _))

private lemma first_power_relation (n : ℕ) :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let T : ℕ → P := fun i ↦ MvPolynomial.X (some i)
    let I := Ideal.span ({F * T 0} ∪ Set.range (fun i ↦ F * T (i + 1) - T i))
    let q : P →+* P ⧸ I := Ideal.Quotient.mk I
    q F ^ n * q (T n) = q (T 0) := by
  dsimp
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_assoc]
      have hr := first_relation k n
      dsimp at hr
      rw [hr, ih]

/-- An element divisible by every power of `f` has zero image in the `f`-adic completion. -/
theorem completion_zero_of_forall_pow_dvd {A : Type*} [CommRing A]
    (f x : A) (h : ∀ n : ℕ, f ^ n ∣ x) :
    AdicCompletion.of (Ideal.span {f}) A x = 0 := by
  apply AdicCompletion.ext
  intro n
  show ((AdicCompletion.of (Ideal.span {f}) A) x).1 n = 0
  rw [AdicCompletion.of_apply]
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simpa only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] using h n

private theorem first_completion_t0_zero :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let T : ℕ → P := fun i ↦ MvPolynomial.X (some i)
    let I := Ideal.span ({F * T 0} ∪ Set.range (fun i ↦ F * T (i + 1) - T i))
    let q : P →+* P ⧸ I := Ideal.Quotient.mk I
    let f := q F
    let t := fun i ↦ q (T i)
    AdicCompletion.of (Ideal.span {f}) (P ⧸ I) (t 0) = 0 := by
  dsimp
  exact completion_zero_of_forall_pow_dvd _ _ fun n ↦
    ⟨Ideal.Quotient.mk _ (MvPolynomial.X (some n)), (first_power_relation k n).symm⟩

private theorem mem_primaryComponent_of_smul_eq_zero {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (f : A) (x : M) (h : f • x = 0) :
    x ∈ Ideal.primaryComponent M (Ideal.span {f}) := by
  rw [Ideal.primaryComponent_mem]
  refine ⟨1, ?_⟩
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨r, hr⟩
  simp only [pow_one, SetLike.mem_coe, Ideal.mem_span_singleton] at hr
  obtain ⟨a, rfl⟩ := hr
  show (f * a) • x = 0
  rw [mul_comm f a, mul_smul, h, smul_zero]

private theorem first_t0_primary :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let T : ℕ → P := fun i ↦ MvPolynomial.X (some i)
    let I := Ideal.span ({F * T 0} ∪ Set.range (fun i ↦ F * T (i + 1) - T i))
    let q : P →+* P ⧸ I := Ideal.Quotient.mk I
    let f := q F
    let t := fun i ↦ q (T i)
    t 0 ∈ Ideal.primaryComponent (P ⧸ I) (Ideal.span {f}) := by
  dsimp
  exact mem_primaryComponent_of_smul_eq_zero _ _ (first_annihilates k)

private theorem second_relation (n : ℕ) :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let T : ℕ → P := fun i ↦ MvPolynomial.X (some i)
    let I := Ideal.span (Set.range (fun i ↦ F ^ (i + 1) * T i))
    let q : P →+* P ⧸ I := Ideal.Quotient.mk I
    q F ^ (n + 1) * q (T n) = 0 := by
  dsimp
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨n, rfl⟩

private noncomputable def torsionSeries {A : Type*} [CommRing A] (f : A) (t : ℕ → A) :
    AdicCompletion.AdicCauchySequence (Ideal.span {f}) A :=
  AdicCompletion.AdicCauchySequence.mk (Ideal.span {f}) A
    (fun n ↦ ∑ i ∈ Finset.range n, f ^ i * t i) (by
    intro n
    rw [SModEq.sub_mem, Finset.sum_range_succ]
    have hterm : f ^ n * t n ∈ (Ideal.span {f}) ^ n := by
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    simpa only [smul_eq_mul, Ideal.mul_top, sub_add_eq_sub_sub, sub_self, zero_sub,
      Ideal.neg_mem_iff] using hterm)

private lemma torsionSeries_eval {A : Type*} [CommRing A] (f : A) (t : ℕ → A)
    (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {f}) n
      (AdicCompletion.mk (Ideal.span {f}) A (torsionSeries f t)) =
      Ideal.Quotient.mk ((Ideal.span {f}) ^ n)
        (∑ i ∈ Finset.range n, f ^ i * t i) :=
  AdicCompletion.evalₐ_mk _ n _

private lemma torsionSeries_annihilated {A : Type*} [CommRing A]
    (f : A) (t : ℕ → A) (h : ∀ i, f ^ (i + 1) * t i = 0) :
    f • (AdicCompletion.mk (Ideal.span {f}) A (torsionSeries f t)) = 0 := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [Algebra.smul_def, map_mul, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of, torsionSeries_eval,
    ← map_mul]
  have hs : f * (∑ i ∈ Finset.range n, f ^ i * t i) = 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simpa only [pow_succ', mul_assoc] using h i
  simp [hs]

private abbrev truncPoly (n : ℕ) :=
  Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ (n + 1)}

private noncomputable def secondTestHom (n : ℕ) :
    MvPolynomial (Option ℕ) k →+* TrivSqZeroExt (truncPoly k n) (truncPoly k n) := by
  let q : Polynomial k →+* truncPoly k n := Ideal.Quotient.mk _
  exact MvPolynomial.eval₂Hom
    ((TrivSqZeroExt.inlHom (truncPoly k n) (truncPoly k n)).comp (q.comp Polynomial.C))
    (fun
      | none => TrivSqZeroExt.inl (q Polynomial.X)
      | some i => if i = n then TrivSqZeroExt.inr (1 : truncPoly k n) else 0)

private theorem truncPoly_X_pow_succ (n : ℕ) :
    (Ideal.Quotient.mk _ (Polynomial.X : Polynomial k) : truncPoly k n) ^ (n + 1) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

private theorem truncPoly_X_pow_ne (n : ℕ) :
    (Ideal.Quotient.mk _ (Polynomial.X : Polynomial k) : truncPoly k n) ^ n ≠ 0 := by
  intro h
  have hdvd : (Polynomial.X : Polynomial k) ^ (n + 1) ∣
      (Polynomial.X : Polynomial k) ^ n := by
    apply (Ideal.mem_span_singleton).mp
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simpa only [map_pow] using h
  have hcoeff := (Polynomial.X_pow_dvd_iff.mp hdvd) n (by omega)
  simp at hcoeff

private theorem secondTestHom_rel (n i : ℕ) :
    secondTestHom k n
      ((MvPolynomial.X none : MvPolynomial (Option ℕ) k) ^ (i + 1) *
        MvPolynomial.X (some i)) = 0 := by
  by_cases hi : i = n
  · subst i
    apply TrivSqZeroExt.ext
    · simp [secondTestHom]
    · simp [secondTestHom, truncPoly_X_pow_succ]
  · simp [secondTestHom, hi]

private theorem secondIdeal_le_ker (n : ℕ) :
    Ideal.span (Set.range (fun i : ℕ ↦
      (MvPolynomial.X none : MvPolynomial (Option ℕ) k) ^ (i + 1) *
        MvPolynomial.X (some i))) ≤ RingHom.ker (secondTestHom k n) := by
  apply Ideal.span_le.mpr
  rintro p ⟨i, rfl⟩
  exact secondTestHom_rel k n i

private noncomputable def secondQuotTestHom (n : ℕ) :
    (MvPolynomial (Option ℕ) k ⧸ Ideal.span (Set.range (fun i : ℕ ↦
      (MvPolynomial.X none : MvPolynomial (Option ℕ) k) ^ (i + 1) *
        MvPolynomial.X (some i)))) →+*
      TrivSqZeroExt (truncPoly k n) (truncPoly k n) :=
  Ideal.Quotient.lift _ (secondTestHom k n) (secondIdeal_le_ker k n)

private noncomputable def secondBaseHom (n : ℕ) :
    MvPolynomial (Option ℕ) k →+* truncPoly k n := by
  let q : Polynomial k →+* truncPoly k n := Ideal.Quotient.mk _
  exact MvPolynomial.eval₂Hom (q.comp Polynomial.C)
    (fun
      | none => q Polynomial.X
      | some _ => 0)

private theorem secondTestHom_snd_zero_of_not_var (n : ℕ)
    (p : MvPolynomial (Option ℕ) k) (hp : some n ∉ p.vars) :
    (secondTestHom k n p).snd = 0 := by
  have heq : secondTestHom k n p =
      TrivSqZeroExt.inl ((secondBaseHom k n) p) := by
    show secondTestHom k n p =
      ((TrivSqZeroExt.inlHom (truncPoly k n) (truncPoly k n)).comp
        (secondBaseHom k n)) p
    apply MvPolynomial.hom_congr_vars
    · apply RingHom.ext
      intro r
      show secondTestHom k n (MvPolynomial.C r) =
        TrivSqZeroExt.inl (secondBaseHom k n (MvPolynomial.C r))
      simp [secondTestHom, secondBaseHom]
    · intro i hi _
      cases i with
      | none => simp [secondTestHom, secondBaseHom]
      | some j =>
        have hj : j ≠ n := by
          rintro rfl
          exact hp hi
        simp [secondTestHom, secondBaseHom, hj]
    · rfl
  rw [heq, TrivSqZeroExt.snd_inl]

private theorem secondQuotTestHom_f (n : ℕ) :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let I := Ideal.span (Set.range (fun i ↦ F ^ (i + 1) * MvPolynomial.X (some i)))
    let q : P →+* P ⧸ I := Ideal.Quotient.mk I
    secondQuotTestHom k n (q F) =
      TrivSqZeroExt.inl (Ideal.Quotient.mk _ (Polynomial.X : Polynomial k)) := by
  dsimp
  simp [secondQuotTestHom, secondTestHom]

private theorem secondQuotTestHom_t (n i : ℕ) :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let I := Ideal.span (Set.range (fun j ↦ F ^ (j + 1) * MvPolynomial.X (some j)))
    let q : P →+* P ⧸ I := Ideal.Quotient.mk I
    secondQuotTestHom k n (q (MvPolynomial.X (some i))) =
      if i = n then TrivSqZeroExt.inr 1 else 0 := by
  dsimp
  simp [secondQuotTestHom, secondTestHom]

private theorem secondQuotTestHom_f_pow_succ (n : ℕ) :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let I := Ideal.span (Set.range (fun i ↦ F ^ (i + 1) * MvPolynomial.X (some i)))
    let q : P →+* P ⧸ I := Ideal.Quotient.mk I
    secondQuotTestHom k n (q F) ^ (n + 1) = 0 := by
  dsimp
  rw [secondQuotTestHom_f]
  simp only [TrivSqZeroExt.inl_pow, truncPoly_X_pow_succ, TrivSqZeroExt.inl_zero]

private theorem secondQuotTestHom_Jpow_le_ker (n : ℕ) :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let I := Ideal.span (Set.range (fun i ↦ F ^ (i + 1) * MvPolynomial.X (some i)))
    let R := P ⧸ I
    let f : R := Ideal.Quotient.mk I F
    (Ideal.span {f}) ^ (n + 1) ≤ RingHom.ker (secondQuotTestHom k n) := by
  dsimp
  rw [Ideal.span_singleton_pow]
  apply Ideal.span_le.mpr
  rintro a (rfl : a = _)
  show secondQuotTestHom k n
      ((Ideal.Quotient.mk _ (MvPolynomial.X none) :
        MvPolynomial (Option ℕ) k ⧸ _) ^ (n + 1)) = 0
  rw [map_pow]
  exact secondQuotTestHom_f_pow_succ k n

private noncomputable def secondResidueTestHom (n : ℕ) :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let I := Ideal.span (Set.range (fun i ↦ F ^ (i + 1) * MvPolynomial.X (some i)))
    let R := P ⧸ I
    let f : R := Ideal.Quotient.mk I F
    (R ⧸ (Ideal.span {f}) ^ (n + 1)) →+*
      TrivSqZeroExt (truncPoly k n) (truncPoly k n) := by
  dsimp
  exact Ideal.Quotient.lift _ (secondQuotTestHom k n)
    (secondQuotTestHom_Jpow_le_ker k n)

private theorem secondQuotTestHom_series_snd (n : ℕ) :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let T : ℕ → P := fun i ↦ MvPolynomial.X (some i)
    let I := Ideal.span (Set.range (fun i ↦ F ^ (i + 1) * T i))
    let q : P →+* P ⧸ I := Ideal.Quotient.mk I
    let f := q F
    let t := fun i ↦ q (T i)
    (secondQuotTestHom k n
      (∑ i ∈ Finset.range (n + 1), f ^ i * t i)).snd =
      (Ideal.Quotient.mk _ (Polynomial.X : Polynomial k) : truncPoly k n) ^ n := by
  dsimp
  rw [Finset.sum_range_succ, map_add]
  have hz : secondQuotTestHom k n
      (∑ i ∈ Finset.range n,
        (Ideal.Quotient.mk _ (MvPolynomial.X none : MvPolynomial (Option ℕ) k) :
          MvPolynomial (Option ℕ) k ⧸ Ideal.span (Set.range (fun j : ℕ ↦
            (MvPolynomial.X none : MvPolynomial (Option ℕ) k) ^ (j + 1) *
              MvPolynomial.X (some j)))) ^ i *
          Ideal.Quotient.mk _ (MvPolynomial.X (some i) : MvPolynomial (Option ℕ) k)) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_mul, secondQuotTestHom_t k n i, if_neg (Nat.ne_of_lt (Finset.mem_range.mp hi))]
    simp
  rw [hz, zero_add, map_mul, map_pow, secondQuotTestHom_f,
    secondQuotTestHom_t k n n, if_pos rfl]
  simp

private theorem second_series_not_range :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let T : ℕ → P := fun i ↦ MvPolynomial.X (some i)
    let I := Ideal.span (Set.range (fun i ↦ F ^ (i + 1) * T i))
    let R := P ⧸ I
    let f : R := Ideal.Quotient.mk I F
    let t : ℕ → R := fun i ↦ Ideal.Quotient.mk I (T i)
    let J := Ideal.span {f}
    let c := AdicCompletion.of J R
    ∀ x : Ideal.primaryComponent (AdicCompletion J R) J,
      (∀ n : ℕ, AdicCompletion.evalₐ J n x.1 =
        Ideal.Quotient.mk (J ^ n) (∑ i ∈ Finset.range n, f ^ i * t i)) →
      x ∉ Set.range (Ideal.primaryComponent.map J c) := by
  dsimp
  intro x hx hmem
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective y.1
  obtain ⟨n, hn⟩ := Finset.exists_notMem (p.vars.image (fun o ↦ o.getD 0))
  have hnvar : some n ∉ p.vars := fun hm ↦ hn (Finset.mem_image.mpr ⟨some n, hm, rfl⟩)
  have hxy : x.1 = (AdicCompletion.of
      (Ideal.span {(Ideal.Quotient.mk _ (MvPolynomial.X none) :
        MvPolynomial (Option ℕ) k ⧸ _)}) _ ) y.1 :=
    congrArg Subtype.val hy.symm
  have hq := hx (n + 1)
  rw [hxy, AdicCompletion.evalₐ_of, ← hp] at hq
  have ht := congrArg (secondResidueTestHom k n) hq
  have hr := secondQuotTestHom_series_snd k n
  dsimp at hr
  simp only [secondResidueTestHom, secondQuotTestHom, Ideal.Quotient.lift_mk,
    id_eq] at ht
  have heq :
      (secondTestHom k n p).snd =
      (Ideal.Quotient.mk _ (Polynomial.X : Polynomial k) : truncPoly k n) ^ n :=
    (congrArg TrivSqZeroExt.snd ht).trans hr
  exact truncPoly_X_pow_ne k n (secondTestHom_snd_zero_of_not_var k n p hnvar ▸ heq.symm)

private theorem flat_completion_injective_on_annihilator {R : Type*} [CommRing R]
    (f x : R) (hflat : Module.Flat R (AdicCompletion (Ideal.span {f}) R))
    (hfx : f * x = 0) (hcx : AdicCompletion.of (Ideal.span {f}) R x = 0) : x = 0 := by
  have h := ((adicCompletion_isGlueingPair_of_flat f).1 hflat).1 1 (by omega)
  dsimp at h
  have hxmem : x ∈ Submodule.torsionBy R R (f ^ 1) := by
    rw [Submodule.mem_torsionBy_iff]
    simpa only [pow_one, smul_eq_mul] using hfx
  have hzero : (⟨x, hxmem⟩ : Submodule.torsionBy R R (f ^ 1)) = 0 := by
    apply h.2.2.1
    simpa [AdicCompletion.algebraMap_apply] using hcx
  exact congrArg Subtype.val hzero

private theorem flat_completion_covers_annihilator {R : Type*} [CommRing R]
    (f : R) (hflat : Module.Flat R (AdicCompletion (Ideal.span {f}) R))
    (x : AdicCompletion (Ideal.span {f}) R) (hx : f • x = 0) :
    ∃ y : Ideal.primaryComponent R (Ideal.span {f}),
      (Ideal.primaryComponent.map (Ideal.span {f})
        (AdicCompletion.of (Ideal.span {f}) R) y).1 = x := by
  have h := ((adicCompletion_isGlueingPair_of_flat f).1 hflat).1 1 (by omega)
  dsimp at h
  have hxmem : x ∈ Submodule.torsionBy
      (AdicCompletion (Ideal.span {f}) R) (AdicCompletion (Ideal.span {f}) R)
      ((algebraMap R (AdicCompletion (Ideal.span {f}) R) f) ^ 1) := by
    rw [Submodule.mem_torsionBy_iff]
    simpa only [pow_one, smul_eq_mul, Algebra.smul_def] using hx
  have hxrange : x ∈ Set.range (fun y : Submodule.torsionBy R R (f ^ 1) =>
      algebraMap R (AdicCompletion (Ideal.span {f}) R) y.1) := by
    rwa [h.2.2.2]
  obtain ⟨y, hy⟩ := hxrange
  have hyf : f * y.1 = 0 := by
    simpa only [pow_one, smul_eq_mul] using Submodule.smul_coe_torsionBy (f ^ 1) y
  refine ⟨⟨y.1, mem_primaryComponent_of_smul_eq_zero f y.1 hyf⟩, ?_⟩
  show AdicCompletion.of (Ideal.span {f}) R y.1 = x
  simpa [AdicCompletion.algebraMap_apply] using hy

private theorem second_series_witness :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let T : ℕ → P := fun i ↦ MvPolynomial.X (some i)
    let I := Ideal.span (Set.range (fun i ↦ F ^ (i + 1) * T i))
    let R := P ⧸ I
    let f : R := Ideal.Quotient.mk I F
    let t : ℕ → R := fun i ↦ Ideal.Quotient.mk I (T i)
    let J := Ideal.span {f}
    ∃ x : Ideal.primaryComponent (AdicCompletion J R) J,
      (∀ n : ℕ, AdicCompletion.evalₐ J n x.1 =
        Ideal.Quotient.mk (J ^ n) (∑ i ∈ Finset.range n, f ^ i * t i)) ∧
      f • x.1 = 0 ∧
      x ∉ Set.range (Ideal.primaryComponent.map J (AdicCompletion.of J R)) := by
  dsimp
  let I : Ideal (MvPolynomial (Option ℕ) k) := Ideal.span (Set.range (fun i : ℕ ↦
    (MvPolynomial.X none : MvPolynomial (Option ℕ) k) ^ (i + 1) * MvPolynomial.X (some i)))
  let R := MvPolynomial (Option ℕ) k ⧸ I
  let f : R := Ideal.Quotient.mk I (MvPolynomial.X none)
  let t : ℕ → R := fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X (some i))
  let J := Ideal.span {f}
  let z : AdicCompletion J R := AdicCompletion.mk J R (torsionSeries f t)
  have hz : f • z = 0 := torsionSeries_annihilated f t fun i ↦ second_relation k i
  have hmem : z ∈ Ideal.primaryComponent (AdicCompletion J R) J :=
    mem_primaryComponent_of_smul_eq_zero f z hz
  exact ⟨⟨z, hmem⟩, torsionSeries_eval f t, hz,
    second_series_not_range k ⟨z, hmem⟩ (torsionSeries_eval f t)⟩


/-- Two quotients of `k[f, T₁, T₂, …]` for which the canonical map on `f`-power torsion
to the adic completion is respectively noninjective and nonsurjective. In the first example
`T₁` is a nonzero kernel element whose image is divisible by every power of `f`. In the second,
the compatible residues of `T₁ + f T₂ + f² T₃ + ⋯` define an `f`-torsion element outside
the image. The two completion maps are not flat. -/
@[stacks 0BNU]
public theorem adicCompletion_torsionMap_not_bijective_examples (k : Type*) [Field k] :
    let P := MvPolynomial (Option ℕ) k
    let F : P := MvPolynomial.X none
    let T : ℕ → P := fun n ↦ MvPolynomial.X (some n)
    let I₁ : Ideal P := Ideal.span ({F * T 0} ∪ Set.range (fun n ↦ F * T (n + 1) - T n))
    let R₁ := P ⧸ I₁
    let f₁ : R₁ := Ideal.Quotient.mk I₁ F
    let t₁ : ℕ → R₁ := fun n ↦ Ideal.Quotient.mk I₁ (T n)
    let J₁ : Ideal R₁ := Ideal.span {f₁}
    let c₁ := AdicCompletion.of J₁ R₁
    let I₂ : Ideal P := Ideal.span (Set.range (fun n ↦ F ^ (n + 1) * T n))
    let R₂ := P ⧸ I₂
    let f₂ : R₂ := Ideal.Quotient.mk I₂ F
    let t₂ : ℕ → R₂ := fun n ↦ Ideal.Quotient.mk I₂ (T n)
    let J₂ : Ideal R₂ := Ideal.span {f₂}
    let c₂ := AdicCompletion.of J₂ R₂
    t₁ 0 ≠ 0 ∧ t₁ 0 ∈ Ideal.primaryComponent R₁ J₁ ∧ c₁ (t₁ 0) = 0 ∧
    (∀ n : ℕ, f₁ ^ n • c₁ (t₁ n) = c₁ (t₁ 0)) ∧
    (¬ Function.Injective (Ideal.primaryComponent.map J₁ c₁)) ∧
    (¬ Module.Flat R₁ (AdicCompletion J₁ R₁)) ∧
    (¬ Function.Surjective (Ideal.primaryComponent.map J₂ c₂)) ∧
    (∃ x : Ideal.primaryComponent (AdicCompletion J₂ R₂) J₂,
      (∀ n : ℕ, AdicCompletion.evalₐ J₂ n x.1 =
        Ideal.Quotient.mk (J₂ ^ n) (∑ i ∈ Finset.range n, f₂ ^ i * t₂ i)) ∧
      f₂ • x.1 = 0 ∧
      x ∉ Set.range (Ideal.primaryComponent.map J₂ c₂)) ∧
    (¬ Module.Flat R₂ (AdicCompletion J₂ R₂)) := by
  dsimp
  refine ⟨first_T_zero_ne k, first_t0_primary k, first_completion_t0_zero k,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [← map_smul, smul_eq_mul]
    exact congrArg (AdicCompletion.of _ _) (first_power_relation k n)
  · intro hinj
    have hzero : (⟨Ideal.Quotient.mk _ (MvPolynomial.X (some 0)),
        first_t0_primary k⟩ : Ideal.primaryComponent _ _) = 0 := by
      apply hinj
      apply Subtype.ext
      show (AdicCompletion.of _ _)
        (Ideal.Quotient.mk _ (MvPolynomial.X (some 0) : MvPolynomial (Option ℕ) k)) =
        (AdicCompletion.of _ _) 0
      have hc := first_completion_t0_zero k
      dsimp at hc
      simpa only [map_zero] using hc
    exact first_T_zero_ne k (congrArg Subtype.val hzero)
  · intro hflat
    exact first_T_zero_ne k
      (flat_completion_injective_on_annihilator _ _ hflat
        (first_annihilates k) (first_completion_t0_zero k))
  · intro hsurj
    obtain ⟨x, _, _, hnot⟩ := second_series_witness k
    exact hnot (hsurj x)
  · exact second_series_witness k
  · intro hflat
    obtain ⟨x, _, hxann, hnot⟩ := second_series_witness k
    obtain ⟨y, hy⟩ := flat_completion_covers_annihilator _ hflat x.1 hxann
    exact hnot ⟨y, Subtype.ext hy⟩

end

section

private lemma flat_left_of_flat_prod {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R (M × N)] : Module.Flat R M := by
  let i : M →ₗ[R] M × N :=
    { toFun := fun m ↦ (m, 0)
      map_add' := by simp
      map_smul' := by simp }
  let r : M × N →ₗ[R] M := LinearMap.fst R M N
  exact Module.Flat.of_retract i r (by ext; rfl)

/-- **Stacks 0BNP.** Adic completion and localization do not in general form a flat cover: there
is a commutative ring `R` and an element `f` such that the product of the completion of `R` at
`(f)` and `R_f` is not flat over `R`. -/
@[stacks 0BNP]
public theorem exists_nonflat_adicCompletion_prod_localizationAway :
    ∃ (R : Type) (_ : CommRing R) (f : R),
      ¬ Module.Flat R
        (AdicCompletion (Ideal.span ({f} : Set R)) R × Localization.Away f) := by
  let P := MvPolynomial (Option ℕ) ℚ
  let F : P := MvPolynomial.X none
  let T : ℕ → P := fun n ↦ MvPolynomial.X (some n)
  let I : Ideal P :=
    Ideal.span ({F * T 0} ∪ Set.range (fun n ↦ F * T (n + 1) - T n))
  let R := P ⧸ I
  let f : R := Ideal.Quotient.mk I F
  have h := adicCompletion_torsionMap_not_bijective_examples ℚ
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, hnflat, _⟩
  refine ⟨R, inferInstance, f, ?_⟩
  intro hflat
  exact hnflat (flat_left_of_flat_prod (R := R)
    (M := AdicCompletion (Ideal.span ({f} : Set R)) R)
    (N := Localization.Away f))

end

end BeauvilleLaszlo

end
