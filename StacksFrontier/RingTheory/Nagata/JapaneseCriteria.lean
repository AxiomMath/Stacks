module


public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.RingTheory.Nagata.Shrink
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.ZariskisMainTheorem
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Criteria for the N-1 and N-2 (Japanese) conditions

Let `R` be a domain with field of fractions `K = Frac(R)`. Following
[EGA, Chapter 0, Definition 23.1.1], `R` is **N-1** when the integral closure of `R` in `K` is a
finite `R`-module, and **N-2**, or **Japanese**, when the integral closure of `R` in every finite
field extension `L/K` is a finite `R`-module. These are `IsN1` and `IsJapaneseRing`, defined for
Tag 032F in `StacksFrontier.RingTheory.Nagata.Defs` and imported here; this file adds the permanence
properties of the two conditions.

## Main results

* `isN1_and_isJapaneseRing_of_isLocalization` (Tag 032G): N-1 and N-2 pass to a localization.
* `isN1_and_isJapaneseRing_of_localizationSpan` (Tag 032H): N-1 and N-2 descend along a cover of
  `Spec R` by the principal opens attached to a set of elements generating the unit ideal.
* `isJapaneseRing_of_quasiFinite` (Tag 032I): N-2 ascends along a quasi-finite extension of
  domains with Noetherian base.
* `isJapaneseRing_iff_finite_integralClosure_isPurelyInseparable` (Tag 032N): for a Noetherian
  domain, N-2 need only be tested on the finite purely inseparable extensions of `K`.

## Implementation notes

The two conditions are stated over `FractionRing R`, so each proof begins by moving between that
model and whichever field of fractions the argument produces; the private lemmas
`module_finite_integralClosure_of_isN1`, `isN1_of_module_finite_integralClosure` and
`isFractionRing_of_isLocalization_of_isFractionRing` isolate that bookkeeping. They are the
analogues for `IsN1` and `IsJapaneseRing` of `isIntegrallyClosed_iff`; the cross-universe N-2
transport is shared from `Nagata.Shrink`.

`IsJapaneseRing` takes its test extension in `Type u`, the universe of `R` itself, so every
statement here is a statement about rings in one universe and no universe annotation appears. The
coupling is what Tag 032N needs: its proof forms the normal closure of the test extension inside
an algebraic closure, which lives in the universe of that extension.

Tag 032G asks that the localization be a domain rather than that the submonoid avoid `0`; this is
the same hypothesis, since a localization at a submonoid containing `0` is subsingleton, and it is
the form a caller has available. Tag 032N carries no hypothesis on the characteristic of `K`,
although the source states it for characteristic `p > 0`: the argument — factor a finite normal
extension of `K` as a purely inseparable extension followed by a separable one (Tag 030M), then
use that the integral closure in a separable extension of a Noetherian normal domain is finite
(Tag 032L) — never inspects the characteristic, and in characteristic zero the criterion is the
statement that `R` is N-1, purely inseparable extensions of `K` then being trivial.

## References

* [Grothendieck and Dieudonné, *Éléments de géométrie algébrique*][EGA], Chapter 0,
  Definition 23.1.1
* [Stacks Project, Tag 032F](https://stacks.math.columbia.edu/tag/032F)
* [Stacks Project, Tag 032G](https://stacks.math.columbia.edu/tag/032G)
* [Stacks Project, Tag 032H](https://stacks.math.columbia.edu/tag/032H)
* [Stacks Project, Tag 032I](https://stacks.math.columbia.edu/tag/032I)
* [Stacks Project, Tag 032N](https://stacks.math.columbia.edu/tag/032N)
-/

@[expose] public section

open scoped nonZeroDivisors

universe u

/-! ### Reformulations over an arbitrary field of fractions -/

/-- The submonoid at which a nontrivial localization of a domain is taken consists of nonzero
divisors: were `0` in it the localization would be subsingleton. -/
private theorem le_nonZeroDivisors_of_isLocalization {R : Type*} [CommRing R] [IsDomain R]
    (M : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Nontrivial Rₛ] [Algebra R Rₛ]
    [IsLocalization M Rₛ] : M ≤ R⁰ := fun _ hm =>
  mem_nonZeroDivisors_of_ne_zero fun h =>
    have : Subsingleton Rₛ := IsLocalization.subsingleton (h ▸ hm)
    false_of_nontrivial_of_subsingleton Rₛ

/-- **A localization has the same field of fractions.** A field of fractions of a nontrivial
localization `Rₛ` of a domain `R` is a field of fractions of `R`: it is `Rₛ`-isomorphic to
`Frac(Rₛ)`, hence `R`-isomorphic to `Frac(R)`. -/
private theorem isFractionRing_of_isLocalization_of_isFractionRing {R : Type*} [CommRing R]
    [IsDomain R] (M : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [IsDomain Rₛ] [Algebra R Rₛ]
    [IsLocalization M Rₛ] (T : Type*) [Field T] [Algebra Rₛ T] [Algebra R T]
    [IsScalarTower R Rₛ T] [IsFractionRing Rₛ T] : IsFractionRing R T := by
  have hM : M ≤ R⁰ := le_nonZeroDivisors_of_isLocalization M Rₛ
  have hu : ∀ y : M, IsUnit (algebraMap R (FractionRing R) (y : R)) := fun y =>
    isUnit_iff_ne_zero.mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hM y.2))
  let _ : Algebra Rₛ (FractionRing R) := (IsLocalization.lift (M := M) hu).toAlgebra
  have : IsScalarTower R Rₛ (FractionRing R) :=
    .of_algebraMap_eq fun x => (IsLocalization.lift_eq hu x).symm
  have : IsFractionRing Rₛ (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₛ (FractionRing R)
  exact IsFractionRing.of_algHom
    (((FractionRing.algEquiv Rₛ T).symm.trans
      (FractionRing.algEquiv Rₛ (FractionRing R))).toAlgHom.restrictScalars R)

/-- **N-1 over an arbitrary field of fractions.** For an N-1 domain `A` the integral closure of
`A` in any field of fractions `K` of `A` is a finite `A`-module, not only in `FractionRing A`. -/
private theorem module_finite_integralClosure_of_isN1 {A : Type*} [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] (h : IsN1 A) :
    Module.Finite A (integralClosure A K) :=
  have : Module.Finite A (integralClosure A (FractionRing A)) := h
  .equiv (FractionRing.algEquiv A K).mapIntegralClosure.toLinearEquiv

/-- Conversely, finiteness of the integral closure in one field of fractions gives N-1. -/
private theorem isN1_of_module_finite_integralClosure {A : Type*} [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (h : Module.Finite A (integralClosure A K)) : IsN1 A :=
  have := h
  .equiv (FractionRing.algEquiv A K).mapIntegralClosure.symm.toLinearEquiv

/-! ### Tag 032G: N-1 and N-2 pass to a localization -/

/-- **Finiteness of an integral closure passes to a localization.** This is Tag 0307, that forming
the integral closure commutes with localization (`IsLocalization.integralClosure`), together with
the fact that a localization of a finite module is finite (`Module.Finite.of_isLocalization`).

Nothing is asked of `L` beyond being a commutative `R`-algebra and, compatibly, an `Rₛ`-algebra. -/
@[ega "II 6.3.10" "Locality on X"]
private theorem module_finite_integralClosure_of_isLocalization {R : Type*} [CommRing R]
    (M : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization M Rₛ]
    {L : Type*} [CommRing L] [Algebra R L] [Algebra Rₛ L] [IsScalarTower R Rₛ L]
    (h : Module.Finite R (integralClosure R L)) :
    Module.Finite Rₛ (integralClosure Rₛ L) := by
  have hsub : integralClosure R L ≤ Subalgebra.restrictScalars R (integralClosure Rₛ L) :=
    fun _ hx => hx.tower_top
  let _ : Algebra (integralClosure R L) (integralClosure Rₛ L) :=
    (Subalgebra.inclusion hsub).toAlgebra
  have : IsScalarTower (integralClosure R L) (integralClosure Rₛ L) L :=
    .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R (integralClosure R L) (integralClosure Rₛ L) :=
    .of_algebraMap_eq fun _ => Subtype.ext rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid L M) L :=
    IsLocalization.of_le_isUnit fun _ ⟨m, hm, hx⟩ => by
      rw [← hx, IsScalarTower.algebraMap_apply R Rₛ L]
      exact (IsLocalization.map_units Rₛ ⟨m, hm⟩).map _
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L) M)
      (integralClosure Rₛ L) := IsLocalization.integralClosure M
  exact Module.Finite.of_isLocalization R (integralClosure R L) M

/-- **N-1 and N-2 pass to a localization.** Stacks Tag 032G: if a domain `R` is N-1 then so is
every localization of `R` which is again a domain, and the same for N-2. -/
@[stacks 032G]
theorem isN1_and_isJapaneseRing_of_isLocalization {R : Type u} [CommRing R] [IsDomain R]
    (M : Submonoid R) (Rₛ : Type u) [CommRing Rₛ] [IsDomain Rₛ] [Algebra R Rₛ]
    [IsLocalization M Rₛ] :
    (IsN1 R → IsN1 Rₛ) ∧ (IsJapaneseRing R → IsJapaneseRing Rₛ) := by
  -- The composite `R → Rₛ → Frac(Rₛ)` exhibits `Frac(Rₛ)` as a field of fractions of `R`.
  have hfracR : IsFractionRing R (FractionRing Rₛ) :=
    isFractionRing_of_isLocalization_of_isFractionRing M Rₛ (FractionRing Rₛ)
  refine ⟨fun h => ?_, fun h => { finite := fun L _ _ _ _ hfin => ?_ }⟩
  · refine isN1_of_module_finite_integralClosure (FractionRing Rₛ) ?_
    exact module_finite_integralClosure_of_isLocalization M Rₛ
      (module_finite_integralClosure_of_isN1 (FractionRing Rₛ) h)
  · -- `L` is a finite extension of `Frac(Rₛ)`, hence of the field of fractions of `R`.
    let _ : Algebra R L := ((algebraMap Rₛ L).comp (algebraMap R Rₛ)).toAlgebra
    have : IsScalarTower R Rₛ L := .of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _)
    have : IsScalarTower R (FractionRing Rₛ) L := IsScalarTower.to₁₃₄ R Rₛ (FractionRing Rₛ) L
    have : FiniteDimensional (FractionRing Rₛ) L := hfin
    exact module_finite_integralClosure_of_isLocalization M Rₛ
      (module_finite_integralClosure_of_isJapaneseRing h (FractionRing Rₛ) L)

/-! ### Tag 032H: N-1 and N-2 descend along a principal open cover -/

/-- A nonzero element of a domain `R` is invertible in every algebra over a field of fractions
of `R`. -/
private theorem isUnit_algebraMap_of_ne_zero {R : Type*} [CommRing R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] {L : Type*} [Semiring L] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] {x : R} (hx : x ≠ 0) : IsUnit (algebraMap R L x) := by
  rw [IsScalarTower.algebraMap_apply R K L]
  refine IsUnit.map _ (isUnit_iff_ne_zero.mpr ?_)
  rwa [Ne, IsFractionRing.to_map_eq_zero_iff]

/-- **Finiteness of an integral closure descends along a principal open cover.** Let `t ⊆ R`
generate the unit ideal, let `Rₚ g` be the localization of `R` away from `g` for `g ∈ t`, and let
`L` be an `R`-algebra in which every element of `t` is invertible, an algebra over every `Rₚ g`
compatibly with `R`. If the integral closure of `Rₚ g` in `L` is a finite `Rₚ g`-module for every
`g`, then the integral closure of `R` in `L` is a finite `R`-module.

This is Tag 0307 (`IsLocalization.Away.integralClosure`: the integral closure of `Rₚ g` in `L` is
the localization away from `g` of the integral closure of `R` in `L`) followed by Tag 00EO
(`Module.Finite.of_localizationSpan'`: finiteness of a module is local on a principal open
cover). -/
@[ega "II 6.3.10" "Locality on X"]
private theorem module_finite_integralClosure_of_localizationSpan {R : Type*} [CommRing R]
    (t : Set R) (ht : Ideal.span t = ⊤)
    {Rₚ : ∀ _ : t, Type*} [∀ g, CommRing (Rₚ g)] [∀ g, Algebra R (Rₚ g)]
    [∀ g, IsLocalization.Away g.val (Rₚ g)]
    {L : Type*} [CommRing L] [Algebra R L] [∀ g, Algebra (Rₚ g) L]
    [∀ g, IsScalarTower R (Rₚ g) L] (hu : ∀ g : t, IsUnit (algebraMap R L g.val))
    (H : ∀ g, Module.Finite (Rₚ g) (integralClosure (Rₚ g) L)) :
    Module.Finite R (integralClosure R L) := by
  have hsub : ∀ g : t, integralClosure R L ≤
      Subalgebra.restrictScalars R (integralClosure (Rₚ g) L) := fun _ _ hx => hx.tower_top
  let _ : ∀ g : t, Algebra (integralClosure R L) (integralClosure (Rₚ g) L) := fun g =>
    (Subalgebra.inclusion (hsub g)).toAlgebra
  have : ∀ g : t, IsScalarTower (integralClosure R L) (integralClosure (Rₚ g) L) L := fun _ =>
    .of_algebraMap_eq fun _ => rfl
  have : ∀ g : t, IsScalarTower R (integralClosure R L) (integralClosure (Rₚ g) L) := fun _ =>
    .of_algebraMap_eq fun _ => Subtype.ext rfl
  have : ∀ g : t, IsLocalization.Away (algebraMap R L g.val) L := fun g =>
    IsLocalization.of_le_isUnit (Submonoid.powers_le.mpr (hu g))
  have : ∀ g : t, IsLocalizedModule.Away g.val
      (IsScalarTower.toAlgHom R (integralClosure R L) (integralClosure (Rₚ g) L)).toLinearMap :=
    fun g => isLocalizedModule_iff_isLocalization.mpr (by
      rw [Algebra.algebraMapSubmonoid_powers]
      exact IsLocalization.Away.integralClosure (S := L) g.val)
  exact Module.Finite.of_localizationSpan' t ht
    (fun g => (IsScalarTower.toAlgHom R (integralClosure R L)
      (integralClosure (Rₚ g) L)).toLinearMap) H

/-- The previous lemma for a field `L` over `K = Frac(R)`: the localizations `Rₚ g` of a domain `R`
away from the elements of a spanning set `t` are domains with the same field of fractions `K`, and
every element of `t` is invertible in `L`, so all that is asked of the cover is finiteness of the
integral closure of `Rₚ g` in `L`, for a field of fractions of `Rₚ g` lying inside `L` over which
`L` is finite. -/
private theorem module_finite_integralClosure_of_localizationSpan_frac {R : Type u} [CommRing R]
    [IsDomain R] (t : Set R) (ht : Ideal.span t = ⊤)
    {Rₚ : ∀ _ : t, Type u} [∀ g, CommRing (Rₚ g)] [∀ g, IsDomain (Rₚ g)]
    [∀ g, Algebra R (Rₚ g)] [∀ g, IsLocalization.Away g.val (Rₚ g)]
    {L : Type u} [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
    (H : ∀ (g : t) (F : Type u) [Field F] [Algebra (Rₚ g) F] [IsFractionRing (Rₚ g) F]
      [Algebra (Rₚ g) L] [IsScalarTower R (Rₚ g) L] [Algebra F L] [IsScalarTower (Rₚ g) F L]
      [FiniteDimensional F L], Module.Finite (Rₚ g) (integralClosure (Rₚ g) L)) :
    Module.Finite R (integralClosure R L) := by
  have hne : ∀ g : t, (g : R) ≠ 0 := fun g =>
    nonZeroDivisors.coe_ne_zero
      ⟨_, le_nonZeroDivisors_of_isLocalization (Submonoid.powers (g : R)) (Rₚ g)
        (Submonoid.mem_powers _)⟩
  have huK : ∀ g : t, IsUnit (algebraMap R (FractionRing R) (g : R)) := fun g =>
    isUnit_algebraMap_of_ne_zero (FractionRing R) (hne g)
  have huL : ∀ g : t, IsUnit (algebraMap R L (g : R)) := fun g =>
    isUnit_algebraMap_of_ne_zero (FractionRing R) (hne g)
  -- `K = Frac(R)` is a field of fractions of `Rₚ g`, and `L` is an algebra over it.
  let _ : ∀ g : t, Algebra (Rₚ g) (FractionRing R) := fun g =>
    (IsLocalization.Away.lift (S := Rₚ g) (g : R) (huK g)).toAlgebra
  have : ∀ g : t, IsScalarTower R (Rₚ g) (FractionRing R) := fun g =>
    .of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  have : ∀ g : t, IsFractionRing (Rₚ g) (FractionRing R) := fun g =>
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (g : R))
      (Rₚ g) (FractionRing R)
  let _ : ∀ g : t, Algebra (Rₚ g) L := fun g =>
    ((algebraMap (FractionRing R) L).comp (algebraMap (Rₚ g) (FractionRing R))).toAlgebra
  have : ∀ g : t, IsScalarTower (Rₚ g) (FractionRing R) L := fun _ =>
    .of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _)
  have : ∀ g : t, IsScalarTower R (Rₚ g) L := fun g =>
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply (Rₚ g) (FractionRing R) L,
        ← IsScalarTower.algebraMap_apply R (Rₚ g) (FractionRing R),
        ← IsScalarTower.algebraMap_apply R (FractionRing R) L]
  exact module_finite_integralClosure_of_localizationSpan t ht huL fun g => H g (FractionRing R)

/-- **N-1 and N-2 descend along a principal open cover.** Stacks Tag 032H: let `R` be a domain and
let `t ⊆ R` generate the unit ideal. If the localization `R_g` is N-1 for every `g ∈ t` then so is
`R`, and the same for N-2. -/
@[stacks 032H]
theorem isN1_and_isJapaneseRing_of_localizationSpan {R : Type u} [CommRing R] [IsDomain R]
    (t : Set R) (ht : Ideal.span t = ⊤)
    {Rₚ : ∀ _ : t, Type u} [∀ g, CommRing (Rₚ g)] [∀ g, IsDomain (Rₚ g)]
    [∀ g, Algebra R (Rₚ g)] [∀ g, IsLocalization.Away g.val (Rₚ g)] :
    ((∀ g, IsN1 (Rₚ g)) → IsN1 R) ∧
      ((∀ g, IsJapaneseRing (Rₚ g)) → IsJapaneseRing R) := by
  refine ⟨fun H => ?_, fun H => { finite := fun L _ _ _ _ hfin => ?_ }⟩
  · -- `L = K` is a field of fractions of `Rₚ g`, so N-1 for `Rₚ g` is finiteness in `L`.
    refine module_finite_integralClosure_of_localizationSpan_frac (Rₚ := Rₚ)
      (L := FractionRing R) t ht fun g _ _ _ _ _ _ _ _ _ => ?_
    have : IsFractionRing (Rₚ g) (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (g : R))
        (Rₚ g) (FractionRing R)
    exact module_finite_integralClosure_of_isN1 (FractionRing R) (H g)
  · have : FiniteDimensional (FractionRing R) L := hfin
    exact module_finite_integralClosure_of_localizationSpan_frac (Rₚ := Rₚ) (L := L) t ht
      fun g F _ _ _ _ _ _ _ _ => module_finite_integralClosure_of_isJapaneseRing (H g) F L

/-! ### Tag 032N: N-2 is tested on purely inseparable extensions -/

/-- An element of a normal extension `M/K` that is separable over `K` and fixed by every
`K`-automorphism of `M` lies in `K`.

The element lies in `separableClosure K M`, which is Galois over `K`, and it is fixed by every
`K`-automorphism of that field because those are the restrictions of the `K`-automorphisms of `M`,
the extension `M/K` being normal. -/
private theorem mem_bot_of_isSeparable_of_forall_algEquiv_eq {K M : Type*} [Field K] [Field M]
    [Algebra K M] [Normal K M] {x : M} (hx : IsSeparable K x)
    (hfix : ∀ σ : M ≃ₐ[K] M, σ x = x) : x ∈ (⊥ : IntermediateField K M) := by
  have hxs : x ∈ separableClosure K M := mem_separableClosure_iff.mpr hx
  have key : (⟨x, hxs⟩ : separableClosure K M) ∈
      (⊥ : IntermediateField K (separableClosure K M)) :=
    (InfiniteGalois.mem_bot_iff_fixed _).mpr fun τ => by
      obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := M) τ
      exact Subtype.ext ((AlgEquiv.restrictNormal_commutes σ (separableClosure K M)
        ⟨x, hxs⟩).trans (hfix σ))
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp key
  exact IntermediateField.mem_bot.mpr ⟨y, congrArg Subtype.val hy⟩

/-- **Tag 030M, purely inseparable half.** The subfield of a normal extension `M/K` fixed by the
whole group `Aut(M/K)` is purely inseparable over `K`.

Together with `FixedPoints.isSeparable`, which makes `M` separable over that subfield, this is the
factorisation of a normal extension as a purely inseparable extension followed by a separable
one. -/
private theorem isPurelyInseparable_fixedField_top (K M : Type*) [Field K] [Field M] [Algebra K M]
    [Normal K M] :
    IsPurelyInseparable K (IntermediateField.fixedField (⊤ : Subgroup (M ≃ₐ[K] M))) := by
  rw [isPurelyInseparable_iff]
  intro x
  refine ⟨Algebra.IsIntegral.isIntegral x, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp (mem_bot_of_isSeparable_of_forall_algEquiv_eq
    (show IsSeparable K (x : M) by rwa [IsSeparable, ← IntermediateField.minpoly_eq])
    fun σ => (IntermediateField.mem_fixedField_iff _ _).mp x.2 σ (Subgroup.mem_top σ))
  exact ⟨y, Subtype.ext (by simpa using hy)⟩

/-- Over a Noetherian ring, an `R`-subalgebra of a module-finite `R`-subalgebra is
module-finite. -/
private theorem module_finite_of_le_subalgebra {R A : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] {S T : Subalgebra R A} (hST : S ≤ T) (hT : Module.Finite R T) :
    Module.Finite R S :=
  have := hT
  .of_injective (Subalgebra.inclusion hST).toLinearMap (Subalgebra.inclusion_injective hST)

/-- Over a Noetherian ring, finiteness of integral closures descends along an injection of
`R`-algebras `f : A →ₐ[R] B`, which carries the integral closure of `R` in `A` into the integral
closure of `R` in `B`. -/
public theorem module_finite_integralClosure_of_injective {R A B : Type*} [CommRing R]
    [IsNoetherianRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (hf : Function.Injective f) (hB : Module.Finite R (integralClosure R B)) :
    Module.Finite R (integralClosure R A) :=
  have := hB
  .of_injective
    ((f.comp (integralClosure R A).val).codRestrict (integralClosure R B)
      (fun x => x.2.map f)).toLinearMap
    fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

/-- If the integral closure `R'` of a Noetherian domain `R` in a finite extension `F` of its field
of fractions `K` is a finite `R`-module, then so is the integral closure of `R` in any finite
separable extension `M/F`.

This is the composite of Tag 032L (the integral closure of `R'` in `M` is finite over `R'`, since
`R'` is Noetherian, integrally closed, with field of fractions `F`), Tag 00GL (finiteness is
transitive) and Tag 0308 (the integral closure of `R` in `M` sits inside the integral closure of
`R'` in `M`). -/
private theorem module_finite_integralClosure_of_isSeparable (R K F M : Type*) [CommRing R]
    [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field F]
    [Algebra K F] [Algebra R F] [IsScalarTower R K F] [FiniteDimensional K F] [Field M]
    [Algebra F M] [Algebra R M] [IsScalarTower R F M] [FiniteDimensional F M]
    [Algebra.IsSeparable F M] (h : Module.Finite R (integralClosure R F)) :
    Module.Finite R (integralClosure R M) := by
  have : IsNoetherianRing (integralClosure R F) :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower R
      (inferInstance : IsNoetherian R (integralClosure R F)))
  have : IsFractionRing (integralClosure R F) F :=
    integralClosure.isFractionRing_of_finite_extension K F
  have : IsIntegrallyClosed (integralClosure R F) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : Module.Finite (integralClosure R F) (integralClosure (integralClosure R F) M) :=
    IsIntegralClosure.finite (integralClosure R F) F M _
  have hfin : Module.Finite R (integralClosure (integralClosure R F) M) :=
    Module.Finite.trans (integralClosure R F) _
  exact module_finite_of_le_subalgebra
    (T := (integralClosure (integralClosure R F) M).restrictScalars R)
    (fun _ hx => IsIntegral.tower_top (A := integralClosure R F) hx) hfin

/-- **N-2 is tested on purely inseparable extensions.** Stacks Tag 032N: a Noetherian domain `R`
is N-2 if and only if the integral closure of `R` in every finite purely inseparable extension of
its field of fractions is a finite `R`-module.

The source states this for a field of fractions of characteristic `p > 0`; the characteristic
plays no role in the argument, which factors a finite normal extension of `K` as a purely
inseparable extension followed by a separable one (Tag 030M) and is vacuously about `L = K` in
characteristic zero, so no characteristic hypothesis is imposed. -/
@[stacks 032N, ega "0 23.1.2"]
theorem isJapaneseRing_iff_finite_integralClosure_isPurelyInseparable (R : Type u) [CommRing R]
    [IsDomain R] [IsNoetherianRing R] :
    IsJapaneseRing R ↔
      ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [IsPurelyInseparable (FractionRing R) L],
        Module.Finite R (integralClosure R L) := by
  refine ⟨fun hR L _ _ _ _ _ _ => hR.finite L,
    fun h => { finite := fun L _ _ _ _ hfin => ?_ }⟩
  have : FiniteDimensional (FractionRing R) L := hfin
  have : IsScalarTower R (FractionRing R) (AlgebraicClosure L) :=
    IsScalarTower.to₁₂₄ R (FractionRing R) L (AlgebraicClosure L)
  set M := IntermediateField.normalClosure (FractionRing R) L (AlgebraicClosure L)
  set F := IntermediateField.fixedField (⊤ : Subgroup (M ≃ₐ[FractionRing R] M))
  have : IsScalarTower R L M := IsScalarTower.to₁₃₄ R (FractionRing R) L M
  have : IsScalarTower R F M := IsScalarTower.to₁₃₄ R (FractionRing R) F M
  have : IsPurelyInseparable (FractionRing R) F := isPurelyInseparable_fixedField_top _ M
  have : Algebra.IsSeparable F M := FixedPoints.isSeparable _ M
  exact module_finite_integralClosure_of_injective (IsScalarTower.toAlgHom R L M)
    (algebraMap L M).injective
    (module_finite_integralClosure_of_isSeparable R (FractionRing R) F M (h F))

/-! ### Tag 032I: N-2 ascends along a quasi-finite extension -/

section QuasiFinite

attribute [local instance] FractionRing.liftAlgebra

/-- A localization of a domain away from a nonzero element is a domain. -/
private theorem isDomain_of_isLocalizationAway {S : Type*} [CommRing S] [IsDomain S] {g : S}
    (hg : g ≠ 0) (Sg : Type*) [CommRing Sg] [Algebra S Sg] [IsLocalization.Away g Sg] :
    IsDomain Sg :=
  IsLocalization.isDomain_of_le_nonZeroDivisors Sg
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hg))

/-- **N-2 ascends along an injective module-finite extension of domains.** This is the second half
of the proof of Stacks 032I, and the case of the lemma in which `S` is finite over `R`: a finite
extension `M` of `Frac(S)` is also a finite extension of `Frac(R)`, and by Tag 0308 the integral
closures of `R` and of `S` in `M` have the same elements, so a finite `R`-module generating set of
the one is a finite `S`-module generating set of the other. -/
private theorem isJapaneseRing_of_module_finite {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    (hR : IsJapaneseRing R) : IsJapaneseRing S := by
  refine { finite := fun L _ _ _ _ hfin => ?_ }
  have : Module.Finite (FractionRing S) L := hfin
  -- `L` is an extension of `R` through `S`, and a finite extension of `Frac(R)`.
  let _ : Algebra R L := RingHom.toAlgebra ((algebraMap S L).comp (algebraMap R S))
  have : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul S L := FaithfulSMul.trans S (FractionRing S) L
  have : FaithfulSMul R L := FaithfulSMul.trans R S L
  have : IsScalarTower R (FractionRing S) L := IsScalarTower.to₁₃₄ R S (FractionRing S) L
  have : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R S)
  have : Module.Finite (FractionRing R) L := Module.Finite.trans (FractionRing S) L
  -- The integral closures of `R` and of `S` in `L` have the same elements.
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hset : ∀ x : L, x ∈ integralClosure S L ↔ x ∈ integralClosure R L := fun x =>
    ⟨fun hx => isIntegral_trans x hx, fun hx => hx.tower_top⟩
  obtain ⟨t, ht⟩ : (Subalgebra.toSubmodule (integralClosure R L)).FG :=
    Module.Finite.iff_fg.mp (hR.finite L)
  have hB : (Subalgebra.toSubmodule (integralClosure S L)).FG := by
    refine ⟨t, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro x hx
      exact (hset x).mpr (ht ▸ Submodule.subset_span hx :
        x ∈ Subalgebra.toSubmodule (integralClosure R L))
    · intro x hx
      have hx' : x ∈ Submodule.span R (t : Set L) := ht ▸ (hset x).mp hx
      exact Submodule.span_le_restrictScalars R S (t : Set L) hx'
  exact Module.Finite.iff_fg.mpr hB

/-- The map `S'_r → S_r` of Zariski's main theorem is a map of `S'`-algebras: it agrees on `S'`
with the structure map of `S_r`. -/
private theorem awayMap_algebraMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (S' : Subalgebra R S) (r : S') (x : S') :
    Localization.awayMap S'.val.toRingHom r (algebraMap S' (Localization.Away r) x) =
      algebraMap S (Localization.Away ((r : S))) (S'.val x) :=
  IsLocalization.map_eq _ x

/-- N-2 for a localization of `S` away from an element `r` of a subalgebra `S'` module-finite over
`R`, when `S'_r → S_r` is an isomorphism. This is the step of Stacks 032I that turns the
module-finite case into a statement about `S` itself. -/
private theorem isJapaneseRing_localizationAway_of_module_finite {R S : Type u} [CommRing R]
    [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] (S' : Subalgebra R S)
    [Module.Finite R S'] (r : S')
    (hr : Function.Bijective (Localization.awayMap S'.val.toRingHom r))
    [IsDomain (Localization.Away (r : S))] (hR : IsJapaneseRing R) :
    IsJapaneseRing (Localization.Away (r : S)) := by
  have hS' : IsJapaneseRing (S' : Type u) := isJapaneseRing_of_module_finite hR
  let _ : Algebra S' (Localization.Away (r : S)) :=
    RingHom.toAlgebra ((algebraMap S (Localization.Away (r : S))).comp S'.val.toRingHom)
  have : IsLocalization (Submonoid.powers r) (Localization.Away (r : S)) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r)
      { RingEquiv.ofBijective _ hr with commutes' := fun x => awayMap_algebraMap S' r x }
  exact (isN1_and_isJapaneseRing_of_isLocalization (Submonoid.powers r)
    (Localization.Away (r : S))).2 hS'

/-- **N-2 ascends along a quasi-finite extension of domains.** Stacks Tag 032I: let `R ⊆ S` be a
quasi-finite extension of domains with `R` Noetherian and N-2. Then `S` is N-2.

Zariski's main theorem covers `Spec S` by principal opens on which `S` agrees with a subalgebra
module-finite over `R`; N-2 ascends to such a subalgebra, passes to its localizations (Tag 032G),
and descends from the cover (Tag 032H). -/
@[stacks 032I]
theorem isJapaneseRing_of_quasiFinite {R S : Type u} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [Algebra R S] [FaithfulSMul R S] [IsNoetherianRing R] [Algebra.FiniteType R S]
    [Algebra.QuasiFinite R S] (hR : IsJapaneseRing R) : IsJapaneseRing S := by
  -- The nonzero elements of `S` at which Zariski's main theorem holds with a module-finite
  -- subalgebra of `S`.
  set T : Set S := {g : S | g ≠ 0 ∧ ∃ S' : Subalgebra R S, ∃ _ : Module.Finite R S',
      ∃ hg : g ∈ S', Function.Bijective
        (Localization.awayMap S'.val.toRingHom (⟨g, hg⟩ : S'))}
  -- `T` generates the unit ideal: it meets the complement of every maximal ideal.
  have hspan : Ideal.span T = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have : m.IsPrime := hm.isPrime
    have : Algebra.QuasiFiniteAt R m := Algebra.QuasiFinite.instLocalization (R := R) m.primeCompl
    obtain ⟨S', hfg, r, hrm, hbij⟩ :=
      Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective
        (R := R) m (Algebra.ZariskisMainProperty.of_finiteType (R := R) m)
    have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hfg⟩
    exact hrm (hle (Ideal.subset_span
      (⟨fun h => hrm (h ▸ m.zero_mem), S', ‹Module.Finite R S'›, r.2, hbij⟩ : (r : S) ∈ T)))
  have : ∀ g : T, IsDomain (Localization.Away (g : S)) := fun g =>
    isDomain_of_isLocalizationAway g.2.1 (Localization.Away (g : S))
  refine (isN1_and_isJapaneseRing_of_localizationSpan T hspan
    (Rₚ := fun g : T => Localization.Away (g : S))).2 fun g => ?_
  obtain ⟨-, S', hfin, hg, hbij⟩ := g.2
  exact isJapaneseRing_localizationAway_of_module_finite S' ⟨(g : S), hg⟩ hbij hR

end QuasiFinite

end
