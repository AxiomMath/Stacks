module

public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FormallyEtaleCriterion

/-!
# Generic finite étaleness

Let `R ⊆ B` be domains with `B` of finite type over `R`, `R` a Dedekind domain, and suppose the
extension of fraction fields `L / K` is separable algebraic. Then there is a nonzero `g ∈ R` such
that `B_g` is finite étale over `R_g`.

The proof is the usual one. Each of finitely many generators of `B` has an integral multiple
by a nonzero element of `R` (`exists_integral_multiple`), so inverting their product makes `B`
finite. The generic point of `Spec B` lies in the unramified locus, because
`K → L` is separable and `R → K` is a localization, so some basic open `D(f)`, `f ≠ 0`, is
unramified; `f` divides a nonzero element of `R` (`Ideal.comap_ne_bot_of_algebraic_mem`).
Over the Dedekind domain `R_g` the torsion-free `B_g` is flat, and a flat unramified algebra
of finite presentation is étale.

This is the algebra behind the reduction, in Weil II 3.3, of a smooth curve to a finite étale
cover of an open of the affine line.

## Main results

* `Stacks.GenericFiniteEtale.exists_finite_etale_localization`.
-/

@[expose] public section

open Algebra Polynomial

namespace Stacks.GenericFiniteEtale

variable {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B]
  [FaithfulSMul R B]

variable (B) in
/-- The localization `B_g` of `B` at the powers of a `g ∈ R`, an algebra over `R_g`. -/
abbrev Loc (g : R) : Type _ := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))

omit [IsDomain R] [FaithfulSMul R B] in
/-- A nonzero `f ∈ B` divides a nonzero element of `R` when `B` is algebraic over `R`. -/
theorem exists_dvd_algebraMap [Algebra.IsAlgebraic R B] {f : B} (hf : f ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ f ∣ algebraMap R B r := by
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot <|
    Ideal.comap_ne_bot_of_algebraic_mem (I := Ideal.span {f}) hf
      (Ideal.mem_span_singleton_self f) (Algebra.IsAlgebraic.isAlgebraic (R := R) f)
  exact ⟨r, hr0, Ideal.mem_span_singleton.mp hr⟩

omit [IsDomain R] [IsDomain B] [FaithfulSMul R B] in
/-- `B_h` is integral over `R_h` as soon as the image of every `b ∈ B` is. -/
private theorem isIntegral_loc_of_forall_isIntegral {h : R}
    (hB : ∀ b : B, IsIntegral (Localization.Away h) (algebraMap B (Loc B h) b)) :
    Algebra.IsIntegral (Localization.Away h) (Loc B h) := by
  have hhu : IsUnit (algebraMap R (Localization.Away h) h) :=
    IsLocalization.Away.algebraMap_isUnit h
  constructor
  intro x
  obtain ⟨⟨b, ⟨m, hm⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B (Submonoid.powers h)) x
  dsimp only
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  refine (hB b).mul ?_
  have hm' := hm
  obtain ⟨x, ⟨n, rfl⟩, hmn⟩ := hm'
  obtain ⟨v, hv⟩ := hhu.pow n
  have hinv : IsLocalization.mk' (Loc B h) (1 : B) ⟨m, hm⟩ =
      algebraMap (Localization.Away h) (Loc B h) ↑v⁻¹ := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, map_one]
    show (1 : Loc B h) = _ * algebraMap B (Loc B h) m
    rw [← hmn, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R (Localization.Away h) (Loc B h), map_pow, ← hv,
      ← map_mul, Units.inv_mul, map_one]
  rw [hinv]
  exact isIntegral_algebraMap

omit [IsDomain B] [FaithfulSMul R B] in
/-- **Generic finiteness**: if `B` is of finite type and algebraic over `R`, then inverting a
suitable nonzero `g₁ ∈ R`, or any nonzero multiple `h` of it, makes `B_h` integral over `R_h`. -/
theorem exists_isIntegral_loc [Algebra.FiniteType R B] [Algebra.IsAlgebraic R B] :
    ∃ g₁ : R, g₁ ≠ 0 ∧ ∀ h : R, g₁ ∣ h →
      Algebra.IsIntegral (Localization.Away h) (Loc B h) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := B)
  choose y hy0 hyint using fun b : B =>
    (Algebra.IsAlgebraic.isAlgebraic (R := R) b).exists_integral_multiple
  refine ⟨∏ b ∈ s, y b, Finset.prod_ne_zero_iff.2 fun b _ => hy0 b, fun h hdvd => ?_⟩
  have hhu : IsUnit (algebraMap R (Localization.Away h) h) :=
    IsLocalization.Away.algebraMap_isUnit h
  have hunit : ∀ b ∈ s, IsUnit (algebraMap R (Localization.Away h) (y b)) := fun b hb =>
    isUnit_of_dvd_unit (map_dvd _ ((Finset.dvd_prod_of_mem y hb).trans hdvd)) hhu
  let S := (integralClosure (Localization.Away h) (Loc B h)).restrictScalars R
  have hle : Algebra.adjoin R (s : Set B) ≤ S.comap (IsScalarTower.toAlgHom R B (Loc B h)) := by
    rw [Algebra.adjoin_le_iff]
    intro b hb
    obtain ⟨u, hu⟩ := hunit b hb
    have hi : IsIntegral (Localization.Away h)
        (algebraMap B (Loc B h) b * algebraMap (Localization.Away h) (Loc B h) ↑u) := by
      have := ((hyint b).map (IsScalarTower.toAlgHom R B (Loc B h))).tower_top
        (A := Localization.Away h)
      convert this using 1
      rw [hu, ← IsScalarTower.algebraMap_apply, IsScalarTower.toAlgHom_apply, Algebra.smul_def,
        map_mul, mul_comm, ← IsScalarTower.algebraMap_apply]
    refine IsIntegral.of_mul_unit (r := ↑u⁻¹) ?_ hi
    rw [← map_mul, Units.inv_mul, map_one]
  have hB : ∀ b : B, IsIntegral (Localization.Away h) (algebraMap B (Loc B h) b) := fun b =>
    hle (hs ▸ Algebra.mem_top : b ∈ Algebra.adjoin R (s : Set B))
  exact isIntegral_loc_of_forall_isIntegral hB

/-- For a nonzero `g ∈ R`, the localization `B_g` is torsion-free over `R_g`. -/
private theorem isTorsionFree_loc {g : R} (hg : g ≠ 0) :
    Module.IsTorsionFree (Localization.Away g) (Loc B g) := by
  have hle : Submonoid.powers g ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_localization hle
  have hleB : Algebra.algebraMapSubmonoid B (Submonoid.powers g) ≤ nonZeroDivisors B := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _
      (FaithfulSMul.algebraMap_injective R B)).2 (nonZeroDivisors.ne_zero (hle hx)))
  have : IsDomain (Loc B g) := IsLocalization.isDomain_localization hleB
  have : IsLocalization ((Submonoid.powers g).map (algebraMap R B)) (Loc B g) :=
    Localization.isLocalization
  have hinj : Function.Injective (algebraMap (Localization.Away g) (Loc B g)) :=
    IsLocalization.map_injective_of_injective (Submonoid.powers g) (Localization.Away g)
      (Loc B g) (FaithfulSMul.algebraMap_injective R B)
  refine ⟨fun a ha x y hxy => ?_⟩
  simp only [Algebra.smul_def] at hxy
  exact mul_left_cancel₀ (fun h0 => ha.ne_zero (hinj (h0.trans (map_zero _).symm))) hxy

variable (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L]

omit [IsDomain B] [FaithfulSMul R B] in
include K L in
/-- `B` is algebraic over `R` when its fraction field is algebraic over that of `R`. -/
theorem isAlgebraic_of_isAlgebraic_fractionRing [Algebra.IsAlgebraic K L] :
    Algebra.IsAlgebraic R B := by
  refine ⟨fun b => ?_⟩
  have hL : IsAlgebraic K (algebraMap B L b) := Algebra.IsAlgebraic.isAlgebraic _
  have hR : IsAlgebraic R (algebraMap B L b) := (IsFractionRing.isAlgebraic_iff R K L).2 hL
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R B L)
    (IsFractionRing.injective B L)).1 hR

omit [IsDomain R] [FaithfulSMul R B] in
include K L in
/-- **The generic point is unramified**: some basic open `D(f)`, `f ≠ 0`, of `Spec B` is
formally unramified over `R`, when `L / K` is separable. -/
theorem exists_formallyUnramified_away [Algebra.EssFiniteType R B] [Algebra.IsSeparable K L] :
    ∃ f : B, f ≠ 0 ∧ Algebra.FormallyUnramified R (Localization.Away f) := by
  have h1 : FormallyUnramified R K := FormallyUnramified.of_isLocalization (nonZeroDivisors R)
  have h2 : FormallyUnramified K L := FormallyUnramified.of_isSeparable K L
  have h3 : FormallyUnramified R L := FormallyUnramified.comp R K L
  have : IsFractionRing B (Localization.AtPrime (⊥ : Ideal B)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal B).primeCompl)
  let e : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[R] L :=
    (IsLocalization.algEquiv (nonZeroDivisors B) (Localization.AtPrime (⊥ : Ideal B)) L)
      |>.restrictScalars R
  have : IsUnramifiedAt R (⊥ : Ideal B) := FormallyUnramified.of_equiv e.symm
  obtain ⟨f, hf, H⟩ := exists_formallyUnramified_of_isUnramifiedAt (R := R) (⊥ : Ideal B)
  exact ⟨f, fun h => hf (h ▸ Submodule.zero_mem _), H⟩

include K L in
/-- **Generic finite étaleness.** Let `R ⊆ B` be domains, `R` Dedekind and `B` of finite type
over `R`, with separable extension of fraction fields `L / K`. Then for some nonzero `g ∈ R` the
localization `B_g` is finite and étale over `R_g`. -/
theorem exists_finite_etale_localization [IsDedekindDomain R] [Algebra.FiniteType R B]
    [Algebra.IsSeparable K L] :
    ∃ g : R, g ≠ 0 ∧ Module.Finite (Localization.Away g) (Loc B g) ∧
      Algebra.Etale (Localization.Away g) (Loc B g) := by
  have := isAlgebraic_of_isAlgebraic_fractionRing (R := R) (B := B) K L
  obtain ⟨f, hf0, hfu⟩ := exists_formallyUnramified_away (R := R) (B := B) K L
  obtain ⟨r, hr0, hfr⟩ := exists_dvd_algebraMap (R := R) hf0
  obtain ⟨g₁, hg₁0, hint⟩ := exists_isIntegral_loc (R := R) (B := B)
  have hg0 : g₁ * r ≠ 0 := mul_ne_zero hg₁0 hr0
  refine ⟨g₁ * r, hg0, ?_⟩
  set g := g₁ * r
  have := hint g (dvd_mul_right _ _)
  set c := algebraMap R B g
  have hpow : Algebra.algebraMapSubmonoid B (Submonoid.powers g) = Submonoid.powers c :=
    Submonoid.map_powers _ _
  have hloc : IsLocalization (Submonoid.powers c) (Loc B g) := by
    rw [← hpow]
    infer_instance
  -- finite type and finiteness
  have : Algebra.FiniteType B (Loc B g) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers c) (Loc B g)
  have : Algebra.FiniteType R (Loc B g) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have : Algebra.FiniteType (Localization.Away g) (Loc B g) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have hfin : Module.Finite (Localization.Away g) (Loc B g) := Algebra.IsIntegral.finite
  -- unramified
  have hUc : FormallyUnramified R (Localization.Away c) := by
    rw [← basicOpen_subset_unramifiedLocus_iff]
    refine subset_trans ?_ (basicOpen_subset_unramifiedLocus_iff.2 hfu)
    intro p hp hpf
    exact hp (Ideal.mem_of_dvd _ (hfr.trans (map_dvd _ (dvd_mul_left r g₁))) hpf)
  have : FormallyUnramified R (Loc B g) := FormallyUnramified.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers c) (Localization.Away c) (Loc B g)).restrictScalars
      R)
  have : FormallyUnramified (Localization.Away g) (Loc B g) :=
    FormallyUnramified.of_restrictScalars R _ _
  -- flat
  have hle : Submonoid.powers g ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg0
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_localization hle
  have : IsDedekindDomain (Localization.Away g) :=
    IsLocalization.isDedekindDomain R hle (Localization.Away g)
  have := isTorsionFree_loc (B := B) hg0
  have : Algebra.FormallyEtale (Localization.Away g) (Loc B g) :=
    Stacks.FormallyEtale.formallyEtale_of_flat
  have : Algebra.FinitePresentation (Localization.Away g) (Loc B g) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  exact ⟨hfin, ⟨inferInstance, inferInstance⟩⟩

end Stacks.GenericFiniteEtale
