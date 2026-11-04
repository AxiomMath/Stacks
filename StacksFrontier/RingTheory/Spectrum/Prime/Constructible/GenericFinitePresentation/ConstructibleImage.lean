module

import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.LinearCombination
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible images (Stacks 00FH)

For a finite-type ring map, the image of a constructible set contains an open dense
subset of the closure of each of its points.

The ring-hom formulation of 00FG is proved by induction on generators, using a minimal-degree
relation in the one-generator case and gluing finite-presentation composites along the tower.
In the domain case of 00FH, localizing gives a finitely presented map, to which Chevalley's
theorem applies. A constructible set containing a point contains an open dense subset of
its closure, in any topological space. For general rings, passage to prime quotients reduces
to the domain case, and the quotient-spectrum homeomorphisms transport this subset back.
-/

@[expose] public section

open Topology

/-! ### Stacks 00FG: localizing an inclusion of domains to finite presentation -/

open Polynomial in
/-- The lift `A[1/f] → P` of a ring map `φ : A →+* P` inverting `f` is of finite presentation
iff `φ` is. -/
private lemma finitePresentation_away_lift_iff {A P : Type*} [CommRing A] [CommRing P] {f : A}
    {φ : A →+* P} (hu : IsUnit (φ f)) :
    (IsLocalization.Away.lift (S := Localization.Away f) f hu).FinitePresentation ↔
      φ.FinitePresentation := by
  have hAAf : (algebraMap A (Localization.Away f)).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr (IsLocalization.Away.finitePresentation f)
  have hcomp := IsLocalization.Away.lift_comp (S := Localization.Away f) f hu
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← hcomp]
    exact h.comp hAAf
  · exact .of_comp_finiteType (algebraMap A _) (by rw [hcomp]; exact h)
      (.of_finitePresentation hAAf)

/-- From the composite ring map `A → C → C_{ψf·g}` being finitely presented, package it back
into the `IsLocalization.Away.lift` form. -/
private lemma locFP_package {A C : Type*} [CommRing A] [CommRing C]
    (ψ : A →+* C) (f : A) (g : C)
    (coreFP : ((algebraMap C (Localization.Away (ψ f * g))).comp ψ).FinitePresentation) :
    ∃ (hu : IsUnit ((algebraMap C (Localization.Away (ψ f * g))).comp ψ f)),
      (IsLocalization.Away.lift (S := Localization.Away f)
          (P := Localization.Away (ψ f * g)) f hu).FinitePresentation := by
  have hu : IsUnit ((algebraMap C (Localization.Away (ψ f * g))).comp ψ f) := by
    rw [RingHom.comp_apply]
    exact IsLocalization.Away.isUnit_of_dvd (ψ f * g) (dvd_mul_right _ g)
  exact ⟨hu, (finitePresentation_away_lift_iff hu).2 coreFP⟩

open Polynomial in
/-- Generic last step of the transcendental branch: if `B` is finitely presented over `A`, the
composite `A → B → B_{φf·g}` is of finite presentation for any `f, g`. -/
private lemma locFP_core_of_BFP {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (f : A) (g : B) (hBfp : Algebra.FinitePresentation A B) :
    ((algebraMap B (Localization.Away (algebraMap A B f * g))).comp
        (algebraMap A B)).FinitePresentation :=
  (RingHom.finitePresentation_algebraMap.mpr
      (IsLocalization.Away.finitePresentation (algebraMap A B f * g))).comp
    (RingHom.finitePresentation_algebraMap.mpr hBfp)

open Polynomial in
/-- Bridge: the core composite `A → B → B_{φf·g}` being finitely presented is equivalent to
`B_{φf·g}` being a finitely presented `A`-algebra (for the natural scalar-tower structure). -/
private lemma locFP_core_of_PFP {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (f : A) (g : B)
    (hPFP : Algebra.FinitePresentation A (Localization.Away (algebraMap A B f * g))) :
    ((algebraMap B (Localization.Away (algebraMap A B f * g))).comp
        (algebraMap A B)).FinitePresentation := by
  rw [← IsScalarTower.algebraMap_eq]
  exact RingHom.finitePresentation_algebraMap.mpr hPFP

open Polynomial in
/-- A monic polynomial of least degree vanishing at `b` generates the kernel of `aeval b`. -/
theorem Polynomial.ker_aeval_eq_span_of_monic_of_forall_natDegree_le {D E : Type*} [CommRing D]
    [Nontrivial D] [Ring E] [Algebra D E] {b : E} {p : D[X]} (hp : p.Monic)
    (hpb : aeval b p = 0) (hmin : ∀ q : D[X], q ≠ 0 → aeval b q = 0 → p.natDegree ≤ q.natDegree) :
    RingHom.ker (aeval b : D[X] →ₐ[D] E) = Ideal.span {p} := by
  refine le_antisymm (fun q hq => ?_)
    ((Ideal.span_singleton_le_iff_mem _).2 (RingHom.mem_ker.2 hpb))
  rw [Ideal.mem_span_singleton, ← modByMonic_eq_zero_iff_dvd hp]
  by_contra h
  have hr : aeval b (q %ₘ p) = 0 := by
    rw [modByMonic_eq_sub_mul_div, map_sub, map_mul, hpb, zero_mul, sub_zero]
    exact RingHom.mem_ker.1 hq
  exact (natDegree_lt_natDegree h (degree_modByMonic_lt q hp)).not_ge (hmin _ h hr)

open Polynomial in
/-- Make a monic associate of a polynomial with unit leading coefficient over a domain. -/
private lemma locFP_monic_associate {Au : Type*} [CommRing Au] [IsDomain Au] (q : Au[X])
    (hq0 : q ≠ 0) (hlc : IsUnit q.leadingCoeff) :
    ∃ pt : Au[X], pt.Monic ∧ pt.natDegree = q.natDegree ∧ Ideal.span {pt} = Ideal.span {q} := by
  obtain ⟨c, hc⟩ := hlc.exists_left_inv
  have hcu : IsUnit c := ⟨⟨c, q.leadingCoeff, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
  have hcne : c ≠ 0 := hcu.ne_zero
  refine ⟨C c * q, ?_, ?_, ?_⟩
  · rw [Polynomial.Monic.def, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc]
  · rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hcne) hq0, Polynomial.natDegree_C,
      zero_add]
  · rw [Ideal.span_singleton_eq_span_singleton]
    exact associated_unit_mul_left q (C c) (hcu.map Polynomial.C)

open Polynomial in
/-- The algebraic-case core: if `p` is a nonzero minimal-degree polynomial in the kernel of
`aeval a`, then `B` localized away from the image of `u = p.leadingCoeff` is a finitely presented
`A`-algebra. -/
private lemma exists_finitePresentation_away_leadingCoeff_of_minimal {A B : Type*}
    [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (hinj : Function.Injective (algebraMap A B)) (a : B)
    (hgen : Algebra.adjoin A {a} = (⊤ : Subalgebra A B))
    (p : A[X]) (hp0 : p ≠ 0)
    (hpa : Polynomial.aeval a p = 0)
    (hpmin : ∀ r : A[X], r ≠ 0 → Polynomial.aeval a r = 0 → p.natDegree ≤ r.natDegree) :
    ∃ u : A, u ≠ 0 ∧ Algebra.FinitePresentation A (Localization.Away (algebraMap A B u)) := by
  have : IsDomain A := hinj.isDomain
  classical
  set u := p.leadingCoeff with hu
  have hu0 : u ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  refine ⟨u, hu0, ?_⟩
  let : Algebra (Localization.Away u) (Localization.Away (algebraMap A B u)) :=
    (Localization.awayMap (algebraMap A B) u).toAlgebra
  set Au := Localization.Away u
  set Bu := Localization.Away (algebraMap A B u)
  have hdAu : IsDomain Au := by
    have hle : (Submonoid.powers u) ≤ nonZeroDivisors A := by
      rw [Submonoid.powers_le]; exact mem_nonZeroDivisors_of_ne_zero hu0
    have : IsLocalization (Submonoid.powers u) Au := Localization.isLocalization
    exact IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers u) Au hle
  have hT : IsScalarTower A Au Bu := by
    apply IsScalarTower.of_algebraMap_eq; intro x
    rw [RingHom.algebraMap_toAlgebra]
    have hmc := IsLocalization.map_comp (S := Au) (Q := Bu) (g := algebraMap A B)
      (T := Submonoid.powers (algebraMap A B u))
      (show Submonoid.powers u ≤
          Submonoid.comap (algebraMap A B) (Submonoid.powers (algebraMap A B u)) from by
        rintro y ⟨k, rfl⟩; exact ⟨k, by simp⟩)
    have h2 := RingHom.congr_fun hmc x
    simp only [Localization.awayMap, IsLocalization.Away.map, RingHom.comp_apply] at h2 ⊢
    rw [h2, IsScalarTower.algebraMap_apply A B Bu]
  set b : Bu := algebraMap B Bu a with hb
  -- B → Bu injective (domain, nonzero denominator)
  have hBuInj : Function.Injective (algebraMap B Bu) := by
    apply IsLocalization.injective Bu (M := Submonoid.powers (algebraMap A B u))
    rw [Submonoid.powers_le]
    refine mem_nonZeroDivisors_of_ne_zero ?_
    exact (map_ne_zero_iff (algebraMap A B) hinj).mpr hu0
  -- q and its monic associate
  set q : Au[X] := p.map (algebraMap A Au) with hq
  have hAuInj : Function.Injective (algebraMap A Au) :=
    IsLocalization.injective Au
      (by rw [Submonoid.powers_le]; exact mem_nonZeroDivisors_of_ne_zero hu0)
  have hq0 : q ≠ 0 := by
    rw [hq]; exact (Polynomial.map_ne_zero_iff hAuInj).mpr hp0
  have hqlc : q.leadingCoeff = algebraMap A Au u := by
    rw [hq]; exact Polynomial.leadingCoeff_map_of_injective hAuInj p
  have hqlcU : IsUnit q.leadingCoeff := by
    rw [hqlc]; exact IsLocalization.Away.algebraMap_isUnit u
  obtain ⟨pt, hptM, hptdeg, hptspan⟩ := locFP_monic_associate q hq0 hqlcU
  -- aeval b q = 0
  have hevcomm : ∀ (P : A[X]), Polynomial.aeval b P = algebraMap B Bu (Polynomial.aeval a P) := by
    intro P
    have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom A B Bu) a P
    simpa [hb] using this
  have haevalbq : Polynomial.aeval b q = 0 := by
    rw [hq, Polynomial.aeval_map_algebraMap, hevcomm, hpa, map_zero]
  have haevalbpt : Polynomial.aeval b pt = 0 := by
    have hmem : pt ∈ Ideal.span ({q} : Set Au[X]) := by
      rw [← hptspan]; exact Ideal.mem_span_singleton_self pt
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨s, rfl⟩ := hmem
    rw [map_mul, haevalbq, zero_mul]
  -- surjectivity of aeval b over Au
  have hmemAdj : ∀ β : B, algebraMap B Bu β ∈ Algebra.adjoin Au {b} := by
    intro β
    have hβ : β ∈ Algebra.adjoin A {a} := hgen ▸ Algebra.mem_top
    induction hβ using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff] at hx; subst hx; exact Algebra.subset_adjoin rfl
    | algebraMap x =>
        rw [← IsScalarTower.algebraMap_apply A B Bu, IsScalarTower.algebraMap_apply A Au Bu]
        exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hxm hym => rw [map_add]; exact Subalgebra.add_mem _ hxm hym
    | mul x y _ _ hxm hym => rw [map_mul]; exact Subalgebra.mul_mem _ hxm hym
  have hsurjAu : Function.Surjective (Polynomial.aeval b : Au[X] →ₐ[Au] Bu) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval, eq_top_iff]
    rintro y -
    obtain ⟨⟨β, ⟨n, hn⟩⟩, hy⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A B u)) y
    simp only at hy
    rw [← hy]
    obtain ⟨k, rfl⟩ := hn
    have hAuU : IsUnit (algebraMap A Au u) := IsLocalization.Away.algebraMap_isUnit u
    obtain ⟨w, hw⟩ := hAuU.exists_left_inv
    have key : algebraMap Au Bu w * algebraMap A Bu u = 1 := by
      rw [IsScalarTower.algebraMap_apply A Au Bu u, ← map_mul, hw, map_one]
    have hmk : IsLocalization.mk' Bu β
          (⟨(algebraMap A B u) ^ k, k, rfl⟩ : Submonoid.powers (algebraMap A B u))
        = algebraMap B Bu β * (algebraMap Au Bu w) ^ k := by
      rw [eq_comm, IsLocalization.eq_mk'_iff_mul_eq, mul_assoc]
      rw [show ((⟨(algebraMap A B u) ^ k, k, rfl⟩ : Submonoid.powers (algebraMap A B u)) : B)
          = (algebraMap A B u) ^ k from rfl]
      have h1 : (algebraMap Au Bu w) ^ k * algebraMap B Bu ((algebraMap A B u) ^ k) = 1 := by
        rw [map_pow, ← mul_pow,
          show algebraMap B Bu (algebraMap A B u) = algebraMap A Bu u from
            (IsScalarTower.algebraMap_apply A B Bu u).symm, key, one_pow]
      rw [h1, mul_one]
    rw [hmk]
    exact Subalgebra.mul_mem _ (hmemAdj β)
      (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ w) k)
  -- minimality over Au
  have hminAu : ∀ r : Au[X], r ≠ 0 → Polynomial.aeval b r = 0 → pt.natDegree ≤ r.natDegree := by
    intro r hr0 hrb
    rw [hptdeg, hq, Polynomial.natDegree_map_eq_of_injective hAuInj]
    -- clear denominators: r' := integerNormalization (powers u) r ∈ A[X]
    set r' := IsLocalization.integerNormalization (Submonoid.powers u) r with hr'
    obtain ⟨c, hcmem, hcspec⟩ := IsLocalization.integerNormalization_spec (Submonoid.powers u) r
    -- aeval b r' = 0
    have hr'b : Polynomial.aeval b r' = 0 := by
      have := IsLocalization.integerNormalization_aeval_eq_zero (Submonoid.powers u) r
        (R' := Bu) (x := b) hrb
      simpa [hr'] using this
    -- aeval a r' = 0
    have har' : Polynomial.aeval a r' = 0 :=
      hBuInj (by rw [map_zero, ← hevcomm r']; exact hr'b)
    -- r' ≠ 0
    have hcne : (c : A) ≠ 0 := by
      obtain ⟨j, hj⟩ := hcmem
      rw [← hj]; exact pow_ne_zero j hu0
    have hr'0 : r' ≠ 0 := by
      have : Module.IsTorsionFree A Au :=
        Module.isTorsionFree_iff_algebraMap_injective.mpr hAuInj
      intro h
      rw [← hr', h, Polynomial.map_zero] at hcspec
      rcases (smul_eq_zero.mp hcspec.symm) with hc | hc
      · exact hcne hc
      · exact hr0 hc
    -- natDegree r' = natDegree r
    have hdeg : r'.natDegree = r.natDegree := by
      have hmap : (r'.map (algebraMap A Au)).natDegree = r.natDegree := by
        rw [hr', hcspec, ← IsScalarTower.algebraMap_smul Au c r, Polynomial.natDegree_smul]
        rw [Ne, map_eq_zero_iff _ hAuInj]; exact hcne
      rw [← hmap, Polynomial.natDegree_map_eq_of_injective hAuInj]
    rw [← hdeg]
    exact hpmin r' hr'0 har'
  -- kernel = span {pt}
  have hkerspan : RingHom.ker (Polynomial.aeval b : Au[X] →ₐ[Au] Bu).toRingHom
      = Ideal.span {pt} := by
    rw [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom]
    exact Polynomial.ker_aeval_eq_span_of_monic_of_forall_natDegree_le hptM haevalbpt hminAu
  -- A_u → B_u finite presentation
  have hAuBuFP : Algebra.FinitePresentation Au Bu := by
    have hpolyFP : Algebra.FinitePresentation Au Au[X] :=
      Algebra.FinitePresentation.polynomial Au Au
    refine Algebra.FinitePresentation.of_surjective (f := (Polynomial.aeval b : Au[X] →ₐ[Au] Bu))
      hsurjAu ?_
    rw [hkerspan]
    exact (Submodule.fg_span (Set.finite_singleton pt))
  -- A → A_u finite presentation
  have hAAuFP : Algebra.FinitePresentation A Au := IsLocalization.Away.finitePresentation u
  -- trans
  exact Algebra.FinitePresentation.trans A Au Bu

/-- For an inclusion of domains generated by one element, suitable localizations are of
finite presentation. If the evaluation kernel is zero, the algebra is a polynomial ring.
Otherwise, invert the leading coefficient of a nonzero relation of least degree.
Its monic associate generates the localized kernel by division and clearing denominators
with `IsLocalization.integerNormalization`. -/
theorem exists_finitePresentation_awayLift_of_adjoin_singleton_eq_top
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (hinj : Function.Injective (algebraMap A B)) (a : B)
    (hgen : Algebra.adjoin A {a} = (⊤ : Subalgebra A B)) :
    ∃ (f : A) (g : B), f ≠ 0 ∧ g ≠ 0 ∧
      ∃ (hu : IsUnit ((algebraMap B (Localization.Away (algebraMap A B f * g))).comp
          (algebraMap A B) f)),
        (IsLocalization.Away.lift (S := Localization.Away f)
            (P := Localization.Away (algebraMap A B f * g)) f hu).FinitePresentation := by
  have : IsDomain A := hinj.isDomain
  classical
  have hsurj : Function.Surjective (Polynomial.aeval a : Polynomial A →ₐ[A] B) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval, hgen]
  by_cases hker : RingHom.ker (Polynomial.aeval a : Polynomial A →ₐ[A] B).toRingHom = ⊥
  · -- TRANSCENDENTAL case: B ≅ A[X], take f = g = 1.
    have hBfp : Algebra.FinitePresentation A B := by
      have : Algebra.FinitePresentation A (Polynomial A) :=
        Algebra.FinitePresentation.polynomial A A
      exact Algebra.FinitePresentation.of_surjective hsurj
        (by rw [hker]; exact Submodule.fg_bot)
    refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
    exact locFP_package (algebraMap A B) 1 1 (locFP_core_of_BFP 1 1 hBfp)
  · -- ALGEBRAIC case.
    -- extract a minimal-degree nonzero polynomial in the kernel
    set I := RingHom.ker (Polynomial.aeval a : Polynomial A →ₐ[A] B).toRingHom with hI
    have hIne : ∃ pp ∈ I, pp ≠ 0 := by
      by_contra h
      push Not at h
      exact hker (by rw [eq_bot_iff]; intro x hx; simp only [Ideal.mem_bot]; exact h x hx)
    obtain ⟨p0, hp0I, hp00⟩ := hIne
    set S := {n : ℕ | ∃ r ∈ I, r ≠ 0 ∧ r.natDegree = n} with hS
    have hSne : S.Nonempty := ⟨p0.natDegree, p0, hp0I, hp00, rfl⟩
    obtain ⟨d, ⟨p, hpI, hp0, hpd⟩, hmin⟩ := Nat.lt_wfRel.wf.has_min S hSne
    have hpa : Polynomial.aeval a p = 0 := by
      have := hpI; rw [hI, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
      exact this
    have hpmin : ∀ r : Polynomial A, r ≠ 0 → Polynomial.aeval a r = 0 →
        p.natDegree ≤ r.natDegree := by
      intro r hr0 hra
      by_contra hlt
      push Not at hlt
      refine hmin r.natDegree ⟨r, ?_, hr0, rfl⟩ (show r.natDegree < d by rw [← hpd]; exact hlt)
      rw [hI, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]; exact hra
    obtain ⟨u, hu0, hPFP⟩ :=
      exists_finitePresentation_away_leadingCoeff_of_minimal hinj a hgen p hp0 hpa hpmin
    refine ⟨u, 1, hu0, one_ne_zero, ?_⟩
    apply locFP_package (algebraMap A B) u 1
    apply locFP_core_of_PFP u 1
    rwa [mul_one]

section

variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]

/-- Inverting a multiple preserves finite presentation of the composite `A → B → B[1/c]`. -/
theorem RingHom.FinitePresentation.algebraMap_away_comp_of_dvd {φ : A →+* B} {c w : B}
    (h : ((algebraMap B (Localization.Away c)).comp φ).FinitePresentation) (hcw : c ∣ w) :
    ((algebraMap B (Localization.Away w)).comp φ).FinitePresentation := by
  have hu := IsLocalization.Away.isUnit_of_dvd (S := Localization.Away w) w hcw
  have hι := (finitePresentation_away_lift_iff hu).2
    (RingHom.finitePresentation_algebraMap.2 (IsLocalization.Away.finitePresentation w))
  rw [← IsLocalization.Away.lift_comp (S := Localization.Away c) c hu, RingHom.comp_assoc]
  exact hι.comp h

/-- Finite presentation of `A → A'[1/g₁]` and `A' → B[1/w]` glues if the image of `g₁`
divides `w`. -/
theorem RingHom.FinitePresentation.algebraMap_away_comp_comp {φ₁ : A →+* A'} {φ₂ : A' →+* B}
    {g₁ : A'} {w : B} (h₁ : ((algebraMap A' (Localization.Away g₁)).comp φ₁).FinitePresentation)
    (h₂ : ((algebraMap B (Localization.Away w)).comp φ₂).FinitePresentation) (hdvd : φ₂ g₁ ∣ w) :
    ((algebraMap B (Localization.Away w)).comp (φ₂.comp φ₁)).FinitePresentation := by
  have hu : IsUnit (((algebraMap B (Localization.Away w)).comp φ₂) g₁) := by
    rw [RingHom.comp_apply]
    exact IsLocalization.Away.isUnit_of_dvd w hdvd
  rw [← RingHom.comp_assoc, ← IsLocalization.Away.lift_comp (S := Localization.Away g₁) g₁ hu,
    RingHom.comp_assoc]
  exact ((finitePresentation_away_lift_iff hu).2 h₂).comp h₁

end

/-- Generic finite presentation is transitive across injective maps, provided the final
target has no zero divisors. -/
theorem exists_finitePresentation_awayLift_comp
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [NoZeroDivisors C]
    (ψ₁ : A →+* B) (ψ₂ : B →+* C)
    (hinj₂ : Function.Injective ψ₂)
    (h₁ : ∃ (f : A) (g : B), f ≠ 0 ∧ g ≠ 0 ∧
        ∃ (hu : IsUnit ((algebraMap B (Localization.Away (ψ₁ f * g))).comp ψ₁ f)),
          (IsLocalization.Away.lift (S := Localization.Away f)
              (P := Localization.Away (ψ₁ f * g)) f hu).FinitePresentation)
    (h₂ : ∃ (f : B) (g : C), f ≠ 0 ∧ g ≠ 0 ∧
        ∃ (hu : IsUnit ((algebraMap C (Localization.Away (ψ₂ f * g))).comp ψ₂ f)),
          (IsLocalization.Away.lift (S := Localization.Away f)
              (P := Localization.Away (ψ₂ f * g)) f hu).FinitePresentation) :
    ∃ (f : A) (g : C), f ≠ 0 ∧ g ≠ 0 ∧
      ∃ (hu : IsUnit ((algebraMap C (Localization.Away ((ψ₂.comp ψ₁) f * g))).comp (ψ₂.comp ψ₁) f)),
        (IsLocalization.Away.lift (S := Localization.Away f)
            (P := Localization.Away ((ψ₂.comp ψ₁) f * g)) f hu).FinitePresentation := by
  obtain ⟨f₁, g₁, hf₁, hg₁, hu₁, hfp₁⟩ := h₁
  obtain ⟨f₂, g₂, hf₂, hg₂, hu₂, hfp₂⟩ := h₂
  refine ⟨f₁, ψ₂ g₁ * (ψ₂ f₂ * g₂), hf₁, mul_ne_zero ((map_ne_zero_iff ψ₂ hinj₂).2 hg₁)
    (mul_ne_zero ((map_ne_zero_iff ψ₂ hinj₂).2 hf₂) hg₂), locFP_package (ψ₂.comp ψ₁) f₁ _ ?_⟩
  refine ((finitePresentation_away_lift_iff hu₁).1 hfp₁).algebraMap_away_comp_comp
    (((finitePresentation_away_lift_iff hu₂).1 hfp₂).algebraMap_away_comp_of_dvd
      ((dvd_mul_left _ _).mul_left _)) ?_
  rw [RingHom.comp_apply, map_mul, ← mul_assoc]
  exact dvd_mul_right _ _

/-- **Stacks 00FG (Lemma 10.30.1): localizing an inclusion of domains to finite presentation.**

Let `R ⊆ S` (`φ` injective) be a finite-type inclusion of integral domains. Then there exist
nonzero `f ∈ R` and `g ∈ S` such that, inverting `f` in `R` and `φf·g` in `S`, the induced ring
map `R_f → S_{φf·g}` is of *finite presentation*. (`IsLocalization.Away.lift f hu` is exactly
the induced map `R_f → S_{φf·g}`, where `hu` witnesses that `φ f` is a unit in `S_{φf·g}`.) -/
theorem exists_localization_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (hφ : φ.FiniteType) (hinj : Function.Injective φ) :
    ∃ (f : R) (g : S), f ≠ 0 ∧ g ≠ 0 ∧
      ∃ (hu : IsUnit ((algebraMap S (Localization.Away (φ f * g))).comp φ f)),
        (IsLocalization.Away.lift (S := Localization.Away f)
            (P := Localization.Away (φ f * g)) f hu).FinitePresentation := by
  have : IsDomain R := hinj.isDomain
  classical
  let := φ.toAlgebra
  have hft : Algebra.FiniteType R S := hφ
  obtain ⟨s, hs⟩ := hft.out
  -- injectivity of any algebraMap R (Algebra.adjoin R ...)
  have hinjAdj : ∀ (B : Subalgebra R S), Function.Injective (algebraMap R B) := fun B =>
    .of_comp (f := algebraMap B S) (by rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq])
  -- The tower-induction key claim
  have key : ∀ t : Finset S,
      ∃ (f : R) (g : (Algebra.adjoin R (↑t : Set S))), f ≠ 0 ∧ g ≠ 0 ∧
        ∃ (hu : IsUnit ((algebraMap _ (Localization.Away
            (algebraMap R (Algebra.adjoin R (↑t : Set S)) f * g))).comp
              (algebraMap R (Algebra.adjoin R (↑t : Set S))) f)),
          (IsLocalization.Away.lift (S := Localization.Away f)
              (P := Localization.Away (algebraMap R (Algebra.adjoin R (↑t : Set S)) f * g))
              f hu).FinitePresentation := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        set B0 := Algebra.adjoin R (↑(∅ : Finset S) : Set S) with hB0
        have hsurj : Function.Surjective (algebraMap R B0) := by
          rintro ⟨x, hx⟩
          rw [hB0, Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot, Set.mem_range] at hx
          exact hx.imp fun r hr => Subtype.ext hr
        have hRB0fp : (algebraMap R B0).FinitePresentation := .of_bijective ⟨hinjAdj B0, hsurj⟩
        refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
        apply locFP_package (algebraMap R B0) 1 1
        exact (RingHom.finitePresentation_algebraMap.mpr
          (IsLocalization.Away.finitePresentation (algebraMap R B0 1 * 1))).comp hRB0fp
    | @insert a t hat ih =>
        set Bt := Algebra.adjoin R (↑t : Set S) with hBt
        set Bi := Algebra.adjoin R (↑(insert a t) : Set S) with hBi
        have hle : Bt ≤ Bi := Algebra.adjoin_mono (Finset.coe_subset.mpr (Finset.subset_insert a t))
        have haBi : a ∈ Bi := Algebra.subset_adjoin (by simp)
        let : Algebra Bt Bi := (Subalgebra.inclusion hle).toAlgebra
        let ψ₁ : R →+* Bt := algebraMap R Bt
        let ψ₂ : Bt →+* Bi := (Subalgebra.inclusion hle).toRingHom
        have hi2 : Function.Injective ψ₂ := Subalgebra.inclusion_injective hle
        have hamBtBi : (algebraMap Bt Bi) = ψ₂ := RingHom.algebraMap_toAlgebra _
        have hgen : Algebra.adjoin Bt {(⟨a, haBi⟩ : Bi)} = (⊤ : Subalgebra Bt Bi) := by
          rw [_root_.eq_top_iff]
          rintro ⟨x, hx⟩ -
          induction hx using Algebra.adjoin_induction with
          | mem y hy =>
              simp only [Finset.coe_insert, Set.mem_insert_iff] at hy
              rcases hy with rfl | hyt
              · exact Algebra.subset_adjoin (by simp)
              · have hyBt : y ∈ Bt := Algebra.subset_adjoin hyt
                have hrw : (⟨y, hle hyBt⟩ : Bi) = algebraMap Bt Bi ⟨y, hyBt⟩ := by
                  rw [hamBtBi]
                  exact (Subalgebra.inclusion_mk hle y hyBt).symm
                rw [hrw]
                exact Subalgebra.algebraMap_mem _ _
          | algebraMap r =>
              have hrw : (⟨(algebraMap R S) r, Subalgebra.algebraMap_mem Bi r⟩ : Bi)
                  = algebraMap Bt Bi (algebraMap R Bt r) := by
                rw [hamBtBi]
                exact ((Subalgebra.inclusion hle).commutes r).symm
              rw [hrw]
              exact Subalgebra.algebraMap_mem _ _
          | add x y hx hy hhx hhy => exact Subalgebra.add_mem _ hhx hhy
          | mul x y hx hy hhx hhy => exact Subalgebra.mul_mem _ hhx hhy
        have hloc2 : ∃ (f : Bt) (g : Bi), f ≠ 0 ∧ g ≠ 0 ∧
            ∃ (hu : IsUnit ((algebraMap Bi (Localization.Away (ψ₂ f * g))).comp ψ₂ f)),
              (IsLocalization.Away.lift (S := Localization.Away f)
                  (P := Localization.Away (ψ₂ f * g)) f hu).FinitePresentation := by
          have := exists_finitePresentation_awayLift_of_adjoin_singleton_eq_top
            (A := Bt) (B := Bi) (by rwa [hamBtBi]) ⟨a, haBi⟩ hgen
          rwa [hamBtBi] at this
        have hcomp : ψ₂.comp ψ₁ = algebraMap R Bi :=
          AlgHom.comp_algebraMap (Subalgebra.inclusion hle)
        have hfin := exists_finitePresentation_awayLift_comp ψ₁ ψ₂ hi2 ih hloc2
        rwa [hcomp] at hfin
  -- apply key at s, transport ⊤ → S
  set Bs := Algebra.adjoin R (↑s : Set S) with hBsdef
  let χ₁ : R →+* Bs := algebraMap R Bs
  let χ₂ : Bs →+* S := algebraMap Bs S
  have hχi2 : Function.Injective χ₂ := FaithfulSMul.algebraMap_injective Bs S
  have hχgen : Algebra.adjoin Bs {(0 : S)} = (⊤ : Subalgebra Bs S) := by
    rw [_root_.eq_top_iff]
    intro x _
    simpa [Algebra.mem_bot] using (hs ▸ Algebra.mem_top : x ∈ Bs)
  have hloc2 : ∃ (f : Bs) (g : S), f ≠ 0 ∧ g ≠ 0 ∧
      ∃ (hu : IsUnit ((algebraMap S (Localization.Away (χ₂ f * g))).comp χ₂ f)),
        (IsLocalization.Away.lift (S := Localization.Away f)
            (P := Localization.Away (χ₂ f * g)) f hu).FinitePresentation :=
    exists_finitePresentation_awayLift_of_adjoin_singleton_eq_top (A := Bs) (B := S) hχi2 0 hχgen
  have hcomp2 : χ₂.comp χ₁ = φ := (IsScalarTower.algebraMap_eq R Bs S).symm
  have hfin := exists_finitePresentation_awayLift_comp χ₁ χ₂ hχi2 (key s) hloc2
  rwa [hcomp2] at hfin

/-! ### The topological core, and the case of domains -/

/-- Every point of a constructible set has an open neighbourhood whose intersection with
the closure of the point lies in the set. -/
@[stacks 005K "constructible case, (3) ⇒ (1)"]
theorem Topology.IsConstructible.exists_isOpen_inter_closure_singleton_subset {X : Type*}
    [TopologicalSpace X] {s : Set X} (hs : IsConstructible s) {x : X} (hx : x ∈ s) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ closure {x} ⊆ s := by
  suffices H : (∀ x ∈ s, ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ closure {x} ⊆ s) ∧
      ∀ x ∈ sᶜ, ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ closure {x} ⊆ sᶜ from H.1 x hx
  clear hx x
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    refine ⟨fun x hx => ⟨U, hU, hx, Set.inter_subset_left⟩,
      fun x hx => ⟨Set.univ, isOpen_univ, Set.mem_univ x, ?_⟩⟩
    rw [Set.univ_inter]
    exact closure_minimal (Set.singleton_subset_iff.2 hx) hU.isClosed_compl
  | union s _ t _ hs ht =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rcases hx with hx | hx
      · obtain ⟨U, hU, hxU, h⟩ := hs.1 x hx
        exact ⟨U, hU, hxU, h.trans Set.subset_union_left⟩
      · obtain ⟨U, hU, hxU, h⟩ := ht.1 x hx
        exact ⟨U, hU, hxU, h.trans Set.subset_union_right⟩
    · rw [Set.compl_union] at hx ⊢
      obtain ⟨U, hU, hxU, h⟩ := hs.2 x hx.1
      obtain ⟨V, hV, hxV, h'⟩ := ht.2 x hx.2
      exact ⟨U ∩ V, hU.inter hV, Set.mem_inter hxU hxV,
        Set.subset_inter ((Set.inter_subset_inter_left _ Set.inter_subset_left).trans h)
          ((Set.inter_subset_inter_left _ Set.inter_subset_right).trans h')⟩
  | compl s _ hs => exact ⟨hs.2, by rw [compl_compl]; exact hs.1⟩

/-- If an open neighbourhood of `x` meets `closure {x}` only in `T`, then `T` contains
an open dense subset of `closure {x}`. -/
theorem exists_isOpen_dense_subset_closure_singleton_of_isOpen {X : Type*} [TopologicalSpace X]
    {x : X} {U T : Set X} (hU : IsOpen U) (hxU : x ∈ U) (hUT : U ∩ closure {x} ⊆ T) :
    ∃ D : Set (closure {x} : Set X), IsOpen D ∧ Dense D ∧ Subtype.val '' D ⊆ closure {x} ∩ T := by
  have := Subtype.preirreducibleSpace (isIrreducible_singleton (x := x)).closure.isPreirreducible
  have hD : IsOpen (Subtype.val ⁻¹' U : Set (closure {x} : Set X)) :=
    hU.preimage continuous_subtype_val
  refine ⟨_, hD, hD.dense (Set.nonempty_of_mem (x := ⟨x, isGenericPoint_closure.mem⟩)
    (Set.mem_preimage.2 hxU)), ?_⟩
  rw [Subtype.image_preimage_coe]
  exact Set.subset_inter Set.inter_subset_left ((Set.inter_comm _ _).subset.trans hUT)

/-- A constructible set containing `ξ` contains an open dense subset of `closure {ξ}`.
This is the constructible case of Stacks 005K, (3) ⇒ (1). -/
@[sga "1 IV 6.1" "special case"]
theorem Topology.IsConstructible.exists_isOpen_dense_subset_closure_singleton
    {X : Type*} [TopologicalSpace X] {C : Set X}
    (hC : Topology.IsConstructible C) {ξ : X} (hξ : ξ ∈ C) :
    ∃ D : Set (closure {ξ} : Set X),
      IsOpen D ∧ Dense D ∧ Subtype.val '' D ⊆ C := by
  obtain ⟨U, hU, hξU, hUC⟩ := hC.exists_isOpen_inter_closure_singleton_subset hξ
  obtain ⟨D, hD, hDd, hDs⟩ := exists_isOpen_dense_subset_closure_singleton_of_isOpen hU hξU hUC
  exact ⟨D, hD, hDd, hDs.trans Set.inter_subset_right⟩

/-- A commuting square of ring maps gives a commuting square of `PrimeSpectrum.comap`s. -/
private lemma comap_comap_eq_of_comp_eq {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T]
    [CommRing U] {f : R →+* S} {g : S →+* U} {h : R →+* T} {k : T →+* U}
    (H : g.comp f = k.comp h) (z : PrimeSpectrum U) :
    PrimeSpectrum.comap f (PrimeSpectrum.comap g z) =
      PrimeSpectrum.comap h (PrimeSpectrum.comap k z) := by
  rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, H]

/-- **The special case of 00FH for a finite-type injection of domains, at the generic points.**

Let `φ : R →+* S` be an injective finite-type map of integral domains. Let `E ⊆ Spec S` be
constructible and contain the generic point `η = (0)` of `Spec S`. Then `f(E)` contains a dense
open subset of `closure {ξ}`, where `ξ = (0)` is the generic point of `Spec R`.

The proof assembles Stacks 00FG, finite-presentation Chevalley, and the topological core.
1. By `exists_localization_finitePresentation` get nonzero `f ∈ R`, `g ∈ S` with
   `R_f → S_{φf·g}` of finite presentation.
2. `D(f) ⊆ Spec R` is a dense open containing `ξ = (0)` (as `f ≠ 0` in the domain `R`); likewise
   `D(φf·g) ⊆ Spec S` is open and contains `η = (0)`. Under `comap φ`, `D(φf·g) → D(f)` is the
   comap of the finite-presentation map `R_f → S_{φf·g}` (localization functoriality on spectra:
   `PrimeSpectrum.localization_away_comap_range`, `IsLocalization.Away`).
3. `E ∩ D(φf·g)` is constructible (intersection of constructible `E` with the retrocompact open
   `D(φf·g)`); its image `f(E ∩ D(φf·g)) ⊆ D(f)` is constructible by finite-presentation
   Chevalley `PrimeSpectrum.isConstructible_comap_image`, and contains `ξ = f(η)`.
4. Apply `exists_open_dense_in_closure_of_constructible` to this constructible set in `Spec R`:
   it contains an open dense subset `D` of `closure {ξ} = Spec R`, and
   `D ⊆ f(E ∩ D(φf·g)) ⊆ f(E)`. -/
theorem exists_open_dense_subset_comap_image_of_injective
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (φ : R →+* S) (hφ : φ.FiniteType) (hinj : Function.Injective φ)
    (E : Set (PrimeSpectrum S)) (hE : Topology.IsConstructible E)
    (hηE : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) ∈ E) :
    ∃ D : Set (closure {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} : Set (PrimeSpectrum R)),
      IsOpen D ∧ Dense D ∧
      Subtype.val '' D ⊆ PrimeSpectrum.comap φ '' E := by
  obtain ⟨f, g, hf, hg, hu, hfp⟩ := exists_localization_finitePresentation φ hφ hinj
  set A := Localization.Away f with hA
  set B := Localization.Away (φ f * g) with hB
  set ψ := IsLocalization.Away.lift (S := A) (P := B) f hu with hψ
  -- composition compatibility: `ψ ∘ (R → A) = (S → B) ∘ φ`
  have hcomp : ψ.comp (algebraMap R A) = (algebraMap S B).comp φ := by
    rw [hψ]; exact IsLocalization.Away.lift_comp f hu
  -- `φf·g ≠ 0` (as `φ` is injective and `R`, `S` are domains)
  have hfg : φ f * g ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨fun h => hf ((map_eq_zero_iff φ hinj).mp h), hg⟩
  -- open embeddings of the two localization spectra onto basic opens
  have hoeA : IsOpenEmbedding (PrimeSpectrum.comap (algebraMap R A)) :=
    PrimeSpectrum.localization_away_isOpenEmbedding A f
  have hoeB : IsOpenEmbedding (PrimeSpectrum.comap (algebraMap S B)) :=
    PrimeSpectrum.localization_away_isOpenEmbedding B (φ f * g)
  -- the constructible chain  `E ↦ E_B ↦ comap ψ '' E_B ↦ C₀`
  have hEB : Topology.IsConstructible (PrimeSpectrum.comap (algebraMap S B) ⁻¹' E) :=
    hE.preimage_of_isOpenEmbedding hoeB
  have hImg : Topology.IsConstructible
      (PrimeSpectrum.comap ψ '' (PrimeSpectrum.comap (algebraMap S B) ⁻¹' E)) :=
    PrimeSpectrum.isConstructible_comap_image hfp hEB
  have hrange : IsRetrocompact (Set.range (PrimeSpectrum.comap (algebraMap R A))) := by
    rw [PrimeSpectrum.localization_away_comap_range A f]
    exact PrimeSpectrum.isRetrocompact_basicOpen
  set C₀ := PrimeSpectrum.comap (algebraMap R A) ''
      (PrimeSpectrum.comap ψ '' (PrimeSpectrum.comap (algebraMap S B) ⁻¹' E)) with hC₀
  have hC₀c : Topology.IsConstructible C₀ :=
    hImg.image_of_isOpenEmbedding hoeA hrange
  -- `C₀ ⊆ comap φ '' E` (using the commuting square and `image_preimage ⊆ id`)
  have hsub : C₀ ⊆ PrimeSpectrum.comap φ '' E := by
    rw [hC₀, Set.image_image]
    have heq : (fun x => PrimeSpectrum.comap (algebraMap R A) (PrimeSpectrum.comap ψ x))
        = PrimeSpectrum.comap φ ∘ PrimeSpectrum.comap (algebraMap S B) :=
      funext (comap_comap_eq_of_comp_eq hcomp)
    rw [heq, Set.image_comp]
    exact Set.image_mono (Set.image_preimage_subset _ _)
  -- the generic points `ξ = (0) ∈ Spec R`, `η = (0) ∈ Spec S`, with `ξ = comap φ η`
  set ξ : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩ with hξdef
  set η : PrimeSpectrum S := ⟨⊥, Ideal.isPrime_bot⟩ with hηdef
  have hξη : ξ = PrimeSpectrum.comap φ η := by
    apply PrimeSpectrum.ext
    simp only [PrimeSpectrum.comap_asIdeal, hξdef, hηdef]
    rw [Ideal.comap_bot_of_injective φ hinj]
  -- `η ∈ D(φf·g) = range (comap (S → B))`, so it lifts to some `ηB ∈ Spec B`
  have hηmem : η ∈ (PrimeSpectrum.basicOpen (φ f * g) : Set (PrimeSpectrum S)) := by
    simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hηdef, Ideal.mem_bot]
    exact hfg
  rw [← PrimeSpectrum.localization_away_comap_range B (φ f * g)] at hηmem
  obtain ⟨ηB, hηB⟩ := hηmem
  -- `ξ ∈ C₀`
  have hξC₀ : ξ ∈ C₀ := by
    rw [hC₀]
    refine ⟨PrimeSpectrum.comap ψ ηB, ⟨ηB, ?_, rfl⟩, ?_⟩
    · rw [Set.mem_preimage]
      rw [hηB]; exact hηE
    · rw [comap_comap_eq_of_comp_eq hcomp, hηB, ← hξη]
  -- apply (D) to the constructible set `C₀ ∋ ξ`
  obtain ⟨D, hDopen, hDdense, hDsub⟩ :=
    hC₀c.exists_isOpen_dense_subset_closure_singleton hξC₀
  exact ⟨D, hDopen, hDdense, hDsub.trans hsub⟩

/-! ### Main statement -/

/-- **Stacks 00FH (Lemma 10.30.2).**  Let `φ : R →+* S` be a ring map of finite type, let
`E ⊆ Spec S` be constructible, and let `ξ ∈ Spec R` lie in the image `f(E)` of `E` under
`f = PrimeSpectrum.comap φ`.  Then `closure {ξ} ∩ f(E)` contains a subset `D` that is open and
dense in the subspace `closure {ξ}`. -/
@[stacks 00FH]
theorem image_constructible_contains_open_dense_in_closure
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : φ.FiniteType)
    (E : Set (PrimeSpectrum S)) (hE : Topology.IsConstructible E)
    (ξ : PrimeSpectrum R)
    (hξ : ξ ∈ PrimeSpectrum.comap φ '' E) :
    ∃ D : Set (closure {ξ} : Set (PrimeSpectrum R)),
      IsOpen D ∧ Dense D ∧
      (Subtype.val '' D) ⊆ closure {ξ} ∩ (PrimeSpectrum.comap φ '' E) := by
  -- Reduction to the domains special case `exists_open_dense_subset_comap_image_of_injective`.
  --
  -- Choose `η ∈ E` with `comap φ η = ξ`; set `𝔭 = ξ.asIdeal`, `𝔮 = η.asIdeal`. Then
  -- `φ⁻¹(𝔮) = 𝔭`, so `φ` descends to an injective finite-type map of domains
  -- `φ̄ : R/𝔭 → S/𝔮`. Let `πR : R →+* R/𝔭`, `πS : S →+* S/𝔮` be the quotient maps with comaps
  -- `cR := comap πR`, `cS := comap πS` (closed immersions onto `V(𝔭) = closure {ξ}`, `V(𝔮)`).
  --   * `E' := cS ⁻¹' E` is constructible in `Spec (S/𝔮)` by the preimage direction
  --     (`Topology.IsConstructible.preimage`, using compact preimages), and the
  --     generic point `η' = (0)` of `Spec (S/𝔮)` lies in `E'` since `cS η' = η ∈ E`.
  --   * Apply `exists_open_dense_subset_comap_image_of_injective φ̄ … E' … (η' ∈ E')` to get
  --     `D'` open dense in `closure {ξ'} = Spec (R/𝔭)` with `Subtype.val '' D' ⊆ comap φ̄ '' E'`.
  --   * Transport `D'` through the homeomorphism `cR : Spec (R/𝔭) ≃ₜ V(𝔭) = closure {ξ}`
  --     (`PrimeSpectrum.comap` of a surjection is a closed embedding onto `V(ker)`; here
  --     `ker πR = 𝔭`). The commuting square `cR ∘ comap φ̄ = comap φ ∘ cS` then gives
  --     `Subtype.val '' D ⊆ closure {ξ} ∩ (comap φ '' E)` for the transported `D`.
  --
  -- The reduction uses only the preimage direction of constructibility, together with the
  -- standard quotient-spectrum and closed-immersion API.  Chevalley's theorem in the form
  -- `IsConstructible (comap φ '' E)` is not available for a mere finite-type map, which is why
  -- the route through the case of domains is taken.
  obtain ⟨η, hηE, hηξ⟩ := hξ
  -- 𝔭 = comap φ 𝔮
  have hpq : ξ.asIdeal = Ideal.comap φ η.asIdeal := by
    rw [← hηξ, PrimeSpectrum.comap_asIdeal]
  -- quotient maps
  set πR := Ideal.Quotient.mk ξ.asIdeal with hπR
  set πS := Ideal.Quotient.mk η.asIdeal with hπS
  -- induced map
  have hle : ξ.asIdeal ≤ Ideal.comap φ η.asIdeal := hpq.le
  set φbar := Ideal.quotientMap η.asIdeal φ hle with hφbar
  -- compatibility
  have hcompat : φbar.comp πR = πS.comp φ := Ideal.quotientMap_comp_mk hle
  -- injectivity
  have hinj : Function.Injective φbar :=
    Ideal.quotientMap_injective' hpq.ge
  -- domain instances
  have : IsDomain (R ⧸ ξ.asIdeal) := Ideal.Quotient.isDomain ξ.asIdeal
  have : IsDomain (S ⧸ η.asIdeal) := Ideal.Quotient.isDomain η.asIdeal
  -- surjectivity of quotient maps
  have hπRsurj : Function.Surjective πR := Ideal.Quotient.mk_surjective
  have hπSsurj : Function.Surjective πS := Ideal.Quotient.mk_surjective
  -- finite type of φbar
  have hφbarft : φbar.FiniteType :=
    .of_comp_finiteType (f := πR) (hcompat ▸ hφ.comp_surjective hπSsurj)
  -- comaps of quotient maps are closed embeddings
  set cR := PrimeSpectrum.comap πR with hcR
  set cS := PrimeSpectrum.comap πS with hcS
  have hceR : IsClosedEmbedding cR :=
    PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ πR hπRsurj
  have hceS : IsClosedEmbedding cS :=
    PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ πS hπSsurj
  -- `E' := cS ⁻¹' E` is constructible (preimage under the closed embedding `cS`)
  set E' := cS ⁻¹' E with hE'
  have hE'c : Topology.IsConstructible E' :=
    .preimage hceS.continuous (fun t htopen htretro => (hceS.isCompact_preimage
      htretro.isCompact).isRetrocompact (htopen.preimage hceS.continuous)) hE
  -- generic point of `Spec (S ⧸ 𝔮)`
  set η' : PrimeSpectrum (S ⧸ η.asIdeal) := ⟨⊥, Ideal.isPrime_bot⟩ with hη'def
  -- `cS η' = η`
  have hcSη' : cS η' = η := by
    apply PrimeSpectrum.ext
    rw [hcS, PrimeSpectrum.comap_asIdeal, hη'def, ← RingHom.ker_eq_comap_bot, hπS, Ideal.mk_ker]
  -- apply the domains lemma
  obtain ⟨D', hD'open, hD'dense, hD'sub⟩ :=
    exists_open_dense_subset_comap_image_of_injective φbar hφbarft hinj E' hE'c
      (by rwa [hE', Set.mem_preimage, hcSη'])
  -- `range cR = closure {ξ} = zeroLocus 𝔭`
  have hrange : Set.range cR = (closure {ξ} : Set (PrimeSpectrum R)) := by
    rw [PrimeSpectrum.closure_singleton]
    ext p
    rw [PrimeSpectrum.mem_range_comap_iff]
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    rw [Ideal.comap_map_of_surjective _ hπRsurj, ← RingHom.ker_eq_comap_bot, hπR, Ideal.mk_ker]
    exact ⟨fun h => h ▸ le_sup_right, sup_eq_left.mpr⟩
  -- the generic point of `Spec (R ⧸ 𝔭)` (must use the literal term to match `D'`'s type)
  -- `closure {ξ'} = univ`
  have hξ'closure :
      (closure {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (R ⧸ ξ.asIdeal))} :
        Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) = Set.univ := by
    rw [PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  -- commuting square: `cR ∘ comap φbar = comap φ ∘ cS`
  have hsquare : ∀ z, cR (PrimeSpectrum.comap φbar z) = PrimeSpectrum.comap φ (cS z) :=
    comap_comap_eq_of_comp_eq hcompat
  -- homeomorphisms
  -- `e1 : ↥(closure {ξ'}) ≃ₜ PrimeSpectrum (R ⧸ 𝔭)`
  let e1 :
      (closure {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (R ⧸ ξ.asIdeal))} :
        Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ≃ₜ PrimeSpectrum (R ⧸ ξ.asIdeal) :=
    (Homeomorph.setCongr hξ'closure).trans (Homeomorph.Set.univ _)
  -- `e2 : PrimeSpectrum (R ⧸ 𝔭) ≃ₜ ↥(closure {ξ})`
  let e2 : PrimeSpectrum (R ⧸ ξ.asIdeal) ≃ₜ (closure {ξ} : Set (PrimeSpectrum R)) :=
    (Topology.IsEmbedding.toHomeomorph hceR.isEmbedding).trans (Homeomorph.setCongr hrange)
  let eRtot :
      (closure {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (R ⧸ ξ.asIdeal))} :
        Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ≃ₜ (closure {ξ} : Set (PrimeSpectrum R)) :=
    e1.trans e2
  -- key: `Subtype.val (eRtot y) = cR (Subtype.val y)`
  have hval : ∀ y : (closure {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (R ⧸ ξ.asIdeal))} :
        Set (PrimeSpectrum (R ⧸ ξ.asIdeal))),
      (eRtot y : PrimeSpectrum R) = cR (y : PrimeSpectrum (R ⧸ ξ.asIdeal)) := by
    intro y
    simp [eRtot, e1, e2, Homeomorph.setCongr]
  refine ⟨eRtot '' D', ?_, ?_, ?_⟩
  · exact eRtot.isOpen_image.mpr hD'open
  · -- dense
    rw [dense_iff_closure_eq, ← Homeomorph.image_closure, hD'dense.closure_eq]
    simp
  · -- inclusion
    rintro p ⟨x, hxD, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hxD
    refine ⟨(eRtot y).property, ?_⟩
    rw [hval y]
    obtain ⟨z, hzE', hz⟩ := hD'sub ⟨y, hy, rfl⟩
    rw [← hz, hsquare z]
    exact ⟨cS z, hzE', rfl⟩
