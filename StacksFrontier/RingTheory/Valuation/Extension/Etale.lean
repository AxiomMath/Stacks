module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.RingTheory.Finiteness.Descent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Smooth.Normal
public import StacksFrontier.RingTheory.Valuation.Extension.Defs
public import StacksFrontier.RingTheory.Valuation.Extension.FundamentalInequality

/-!
# Etale and henselian extensions of valuation rings

Let `A` be a valuation ring. Localizing an etale `A`-algebra at a prime lying over the maximal
ideal of `A` gives a weakly unramified extension of valuation rings. The same holds for the
henselization and the strict henselization of `A`, which are themselves valuation rings, because
each is a filtered colimit of etale `A`-algebras.

## Main definitions

No new definitions are introduced; the notions used are those of
`StacksFrontier.RingTheory.Valuation.Extension.Defs`.

## Main results

* `ValuationRing.isWeaklyUnramified_localization_atPrime_of_etale`: an etale algebra over a
  valuation ring, localized at a prime over the maximal ideal, is a weakly unramified extension
  of valuation rings.
* `ValuationRing.isWeaklyUnramified_henselization_and_strictHenselization`: the henselization and
  the strict henselization of a valuation ring are valuation rings, and both canonical inclusions
  are weakly unramified extensions.

## Implementation notes

The domain and valuation-ring structures on a localization of an etale algebra, and on a
henselization, are part of the conclusion rather than hypotheses, so the corresponding instances
are existentially quantified before the extension and weak-unramifiedness assertions.

Henselizations and strict henselizations are represented by arbitrary models satisfying
`IsLocalRing.IsHenselization`; the ind-etale hypothesis feeding the etale argument is that
class's `ind_etale` field. The canonical map from the henselization to the strict henselization is
specified by the algebra tower and its local-ring-map instance.

Surjectivity of the value-group map is obtained from the fundamental inequality of Tag 0ASH via
`ValuationRing.valueGroupMap_range_eq_valueGroupHom_range`, which is what makes the index of the
range of `valueGroupHom` a statement about `valueGroupMap`.

## References

* [Stacks, Tag 0ASJ](https://stacks.math.columbia.edu/tag/0ASJ)
* [Stacks, Tag 0ASK](https://stacks.math.columbia.edu/tag/0ASK)
-/

@[expose] public section

set_option maxRecDepth 4096

universe u v w

open IsLocalRing ValuationRing

section EtaleExtension

open TensorProduct

namespace ValuationRing

private lemma valuationRing_of_flat_ideals (R : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] (h : ∀ I : Ideal R, Module.Flat R I) : ValuationRing R := by
  have hb : IsBezout R := by
    rw [IsBezout.iff_span_pair_isPrincipal]
    intro a b
    let I : Ideal R := Ideal.span {a, b}
    let : Module.Flat R I := h I
    have : Module.Finite R I := Module.Finite.iff_fg.mpr (by
      simpa [I] using (Submodule.fg_span (s := ({a, b} : Set R)) (by simp)))
    let : Module.Free R I := Module.free_of_flat_of_isLocalRing
    apply (Submodule.rank_le_one_iff_isPrincipal I).mp
    calc
      Module.rank R I ≤ Module.rank R R := Submodule.rank_le I
      _ = 1 := by simp
  exact ValuationRing.iff_local_bezout_domain.mpr ⟨inferInstance, hb⟩

private alias isNormalRing_of_domain := IsNormalRing.of_isIntegrallyClosed


private lemma isDomain_localization_atPrime_of_etale
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (m : Ideal B) [m.IsPrime] :
    IsDomain (Localization.AtPrime m) := by
  have hB : IsNormalRing B :=
    Algebra.isNormalRing_of_smooth A B (isNormalRing_of_domain A)
  exact (hB m).1

private lemma isLocalHom_localization_atPrime_of_liesOver
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B]
    (m : Ideal B) [m.IsPrime] (hm : m.LiesOver (maximalIdeal A)) :
    IsLocalHom (algebraMap A (Localization.AtPrime m)) := by
  let : IsLocalRing A := inferInstance
  let : IsLocalRing (Localization.AtPrime m) := inferInstance
  have : IsScalarTower A B (Localization.AtPrime m) := inferInstance
  apply IsLocalHom.mk
  intro a ha
  by_contra hna
  have hmem : a ∈ maximalIdeal A := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hna
  have hmap : algebraMap A B a ∈ m := by
    change a ∈ m.under A
    simpa only [← hm.over] using hmem
  have hmap' := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime m) m (algebraMap A B a)).2 hmap
  have hunit : IsUnit ((algebraMap B (Localization.AtPrime m)) (algebraMap A B a)) := by
    rwa [IsScalarTower.algebraMap_apply A B (Localization.AtPrime m)] at ha
  have hnot : ¬ IsUnit ((algebraMap B (Localization.AtPrime m)) (algebraMap A B a)) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hmap'
  exact hnot hunit

private lemma algebraMap_injective_localization_atPrime_of_etale
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (m : Ideal B) [m.IsPrime] (hm : m.LiesOver (maximalIdeal A)) :
    Function.Injective (algebraMap A (Localization.AtPrime m)) := by
  let : IsLocalRing A := inferInstance
  let : IsLocalRing (Localization.AtPrime m) := inferInstance
  let : IsLocalHom (algebraMap A (Localization.AtPrime m)) :=
    isLocalHom_localization_atPrime_of_liesOver A B m hm
  have : Module.Flat A (Localization.AtPrime m) := inferInstance
  have : Module.FaithfullyFlat A (Localization.AtPrime m) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective A (Localization.AtPrime m)

private lemma valuationRing_localization_atPrime_of_etale
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (m : Ideal B) [m.IsPrime] (hm : m.LiesOver (maximalIdeal A)) :
    ∃ (_ : IsDomain (Localization.AtPrime m)),
      ValuationRing (Localization.AtPrime m) := by
  let hdomain : IsDomain (Localization.AtPrime m) :=
    isDomain_localization_atPrime_of_etale A B m
  let : IsDomain (Localization.AtPrime m) := hdomain
  let : IsLocalRing (Localization.AtPrime m) := inferInstance
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime m)) :=
    algebraMap_injective_localization_atPrime_of_etale A B m hm
  refine ⟨hdomain, valuationRing_of_flat_ideals (Localization.AtPrime m) ?_⟩
  intro I
  let : Module.IsTorsionFree A (Localization.AtPrime m) :=
    Module.IsTorsionFree.comap (algebraMap A (Localization.AtPrime m))
      (fun a ha => isRegular_iff_ne_zero.mpr
        (fun he => (isRegular_iff_ne_zero.mp ha) (hinj (by simpa using he))))
      (fun _ _ => by simp [Algebra.smul_def])
  let : Module.IsTorsionFree A I := inferInstance
  have hflatA : Module.Flat A I :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).2
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  let : Module.Flat A I := hflatA
  exact Algebra.FormallyUnramified.flat_of_restrictScalars A (Localization.AtPrime m) I

private lemma isValuationRingExtension_localization_atPrime_of_etale
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (m : Ideal B) [m.IsPrime] (hm : m.LiesOver (maximalIdeal A)) :
    ∃ (_ : IsDomain (Localization.AtPrime m))
      (_ : ValuationRing (Localization.AtPrime m)),
      IsExtension
        (algebraMap A (Localization.AtPrime m)) := by
  obtain ⟨hdomain, hvaluation⟩ := valuationRing_localization_atPrime_of_etale A B m hm
  let : IsDomain (Localization.AtPrime m) := hdomain
  let : ValuationRing (Localization.AtPrime m) := hvaluation
  exact ⟨hdomain, hvaluation,
    algebraMap_injective_localization_atPrime_of_etale A B m hm,
    isLocalHom_localization_atPrime_of_liesOver A B m hm⟩

private lemma finite_fractionRing_of_formallyUnramified
    (A : Type u) (C : Type v)
    [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Algebra A C] [Algebra.FormallyUnramified A C]
    [Algebra.EssFiniteType A C] [FaithfulSMul A C] :
    letI : Algebra (FractionRing A) (FractionRing C) :=
      FractionRing.liftAlgebra A (FractionRing C)
    Module.Finite (FractionRing A) (FractionRing C) := by
  let : Algebra (FractionRing A) (FractionRing C) :=
    FractionRing.liftAlgebra A (FractionRing C)
  have : Algebra.FormallyUnramified (FractionRing A) (FractionRing C) :=
    Algebra.FormallyUnramified.of_restrictScalars A (FractionRing A) (FractionRing C)
  have : Algebra.EssFiniteType (FractionRing A) (FractionRing C) :=
    Algebra.EssFiniteType.of_comp A (FractionRing A) (FractionRing C)
  exact Algebra.FormallyUnramified.finite_of_free (FractionRing A) (FractionRing C)

private lemma valueGroupMap_injective_of_local
    {A B : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [ValuationRing B]
    (f : A →+* B) (hf : IsExtension f) :
    Function.Injective (valueGroupMap
      (K := FractionRing A) (L := FractionRing B) f hf) := by
  let : CommGroupWithZero (ValueGroup A (FractionRing A)) := inferInstance
  let : CommGroupWithZero (ValueGroup B (FractionRing B)) := inferInstance
  intro x y heq
  apply Units.ext
  obtain ⟨a, ha⟩ := Quotient.exists_rep (x : ValueGroup A (FractionRing A))
  obtain ⟨b, hb⟩ := Quotient.exists_rep (y : ValueGroup A (FractionRing A))
  have hna : (valuation A (FractionRing A) a) ≠ 0 := by
    have hav : valuation A (FractionRing A) a = (x : ValueGroup A (FractionRing A)) := ha
    rw [hav]
    exact Units.ne_zero x
  have hnb : (valuation A (FractionRing A) b) ≠ 0 := by
    have hbv : valuation A (FractionRing A) b = (y : ValueGroup A (FractionRing A)) := hb
    rw [hbv]
    exact Units.ne_zero y
  let ua := Units.mk0 (valuation A (FractionRing A) a) hna
  let ub := Units.mk0 (valuation A (FractionRing A) b) hnb
  have hxa : x = ua := Units.ext ha.symm
  have hyb : y = ub := Units.ext hb.symm
  rw [hxa, hyb] at heq
  let q : A →+* FractionRing B := (algebraMap B (FractionRing B)).comp f
  have hq : Function.Injective q := (IsFractionRing.injective B (FractionRing B)).comp hf.1
  let g : FractionRing A →+* FractionRing B := IsFractionRing.lift (g := q) hq
  have hval := congrArg (fun z : (ValueGroup B (FractionRing B))ˣ =>
    (z : ValueGroup B (FractionRing B))) heq
  change (Quotient.mk'' (g a) : ValueGroup B (FractionRing B)) = Quotient.mk'' (g b) at hval
  rw [← ha, ← hb]
  have han : a ≠ 0 := by
    intro ha0
    subst a
    exact hna (map_zero (valuation A (FractionRing A)))
  have hbn : b ≠ 0 := by
    intro hb0
    subst b
    exact hnb (map_zero (valuation A (FractionRing A)))
  have of_le (r s : FractionRing A) (hs : s ≠ 0)
      (hrs : (Quotient.mk'' (g r) : ValueGroup B (FractionRing B)) = Quotient.mk'' (g s))
      (hle : valuation A (FractionRing A) r ≤ valuation A (FractionRing A) s) :
      (Quotient.mk'' r : ValueGroup A (FractionRing A)) = Quotient.mk'' s := by
    obtain ⟨w, hw⟩ := Quotient.exact' hrs
    change ∃ c : A, c • s = r at hle
    obtain ⟨c, hc⟩ := hle
    have hcunit : IsUnit c := by
      let : IsLocalHom f := hf.2
      have hgs : g s ≠ 0 := by
        intro hz
        exact hs ((RingHom.injective g) (by simpa using hz))
      have hmul : (algebraMap B (FractionRing B) (w : B)) * g s = q c * g s := by
        calc
          _ = g r := by simpa [Algebra.smul_def, Units.smul_def] using hw
          _ = g (c • s) := congrArg g hc.symm
          _ = q c * g s := by
            rw [Algebra.smul_def, map_mul]
            congr 1
            exact IsFractionRing.lift_algebraMap (g := q) hq c
      have hqu : q c = algebraMap B (FractionRing B) (w : B) :=
        mul_right_cancel₀ hgs hmul.symm
      have hfu : f c = (w : B) :=
        (IsFractionRing.injective B (FractionRing B)) (by simpa [q] using hqu)
      exact (isUnit_map_iff f c).mp (hfu ▸ w.isUnit)
    obtain ⟨cu, rfl⟩ := hcunit
    exact Quotient.sound' ⟨cu, hc⟩
  rcases ValuationRing.le_total A (FractionRing A)
    (valuation A (FractionRing A) a) (valuation A (FractionRing A) b) with hle | hle
  · exact of_le a b hbn hval hle
  · exact (of_le b a han hval.symm hle).symm

private lemma valueGroupMap_range_index_ne_zero
    (A : Type u) (C : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing C] [IsDomain C] [ValuationRing C]
    [Algebra A C] [FaithfulSMul A C]
    [Algebra.FormallyUnramified A C] [Algebra.EssFiniteType A C]
    [IsLocalHom (algebraMap A C)]
    (h : IsExtension (algebraMap A C)) :
    (valueGroupMap (K := FractionRing A) (L := FractionRing C)
      (algebraMap A C) h).range.index ≠ 0 := by
  let : Algebra (FractionRing A) (FractionRing C) :=
    FractionRing.liftAlgebra A (FractionRing C)
  let : Module.Finite (FractionRing A) (FractionRing C) :=
    finite_fractionRing_of_formallyUnramified A C
  have hindex := (ext_valuation_rings_degree_ineq A C (FractionRing A) (FractionRing C)
    (finite_fractionRing_of_formallyUnramified A C)).2.1
  rw [← valueGroupMap_range_eq_valueGroupHom_range A C h] at hindex
  exact hindex

private lemma surjective_of_valuation_mem_range
    (C : Type u) (L : Type v)
    [CommRing C] [IsDomain C] [ValuationRing C]
    [Field L] [Algebra C L] [IsFractionRing C L]
    {G : Type*} [Group G] (f : G →* (ValueGroup C L)ˣ)
    (H : ∀ c : C, ∀ hc : c ≠ 0,
      (Units.map ((valuation C L).toMonoidWithZeroHom.toMonoidHom)
        (Units.mk0 (algebraMap C L c)
          (by simpa using (IsFractionRing.injective C L).ne hc))) ∈ f.range) :
    Function.Surjective f := by
  let v : Lˣ →* (ValueGroup C L)ˣ :=
    Units.map ((valuation C L).toMonoidWithZeroHom.toMonoidHom)
  have hv : Function.Surjective v := units_valuation_surjective C L
  intro y
  obtain ⟨x, rfl⟩ := hv y
  rcases (ValuationRing.iff_isInteger_or_isInteger C L).mp inferInstance (x : L) with
    ⟨c, hc⟩ | ⟨c, hc⟩
  · have hc0 : c ≠ 0 := by
      intro hz
      subst c
      exact Units.ne_zero x (by simpa using hc.symm)
    let t : Lˣ := Units.mk0 (algebraMap C L c)
      (by simpa using (IsFractionRing.injective C L).ne hc0)
    have ht : t = x := Units.ext hc
    change v x ∈ f.range
    rw [← ht]
    exact H c hc0
  · have hc0 : c ≠ 0 := by
      intro hz
      subst c
      exact Units.ne_zero x⁻¹ (by simpa using hc.symm)
    let t : Lˣ := Units.mk0 (algebraMap C L c)
      (by simpa using (IsFractionRing.injective C L).ne hc0)
    have ht : t = x⁻¹ := by
      apply Units.ext
      simpa [t, Units.mk0] using hc
    have hvinv : v x⁻¹ ∈ f.range := by
      rw [← ht]
      exact H c hc0
    change v x ∈ f.range
    have hvx := f.range.inv_mem hvinv
    simpa using hvx

private lemma finite_index_localization_atPrime_of_etale
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (m : Ideal B) [m.IsPrime] (hm : m.LiesOver (maximalIdeal A)) :
    ∃ (_ : IsDomain (Localization.AtPrime m))
      (_ : ValuationRing (Localization.AtPrime m))
      (h : IsExtension
        (algebraMap A (Localization.AtPrime m))),
      (valueGroupMap
        (K := FractionRing A) (L := FractionRing (Localization.AtPrime m))
        (algebraMap A (Localization.AtPrime m)) h).range.index ≠ 0 := by
  obtain ⟨hd, hv, h⟩ := isValuationRingExtension_localization_atPrime_of_etale A B m hm
  let : IsDomain (Localization.AtPrime m) := hd
  let : ValuationRing (Localization.AtPrime m) := hv
  let : FaithfulSMul A (Localization.AtPrime m) :=
    (faithfulSMul_iff_algebraMap_injective A (Localization.AtPrime m)).2 h.1
  let : IsLocalHom (algebraMap A (Localization.AtPrime m)) := h.2
  exact ⟨hd, hv, h,
    valueGroupMap_range_index_ne_zero A (Localization.AtPrime m) h⟩

private lemma dvd_of_pow_dvd_pow_of_isNormalRing {R : Type*} [CommRing R]
    (hR : IsNormalRing R) {x y : R} {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n ∣ y ^ n) : x ∣ y := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.mem_of_localization_maximal
  intro p hp
  let := hp
  let := (hR p).1
  let := (hR p).2
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  apply (IsIntegrallyClosed.pow_dvd_pow_iff hn).mp
  simpa only [map_pow] using map_dvd (algebraMap R (Localization.AtPrime p)) h

/-- Flat base change preserves the kernel of the map to the quotient by an ideal. -/
private lemma mem_map_comap_of_tmul_mem {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (I : Ideal S) (x : S)
    (hx : x ⊗ₜ[R] (1 : S) ∈ I.map (Algebra.TensorProduct.includeRight :
      S →ₐ[R] S ⊗[R] S)) :
    x ∈ (I.comap (algebraMap R S)).map (algebraMap R S) := by
  let q : S →ₐ[R] S ⧸ I := Ideal.Quotient.mkₐ R I
  let f : R →ₗ[R] S ⧸ I := q.toLinearMap.comp (Algebra.linearMap R S)
  let t : S ⊗[R] S →ₐ[S] S ⊗[R] (S ⧸ I) :=
    Algebra.TensorProduct.map (AlgHom.id S S) q
  have ht : t (x ⊗ₜ[R] (1 : S)) = 0 := by
    change x ⊗ₜ[R] (1 : S) ∈ RingHom.ker t.toRingHom
    apply Ideal.map_le_iff_le_comap.mpr ?_ hx
    intro y hy
    change t (1 ⊗ₜ[R] y) = 0
    simp [t, q, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  have hker : x ⊗ₜ[R] (1 : R) ∈
      LinearMap.ker (AlgebraTensorModule.lTensor S S f) := by
    simpa [f, t] using ht
  rw [Module.Flat.ker_lTensor_eq] at hker
  obtain ⟨z, hz⟩ := hker
  have hzmem : (AlgebraTensorModule.rid R S S)
      ((AlgebraTensorModule.lTensor S S f.ker.subtype) z) ∈
      (I.comap (algebraMap R S)).map (algebraMap R S) := by
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      have ha := a.property
      change Ideal.Quotient.mk I (algebraMap R S a.val) = 0 at ha
      have ha' : a.val ∈ I.comap (algebraMap R S) :=
        (Ideal.Quotient.eq_zero_iff_mem (I := I)).mp ha
      simpa [Algebra.smul_def, mul_comm] using
        Ideal.mul_mem_left _ s (Ideal.mem_map_of_mem (algebraMap R S) ha')
    | add z w hz hw => simpa only [map_add] using add_mem hz hw
  simpa [hz] using hzmem


private lemma isNormalRing_tensor_localization (A B C : Type*)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra B C] [IsScalarTower A B C] [Algebra.Etale A B]
    (M : Submonoid B) [IsLocalization M C] [IsDomain C] [IsIntegrallyClosed C] :
    IsNormalRing (C ⊗[A] C) := by
  let f : C ⊗[A] B →ₐ[C] C ⊗[A] C :=
    Algebra.TensorProduct.map (AlgHom.id C C) (IsScalarTower.toAlgHom A B C)
  let : Algebra (C ⊗[A] B) (C ⊗[A] C) := f.toRingHom.toAlgebra
  have : IsScalarTower C (C ⊗[A] B) (C ⊗[A] C) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have := IsLocalization.tensorProduct_tensorProduct_right A C M C (by
    ext b
    simp [f, RingHom.algebraMap_toAlgebra])
  exact (Algebra.isNormalRing_of_smooth C (C ⊗[A] B)
    (isNormalRing_of_domain C)).isLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := A) (A := C))) _

/-- A principal ideal whose power descends also descends when the tensor square is normal. -/
private lemma exists_associated_of_associated_pow {A C : Type*}
    [CommRing A] [CommRing C] [IsDomain C] [Algebra A C]
    [Module.FaithfullyFlat A C] [IsBezout A]
    (hnormal : IsNormalRing (C ⊗[A] C))
    (h : C) (f : A) (n : ℕ) (hn : n ≠ 0)
    (hpow : Associated (algebraMap A C f) (h ^ n)) :
    ∃ g : A, Associated (algebraMap A C g) h := by
  let l : C →ₐ[A] C ⊗[A] C := Algebra.TensorProduct.includeLeft
  let r : C →ₐ[A] C ⊗[A] C := Algebra.TensorProduct.includeRight
  have he : l (algebraMap A C f) = r (algebraMap A C f) := by
    rw [l.commutes, r.commutes]
  have hp : r h ^ n ∣ l h ^ n := by
    have hr := (hpow.map r.toMonoidHom).symm
    have hl := hpow.map l.toMonoidHom
    change Associated (l (algebraMap A C f)) (l (h ^ n)) at hl
    rw [he] at hl
    simpa using (hr.trans hl).dvd
  have hd : r h ∣ l h := dvd_of_pow_dvd_pow_of_isNormalRing hnormal hn hp
  let I : Ideal C := Ideal.span {h}
  let J : Ideal A := I.comap (algebraMap A C)
  have hmem : h ∈ J.map (algebraMap A C) := by
    apply mem_map_comap_of_tmul_mem I h
    simpa [I, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, l, r] using hd
  have heq : J.map (algebraMap A C) = I := by
    apply le_antisymm Ideal.map_comap_le
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  have hfg : J.FG := Ideal.FG.of_FG_map_of_faithfullyFlat (S := C)
    (heq ▸ Submodule.fg_span_singleton h)
  have : J.IsPrincipal := IsBezout.isPrincipal_of_FG J hfg
  refine ⟨Submodule.IsPrincipal.generator J, Ideal.span_singleton_eq_span_singleton.mp ?_⟩
  rw [← Set.image_singleton, ← Ideal.map_span, Ideal.span_singleton_generator]
  exact heq

private lemma dvd_of_map_dvd_of_faithfullyFlat {A C : Type*}
    [CommRing A] [CommRing C] [Algebra A C] [Module.FaithfullyFlat A C]
    {a b : A} (h : algebraMap A C a ∣ algebraMap A C b) : a ∣ b := by
  apply Ideal.mem_span_singleton.mp
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) (Ideal.span {a})]
  simpa [Ideal.mem_comap, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] using h

private lemma exists_algebraMap_eq_of_fractionRing
    {A C K L : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Field K] [Field L] [Algebra A C] [Algebra A K] [IsFractionRing A K]
    [Algebra C L] [IsFractionRing C L] [Algebra A L] [IsScalarTower A C L]
    [Algebra K L] [IsScalarTower A K L] [Module.FaithfullyFlat A C]
    (c : C) (k : K) (hk : algebraMap K L k = algebraMap C L c) :
    ∃ a : A, algebraMap A C a = c := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A k
  have hbC : algebraMap A C b ≠ 0 :=
    by simpa using (FaithfulSMul.algebraMap_injective A C).ne (nonZeroDivisors.ne_zero hb)
  have hbL : algebraMap A L b ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A C L]
    simpa using (IsFractionRing.injective C L).ne hbC
  rw [← hab, map_div₀, ← IsScalarTower.algebraMap_apply A K L,
    ← IsScalarTower.algebraMap_apply A K L, div_eq_iff hbL] at hk
  have hc : algebraMap A C a = c * algebraMap A C b := by
    apply IsFractionRing.injective C L
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply A C L] using hk
  obtain ⟨g, hg⟩ := dvd_of_map_dvd_of_faithfullyFlat (show
    algebraMap A C b ∣ algebraMap A C a from ⟨c, hc.trans (mul_comm _ _)⟩)
  refine ⟨g, ?_⟩
  apply mul_left_cancel₀ hbC
  simpa [hg, map_mul, mul_comm] using hc

private lemma exists_associated_pow_of_valueGroup_index
    (A C : Type*) [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [ValuationRing C] [Algebra A C] [Module.FaithfullyFlat A C]
    (hindex : letI := FractionRing.liftAlgebra A (FractionRing C)
      (valueGroupHom C (FractionRing A) (FractionRing C)).range.index ≠ 0)
    (c : C) (hc : c ≠ 0) :
    ∃ (n : ℕ) (_ : 0 < n) (a : A), Associated (algebraMap A C a) (c ^ n) := by
  let := FractionRing.liftAlgebra A (FractionRing C)
  let cu : (FractionRing C)ˣ := Units.mk0 (algebraMap C (FractionRing C) c)
    (by simpa using (IsFractionRing.injective C (FractionRing C)).ne hc)
  let v : (FractionRing C)ˣ →* (ValueGroup C (FractionRing C))ˣ :=
    Units.map (valuation C (FractionRing C)).toMonoidWithZeroHom.toMonoidHom
  obtain ⟨n, hn, _, k, hk⟩ :=
    (valueGroupHom C (FractionRing A) (FractionRing C)).range.exists_pow_mem_of_index_ne_zero
      hindex (v cu)
  have he := congrArg (fun z : (ValueGroup C (FractionRing C))ˣ =>
    (z : ValueGroup C (FractionRing C))) hk
  change valuation C (FractionRing C) (algebraMap (FractionRing A) (FractionRing C) k) =
    (valuation C (FractionRing C) (algebraMap C (FractionRing C) c)) ^ n at he
  rw [← map_pow, ← map_pow] at he
  obtain ⟨w, hw⟩ := Quotient.exact' he
  have hw' : algebraMap C (FractionRing C) (w : C) *
    algebraMap C (FractionRing C) (c ^ n) =
    algebraMap (FractionRing A) (FractionRing C) k := by
      simpa [Units.smul_def, Algebra.smul_def] using hw
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_fractionRing (A := A) (L := FractionRing C)
    ((w : C) * c ^ n) (k : FractionRing A) (by simpa only [map_mul] using hw'.symm)
  refine ⟨n, hn, a, ?_⟩
  rw [ha]
  exact associated_unit_mul_left _ _ w.isUnit


/-- **Stacks Tag 0ASJ.** If `A` is a valuation ring, `A → B` is étale, and `m` is a
prime of `B` lying over the maximal ideal of `A`, then the canonical map from `A` to `Bₘ` is
a weakly unramified extension of valuation rings. -/
@[stacks 0ASJ]
theorem isWeaklyUnramified_localization_atPrime_of_etale
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (m : Ideal B) [m.IsPrime] (hm : m.LiesOver (maximalIdeal A)) :
    ∃ (_ : IsDomain (Localization.AtPrime m))
      (_ : ValuationRing (Localization.AtPrime m))
      (h : IsExtension
        (algebraMap A (Localization.AtPrime m))),
      IsWeaklyUnramified (algebraMap A (Localization.AtPrime m)) h := by
  obtain ⟨hd, hv, h, hi⟩ := finite_index_localization_atPrime_of_etale A B m hm
  let C := Localization.AtPrime m
  let : IsDomain C := hd
  let : ValuationRing C := hv
  let : IsLocalHom (algebraMap A C) := h.2
  have : Module.FaithfullyFlat A C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let := FractionRing.liftAlgebra A (FractionRing C)
  have hnormal : IsNormalRing (C ⊗[A] C) :=
    isNormalRing_tensor_localization A B C m.primeCompl
  have hindex : (valueGroupHom C (FractionRing A) (FractionRing C)).range.index ≠ 0 := by
    rwa [← valueGroupMap_range_eq_valueGroupHom_range A C h]
  refine ⟨hd, hv, h, valueGroupMap_injective_of_local (algebraMap A C) h, ?_⟩
  apply surjective_of_valuation_mem_range C (FractionRing C)
  intro c hc
  obtain ⟨n, hn, a, ha⟩ := exists_associated_pow_of_valueGroup_index A C hindex c hc
  obtain ⟨g, hg⟩ := exists_associated_of_associated_pow hnormal c a n hn.ne' ha
  have hg0 : g ≠ 0 := by
    intro hg0
    apply hc
    simpa [hg0] using hg.eq_zero_iff.mp (by simp [hg0])
  rw [valueGroupMap_range_eq_valueGroupHom_range A C h]
  refine ⟨Units.mk0 (algebraMap A (FractionRing A) g)
    (by simpa using (IsFractionRing.injective A (FractionRing A)).ne hg0), ?_⟩
  apply Units.ext
  change valuation C (FractionRing C)
    (algebraMap (FractionRing A) (FractionRing C) (algebraMap A (FractionRing A) g)) =
    valuation C (FractionRing C) (algebraMap C (FractionRing C) c)
  rw [← IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing C),
    IsScalarTower.algebraMap_apply A C (FractionRing C)]
  obtain ⟨w, hw⟩ := hg.symm
  apply Quotient.sound'
  refine ⟨w, ?_⟩
  simpa [Units.smul_def, Algebra.smul_def, ← map_mul, mul_comm] using
    congrArg (algebraMap C (FractionRing C)) hw

end ValuationRing

end EtaleExtension

section Henselization

open CategoryTheory CategoryTheory.Limits

namespace ValuationRing

private instance (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) := by
  change PreservesFilteredColimits
    ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R))
  infer_instance

private instance (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget (CommAlgCat.{u} R)) := by
  change PreservesFilteredColimits
    ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) ⋙ forget CommRingCat.{u})
  infer_instance

private theorem isLocalHom_of_residueFieldEquiv
    (R S : Type u) [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    (L : Type v) [Field L] [Algebra (ResidueField R) L]
    (e : L ≃+* ResidueField S)
    (he : ∀ x : R,
      e (algebraMap (ResidueField R) L (residue R x)) =
        residue S (algebraMap R S x)) :
    IsLocalHom (algebraMap R S) := by
  refine ⟨fun x hx => ?_⟩
  apply notMem_maximalIdeal.mp
  intro hnonunit
  have hres : residue R x = 0 := (residue_eq_zero_iff x).2 hnonunit
  have hs : residue S (algebraMap R S x) = 0 := by
    rw [← he, hres, map_zero, map_zero]
  exact (notMem_maximalIdeal.mpr hx) ((residue_eq_zero_iff _).1 hs)

private theorem exists_etale_stage
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S))
    (x : S) :
    ∃ (B : CommAlgCat.{u} R) (_ : Algebra.Etale R (B : Type u))
      (f : B ⟶ CommAlgCat.of R S) (b : B), f.hom b = x := by
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  obtain ⟨j, b, hb⟩ := CommAlgCat.exists_app_eq pres.isColimit x
  exact ⟨pres.diag.obj j, hpres j, pres.ι.app j, b, hb⟩

private theorem exists_etale_stage₂
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S))
    (x y : S) :
    ∃ (B : CommAlgCat.{u} R) (_ : Algebra.Etale R (B : Type u))
      (f : B ⟶ CommAlgCat.of R S) (b c : B), f.hom b = x ∧ f.hom c = y := by
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  obtain ⟨i, b, hb⟩ := CommAlgCat.exists_app_eq pres.isColimit x
  obtain ⟨j, c, hc⟩ := CommAlgCat.exists_app_eq pres.isColimit y
  let k := IsFiltered.max i j
  let b' := (pres.diag.map (IsFiltered.leftToMax i j)).hom b
  let c' := (pres.diag.map (IsFiltered.rightToMax i j)).hom c
  refine ⟨pres.diag.obj k, hpres k, pres.ι.app k, b', c', ?_, ?_⟩
  · rw [← hb]
    exact ConcreteCategory.congr_hom (pres.cocone.w (IsFiltered.leftToMax i j)) b
  · rw [← hc]
    exact ConcreteCategory.congr_hom (pres.cocone.w (IsFiltered.rightToMax i j)) c

private theorem exists_etale_stage_zero_product
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S))
    (x y : S) (hxy : x * y = 0) :
    ∃ (B : CommAlgCat.{u} R) (_ : Algebra.Etale R (B : Type u))
      (f : B ⟶ CommAlgCat.of R S) (b c : B),
      f.hom b = x ∧ f.hom c = y ∧ b * c = 0 := by
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  obtain ⟨i, b, hb⟩ := CommAlgCat.exists_app_eq pres.isColimit x
  obtain ⟨j, c, hc⟩ := CommAlgCat.exists_app_eq pres.isColimit y
  let k := IsFiltered.max i j
  let b' := (pres.diag.map (IsFiltered.leftToMax i j)).hom b
  let c' := (pres.diag.map (IsFiltered.rightToMax i j)).hom c
  have hb' : (pres.ι.app k).hom b' = x := by
    rw [← hb]
    exact ConcreteCategory.congr_hom (pres.cocone.w (IsFiltered.leftToMax i j)) b
  have hc' : (pres.ι.app k).hom c' = y := by
    rw [← hc]
    exact ConcreteCategory.congr_hom (pres.cocone.w (IsFiltered.rightToMax i j)) c
  have heq : (pres.ι.app k).hom (b' * c') = (pres.ι.app k).hom 0 := by
    rw [map_mul, hb', hc', hxy, map_zero]
  obtain ⟨l, p, q, hpq⟩ :=
    Concrete.isColimit_exists_of_rep_eq pres.diag pres.isColimit (b' * c') 0 heq
  let r : k ⟶ IsFiltered.coeq p q := p ≫ IsFiltered.coeqHom p q
  have hr : (pres.diag.map r).hom (b' * c') = 0 := by
    change (pres.diag.map (p ≫ IsFiltered.coeqHom p q)).hom (b' * c') = 0
    rw [Functor.map_comp, CommAlgCat.hom_comp, AlgHom.comp_apply, hpq]
    simp
  refine ⟨pres.diag.obj (IsFiltered.coeq p q), hpres _, pres.ι.app _,
    (pres.diag.map r).hom b', (pres.diag.map r).hom c', ?_, ?_, ?_⟩
  · calc
      _ = (pres.ι.app k).hom b' := by
        simpa only [CommAlgCat.hom_comp, AlgHom.comp_apply] using
          ConcreteCategory.congr_hom (pres.cocone.w r) b'
      _ = x := hb'
  · calc
      _ = (pres.ι.app k).hom c' := by
        simpa only [CommAlgCat.hom_comp, AlgHom.comp_apply] using
          ConcreteCategory.congr_hom (pres.cocone.w r) c'
      _ = y := hc'
  · rw [← map_mul]
    exact hr

private theorem localize_etale_stage
    (R S : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (B : CommAlgCat.{u} R) (f : B ⟶ CommAlgCat.of R S) :
    ∃ (m : Ideal B) (_ : m.IsPrime) (_ : m.LiesOver (maximalIdeal R))
      (g : Localization.AtPrime m →ₐ[R] S),
      ∀ b : B, g (algebraMap B (Localization.AtPrime m) b) = f.hom b := by
  let m : Ideal B := (maximalIdeal S).comap f.hom
  have hm : m.IsPrime := Ideal.comap_isPrime _ _
  have hover : m.LiesOver (maximalIdeal R) := ⟨by
    change maximalIdeal R = ((maximalIdeal S).comap f.hom).comap (algebraMap R B)
    symm
    ext a
    change f.hom (algebraMap R B a) ∈ maximalIdeal S ↔ a ∈ maximalIdeal R
    rw [f.hom.commutes]
    exact congrArg (fun I : Ideal R => a ∈ I)
      (IsLocalRing.maximalIdeal_comap (algebraMap R S)) |>.to_iff⟩
  have hunit : ∀ y : m.primeCompl, IsUnit (f.hom (y : B)) := by
    intro y
    apply notMem_maximalIdeal.mp
    exact y.2
  let g : Localization.AtPrime m →ₐ[R] S :=
    IsLocalization.liftAlgHom (M := m.primeCompl) (f := f.hom) hunit
  refine ⟨m, hm, hover, g, fun b => ?_⟩
  change IsLocalization.liftAlgHom hunit (algebraMap B (Localization.AtPrime m) b) = f.hom b
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

private theorem exists_local_etale_stage
    (R S : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S))
    (x : S) :
    ∃ (B : CommAlgCat.{u} R) (_ : Algebra.Etale R (B : Type u))
      (m : Ideal B) (_ : m.IsPrime) (_ : m.LiesOver (maximalIdeal R))
      (g : Localization.AtPrime m →ₐ[R] S) (b : B),
      g (algebraMap B (Localization.AtPrime m) b) = x := by
  obtain ⟨B, hB, f, b, hb⟩ := exists_etale_stage R S hind x
  obtain ⟨m, hm, hover, g, hg⟩ := localize_etale_stage R S B f
  exact ⟨B, hB, m, hm, hover, g, b, (hg b).trans hb⟩

private theorem exists_local_etale_stage₂
    (R S : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S))
    (x y : S) :
    ∃ (B : CommAlgCat.{u} R) (_ : Algebra.Etale R (B : Type u))
      (m : Ideal B) (_ : m.IsPrime) (_ : m.LiesOver (maximalIdeal R))
      (g : Localization.AtPrime m →ₐ[R] S) (b c : B),
      g (algebraMap B (Localization.AtPrime m) b) = x ∧
        g (algebraMap B (Localization.AtPrime m) c) = y := by
  obtain ⟨B, hB, f, b, c, hb, hc⟩ := exists_etale_stage₂ R S hind x y
  obtain ⟨m, hm, hover, g, hg⟩ := localize_etale_stage R S B f
  exact ⟨B, hB, m, hm, hover, g, b, c, (hg b).trans hb, (hg c).trans hc⟩

private theorem exists_local_etale_stage_zero_product
    (R S : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S))
    (x y : S) (hxy : x * y = 0) :
    ∃ (B : CommAlgCat.{u} R) (_ : Algebra.Etale R (B : Type u))
      (m : Ideal B) (_ : m.IsPrime) (_ : m.LiesOver (maximalIdeal R))
      (g : Localization.AtPrime m →ₐ[R] S) (b c : B),
      g (algebraMap B (Localization.AtPrime m) b) = x ∧
        g (algebraMap B (Localization.AtPrime m) c) = y ∧ b * c = 0 := by
  obtain ⟨B, hB, f, b, c, hb, hc, hbc⟩ :=
    exists_etale_stage_zero_product R S hind x y hxy
  obtain ⟨m, hm, hover, g, hg⟩ := localize_etale_stage R S B f
  exact ⟨B, hB, m, hm, hover, g, b, c, (hg b).trans hb, (hg c).trans hc, hbc⟩

private theorem isDomain_and_valuationRing_of_ind_etale
    (R S : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S)) :
    ∃ (_ : IsDomain S), ValuationRing S := by
  have hzd : NoZeroDivisors S := ⟨by
    intro x y hxy
    obtain ⟨B, hB, m, hm, hover, g, b, c, hb, hc, hbc⟩ :=
      exists_local_etale_stage_zero_product R S hind x y hxy
    let : Algebra.Etale R B := hB
    let : m.IsPrime := hm
    obtain ⟨hdom, _, _, _⟩ :=
      isWeaklyUnramified_localization_atPrime_of_etale R B m hover
    let : IsDomain (Localization.AtPrime m) := hdom
    have hzero :
        (algebraMap B (Localization.AtPrime m) b) *
          (algebraMap B (Localization.AtPrime m) c) = 0 := by
      rw [← map_mul, hbc, map_zero]
    rcases mul_eq_zero.mp hzero with h | h
    · left
      rw [← hb, h, map_zero]
    · right
      rw [← hc, h, map_zero]⟩
  let : NoZeroDivisors S := hzd
  let : IsDomain S := NoZeroDivisors.to_isDomain S
  refine ⟨inferInstance, ?_⟩
  have hpre : PreValuationRing S := ⟨by
    intro x y
    obtain ⟨B, hB, m, hm, hover, g, b, c, hb, hc⟩ :=
      exists_local_etale_stage₂ R S hind x y
    let : Algebra.Etale R B := hB
    let : m.IsPrime := hm
    obtain ⟨hdom, hval, _, _⟩ :=
      isWeaklyUnramified_localization_atPrime_of_etale R B m hover
    let : IsDomain (Localization.AtPrime m) := hdom
    let : ValuationRing (Localization.AtPrime m) := hval
    obtain ⟨d, hd | hd⟩ := ValuationRing.cond
      (algebraMap B (Localization.AtPrime m) b)
      (algebraMap B (Localization.AtPrime m) c)
    · refine ⟨g d, Or.inl ?_⟩
      rw [← hb, ← hc, ← map_mul, hd]
    · refine ⟨g d, Or.inr ?_⟩
      rw [← hb, ← hc, ← map_mul, hd]⟩
  exact ⟨⟩

private theorem injective_algebraMap_of_ind_etale
    (R S : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S)) :
    Function.Injective (algebraMap R S) := by
  apply (injective_iff_map_eq_zero (algebraMap R S)).2
  intro a ha
  obtain ⟨J, hcat, hfil, pres, hpres⟩ := hind
  let := hcat
  let := hfil
  obtain ⟨j⟩ := (IsFiltered.nonempty : Nonempty J)
  have heq : (pres.ι.app j).hom (algebraMap R (pres.diag.obj j) a) =
      (pres.ι.app j).hom 0 := by
    calc
      _ = algebraMap R S a := (pres.ι.app j).hom.commutes a
      _ = 0 := ha
      _ = _ := (pres.ι.app j).hom.map_zero.symm
  obtain ⟨l, p, q, hpq⟩ :=
    Concrete.isColimit_exists_of_rep_eq pres.diag pres.isColimit
      (algebraMap R (pres.diag.obj j) a) 0 heq
  let r : j ⟶ IsFiltered.coeq p q := p ≫ IsFiltered.coeqHom p q
  have hr : (algebraMap R (pres.diag.obj (IsFiltered.coeq p q))) a = 0 := by
    have hmap : (pres.diag.map r).hom (algebraMap R (pres.diag.obj j) a) = 0 := by
      change (pres.diag.map (p ≫ IsFiltered.coeqHom p q)).hom
        (algebraMap R (pres.diag.obj j) a) = 0
      rw [Functor.map_comp, CommAlgCat.hom_comp, AlgHom.comp_apply, hpq]
      simp
    simpa only [(pres.diag.map r).hom.commutes] using hmap
  let B := pres.diag.obj (IsFiltered.coeq p q)
  let f := pres.ι.app (IsFiltered.coeq p q)
  obtain ⟨m, hm, hover, g, hg⟩ := localize_etale_stage R S B f
  let : Algebra.Etale R B := hpres _
  let : m.IsPrime := hm
  obtain ⟨hdom, hval, hext, hweak⟩ :=
    isWeaklyUnramified_localization_atPrime_of_etale R B m hover
  let : IsDomain (Localization.AtPrime m) := hdom
  let : ValuationRing (Localization.AtPrime m) := hval
  apply hext.1
  calc
    algebraMap R (Localization.AtPrime m) a =
        algebraMap B (Localization.AtPrime m) (algebraMap R B a) :=
      IsScalarTower.algebraMap_apply R B (Localization.AtPrime m) a
    _ = 0 := by rw [hr, map_zero]
    _ = algebraMap R (Localization.AtPrime m) 0 := (map_zero _).symm

private theorem isValuationRingExtension_of_ind_etale
    (R S : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S)) :
    ∃ (_ : IsDomain S) (_ : ValuationRing S),
      IsExtension (algebraMap R S) := by
  obtain ⟨hdom, hval⟩ := isDomain_and_valuationRing_of_ind_etale R S hind
  let : IsDomain S := hdom
  let : ValuationRing S := hval
  exact ⟨hdom, hval, injective_algebraMap_of_ind_etale R S hind, inferInstance⟩

/-- Every unit of a value group is the valuation of a unit of the fraction field, which is a
quotient of two nonzero elements of the ring. -/
private lemma exists_div_eq_of_units_valueGroup (A : Type*) (K : Type*)
    [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (q : (ValueGroup A K)ˣ) :
    ∃ (z : Kˣ) (a c : A), a ≠ 0 ∧ c ≠ 0 ∧ algebraMap A K a / algebraMap A K c = z ∧
      q = Units.map (valuation A K).toMonoidWithZeroHom.toMonoidHom z := by
  obtain ⟨z, rfl⟩ := units_valuation_surjective A K q
  obtain ⟨a, c, hc, hac⟩ := IsFractionRing.div_surjective A (z : K)
  refine ⟨z, a, c, ?_, nonZeroDivisors.ne_zero hc, hac, rfl⟩
  rintro rfl
  exact z.ne_zero (by simpa using hac.symm)

/-- **A nonzero element of a weakly unramified extension of valuation rings divides, up to a
unit, into the image of the base.** For a weakly unramified extension `f : A → B` of valuation
rings and `b ≠ 0` in `B` there are nonzero `a, c ∈ A` and a unit `u` of `B` with
`f a = u * b * f c`: the value of `b` in the value group of `B` is the image of the value of
some `z` in the fraction field of `A`, and `z = a / c` with `a, c ≠ 0`. -/
theorem factor_of_weak
    {A B : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [ValuationRing B]
    (f : A →+* B) (hf : IsExtension f)
    (hw : IsWeaklyUnramified f hf)
    (b : B) (hb : b ≠ 0) :
    ∃ (a c : A) (u : Bˣ), a ≠ 0 ∧ c ≠ 0 ∧ f a = (u : B) * b * f c := by
  let FA := FractionRing A
  let FB := FractionRing B
  let : CommGroupWithZero (ValueGroup A FA) := inferInstance
  let vb : (ValuationRing.ValueGroup B FB)ˣ :=
    Units.mk0 ((valuation B FB) (algebraMap B FB b)) (by simp [hb])
  obtain ⟨q, hq⟩ := hw.2 vb
  obtain ⟨z, a, c, ha0, hc0, hac, rfl⟩ :=
    exists_div_eq_of_units_valueGroup A (FractionRing A) q
  let f' : A →+* FB := (algebraMap B FB).comp f
  have hf' : Function.Injective f' := (IsFractionRing.injective B FB).comp hf.1
  have hqv : (Quotient.mk'' ((IsFractionRing.lift hf') (z : FA)) : ValueGroup B FB) =
      (Quotient.mk'' (algebraMap B FB b) : ValueGroup B FB) := by
    exact congrArg
      (fun t : (ValuationRing.ValueGroup B FB)ˣ => (t : ValuationRing.ValueGroup B FB)) hq
  obtain ⟨u, hu⟩ := Quotient.exact' hqv
  refine ⟨a, c, u, ha0, hc0, ?_⟩
  apply (IsFractionRing.injective B FB)
  have hu' : (algebraMap B FB (u : B)) * algebraMap B FB b =
      (algebraMap B FB (f a)) / (algebraMap B FB (f c)) := by
    simpa only [Units.smul_def, Algebra.smul_def, ← hac, map_div₀,
      IsFractionRing.lift_algebraMap, f', RingHom.comp_apply] using hu
  have hcB : f c ≠ 0 := by
    intro h
    exact hc0 (hf.1 (by simpa only [map_zero] using h))
  have hcF : algebraMap B FB (f c) ≠ 0 := by
    intro h
    exact hcB ((IsFractionRing.injective B FB) (by simpa only [map_zero] using h))
  calc
    algebraMap B FB (f a) =
        (algebraMap B FB (u : B) * algebraMap B FB b) * algebraMap B FB (f c) := by
      rw [hu', div_mul_cancel₀ _ hcF]
    _ = algebraMap B FB ((u : B) * b * f c) := by simp only [map_mul]

private theorem valueGroupMap_surjective_of_factor
    {A B : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [ValuationRing B]
    (f : A →+* B) (hf : IsExtension f)
    (hfactor : ∀ b : B, b ≠ 0 →
      ∃ (a c : A) (u : Bˣ), a ≠ 0 ∧ c ≠ 0 ∧ f a = (u : B) * b * f c) :
    Function.Surjective (valueGroupMap
      (K := FractionRing A) (L := FractionRing B) f hf) := by
  intro q
  let FA := FractionRing A
  let FB := FractionRing B
  let z : FB := Quotient.out q.val
  have hz : (Quotient.mk'' z : ValueGroup B FB) = q.val := Quotient.out_eq _
  have hz0 : z ≠ 0 := by
    intro h
    have hq0 : (q : ValueGroup B FB) = 0 := by rw [← hz, h]; rfl
    exact q.ne_zero hq0
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective B z
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hb0 : b ≠ 0 := by
    intro h
    apply hz0
    rw [← hbd, h, map_zero, zero_div]
  obtain ⟨a, c, u, ha0, hc0, hfac⟩ := hfactor b hb0
  obtain ⟨a', c', v, ha'0, hc'0, hfa'c'⟩ := hfactor d hd0
  let w : FA := (algebraMap A FA (a * c')) / (algebraMap A FA (a' * c))
  have hw0 : w ≠ 0 := by
    apply div_ne_zero
    · intro h
      exact (mul_ne_zero ha0 hc'0) ((IsFractionRing.injective A FA)
        (by simpa only [map_zero] using h))
    · intro h
      exact (mul_ne_zero ha'0 hc0) ((IsFractionRing.injective A FA)
        (by simpa only [map_zero] using h))
  let r : (ValueGroup A FA)ˣ := Units.mk0 ((valuation A FA) w) (by simp [hw0])
  refine ⟨r, ?_⟩
  apply Units.ext
  let f' : A →+* FB := (algebraMap B FB).comp f
  have hf' : Function.Injective f' := (IsFractionRing.injective B FB).comp hf.1
  change (Quotient.mk'' ((IsFractionRing.lift hf') w) : ValueGroup B FB) = q.val
  rw [← hz]
  apply Quotient.sound'
  refine ⟨u * v⁻¹, ?_⟩
  simp only [Units.smul_def, Algebra.smul_def]
  rw [← hbd]
  have hw : (IsFractionRing.lift hf') w =
      (algebraMap B FB (f (a * c'))) / (algebraMap B FB (f (a' * c))) := by
    dsimp [w]
    rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    rfl
  rw [hw]
  simp only [map_mul, hfac, hfa'c', Units.val_mul, map_units_inv]
  have hne (x : B) (hx : x ≠ 0) : algebraMap B FB x ≠ 0 := by
    intro h
    exact hx ((IsFractionRing.injective B FB) (by simpa only [map_zero] using h))
  have hfc0 : f c ≠ 0 := by
    intro h; exact hc0 (hf.1 (by simpa only [map_zero] using h))
  have hfc'0 : f c' ≠ 0 := by
    intro h; exact hc'0 (hf.1 (by simpa only [map_zero] using h))
  simp only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, mul_eq_mul_left_iff,
    hne _ u.ne_zero, or_false, hne _ hb0]
  rw [mul_inv_rev]
  rw [mul_inv_rev, mul_inv_rev]
  symm
  calc
    _ = ((algebraMap B FB d)⁻¹ * (algebraMap B FB (v : B))⁻¹) *
        (algebraMap B FB (f c) * (algebraMap B FB (f c))⁻¹) *
        (algebraMap B FB (f c') * (algebraMap B FB (f c'))⁻¹) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ (hne _ hfc0), mul_inv_cancel₀ (hne _ hfc'0)]
      simp

private theorem factor_of_ind_etale
    (R S : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S))
    (x : S) (hx : x ≠ 0) :
    ∃ (a c : R) (v : Sˣ), a ≠ 0 ∧ c ≠ 0 ∧
      algebraMap R S a = (v : S) * x * algebraMap R S c := by
  obtain ⟨B, hB, m, hm, hover, g, b, hb⟩ := exists_local_etale_stage R S hind x
  let : Algebra.Etale R B := hB
  let : m.IsPrime := hm
  obtain ⟨hdom, hval, hext, hweak⟩ :=
    isWeaklyUnramified_localization_atPrime_of_etale R B m hover
  let : IsDomain (Localization.AtPrime m) := hdom
  let : ValuationRing (Localization.AtPrime m) := hval
  let t : Localization.AtPrime m := algebraMap B (Localization.AtPrime m) b
  have ht : t ≠ 0 := by
    intro h
    apply hx
    calc
      x = g t := hb.symm
      _ = 0 := by rw [h, map_zero]
  obtain ⟨a, c, v, ha, hc, hv⟩ :=
    factor_of_weak (algebraMap R (Localization.AtPrime m)) hext hweak t ht
  refine ⟨a, c, Units.map g.toRingHom.toMonoidHom v, ha, hc, ?_⟩
  have h := congrArg g hv
  change algebraMap R S a = g v * x * algebraMap R S c
  simpa only [map_mul, g.commutes, ← hb] using h

private theorem isWeaklyUnramified_of_ind_etale
    (R S : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S)) :
    ∃ (_ : IsDomain S) (_ : ValuationRing S)
      (h : IsExtension (algebraMap R S)),
      IsWeaklyUnramified (algebraMap R S) h := by
  obtain ⟨hdom, hval, hext⟩ := isValuationRingExtension_of_ind_etale R S hind
  let : IsDomain S := hdom
  let : ValuationRing S := hval
  refine ⟨hdom, hval, hext, ?_⟩
  exact ⟨valueGroupMap_injective_of_local (algebraMap R S) hext,
    valueGroupMap_surjective_of_factor (algebraMap R S) hext
      (factor_of_ind_etale R S hind)⟩


/-- **Stacks Tag 0ASK.** The henselization and strict henselization of a valuation ring are
valuation rings, and both canonical inclusions induce bijections on value groups. -/
@[stacks 0ASK]
theorem isWeaklyUnramified_henselization_and_strictHenselization
    (A Ah Ash : Type u)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah]
    (ksep : Type v) [Field ksep] [Algebra (ResidueField A) ksep]
    [IsSepClosure (ResidueField A) ksep]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash] [Algebra Ah Ash]
    [IsScalarTower A Ah Ash] [IsHenselization A ksep Ash]
    [IsLocalHom (algebraMap Ah Ash)] :
    ∃ (_ : IsDomain Ah) (_ : ValuationRing Ah)
      (_ : IsDomain Ash) (_ : ValuationRing Ash)
      (hAh : IsExtension (algebraMap A Ah))
      (hAsh : IsExtension (algebraMap Ah Ash)),
      IsWeaklyUnramified (algebraMap A Ah) hAh ∧
        IsWeaklyUnramified (algebraMap Ah Ash) hAsh := by
  obtain ⟨eAh, heAh⟩ :=
    IsHenselization.exists_residueFieldEquiv
      (R := A) (L := ResidueField A) (Rh := Ah)
  let : IsLocalHom (algebraMap A Ah) :=
    isLocalHom_of_residueFieldEquiv A Ah (ResidueField A) eAh heAh
  obtain ⟨hdomAh, hvalAh, hextAh, hweakAh⟩ :=
    isWeaklyUnramified_of_ind_etale A Ah
      (IsHenselization.ind_etale_of_universe_le
        (R := A) (L := ResidueField A) (Rh := Ah))
  let : IsDomain Ah := hdomAh
  let : ValuationRing Ah := hvalAh
  obtain ⟨eAsh, heAsh⟩ :=
    IsHenselization.exists_residueFieldEquiv
      (R := A) (L := ksep) (Rh := Ash)
  let : IsLocalHom (algebraMap A Ash) :=
    isLocalHom_of_residueFieldEquiv A Ash ksep eAsh heAsh
  obtain ⟨hdomAsh, hvalAsh, hextAash, _⟩ :=
    isWeaklyUnramified_of_ind_etale A Ash
      (IsHenselization.ind_etale_of_universe_le (R := A) (L := ksep) (Rh := Ash))
  let : IsDomain Ash := hdomAsh
  let : ValuationRing Ash := hvalAsh
  have hAhAshInj : Function.Injective (algebraMap Ah Ash) := by
    apply (injective_iff_map_eq_zero (algebraMap Ah Ash)).2
    intro x hx
    by_contra hne
    obtain ⟨a, c, z, ha, hc, hfac⟩ :=
      factor_of_ind_etale A Ah (IsHenselization.ind_etale_of_universe_le
        (R := A) (L := ResidueField A) (Rh := Ah)) x hne
    have hzero : algebraMap A Ash a = 0 := by
      have h := congrArg (algebraMap Ah Ash) hfac
      rw [IsScalarTower.algebraMap_apply A Ah Ash a]
      simpa only [map_mul, hx, mul_zero, zero_mul] using h
    exact ha (hextAash.1 (by rw [hzero, map_zero]))
  have hextAhAsh : IsExtension (algebraMap Ah Ash) :=
    ⟨hAhAshInj, inferInstance⟩
  have hfactorAhAsh : ∀ x : Ash, x ≠ 0 →
      ∃ (a c : Ah) (z : Ashˣ), a ≠ 0 ∧ c ≠ 0 ∧
        algebraMap Ah Ash a = (z : Ash) * x * algebraMap Ah Ash c := by
    intro x hx
    obtain ⟨a, c, z, ha, hc, hfac⟩ :=
      factor_of_ind_etale A Ash (IsHenselization.ind_etale_of_universe_le
        (R := A) (L := ksep) (Rh := Ash)) x hx
    refine ⟨algebraMap A Ah a, algebraMap A Ah c, z, ?_, ?_, ?_⟩
    · intro h
      exact ha (hextAh.1 (by simpa only [map_zero] using h))
    · intro h
      exact hc (hextAh.1 (by simpa only [map_zero] using h))
    · rw [← IsScalarTower.algebraMap_apply A Ah Ash a,
        ← IsScalarTower.algebraMap_apply A Ah Ash c]
      exact hfac
  refine ⟨hdomAh, hvalAh, hdomAsh, hvalAsh, hextAh, hextAhAsh,
    hweakAh, ?_⟩
  exact ⟨valueGroupMap_injective_of_local (algebraMap Ah Ash) hextAhAsh,
    valueGroupMap_surjective_of_factor (algebraMap Ah Ash) hextAhAsh
      hfactorAhAsh⟩

end ValuationRing

end Henselization
