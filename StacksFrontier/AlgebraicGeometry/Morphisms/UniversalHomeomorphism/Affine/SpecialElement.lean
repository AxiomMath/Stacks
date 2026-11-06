module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Subalgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SquareCube
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Denominators
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Powers
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.Support
public import StacksFrontier.RingTheory.Support.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Special elements in a universal homeomorphism of spectra

For a proper extension of commutative rings which induces a universal homeomorphism on
spectra, there is an element outside the smaller ring whose square and cube lie in it, or an
analogous element for a prime power together with its prime multiple.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.exists_special_element_of_universalHomeomorphism` produces one of the two
  kinds of special element in a proper ring extension.
* `AlgebraicGeometry.exists_special_element_over_subalgebra` is the same statement for a proper
  intermediate subalgebra.

## Implementation notes

The ring extension is represented by a subring `A : Subring B`; consequently, its being proper
is expressed by `A ≠ ⊤`. The product `p b` of the source is represented by multiplication by
the natural-number cast of `p` in `B`. When the residue fields are unchanged the square-cube
case applies directly; otherwise the argument localizes at a minimal prime of the support and
reads the prime-power case off a purely inseparable residue-field extension.

## References

* [Stacks Project, Tag 0CNC](https://stacks.math.columbia.edu/tag/0CNC)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

private theorem field_purelyInseparable_witness
    {F E : Type u} [Field F] [Field E] (f : F →+* E)
    (hpi : f.IsPurelyInseparable) (hns : ¬ Function.Surjective f) :
    ∃ p : ℕ, Nat.Prime p ∧ ∃ y : E,
      y ∉ Set.range f ∧ (p : E) * y = 0 ∧ y ^ p ∈ Set.range f := by
  classical
  let : Algebra F E := f.toAlgebra
  let q : ℕ := ringExpChar F
  have hqF : ExpChar F q := by simpa [q] using ringExpChar.expChar F
  have hpi' : IsPurelyInseparable F E := by
    simpa [RingHom.IsPurelyInseparable] using hpi
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ Set.range f := not_forall.mp hns
  obtain hqPrime | hqOne := expChar_is_prime_or_one F q
  · let e := IsPurelyInseparable.elemExponent F x
    have hepos : 0 < e := Nat.pos_of_ne_zero fun he0 => hx (by
      simpa [e, he0, RingHom.algebraMap_toAlgebra] using
        IsPurelyInseparable.elemExponent_def' F q x)
    let y : E := x ^ q ^ (e - 1)
    have hy : y ∉ Set.range f := by
      simpa [y, e, RingHom.algebraMap_toAlgebra] using
        (IsPurelyInseparable.elemExponent_min' F q (a := x) (n := e - 1) (by omega))
    have hpow : y ^ q ∈ Set.range f := by
      have hexp : q ^ (e - 1) * q = q ^ e := by rw [← pow_succ, Nat.sub_add_cancel hepos]
      show (x ^ q ^ (e - 1)) ^ q ∈ _
      rw [← pow_mul, hexp]
      simpa [RingHom.algebraMap_toAlgebra] using
        (IsPurelyInseparable.elemExponent_def' F q x)
    have hcharF : CharP F q := ringChar.of_eq <| by
      have hqDef : q = max (ringChar F) 1 := rfl
      have := hqPrime.ne_one
      omega
    have hcharE : CharP E q := charP_of_injective_ringHom f.injective q
    exact ⟨q, hqPrime, y, hy, by rw [CharP.cast_eq_zero E q, zero_mul], hpow⟩
  · exact (hx (by simpa [hqOne, RingHom.algebraMap_toAlgebra] using
      IsPurelyInseparable.pow_mem F q x)).elim

private theorem field_purelyInseparable_witness_of_not_iso
    {F E : Type u} [Field F] [Field E] (f : F →+* E)
    (hpi : f.IsPurelyInseparable)
    (hnotIso : ¬ IsIso (CommRingCat.ofHom f)) :
    ∃ p : ℕ, Nat.Prime p ∧ ∃ y : E,
      y ∉ Set.range f ∧ (p : E) * y = 0 ∧ y ^ p ∈ Set.range f :=
  field_purelyInseparable_witness f hpi fun hsurj => hnotIso
    ((ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom f)).2 ⟨RingHom.injective f, hsurj⟩)

private theorem exists_finite_proper_intermediate
    {B : Type u} [CommRing B] (A : Subring B)
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom A.subtype).op)] (hA : A ≠ ⊤) :
    ∃ C : Subalgebra A B, Module.Finite A C ∧ C ≠ ⊥ ∧
      UniversalHomeomorphism
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := by
  obtain ⟨b, hb⟩ : ∃ b : B, b ∉ A :=
    not_forall.mp fun h => hA (eq_top_iff.2 fun b _ => h b)
  let C : Subalgebra A B := Algebra.adjoin A {b}
  have hmap : (algebraMap A B) = A.subtype := RingHom.ext fun _ => rfl
  have hbase : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) := by
    simpa [hmap] using (inferInstance : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom A.subtype).op))
  have hC : C ≠ ⊥ := fun hC => by
    obtain ⟨a, ha⟩ := Algebra.mem_bot.1
      (show b ∈ (⊥ : Subalgebra A B) from hC ▸ Algebra.self_mem_adjoin_singleton A b)
    exact hb (ha ▸ a.2)
  exact ⟨C, Algebra.finite_adjoin_simple_of_isIntegral
    ((algebraMap_isIntegral_iff.mpr
      (universalHomeomorphism_algebra_isIntegral (A := A) (B := B))) b), hC,
    universalHomeomorphism_specMap_subalgebra C⟩

/-- An element of `C` whose class in `C ⧸ A` vanishes lies in the image of `A`. -/
private lemma mem_range_algebraMap_of_quotient_mk_eq_zero
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {c : C}
    (h : (Submodule.Quotient.mk c : C ⧸ LinearMap.range (Algebra.linearMap A C)) = 0) :
    c ∈ Set.range (algebraMap A C) := by
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 h
  exact ⟨a, by simpa [Algebra.linearMap_apply] using ha⟩

private theorem exists_minimal_support_prime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (hnot : ¬ Function.Surjective (algebraMap R S)) :
    ∃ p : PrimeSpectrum R,
      p ∈ Module.support R (S ⧸ LinearMap.range (Algebra.linearMap R S)) ∧
      p.asIdeal ∈
        (Module.annihilator R (S ⧸ LinearMap.range (Algebra.linearMap R S))).minimalPrimes := by
  let M := S ⧸ LinearMap.range (Algebra.linearMap R S)
  have hnotSub : ¬ Subsingleton M := fun _ => hnot fun c =>
    mem_range_algebraMap_of_quotient_mk_eq_zero (Subsingleton.elim (Submodule.Quotient.mk c : M) 0)
  have hI : Module.annihilator R M ≠ ⊤ := fun htop =>
    hnotSub (Module.annihilator_eq_top_iff.mp htop)
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hI
  refine ⟨⟨p, hp.1.1⟩, ?_, hp⟩
  rw [Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.mem_zeroLocus _ _).2 hp.1.2

private theorem universalHomeomorphism_localization
    {A B R S : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [Algebra A B] [Algebra A R] [Algebra B S]
    (M : Submonoid A) [IsLocalization M R]
    [IsLocalization (M.map (algebraMap A B)) S]
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)] :
    UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom
      (IsLocalization.map (M := M) (S := R) (T := M.map (algebraMap A B)) S
        (algebraMap A B) M.le_comap_map)).op) := by
  let φ := IsLocalization.map (M := M) (S := R) (T := M.map (algebraMap A B)) S
    (algebraMap A B) M.le_comap_map
  let f := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  have hsq : IsPullback (Scheme.Spec.map (CommRingCat.ofHom (algebraMap B S)).op)
      (Scheme.Spec.map (CommRingCat.ofHom φ).op) f
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A R)).op) :=
    isPullback_SpecMap_of_isPushout
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A R))
      (CommRingCat.ofHom (algebraMap B S)) (CommRingCat.ofHom φ)
      (CommRingCat.isPushout_of_isLocalization (algebraMap A B) φ
        (IsLocalization.map_comp M.le_comap_map) M)
  exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq
    (inferInstance : UniversalHomeomorphism f).universally_isHomeomorph⟩

private theorem radical_map_eq_prime_over_maximal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R]
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op)]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∃ q : PrimeSpectrum S,
      PrimeSpectrum.comap (algebraMap R S) q =
        ⟨IsLocalRing.maximalIdeal R,
          (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩ ∧
      (I.map (algebraMap R S)).radical = q.asIdeal := by
  let f := Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op
  have hhomeo : IsHomeomorph f :=
    (inferInstance : UniversalHomeomorphism f).universally_isHomeomorph
      _ _ _ IsPullback.of_id_snd
  have hspec : IsHomeomorph (PrimeSpectrum.comap (algebraMap R S)) := hhomeo
  let p : PrimeSpectrum R :=
    ⟨IsLocalRing.maximalIdeal R,
      (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩
  obtain ⟨q, hq⟩ := hspec.surjective p
  let K := I.map (algebraMap R S)
  have hcomapQ : Ideal.comap (algebraMap R S) q.asIdeal =
      IsLocalRing.maximalIdeal R := by
    simpa [p] using congrArg PrimeSpectrum.asIdeal hq
  have hKq : K ≤ q.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr ((Ideal.le_radical.trans_eq hI).trans_eq hcomapQ.symm)
  refine ⟨q, hq, ?_⟩
  rw [Ideal.radical_eq_sInf]
  refine le_antisymm (sInf_le ⟨hKq, q.isPrime⟩) (le_sInf fun J hJ => ?_)
  have : (Ideal.comap (algebraMap R S) J).IsPrime := hJ.2.comap _
  have hcomap_le : Ideal.comap (algebraMap R S) J ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal_of_isPrime _
  have hmax_le : IsLocalRing.maximalIdeal R ≤ Ideal.comap (algebraMap R S) J :=
    calc
      IsLocalRing.maximalIdeal R = I.radical := hI.symm
      _ ≤ (Ideal.comap (algebraMap R S) J).radical :=
        Ideal.radical_mono (Ideal.map_le_iff_le_comap.mp hJ.1)
      _ = Ideal.comap (algebraMap R S) J :=
        (Ideal.radical_eq_iff.mpr (hJ.2.comap (algebraMap R S)).isRadical)
  have hEq : (⟨J, hJ.2⟩ : PrimeSpectrum S) = q :=
    hspec.injective (PrimeSpectrum.ext ((le_antisymm hcomap_le hmax_le).trans hcomapQ.symm))
  exact (congrArg PrimeSpectrum.asIdeal hEq).ge

/-- The image in `C` of the annihilator of `C ⧸ A` consists of elements of `A`.

An element `i` of that annihilator kills the class of every `d : C`, so `algebraMap A C i * d`
is in the image of `A`; the elements of `C` with that property for every `d` form an ideal, so
that ideal contains the whole image of the annihilator. Pulled out of Tag 0CNC's proof so that
the hand-built ideal elaborates on its own. -/
private lemma mem_range_algebraMap_of_mem_map_annihilator
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {c : C}
    (hc : c ∈ Ideal.map (algebraMap A C)
      (Module.annihilator A (C ⧸ LinearMap.range (Algebra.linearMap A C)))) :
    c ∈ Set.range (algebraMap A C) := by
  have hkill : ∀ i : A,
      i ∈ Module.annihilator A (C ⧸ LinearMap.range (Algebra.linearMap A C)) →
      ∀ d : C, algebraMap A C i * d ∈ Set.range (algebraMap A C) := by
    intro i hi d
    have hz := (Module.mem_annihilator.mp hi)
      (Submodule.Quotient.mk d : C ⧸ LinearMap.range (Algebra.linearMap A C))
    have hz' : (Submodule.Quotient.mk
        (algebraMap A C i * d) : C ⧸ LinearMap.range (Algebra.linearMap A C)) = 0 := by
      simpa [Algebra.smul_def] using
        (Submodule.Quotient.mk_smul (LinearMap.range (Algebra.linearMap A C)) i d).trans hz
    exact mem_range_algebraMap_of_quotient_mk_eq_zero hz'
  let P : Ideal C := {
    carrier := {x | ∀ y, x * y ∈ Set.range (algebraMap A C)}
    zero_mem' := fun _ => ⟨0, by simp⟩
    add_mem' := by
      intro x y hx hy z
      obtain ⟨a, ha⟩ := hx z
      obtain ⟨b, hb⟩ := hy z
      exact ⟨a + b, by rw [map_add, ha, hb, add_mul]⟩
    smul_mem' := by
      intro r x hx z
      convert hx (r * z) using 1
      ring
  }
  have hP : Ideal.map (algebraMap A C)
      (Module.annihilator A (C ⧸ LinearMap.range (Algebra.linearMap A C))) ≤ P :=
    Ideal.map_le_iff_le_comap.mpr hkill
  simpa using hP hc 1

/-- Clearing a denominator inside a localization.

If every element of an ideal `J` of `C` already lies in the image of `A`, then every element
of the extension of `J` to the localization `S` of `C` at the image of `M` lies in the image
of the localization `R` of `A` at `M`: numerator and denominator both come from `A`, and the
denominator is a unit whose inverse therefore has an `R`-preimage as well.

Stated over abstract localizations presented by `IsLocalization` hypotheses so that it
elaborates against these binders. -/
private lemma mem_range_algebraMap_of_mem_map_of_le_range
    {A C R S : Type u} [CommRing A] [CommRing C] [CommRing R] [CommRing S]
    [Algebra A C] [Algebra A R] [Algebra C S] [Algebra R S] [Algebra A S]
    [IsScalarTower A R S] [IsScalarTower A C S]
    (M : Submonoid A) [IsLocalization M R]
    [IsLocalization (M.map (algebraMap A C)) S]
    (J : Ideal C) (hJrange : ∀ c : C, c ∈ J → c ∈ Set.range (algebraMap A C))
    (x : S) (hx : x ∈ J.map (algebraMap C S)) :
    x ∈ Set.range (algebraMap R S) := by
  classical
  have htower (a : A) :
      algebraMap C S (algebraMap A C a) = algebraMap R S (algebraMap A R a) := by
    rw [← IsScalarTower.algebraMap_apply A C S, ← IsScalarTower.algebraMap_apply A R S]
  obtain ⟨w, hxd⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M.map (algebraMap A C)) S).mp hx
  obtain ⟨a, haM, hda⟩ := Submonoid.mem_map.mp w.2.2
  obtain ⟨a₀, ha₀⟩ := hJrange _ w.1.2
  have hnum : algebraMap C S (w.1 : C) = algebraMap R S (algebraMap A R a₀) := by
    rw [← ha₀, htower]
  have hden : algebraMap C S (w.2 : C) = algebraMap R S (algebraMap A R a) := by
    rw [← hda, htower]
  have huC := IsLocalization.map_units S w.2
  let uC := huC.unit
  have hcancel : algebraMap C S (w.2 : C) * uC.inv = 1 := by simp [uC]
  have hxeq : x = algebraMap C S (w.1 : C) * uC.inv := by
    rw [← hxd, mul_assoc, hcancel, mul_one]
  have huA := IsLocalization.map_units R (⟨a, haM⟩ : M)
  let uA := huA.unit
  have hunitEq : uC = Units.map (algebraMap R S).toMonoidHom uA := by
    apply Units.ext
    calc
      (uC : S) = algebraMap C S (w.2 : C) := huC.unit_spec
      _ = algebraMap R S (algebraMap A R a) := hden
      _ = algebraMap R S (uA : R) := by rw [huA.unit_spec]
      _ = (Units.map (algebraMap R S).toMonoidHom uA : S) := rfl
  obtain ⟨v, hv⟩ : uC.inv ∈ Set.range (algebraMap R S) := ⟨uA.inv, by
    calc
      algebraMap R S uA.inv =
          (Units.map (algebraMap R S).toMonoidHom uA⁻¹ : Sˣ) := rfl
      _ = (Units.map (algebraMap R S).toMonoidHom uA).inv := by simp
      _ = uC.inv := by rw [hunitEq]⟩
  refine ⟨algebraMap A R a₀ * v, ?_⟩
  calc
    algebraMap R S (algebraMap A R a₀ * v) =
        algebraMap R S (algebraMap A R a₀) * algebraMap R S v := map_mul _ _ _
    _ = algebraMap C S (w.1 : C) * uC.inv := by rw [← hnum, hv]
    _ = x := hxeq.symm

/-- Localizing a ring extension at a prime of the support of its cokernel keeps the extension
proper. If the localization of `C ⧸ A` at `M` is nontrivial, then the induced map on the
localizations `R` of `A` and `S` of `C` is not surjective.

Stated over abstract localizations `R` and `S` presented by `IsLocalization` hypotheses rather
than over `Localization M` and `Localization (M.map (algebraMap A C))`, so that the
localized-module machinery elaborates against these binders. -/
private lemma not_surjective_algebraMap_of_nontrivial_localizedModule
    {A C R S : Type u} [CommRing A] [CommRing C] [CommRing R] [CommRing S]
    [Algebra A C] [Algebra A R] [Algebra C S] [Algebra R S] [Algebra A S]
    [IsScalarTower A R S] [IsScalarTower A C S]
    (M : Submonoid A) [IsLocalization M R]
    [IsLocalization (Algebra.algebraMapSubmonoid C M) S]
    (hnontriv : Nontrivial
      (LocalizedModule M (C ⧸ LinearMap.range (Algebra.linearMap A C)))) :
    ¬ Function.Surjective (algebraMap R S) := by
  let fA : A →ₗ[A] R := Algebra.linearMap A R
  let fC : C →ₗ[A] S := (IsScalarTower.toAlgHom A C S).toLinearMap
  have : IsLocalizedModule M fA := by
    show IsLocalizedModule M (Algebra.linearMap A R)
    infer_instance
  have : IsLocalizedModule M fC := by
    show IsLocalizedModule M (IsScalarTower.toAlgHom A C S).toLinearMap
    rw [isLocalizedModule_iff_isLocalization]
    infer_instance
  have hmapEq : IsLocalizedModule.map M fA fC (Algebra.linearMap A C) =
      (Algebra.linearMap R S).restrictScalars A := by
    apply IsLocalizedModule.linearMap_ext M fA fC
    ext
    simp only [LinearMap.comp_apply]
    show IsLocalizedModule.map M fA fC (Algebra.linearMap A C)
      (fA 1) = Algebra.linearMap R S (fA 1)
    rw [← IsLocalizedModule.mk'_one M fA (1 : A), IsLocalizedModule.map_mk']
    simp [fA, fC]
  have hnotLocalized : ¬ Function.Surjective (LocalizedModule.map M (Algebra.linearMap A C)) :=
    fun hsurj => not_nontrivial_iff_subsingleton.mpr
      ((LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker M
        (Algebra.linearMap A C)).mp hsurj) hnontriv
  intro hsurj
  refine hnotLocalized ((IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective fA fC
    (l := Algebra.linearMap A C)).mp ?_)
  rw [hmapEq]
  exact hsurj

/-- The prime-power witness of Tag 0CNC, read off residue fields.

Let `f : R →+* S` be compatible, through `ρ`, with surjections `evalA` and `evalC` onto fields,
where `evalC` has kernel `q`, `q` lies in the image of `f` and `ρ` is purely inseparable. If `f`
is not surjective, then neither is `ρ`, and lifting a prime-power witness of `ρ` produces an
element of `S` outside the image whose `r`-th multiple and `r`-th power are in the image. -/
private lemma exists_prime_pow_witness_of_residueField
    {R S K L : Type u} [CommRing R] [CommRing S] [Field K] [Field L] (f : R →+* S)
    (evalA : R →+* K) (evalC : S →+* L) (ρ : K →+* L) (q : Ideal S)
    (hA : Function.Surjective evalA) (hC : Function.Surjective evalC)
    (hker : ∀ c, evalC c = 0 ↔ c ∈ q) (hnat : ∀ a, ρ (evalA a) = evalC (f a))
    (hρ : ρ.IsPurelyInseparable) (hq : (q : Set S) ⊆ Set.range f)
    (hnot : ¬ Function.Surjective f) :
    ∃ r : ℕ, Nat.Prime r ∧ ∃ c : S, c ∉ Set.range f ∧
      (r : S) * c ∈ Set.range f ∧ c ^ r ∈ Set.range f := by
  have hlift : ∀ c a, c - f a ∈ q → c ∈ Set.range f := fun c a hdiff => by
    obtain ⟨b, hb⟩ := hq hdiff
    exact ⟨a + b, by rw [map_add, hb, add_sub_cancel]⟩
  have hns : ¬ Function.Surjective ρ := by
    intro hsurj
    refine hnot fun c => ?_
    obtain ⟨d, hd⟩ := hsurj (evalC c)
    obtain ⟨a, rfl⟩ := hA d
    exact hlift c a ((hker _).mp (by rw [map_sub, ← hnat, hd, sub_self]))
  obtain ⟨r, hr, y, hy, hry, d, hd⟩ := field_purelyInseparable_witness ρ hρ hns
  obtain ⟨c, rfl⟩ := hC y
  obtain ⟨a, rfl⟩ := hA d
  have hcnot : c ∉ Set.range f := by
    rintro ⟨a', rfl⟩
    exact hy ⟨evalA a', hnat a'⟩
  have hrc : (r : S) * c ∈ q := (hker _).mp (by rw [map_mul, map_natCast, hry])
  exact ⟨r, hr, c, hcnot, hq hrc,
    hlift _ a ((hker _).mp (by rw [map_sub, map_pow, ← hnat, hd, sub_self]))⟩

/-- Evaluation at a closed point of an affine scheme is surjective, with kernel the
corresponding maximal ideal. -/
private lemma Γevaluation_surjective_and_eq_zero_iff {R : Type u} [CommRing R]
    (x : Spec (CommRingCat.of R)) [x.asIdeal.IsMaximal] :
    Function.Surjective (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).Γevaluation x)) ∧
      ∀ a, CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).Γevaluation x) a = 0 ↔ a ∈ x.asIdeal := by
  let e : (Spec (CommRingCat.of R)).residueField x ≃+* x.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso (CommRingCat.of R) x).commRingCatIsoToRingEquiv
  have hev : CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec (CommRingCat.of R)).Γevaluation x) =
      (e.symm.toRingHom).comp (algebraMap R x.asIdeal.ResidueField) := by
    have h := congrArg CommRingCat.Hom.hom
      (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of R) x)
    convert h.symm using 1 <;> ext y <;> rfl
  rw [hev]
  refine ⟨e.symm.surjective.comp (Ideal.algebraMap_residueField_surjective x.asIdeal),
    fun a => ?_⟩
  rw [RingHom.comp_apply]
  refine ⟨fun ha => ?_, fun ha => by simp [(Ideal.algebraMap_residueField_eq_zero).2 ha]⟩
  simpa [Ideal.algebraMap_residueField_eq_zero] using congrArg e ha

/-- The residue-field map of `Spec S → Spec R` is compatible with evaluation of global
sections. -/
private lemma residueFieldMap_Γevaluation_algebraMap {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (x : Spec (CommRingCat.of S)) (a : R) :
    CommRingCat.Hom.hom
        ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op).residueFieldMap x)
        (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (Spec (CommRingCat.of R)).Γevaluation
            ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op) x)) a) =
      CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
        (Spec (CommRingCat.of S)).Γevaluation x) (algebraMap R S a) := by
  have hEval := Scheme.Γevaluation_naturality_apply
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op) x
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)
  have hΓ : (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv (algebraMap R S a) :=
    (congrArg (fun k => k a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R S)))).symm
  calc
    _ = (Spec (CommRingCat.of S)).Γevaluation x
        ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) := by
      simpa using hEval
    _ = _ := by
      rw [hΓ]
      rfl

/-- The prime-power witness of Tag 0CNC, over a local base.

Let `R → S` induce a universal homeomorphism on spectra with `R` local, and let `q` be a prime
of `S` lying over the maximal ideal of `R` all of whose elements are already in the image of
`R`. If `R → S` is not surjective, then the residue-field extension at `q` is a proper purely
inseparable extension; reading a generator of it off the residue characteristic `r` and lifting
produces an element of `S` outside the image whose `r`-th multiple and `r`-th power are in the
image.

Stated over abstract `R`, `S` and `algebraMap R S` rather than over the localizations the
tagged theorem builds, so that the residue-field bridge elaborates against these binders
instead of the tagged proof's ambient chain of local definitions. -/
private lemma exists_prime_pow_witness_of_asIdeal_subset_range
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op)]
    (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q =
      ⟨IsLocalRing.maximalIdeal R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩)
    (hqbase : (q.asIdeal : Set S) ⊆ Set.range (algebraMap R S))
    (hnotsurj : ¬ Function.Surjective (algebraMap R S)) :
    ∃ r : ℕ, Nat.Prime r ∧ ∃ c : S, c ∉ Set.range (algebraMap R S) ∧
      (r : S) * c ∈ Set.range (algebraMap R S) ∧
      c ^ r ∈ Set.range (algebraMap R S) := by
  let fLoc := Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op
  have : Algebra.IsIntegral R S :=
    universalHomeomorphism_algebra_isIntegral (A := R) (B := S)
  have hcomapmax : (q.asIdeal.comap (algebraMap R S)).IsMaximal := by
    rw [show q.asIdeal.comap (algebraMap R S) = IsLocalRing.maximalIdeal R by
      simpa using congrArg PrimeSpectrum.asIdeal hq]
    infer_instance
  let qSpec : Spec (CommRingCat.of S) :=
    (specOrderIsoPrimeSpectrum (CommRingCat.of S)).symm (OrderDual.toDual q)
  have : (fLoc qSpec).asIdeal.IsMaximal := hcomapmax
  have : qSpec.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) (S := S) q.asIdeal hcomapmax
  obtain ⟨hevalAsurj, -⟩ := Γevaluation_surjective_and_eq_zero_iff (fLoc qSpec)
  obtain ⟨hevalCsurj, hevalCzero⟩ := Γevaluation_surjective_and_eq_zero_iff qSpec
  exact exists_prime_pow_witness_of_residueField (algebraMap R S) _ _ _ q.asIdeal
    hevalAsurj hevalCsurj hevalCzero (residueFieldMap_Γevaluation_algebraMap qSpec)
    (universalHomeomorphism_residueFieldMap_isPurelyInseparable fLoc qSpec) hqbase hnotsurj

/-- Over a local base, an ideal `K` of `S` with image-valued elements whose radical is a prime
over the maximal ideal yields either a prime-power witness or an element outside the image with
two consecutive powers in it. -/
private lemma exists_special_witness_of_radical_eq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op)]
    (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q =
      ⟨IsLocalRing.maximalIdeal R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩)
    (K : Ideal S) (hK : K.radical = q.asIdeal)
    (hKrange : ∀ x ∈ K, x ∈ Set.range (algebraMap R S))
    (hnot : ¬ Function.Surjective (algebraMap R S)) :
    (∃ r : ℕ, Nat.Prime r ∧ ∃ c : S, c ∉ Set.range (algebraMap R S) ∧
      (r : S) * c ∈ Set.range (algebraMap R S) ∧ c ^ r ∈ Set.range (algebraMap R S)) ∨
    ∃ x : S, x ∉ Set.range (algebraMap R S) ∧ ∃ n : ℕ, 2 ≤ n ∧
      x ^ n ∈ Set.range (algebraMap R S) ∧ x ^ (n + 1) ∈ Set.range (algebraMap R S) := by
  by_cases hqbase : (q.asIdeal : Set S) ⊆ Set.range (algebraMap R S)
  · exact Or.inl (exists_prime_pow_witness_of_asIdeal_subset_range q hq hqbase hnot)
  obtain ⟨x, hxq, hxnot⟩ := Set.not_subset.mp hqbase
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (show x ∈ K.radical by rwa [hK])
  have hKq : K ≤ q.asIdeal := Ideal.le_radical.trans_eq hK
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hKq (by simpa using hn)))
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hxnot (hKrange x (by simpa using hn))
  have hnSucc : x ^ (n + 1) ∈ K := by
    rw [pow_succ]
    exact K.mul_mem_right x hn
  exact Or.inr ⟨x, hxnot, n, by omega, hKrange _ hn, hKrange _ hnSucc⟩

/-- Localizing a finite extension `A → C` at a minimal prime `p` of the support of `C ⧸ A`
yields a special element of the localization of `C` over the localization of `A`. -/
private lemma exists_localized_special_of_mem_minimalPrimes
    {A C R S : Type u} [CommRing A] [CommRing C] [CommRing R] [CommRing S]
    [Algebra A C] [Algebra A R] [Algebra C S] [Algebra R S] [Algebra A S]
    [IsScalarTower A R S] [IsScalarTower A C S]
    (p : Ideal A) [p.IsPrime] [IsLocalization p.primeCompl R]
    [IsLocalization (p.primeCompl.map (algebraMap A C)) S]
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op)]
    (hp : Nontrivial
      (LocalizedModule p.primeCompl (C ⧸ LinearMap.range (Algebra.linearMap A C))))
    (hmin : p ∈
      (Module.annihilator A (C ⧸ LinearMap.range (Algebra.linearMap A C))).minimalPrimes) :
    (∃ r : ℕ, Nat.Prime r ∧ ∃ c : S, c ∉ Set.range (algebraMap R S) ∧
      (r : S) * c ∈ Set.range (algebraMap R S) ∧ c ^ r ∈ Set.range (algebraMap R S)) ∨
    ∃ x : S, x ∉ Set.range (algebraMap R S) ∧ ∃ n : ℕ, 2 ≤ n ∧
      x ^ n ∈ Set.range (algebraMap R S) ∧ x ^ (n + 1) ∈ Set.range (algebraMap R S) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid C p.primeCompl) S :=
    ‹IsLocalization (p.primeCompl.map (algebraMap A C)) S›
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R p
  let I : Ideal A := Module.annihilator A (C ⧸ LinearMap.range (Algebra.linearMap A C))
  have hrad : (I.map (algebraMap A R)).radical = IsLocalRing.maximalIdeal R := by
    rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes R p I hmin,
      IsLocalization.AtPrime.map_eq_maximalIdeal p R]
  obtain ⟨q, hq, hradK⟩ := radical_map_eq_prime_over_maximal (S := S) _ hrad
  refine exists_special_witness_of_radical_eq q hq _ hradK (fun x hx => ?_)
    (not_surjective_algebraMap_of_nontrivial_localizedModule p.primeCompl hp)
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A R S, IsScalarTower.algebraMap_eq A C S,
    ← Ideal.map_map] at hx
  exact mem_range_algebraMap_of_mem_map_of_le_range p.primeCompl (I.map (algebraMap A C))
    (fun _ hc => mem_range_algebraMap_of_mem_map_annihilator hc) x hx

/-- For a tower `A ⊆ C ⊆ B` and `M ⊆ A`, the localization of `C` maps to that of `B`, and an
element lies over the localization of `A` exactly when its image does. -/
private lemma exists_ringHom_localization_mem_range_iff
    {B : Type u} [CommRing B] (A : Subring B) (C : Subalgebra A B) (M : Submonoid A) :
    ∃ φ : Localization (M.map (algebraMap A C)) →+* Localization (M.map A.subtype),
      ∀ c, φ c ∈ Set.range (IsLocalization.map (M := M) (S := Localization M)
          (T := M.map A.subtype) (Localization (M.map A.subtype)) A.subtype M.le_comap_map) ↔
        c ∈ Set.range (IsLocalization.map (M := M) (S := Localization M)
          (T := M.map (algebraMap A C)) (Localization (M.map (algebraMap A C)))
          (algebraMap A C) M.le_comap_map) := by
  let T : Submonoid C := M.map (algebraMap A C)
  let U : Submonoid B := M.map A.subtype
  let Bₚ := Localization U
  let locMap : Localization M →+* Localization T := IsLocalization.map (M := M)
    (S := Localization M) (T := T) (Localization T) (algebraMap A C) M.le_comap_map
  let baseLoc : Localization M →+* Bₚ := IsLocalization.map (M := M)
    (S := Localization M) (T := U) Bₚ A.subtype M.le_comap_map
  have hTU : T.map C.val = U := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨algebraMap A C a, ⟨a, ha, rfl⟩, rfl⟩
  have : IsLocalization (Submonoid.map (C.val : C →+* B) T) Bₚ :=
    hTU.symm ▸ (Localization.isLocalization (M := U))
  let φ : Localization T →+* Bₚ := IsLocalization.map (M := T) (S := Localization T)
    (T := Submonoid.map (C.val : C →+* B) T) Bₚ C.val T.le_comap_map
  have hφ : Function.Injective φ := IsLocalization.map_injective_of_injective (M := T)
    (S := Localization T) (P := B) (g := C.val) (Q := Bₚ) Subtype.val_injective
  have hcomp : φ.comp locMap = baseLoc := by
    apply IsLocalization.ringHom_ext M
    ext a
    simp only [RingHom.comp_apply]
    rw [IsLocalization.map_eq
        (show M ≤ Submonoid.comap (algebraMap A C) T from M.le_comap_map) a,
      IsLocalization.map_eq (M := T) (S := Localization T)
        (T := Submonoid.map (C.val : C →+* B) T) (Q := Bₚ) T.le_comap_map (algebraMap A C a),
      IsLocalization.map_eq (show M ≤ Submonoid.comap A.subtype U from M.le_comap_map) a]
    rfl
  refine ⟨φ, fun c => ⟨?_, ?_⟩⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, hφ ((DFunLike.congr_fun hcomp a).trans ha)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, (DFunLike.congr_fun hcomp a).symm⟩

/-- Clearing denominators in the prime-power case of Tag 0CNC: an element of the localization of
`B` at `M ⊆ A` outside the localization of `A`, whose `r`-th multiple and `r`-th power lie in
it, yields such an element of `B` over `A`. -/
private theorem exists_prime_pow_special_of_localization
    {B : Type u} [CommRing B] (A : Subring B) (M : Submonoid A) {r : ℕ} (hr : Nat.Prime r)
    (z : Localization (M.map A.subtype))
    (hz : z ∉ Set.range (IsLocalization.map (M := M) (S := Localization M)
      (T := M.map A.subtype) (Localization (M.map A.subtype)) A.subtype M.le_comap_map))
    (hrz : (r : Localization (M.map A.subtype)) * z ∈ Set.range (IsLocalization.map (M := M)
      (S := Localization M) (T := M.map A.subtype) (Localization (M.map A.subtype))
      A.subtype M.le_comap_map))
    (hzr : z ^ r ∈ Set.range (IsLocalization.map (M := M) (S := Localization M)
      (T := M.map A.subtype) (Localization (M.map A.subtype)) A.subtype M.le_comap_map)) :
    ∃ y : B, y ∉ A ∧ (r : B) * y ∈ A ∧ y ^ r ∈ A := by
  have hrLower : 2 ≤ r := hr.two_le
  let i0 : Fin (r + 1) := ⟨0, by omega⟩
  let ir : Fin (r + 1) := ⟨r - 1, by omega⟩
  have hirval : ir.val + 1 = r := Nat.sub_add_cancel (by omega)
  have hrsub : r - 1 ≠ 0 := by omega
  have hne : ir ≠ i0 := fun h => hrsub (congrArg Fin.val h)
  let coeff : Fin (r + 1) → B := fun i =>
    if i = i0 then (r : B) else if i = ir then 1 else 0
  have hcoeff : ∀ i, algebraMap B (Localization (M.map A.subtype)) (coeff i) *
      z ^ (i.val + 1) ∈ Set.range (IsLocalization.map (M := M) (S := Localization M)
        (T := M.map A.subtype) (Localization (M.map A.subtype)) A.subtype M.le_comap_map) := by
    intro i
    by_cases hi0 : i = i0
    · subst i
      simpa [coeff, i0] using hrz
    · by_cases hir : i = ir
      · subst i
        simpa [coeff, i0, ir, hne, hrsub, hirval] using hzr
      · refine ⟨0, ?_⟩
        simp [coeff, hi0, hir]
  obtain ⟨-, y, -, hyA, hy⟩ :=
    IsLocalization.exists_numerator_not_mem_of_localization A M coeff z hz hcoeff
  exact ⟨y, hyA, by simpa [coeff, i0] using hy i0,
    by simpa [coeff, ir, i0, hne, hrsub, hirval] using hy ir⟩

/-- Clearing denominators in the square-cube case of Tag 0CNC: an element of the localization of
`B` at `M ⊆ A` outside the localization of `A`, with two consecutive powers in it, yields an
element of `B` outside `A` whose square and cube lie in `A`. -/
private theorem exists_sq_cube_special_of_localization
    {B : Type u} [CommRing B] (A : Subring B) (M : Submonoid A)
    (x : Localization (M.map A.subtype)) {n : ℕ} (hn : 2 ≤ n)
    (hx : x ∉ Set.range (IsLocalization.map (M := M) (S := Localization M)
      (T := M.map A.subtype) (Localization (M.map A.subtype)) A.subtype M.le_comap_map))
    (hxn : x ^ n ∈ Set.range (IsLocalization.map (M := M) (S := Localization M)
      (T := M.map A.subtype) (Localization (M.map A.subtype)) A.subtype M.le_comap_map))
    (hxn1 : x ^ (n + 1) ∈ Set.range (IsLocalization.map (M := M) (S := Localization M)
      (T := M.map A.subtype) (Localization (M.map A.subtype)) A.subtype M.le_comap_map)) :
    ∃ y : B, y ∉ A ∧ y ^ 2 ∈ A ∧ y ^ 3 ∈ A := by
  obtain ⟨z, hz, hz2, hz3⟩ :=
    Subring.exists_not_mem_and_sq_mem_and_cube_mem_of_pow_mem_of_succ_pow_mem
      (IsLocalization.map (M := M) (S := Localization M) (T := M.map A.subtype)
        (Localization (M.map A.subtype)) A.subtype M.le_comap_map).range hx hn hxn hxn1
  let coeff : Fin 3 → B := fun i => if i.val = 0 then 0 else 1
  have hcoeff : ∀ i, algebraMap B (Localization (M.map A.subtype)) (coeff i) *
      z ^ (i.val + 1) ∈ Set.range (IsLocalization.map (M := M) (S := Localization M)
        (T := M.map A.subtype) (Localization (M.map A.subtype)) A.subtype M.le_comap_map) := by
    intro i
    fin_cases i
    · exact ⟨0, by simp [coeff]⟩
    · simpa [coeff] using hz2
    · simpa [coeff] using hz3
  obtain ⟨-, y, -, hyA, hy⟩ :=
    IsLocalization.exists_numerator_not_mem_of_localization A M coeff z hz hcoeff
  exact ⟨y, hyA, by simpa [coeff] using hy ⟨1, by omega⟩, by simpa [coeff] using hy ⟨2, by omega⟩⟩

/-- Tag 0CNC for a finite intermediate subalgebra `A ⊆ C ⊆ B` with `A → C` a non-surjective
universal homeomorphism on spectra. -/
private lemma exists_special_element_of_finite_subalgebra
    {B : Type u} [CommRing B] (A : Subring B) (C : Subalgebra A B) [Module.Finite A C]
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)]
    (hnot : ¬ Function.Surjective (algebraMap A C)) :
    (∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A) ∨
      (∃ p : ℕ, Nat.Prime p ∧ ∃ b : B, b ∉ A ∧ (p : B) * b ∈ A ∧ b ^ p ∈ A) := by
  obtain ⟨p, hpSupport, hpMinimal⟩ := exists_minimal_support_prime hnot
  let Aₚ := Localization p.asIdeal.primeCompl
  let Cₚ := Localization (p.asIdeal.primeCompl.map (algebraMap A C))
  let locMap : Aₚ →+* Cₚ := IsLocalization.map (M := p.asIdeal.primeCompl) (S := Aₚ)
    (T := p.asIdeal.primeCompl.map (algebraMap A C)) Cₚ (algebraMap A C)
    p.asIdeal.primeCompl.le_comap_map
  let : Algebra Aₚ Cₚ := locMap.toAlgebra
  have : IsScalarTower A Aₚ Cₚ := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap C Cₚ (algebraMap A C x) = locMap (algebraMap A Aₚ x)
    exact (IsLocalization.map_eq (M := p.asIdeal.primeCompl) (S := Aₚ)
      (T := p.asIdeal.primeCompl.map (algebraMap A C)) (Q := Cₚ)
      p.asIdeal.primeCompl.le_comap_map x).symm
  have : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Aₚ Cₚ)).op) :=
    universalHomeomorphism_localization (A := A) (B := C) (R := Aₚ) (S := Cₚ)
      p.asIdeal.primeCompl
  obtain ⟨φ, hφ⟩ := exists_ringHom_localization_mem_range_iff A C p.asIdeal.primeCompl
  rcases exists_localized_special_of_mem_minimalPrimes (R := Aₚ) (S := Cₚ) p.asIdeal
      (Module.mem_support_iff.mp hpSupport) hpMinimal with
    ⟨r, hr, c, hc, hrc, hcr⟩ | ⟨x, hx, n, hn, hxn, hxn1⟩
  · exact Or.inr ⟨r, hr, exists_prime_pow_special_of_localization A _ hr (φ c)
      (fun h => hc ((hφ c).1 h)) (by simpa using (hφ _).2 hrc) (by simpa using (hφ _).2 hcr)⟩
  · exact Or.inl (exists_sq_cube_special_of_localization A _ (φ x) hn
      (fun h => hx ((hφ x).1 h)) (by simpa using (hφ _).2 hxn) (by simpa using (hφ _).2 hxn1))

/-- **Stacks Project, Tag 0CNC.** A proper extension inducing a universal homeomorphism on
spectra contains either a square-and-cube special element or a prime-power special element. -/
@[stacks 0CNC]
theorem exists_special_element_of_universalHomeomorphism
    {B : Type u} [CommRing B] (A : Subring B)
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom A.subtype).op)]
    (hA : A ≠ ⊤) :
    (∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A) ∨
      (∃ p : ℕ, Nat.Prime p ∧
        ∃ b : B, b ∉ A ∧ (p : B) * b ∈ A ∧ b ^ p ∈ A) := by
  by_cases hres : ∀ x : Spec (CommRingCat.of B),
      IsIso ((Scheme.Spec.map (CommRingCat.ofHom A.subtype).op).residueFieldMap x)
  · exact Or.inl
      (exists_not_mem_and_sq_mem_and_cube_mem_of_universalHomeomorphism_of_residueFieldMap_isIso
        A hres hA)
  obtain ⟨C, hfinite, hproper, hUH⟩ := exists_finite_proper_intermediate A hA
  refine exists_special_element_of_finite_subalgebra A C fun hsurj =>
    hproper (bot_unique fun x hx => ?_)
  obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
  exact Algebra.mem_bot.2 ⟨a, by simpa [← Subalgebra.algebraMap_eq] using congrArg C.val ha⟩

/-- **Stacks 0CNC.** A proper intermediate subalgebra whose spectrum morphism from `Spec B` is
a universal homeomorphism contains either a square-and-cube special element or a prime-power
special element. -/
lemma exists_special_element_over_subalgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (C : Subalgebra A B)
    (hCB : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap C B)).op)) (hC : C ≠ ⊤) :
    (∃ b : B, b ∉ C ∧ b ^ 2 ∈ C ∧ b ^ 3 ∈ C) ∨
      (∃ p : ℕ, Nat.Prime p ∧ ∃ b : B, b ∉ C ∧ (p : B) * b ∈ C ∧ b ^ p ∈ C) := by
  have hC' : C.toSubring ≠ ⊤ := fun htop =>
    hC (Subalgebra.toSubring_injective (by simpa using htop))
  have : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom C.toSubring.subtype).op) :=
    universalHomeomorphism_specMap_to_subring C hCB
  simpa only [Subalgebra.mem_toSubring] using
    exists_special_element_of_universalHomeomorphism C.toSubring hC'

end AlgebraicGeometry

end
