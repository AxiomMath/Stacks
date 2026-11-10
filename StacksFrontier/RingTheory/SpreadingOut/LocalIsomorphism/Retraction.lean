module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.SpreadingOut.LocalIsomorphism.StageFactorization

/-!
# Retractions of `R_f → S_f` for a local isomorphism

Continuing the proof of Stacks Tag 00QR: under the hypotheses of
`exists_stage_factorization`, after inverting one element `f ∉ p` the map `R_f → S_f` has a
retraction whose kernel satisfies `I ⊆ I²` after a further localization.

## Main results

* `exists_retraction_away_of_bijective_localRingHom`: a retraction `S_f → R_f` of `R_f → S_f`
  whose kernel is finitely generated and annihilated by some `t ∉ q`.
* `exists_notMem_map_ker_le_mul_self`: the kernel `I` of the retraction satisfies `I ⊆ I²` after
  inverting one more element of `R` outside `p`.
-/

@[expose] public section

universe u v v' w w'

@[expose] public section

open Localization

/-- The map `R_f → S_f` sends the image of `r : R` to the image of `φ r`. -/
private theorem awayMap_algebraMap_apply {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (f r : R) :
    Localization.awayMap (algebraMap R S) f (algebraMap R (Localization.Away f) r) =
      algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S r) := by
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]

/-- The prime `q S_f` of `S_f` is prime and contracts back to `q`. -/
private theorem isPrime_map_away_and_comap (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S)) (f : R)
    (hf : f ∉ p) :
    (q.map (algebraMap S (Localization.Away (algebraMap R S f)))).IsPrime ∧
      (q.map (algebraMap S (Localization.Away (algebraMap R S f)))).comap
        (algebraMap S (Localization.Away (algebraMap R S f))) = q := by
  have hdis := (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := q) (algebraMap R S f)).mpr
    fun h => hf (by rw [hpq]; exact h)
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (algebraMap R S f)) _ q
    ‹_› hdis, IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (algebraMap R S f)) _
    ‹_› hdis⟩

/-- A ring-hom `σ : S_f → R_f` extending `θf : S → R_f` is a retraction of `R_f → S_f`. -/
private theorem retraction_comp_awayMap (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (f : R) (θf : S →+* Localization.Away f)
    (hθf : θf.comp (algebraMap R S) = algebraMap R (Localization.Away f))
    (σ : Localization.Away (algebraMap R S f) →+* Localization.Away f)
    (hσ : σ.comp (algebraMap S (Localization.Away (algebraMap R S f))) = θf) :
    σ.comp (Localization.awayMap (algebraMap R S) f) = RingHom.id (Localization.Away f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  change σ (Localization.awayMap (algebraMap R S) f (algebraMap R (Localization.Away f) r)) =
    algebraMap R (Localization.Away f) r
  rw [awayMap_algebraMap_apply]
  exact (RingHom.congr_fun hσ _).trans (RingHom.congr_fun hθf r)

/-- A retraction `σ : S_f → R_f` of `ν_f` has finitely generated kernel. -/
private theorem ker_fg_of_retraction (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (f : R)
    (σ :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Localization.Away (algebraMap R S f) →+* Localization.Away f)
    (hsec :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      σ.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) =
        RingHom.id (Localization.Away f)) :
    (RingHom.ker σ).FG := by
  let : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  have hst : IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    .of_algebraMap_eq fun x => (awayMap_algebraMap_apply f x).symm
  have hSfR : Algebra.FinitePresentation R (Localization.Away (algebraMap R S f)) :=
    instFinitePresentationAway (algebraMap R S f)
  have hRfFT : Algebra.FiniteType R (Localization.Away f) := by
    have : Algebra.FinitePresentation R (Localization.Away f) :=
      IsLocalization.Away.finitePresentation f
    infer_instance
  have hfp :
    Algebra.FinitePresentation (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation (R := R)
      (Localization.Away f) (Localization.Away (algebraMap R S f))
  have hcomm : ∀ r : Localization.Away f,
      σ (algebraMap _ (Localization.Away (algebraMap R S f)) r) = algebraMap _ _ r := fun r => by
    simpa using RingHom.congr_fun hsec r
  exact Algebra.FinitePresentation.ker_fG_of_surjective
    ({ σ with commutes' := hcomm } : Localization.Away (algebraMap R S f) →ₐ[Localization.Away f]
      Localization.Away f)
    fun x => ⟨algebraMap _ _ x, by simp⟩

/-- Under the hypotheses of `exists_notMem_mul_ker_eq_zero`, the prime `Q = q S_f` of `S_f` is not
in the support of the `S_f`-module `ker σ`. -/
theorem notMem_support_ker_of_bijective (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S))
    [Algebra.FinitePresentation R S]
    (hiso : Function.Bijective (Localization.localRingHom p q (algebraMap R S) hpq)) (f : R)
    (hf : f ∉ p) (θf : S →+* Localization.Away f)
    (cf : Localization.Away f →+* Localization.AtPrime p)
    (hcompat :
      ∀ s : S,
        cf (θf s) =
          (RingEquiv.ofBijective (Localization.localRingHom p q (algebraMap R S) hpq) hiso).symm
            ((algebraMap S (Localization.AtPrime q)) s))
    (σ : Localization.Away (algebraMap R S f) →+* Localization.Away f)
    (hσ : σ.comp (algebraMap S (Localization.Away (algebraMap R S f))) = θf)
    (Q : Ideal (Localization.Away (algebraMap R S f)))
    (hQdef : Q = q.map (algebraMap S (Localization.Away (algebraMap R S f)))) (hQp : Q.IsPrime) :
    (⟨Q, hQp⟩ : PrimeSpectrum (Localization.Away (algebraMap R S f))) ∉
      Module.support (Localization.Away (algebraMap R S f)) (RingHom.ker σ) := by
  classical
  set Sf := Localization.Away (algebraMap R S f) with hSf
  set Rp := Localization.AtPrime p with hRp
  set Sq := Localization.AtPrime Q with hSqdef'
  set Sqq := Localization.AtPrime q with hSqq
  set e := RingEquiv.ofBijective (Localization.localRingHom p q (algebraMap R S) hpq) hiso with he
  have hcomapQ : Q.comap (algebraMap S Sf) = q :=
    hQdef ▸ (isPrime_map_away_and_comap R S p q hpq f hf).2
  have hSqloc : IsLocalization.AtPrime Sq q := by
    have h :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers (algebraMap R S f)) Sq Q
    exact hcomapQ ▸ h
  have hunits :
    ∀ y : q.primeCompl, IsUnit (((e.symm.toRingHom).comp (algebraMap S Sqq)) (y : S)) := by
    intro y
    rw [RingHom.comp_apply]
    exact (IsLocalization.map_units Sqq y).map e.symm.toRingHom
  set g : Sq →+* Rp := IsLocalization.lift (M := q.primeCompl) (S := Sq) hunits with hg
  have hgeq : ∀ s : S, g (algebraMap S Sq s) = e.symm (algebraMap S Sqq s) := by
    intro s
    rw [hg]
    have := IsLocalization.lift_eq (M := q.primeCompl) (S := Sq) hunits s
    rw [this, RingHom.comp_apply]
    rfl
  have hginj : Function.Injective g := by
    rw [hg, IsLocalization.lift_injective_iff]
    intro x y
    rw [RingHom.comp_apply, RingHom.comp_apply]
    constructor
    · intro hxy
      have heq : (algebraMap S Sqq) x = (algebraMap S Sqq) y :=
        (IsLocalization.eq_iff_eq (M := q.primeCompl) (S := Sq) (P := Sqq)).mp hxy
      rw [show e.symm.toRingHom (algebraMap S Sqq x) = e.symm (algebraMap S Sqq x) from rfl,
        show e.symm.toRingHom (algebraMap S Sqq y) = e.symm (algebraMap S Sqq y) from rfl, heq]
    · intro hxy
      have hxy' : e.symm (algebraMap S Sqq x) = e.symm (algebraMap S Sqq y) := hxy
      exact
        (IsLocalization.eq_iff_eq (M := q.primeCompl) (S := Sq) (P := Sqq)).mpr
          (e.symm.injective hxy')
  have hcomm : g.comp (algebraMap Sf Sq) = cf.comp σ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R S f))
    ext s
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
    have hl : (algebraMap Sf Sq) (algebraMap S Sf s) = algebraMap S Sq s := by
      rw [← IsScalarTower.algebraMap_apply]
    rw [hl, hgeq s]
    have hr : σ (algebraMap S Sf s) = θf s := RingHom.congr_fun hσ s
    rw [hr, hcompat s]
  have key : ∀ x ∈ RingHom.ker σ, ∃ s ∈ Q.primeCompl, s * x = 0 := by
    intro x hx
    have hσx : σ x = 0 := hx
    have hgx : g (algebraMap Sf Sq x) = 0 := by
      have hcx := RingHom.congr_fun hcomm x
      rw [RingHom.comp_apply, RingHom.comp_apply] at hcx
      rw [hcx, hσx, map_zero]
    have hz : algebraMap Sf Sq x = 0 := hginj (by rw [hgx, map_zero])
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl Sq x).mp hz
    exact ⟨(m : Sf), m.property, hm⟩
  rw [Module.notMem_support_iff, LocalizedModule.subsingleton_iff]
  rintro ⟨x, hx⟩
  obtain ⟨s, hs, hsx⟩ := key x hx
  refine ⟨s, hs, ?_⟩
  ext
  change s * x = 0
  exact hsx

/-- The kernel of the retraction `σ` dies at `q`: it is annihilated by the image of some element
of `S ∖ q`. -/
theorem exists_notMem_mul_ker_eq_zero (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (p :
  Ideal R)
    [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S))
    [Algebra.FinitePresentation R S]
    (hiso : Function.Bijective (Localization.localRingHom p q (algebraMap R S) hpq)) (f : R)
    (hf : f ∉ p) (θf : S →+* Localization.Away f)
    (hθf : θf.comp (algebraMap R S) = algebraMap R (Localization.Away f))
    (cf : Localization.Away f →+* Localization.AtPrime p)
    (hcompat :
      ∀ s : S,
        cf (θf s) =
          (RingEquiv.ofBijective (Localization.localRingHom p q (algebraMap R S) hpq) hiso).symm
            ((algebraMap S (Localization.AtPrime q)) s))
    (σ : Localization.Away (algebraMap R S f) →+* Localization.Away f)
    (hσ : σ.comp (algebraMap S (Localization.Away (algebraMap R S f))) = θf) :
    ∃ t : S,
      t ∉ q ∧
        ∀ x ∈ RingHom.ker σ, (algebraMap S (Localization.Away (algebraMap R S f)) t) * x = 0 := by
  classical
  let : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  have hsec :
    σ.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) =
      RingHom.id (Localization.Away f) := retraction_comp_awayMap R S f θf hθf σ hσ
  have hkerfg : (RingHom.ker σ).FG := ker_fg_of_retraction R S f σ hsec
  set Sf := Localization.Away (algebraMap R S f)
  have : Module.Finite Sf (RingHom.ker σ) := Module.Finite.of_fg hkerfg
  set Q : Ideal Sf := q.map (algebraMap S Sf) with hQdef
  have hQp : Q.IsPrime := (isPrime_map_away_and_comap R S p q hpq f hf).1
  have hsupp : (⟨Q, hQp⟩ : PrimeSpectrum Sf) ∉ Module.support Sf (RingHom.ker σ) :=
    notMem_support_ker_of_bijective R S p q hpq hiso f hf θf cf hcompat σ hσ Q hQdef hQp
  rw [Module.mem_support_iff_of_finite] at hsupp
  obtain ⟨s, hs, hsQ⟩ := IsConcreteLE.not_le_iff_exists.mp hsupp
  have hann : ∀ x ∈ RingHom.ker σ, s * x = 0 := by
    intro x hx
    have := Module.mem_annihilator.mp hs ⟨x, hx⟩
    simpa using this
  obtain ⟨⟨a, m⟩, hsm⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R S f)) s
  have hmunit : IsUnit (algebraMap S Sf (m : S)) := IsLocalization.map_units _ m
  refine ⟨a, ?_, ?_⟩
  · intro haq
    apply hsQ
    have hmemQ : algebraMap S Sf a ∈ Q := Ideal.mem_map_of_mem _ haq
    rw [← hsm] at hmemQ
    exact (Ideal.mul_unit_mem_iff_mem Q hmunit).mp hmemQ
  · intro x hx
    have h : algebraMap S Sf a * x = algebraMap S Sf (m : S) * (s * x) := by
      rw [← hsm]; ring
    rw [h, hann x hx, mul_zero]

/-- If `S` is of finite presentation over `R` and `φ_p : R_p → S_q` is bijective, then for some
`f ∉ p` the localized structure map `ν_f := awayMap φ f : R_f → S_f` has a ring-hom retraction
`σ : S_f → R_f` whose kernel is annihilated by the image in `S_f` of some `t ∈ S` with
`t ∉ q`. -/
theorem exists_retraction_of_localRingHom_bijective (R S : Type) [CommRing R] [CommRing S] [Algebra
  R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S))
    [Algebra.FinitePresentation R S]
    (hiso : Function.Bijective (Localization.localRingHom p q (algebraMap R S) hpq)) :
    ∃ f : R,
      f ∉ p ∧
        letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
          (Localization.awayMap (algebraMap R S) f).toAlgebra
        ∃ σ : Localization.Away (algebraMap R S f) →+* Localization.Away f,
          (σ.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) =
              RingHom.id (Localization.Away f)) ∧
            (∃ t : S,
              t ∉ q ∧
                ∀ x ∈ RingHom.ker σ,
                  (algebraMap S (Localization.Away (algebraMap R S f)) t) * x = 0) := by
  obtain ⟨f, hf, θf, hθf, cf, _, hcompat⟩ := exists_stage_factorization R S p q hpq hiso
  refine ⟨f, hf, ?_⟩
  let : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  have hfa : θf (algebraMap R S f) = algebraMap R (Localization.Away f) f := by
    simpa using RingHom.congr_fun hθf f
  have hunit : IsUnit (θf (algebraMap R S f)) := by
    rw [hfa]; exact IsLocalization.Away.algebraMap_isUnit f
  let σ : Localization.Away (algebraMap R S f) →+* Localization.Away f :=
    IsLocalization.Away.lift (S := Localization.Away (algebraMap R S f)) (algebraMap R S f) hunit
  have hσ : σ.comp (algebraMap S (Localization.Away (algebraMap R S f))) = θf :=
    IsLocalization.Away.lift_comp (algebraMap R S f) hunit
  refine ⟨σ, ?_, ?_⟩
  · change
      σ.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) =
        RingHom.id (Localization.Away f)
    exact retraction_comp_awayMap R S f θf hθf σ hσ
  · exact exists_notMem_mul_ker_eq_zero R S p q hpq hiso f hf θf hθf cf hcompat σ hσ

/-- Spreading out the retraction: from the local isomorphism at `q` there is an `f ∉ p` and an
`R_f`-algebra retraction of `S_f → R_f` whose kernel is finitely generated and annihilated by
some `t ∈ S ∖ q`. -/
theorem exists_retraction_away_of_bijective_localRingHom (R S : Type) [CommRing R] [CommRing S]
  [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S))
    [Algebra.FinitePresentation R S]
    (hiso : Function.Bijective (Localization.localRingHom p q (algebraMap R S) hpq)) :
    ∃ f : R,
      f ∉ p ∧
        letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
          (Localization.awayMap (algebraMap R S) f).toAlgebra
        ∃ σ : Localization.Away (algebraMap R S f) →+* Localization.Away f,
          (σ.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) =
              RingHom.id (Localization.Away f)) ∧
            (RingHom.ker σ).FG ∧
            (∃ t : S,
              t ∉ q ∧
                ∀ x ∈ RingHom.ker σ,
                  (algebraMap S (Localization.Away (algebraMap R S f)) t) * x = 0) := by
  obtain ⟨f, hf, σ, hsec, hdies⟩ := exists_retraction_of_localRingHom_bijective R S p q hpq hiso
  refine ⟨f, hf, σ, hsec, ?_, hdies⟩
  exact ker_fg_of_retraction R S f σ hsec

/-- An ideal `I` with `I ≤ I * I` is idempotent. -/
lemma isIdempotentElem_of_le_mul_self {B : Type} [CommRing B] (I : Ideal B) (hle : I ≤ I * I) :
    IsIdempotentElem I := by
  rw [IsIdempotentElem]
  exact le_antisymm Ideal.mul_le_left hle

/-- Let `Sf` be an `Rf`-algebra and `M` a finitely generated `Sf`-module with
`IsScalarTower Rf Sf M`. If some function `σ : Sf → Rf` satisfies `s • m = σ s • m` for all `s`
and `m`, then `M` is finitely generated over `Rf`. -/
theorem module_finite_of_smul_factor {Rf Sf M : Type} [CommRing Rf] [CommRing Sf] [Algebra Rf Sf]
    [AddCommGroup M] [Module Sf M] [Module Rf M] [IsScalarTower Rf Sf M] [Module.Finite Sf M]
    (σ : Sf → Rf) (hσ : ∀ (s : Sf) (m : M), s • m = σ s • m) : Module.Finite Rf M := by
  rw [Module.finite_def]
  obtain ⟨gen, hgen⟩ := (Module.Finite.fg_top (R := Sf) (M := M))
  refine ⟨gen, le_antisymm le_top fun x _ => ?_⟩
  have hx : x ∈ Submodule.span Sf (gen : Set M) := hgen ▸ Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy; exact Submodule.subset_span hy
  · exact Submodule.zero_mem _
  · intro y z _ _ hy hz; exact Submodule.add_mem _ hy hz
  · intro s y _ hy
    rw [hσ s y]
    exact Submodule.smul_mem _ _ hy

/-- For a retraction `σ : S_f → R_f` of `ν_f` and `t ∈ S ∖ q`, the element `σ (ι_f^S t)` lies
outside the prime `p R_f = p.map (algebraMap R R_f)`. -/
theorem retraction_apply_notMem_map_prime (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S))
    (f : R) (hf : f ∉ p)
    (σ :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Localization.Away (algebraMap R S f) →+* Localization.Away f)
    (hsec :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      σ.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) =
        RingHom.id (Localization.Away f))
    (t : S) (ht : t ∉ q)
    (hann : ∀ x ∈ RingHom.ker σ, (algebraMap S (Localization.Away (algebraMap R S f)) t) * x = 0) :
    σ (algebraMap S (Localization.Away (algebraMap R S f)) t) ∉
      p.map (algebraMap R (Localization.Away f)) := by
  classical
  let : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  set Rf := Localization.Away f with hRfdef
  set Sf := Localization.Away (algebraMap R S f) with hSfdef
  set ν : Rf →+* Sf := algebraMap Rf Sf with hνdef
  set u : Sf := algebraMap S Sf t with hudef
  set a : Rf := σ u with hadef
  set Q : Ideal Sf := q.map (algebraMap S Sf) with hQdef
  obtain ⟨hQp, hcomapQ⟩ := isPrime_map_away_and_comap R S p q hpq f hf
  have huQ : u ∉ Q := by
    intro hu
    have : t ∈ Q.comap (algebraMap S Sf) := by
      rw [Ideal.mem_comap]; exact hu
    rw [hcomapQ] at this
    exact ht this
  have hσν : σ (ν a) = a := by
    have := RingHom.congr_fun hsec a
    simpa using this
  have hx0ker : u - ν a ∈ RingHom.ker σ := by rw [RingHom.mem_ker, map_sub, hσν, hadef, sub_self]
  have hmul : u * (u - ν a) = 0 := hann _ hx0ker
  have hxQ : u - ν a ∈ Q := by
    have hmem : u * (u - ν a) ∈ Q := by
      rw [hmul]; exact Q.zero_mem
    rcases hQp.mem_or_mem hmem with h | h
    · exact absurd h huQ
    · exact h
  intro hapRf
  have hsquare : ∀ r : R, ν (algebraMap R Rf r) = algebraMap S Sf (algebraMap R S r) :=
    awayMap_algebraMap_apply f
  have hle : p.map (algebraMap R Rf) ≤ Q.comap ν := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_comap, hsquare r]
    apply Ideal.mem_map_of_mem
    have : algebraMap R S r ∈ q := by
      rw [hpq] at hr; rw [Ideal.mem_comap] at hr; exact hr
    exact this
  have hνaQ : ν a ∈ Q := by
    have := hle hapRf
    rw [Ideal.mem_comap] at this
    exact this
  have huinQ : u ∈ Q := by
    have : (u - ν a) + ν a ∈ Q := Q.add_mem hxQ hνaQ
    simpa using this
  exact huQ huinQ

/-- Let `σ : S_f → R_f` be a retraction of `ν_f` whose kernel `I` is finitely generated and
annihilated by the image of some `t ∈ S ∖ q`. Then there is `f₁ ∉ p` such that every `x ∈ I` is
carried into `I * I` by some power of `ι_f^S (φ f₁)`. -/
theorem exists_pow_mul_mem_ker_mul_ker (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S))
    [Algebra.FinitePresentation R S] (f : R) (hf : f ∉ p)
    (σ :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Localization.Away (algebraMap R S f) →+* Localization.Away f)
    (hsec :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      σ.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) =
        RingHom.id (Localization.Away f))
    (hfg : (RingHom.ker σ).FG) (t : S) (ht : t ∉ q)
    (hann : ∀ x ∈ RingHom.ker σ, (algebraMap S (Localization.Away (algebraMap R S f)) t) * x = 0) :
    ∃ f₁ : R,
      f₁ ∉ p ∧
        ∀ x ∈ RingHom.ker σ,
          ∃ n : ℕ,
            (algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S f₁)) ^ n * x ∈
              (RingHom.ker σ) * (RingHom.ker σ) := by
  let : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  set Rf := Localization.Away f with hRf
  set Sf := Localization.Away (algebraMap R S f) with hSf
  set νS : S →+* Sf := algebraMap S Sf with hνS
  set I : Ideal Sf := RingHom.ker σ with hI
  set M := I.Cotangent with hM
  let : Module Rf M := Ideal.instModuleCotangentOfAlgebra I
  have : Module.Finite Sf (↥I) := Module.Finite.of_fg hfg
  have hMSf : Module.Finite Sf M :=
    Module.Finite.of_surjective I.toCotangent I.toCotangent_surjective
  have hσfact : ∀ (s : Sf) (m : M), s • m = σ s • m := by
    intro s m
    have hmem : s - algebraMap Rf Sf (σ s) ∈ I := by
      rw [hI, RingHom.mem_ker, map_sub]
      have : σ (algebraMap Rf Sf (σ s)) = σ s := RingHom.congr_fun hsec (σ s)
      rw [this, sub_self]
    have htor := I.isTorsionBySet_cotangent (x := m) (a := ⟨_, hmem⟩)
    simp only [sub_smul] at htor
    have h2 : (algebraMap Rf Sf (σ s)) • m = σ s • m := (algebra_compatible_smul Sf (σ s) m).symm
    rw [sub_eq_zero] at htor
    rw [htor, h2]
  have hMRf : Module.Finite Rf M := module_finite_of_smul_factor σ hσfact
  set s₀ : Rf := σ (νS t) with hs₀
  have hs₀ann : ∀ m : M, s₀ • m = 0 := by
    intro m
    have hbase : (νS t) • m = 0 := by
      obtain ⟨y, rfl⟩ := I.toCotangent_surjective m
      rw [← map_smul, Ideal.toCotangent_eq_zero]
      have hzero : ((νS t) • y : ↥I) = 0 := by
        ext
        change (νS t) * (y : Sf) = 0
        exact hann y y.property
      rw [hzero]; simp
    rw [← hbase, hσfact (νS t) m]
  have hs₀out : s₀ ∉ p.map (algebraMap R Rf) :=
    retraction_apply_notMem_map_prime R S p q hpq f hf σ hsec t ht hann
  set pRf : Ideal Rf := p.map (algebraMap R Rf) with hpRf
  have hpRfPrime : pRf.IsPrime := by
    rw [hpRf]
    apply IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f)
    · infer_instance
    · rw [Set.disjoint_left]
      rintro x ⟨n, rfl⟩ hx
      exact hf ((‹p.IsPrime›).mem_of_pow_mem n hx)
  have hsub0 : Subsingleton (LocalizedModule pRf.primeCompl M) := by
    rw [LocalizedModule.subsingleton_iff]
    intro m
    exact ⟨s₀, hs₀out, hs₀ann m⟩
  obtain ⟨g, hg, hsubg⟩ := LocalizedModule.exists_subsingleton_away (M := M) pRf
  rw [LocalizedModule.subsingleton_iff] at hsubg
  obtain ⟨⟨f₁, d⟩, hsurj⟩ := IsLocalization.surj (Submonoid.powers f) g
  have hdunit : IsUnit (algebraMap R Rf (d : R)) := by
    obtain ⟨n, hn⟩ := d.property
    rw [← hn, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit f).pow n
  obtain ⟨ud, hud⟩ := hdunit
  have hgeq : g = (↑ud⁻¹ : Rf) * algebraMap R Rf f₁ := by
    have h0 : g * (↑ud : Rf) = algebraMap R Rf f₁ := by
      rw [hud]; exact hsurj
    rw [← h0, mul_comm (↑ud⁻¹ : Rf), mul_assoc]
    simp
  have hf₁p : f₁ ∉ p := by
    intro hf₁
    apply hg
    rw [hgeq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hf₁)
  refine ⟨f₁, hf₁p, ?_⟩
  have hsquare : algebraMap Rf Sf (algebraMap R Rf f₁) = algebraMap S Sf (algebraMap R S f₁) :=
    awayMap_algebraMap_apply f f₁
  set sf : Sf := algebraMap S Sf (algebraMap R S f₁) with hsf
  have hνg : algebraMap Rf Sf g = algebraMap Rf Sf (↑ud⁻¹ : Rf) * sf := by
    rw [hgeq, map_mul, hsquare]
  have huunit : IsUnit (algebraMap Rf Sf (↑ud⁻¹ : Rf)) := (ud⁻¹).isUnit.map _
  intro x hx
  obtain ⟨r, hr, hr0⟩ := hsubg (I.toCotangent ⟨x, hx⟩)
  obtain ⟨k, rfl⟩ := hr
  have hmem2 : (algebraMap Rf Sf g) ^ k * x ∈ I ^ 2 := by
    rw [algebra_compatible_smul Sf (g ^ k) (I.toCotangent ⟨x, hx⟩)] at hr0
    rw [← map_smul, Ideal.toCotangent_eq_zero, map_pow] at hr0
    convert hr0 using 2
  refine ⟨k, ?_⟩
  have hexp : (algebraMap Rf Sf g) ^ k = (algebraMap Rf Sf (↑ud⁻¹ : Rf)) ^ k * sf ^ k := by
    rw [hνg, mul_pow]
  rw [hexp, mul_assoc] at hmem2
  have huk : IsUnit ((algebraMap Rf Sf (↑ud⁻¹ : Rf)) ^ k) := huunit.pow k
  have hfin : sf ^ k * x ∈ I ^ 2 := (Ideal.unit_mul_mem_iff_mem _ huk).mp hmem2
  rw [sq] at hfin
  exact hfin

/-- Under the hypotheses of `exists_pow_mul_mem_ker_mul_ker`, there is `f₁ ∉ p` such that, for
`κ : S_f → (S_f)_{sf}` the localization away from `sf := ι_f^S (φ f₁)` and
`I' := Ideal.map κ (ker σ)`, every `κ x` with `x ∈ ker σ` lies in `I' * I'`. -/
theorem exists_forall_map_ker_mem_sq (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S))
    [Algebra.FinitePresentation R S] (f : R) (hf : f ∉ p)
    (σ :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Localization.Away (algebraMap R S f) →+* Localization.Away f)
    (hsec :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      σ.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) =
        RingHom.id (Localization.Away f))
    (hfg : (RingHom.ker σ).FG) (t : S) (ht : t ∉ q)
    (hann : ∀ x ∈ RingHom.ker σ, (algebraMap S (Localization.Away (algebraMap R S f)) t) * x = 0) :
    ∃ f₁ : R,
      f₁ ∉ p ∧
        letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
          (Localization.awayMap (algebraMap R S) f).toAlgebra
        let sf := algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S f₁)
        ∀ x ∈ RingHom.ker σ,
          (algebraMap (Localization.Away (algebraMap R S f)) (Localization.Away sf)) x ∈
            (Ideal.map (algebraMap (Localization.Away (algebraMap R S f)) (Localization.Away sf))
                (RingHom.ker σ)) *
              (Ideal.map (algebraMap (Localization.Away (algebraMap R S f)) (Localization.Away sf))
                (RingHom.ker σ)) := by
  obtain ⟨f₁, hf₁, hpow⟩ :=
    exists_pow_mul_mem_ker_mul_ker R S p q hpq f hf σ hsec hfg t ht hann
  refine ⟨f₁, hf₁, ?_⟩
  intro sf x hx
  obtain ⟨n, hn⟩ := hpow x hx
  have hn2 : sf ^ n * x ∈ RingHom.ker σ * RingHom.ker σ := hn
  rw [← Ideal.map_mul]
  have hunit :
    IsUnit ((algebraMap (Localization.Away (algebraMap R S f)) (Localization.Away sf)) sf) :=
    IsLocalization.Away.algebraMap_isUnit sf
  have hmem :=
    Ideal.mem_map_of_mem (algebraMap (Localization.Away (algebraMap R S f)) (Localization.Away sf))
      hn2
  rw [map_mul, map_pow] at hmem
  have hu :
    IsUnit ((algebraMap (Localization.Away (algebraMap R S f)) (Localization.Away sf)) sf ^ n) :=
    hunit.pow n
  rwa [Ideal.unit_mul_mem_iff_mem _ hu] at hmem

/-- The descent step: given the retraction at `f`, produce an enlarging element `f₁ ∉ p` on
whose basic open the conormal module `I/I²` vanishes. -/
theorem exists_notMem_map_ker_le_mul_self (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S))
    [Algebra.FinitePresentation R S] (f : R) (hf : f ∉ p)
    (σ :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Localization.Away (algebraMap R S f) →+* Localization.Away f)
    (hsec :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      σ.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) =
        RingHom.id (Localization.Away f))
    (hfg : (RingHom.ker σ).FG) (t : S) (ht : t ∉ q)
    (hann : ∀ x ∈ RingHom.ker σ, (algebraMap S (Localization.Away (algebraMap R S f)) t) * x = 0) :
    ∃ f₁ : R,
      f₁ ∉ p ∧
        letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
          (Localization.awayMap (algebraMap R S) f).toAlgebra
        let sf := algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S f₁)
        (Ideal.map (algebraMap (Localization.Away (algebraMap R S f)) (Localization.Away sf))
            (RingHom.ker σ)) ≤
          (Ideal.map (algebraMap (Localization.Away (algebraMap R S f)) (Localization.Away sf))
              (RingHom.ker σ)) *
            (Ideal.map (algebraMap (Localization.Away (algebraMap R S f)) (Localization.Away sf))
              (RingHom.ker σ)) := by
  obtain ⟨f₁, hf₁, hmem⟩ :=
    exists_forall_map_ker_mem_sq R S p q hpq f hf σ hsec hfg t ht hann
  refine ⟨f₁, hf₁, ?_⟩
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact hmem x hx
