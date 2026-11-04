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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Isomorphic local rings give isomorphic localizations away from one element

## Main results

* `Stacks.SpreadingOut.LocalIsoSplitting.exists_mem_algHom_localizationAway_of_finitePresentation`:
  for `S` of finite presentation over `R`, every `R`-algebra map from `S` to a localization `Tₘ`
  of `T` at `M` factors through the localization of `T` away from a single element of `M`.
* `exists_notMem_algEquiv_localizationAway_of_isLocalization_atPrime`, in the namespace
  `Stacks.SpreadingOut.LocalIsoSplitting`: if `A` is of finite presentation over `B` and
  `B_p → A_Q` is an isomorphism, then `A_a ≅ B_f` as `B`-algebras for some `f ∉ p` and `a ∉ Q`.
* `Algebra.FinitePresentation.exists_algEquiv_localizationAway_of_algEquiv_atPrime`: algebras
  of finite presentation with isomorphic local rings become isomorphic after inverting one
  element on each side.

## Implementation notes

In `Algebra.FinitePresentation.exists_algEquiv_localizationAway_of_algEquiv_atPrime` the local
rings `Sq` and `Sq'` are any `S`-algebra with `IsLocalization.AtPrime Sq q` whose `R`-algebra
structure is the composite `R → S → Sq` (`IsScalarTower R S Sq`), and similarly for `Sq'`. The
localizations of the conclusion are the models `Localization.Away g` and `Localization.Away g'`;
by uniqueness of localizations (`IsLocalization.algEquiv`) this is no loss of generality. Only
the existence of an `R`-algebra isomorphism `S_g ≅ S'_{g'}` is asserted.

## References

* [Stacks Project, Tag 00QS](https://stacks.math.columbia.edu/tag/00QS)
-/

@[expose] public section

universe u v v' w w'

@[expose] public section

open Localization

@[expose] public section

namespace Stacks.SpreadingOut.LocalIsoSplitting

/-- The defining property of `IsLocalization.mk'`, pushed along an `A`-algebra map out of the
localization: `g (x / y) * y = x`. -/
public theorem mk'_mul_algebraMap {A : Type*} [CommRing A] {N : Submonoid A} {L : Type*}
    [CommRing L] [Algebra A L] [IsLocalization N L] {B : Type*} [CommRing B] [Algebra A B]
    (g : L →ₐ[A] B) (x : A) (y : N) :
    g (IsLocalization.mk' L x y) * algebraMap A B (y : A) = algebraMap A B x := by
  rw [← g.commutes (y : A), ← map_mul, IsLocalization.mk'_spec, g.commutes]

/-- Two ring maps out of a localization that agree after composing with `algebraMap` agree. -/
private theorem localization_apply_eq_of_comp_eq {A L P : Type*} [CommSemiring A] [CommSemiring L]
    [Semiring P] [Algebra A L] (M : Submonoid A) [IsLocalization M L] {j k : L →+* P}
    (h : j.comp (algebraMap A L) = k.comp (algebraMap A L)) (x : L) : j x = k x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext M h) x

/-- A divisor of an inverted element is itself inverted. -/
public theorem isUnit_algebraMap_of_dvd {A : Type*} [CommRing A] {b t : A} (h : b ∣ t) (L : Type*)
    [CommRing L] [Algebra A L] [IsLocalization.Away t L] : IsUnit (algebraMap A L b) := by
  exact IsLocalization.Away.isUnit_of_dvd t h

/-- An algebra map descends along a surjection whose kernel it kills. -/
public theorem exists_algHom_comp_eq {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C] (π : A →ₐ[R] B)
    (hπ : Function.Surjective π) (g : A →ₐ[R] C)
    (hle : RingHom.ker π.toRingHom ≤ RingHom.ker g.toRingHom) : ∃ ψ : B →ₐ[R] C, ψ.comp π = g := by
  set L := RingHom.liftOfSurjective π.toRingHom hπ ⟨g.toRingHom, hle⟩
  have key : ∀ a, L (π a) = g a := fun a =>
    RingHom.liftOfSurjective_comp_apply π.toRingHom hπ ⟨g.toRingHom, hle⟩ a
  refine ⟨{ L with commutes' := fun r => ?_ }, ?_⟩
  · show L (algebraMap R B r) = algebraMap R C r
    rw [← π.commutes r, key, g.commutes]
  · ext a; exact key a

/-- If `L` is the localization of `A` at `M` and every element of a finitely generated ideal
`I ⊆ A` maps to `0` in `L`, then there is a single `m ∈ M` with `m * x = 0` for all `x ∈ I`. -/
public theorem exists_mem_mul_eq_zero_of_fg {A : Type*} [CommRing A] (M : Submonoid A) (L : Type*)
    [CommRing L] [Algebra A L] [IsLocalization M L] {I : Ideal A} (hI : I.FG)
    (hle : I ≤ RingHom.ker (algebraMap A L)) : ∃ m ∈ M, ∀ x ∈ I, m * x = 0 := by
  classical
  obtain ⟨G, hG⟩ := hI
  choose! m hm using fun x (hx : x ∈ G) =>
    (IsLocalization.map_eq_zero_iff M L x).mp (hle (hG ▸ Ideal.subset_span hx))
  set c : A := ∏ x ∈ G, (m x : A) with hc
  refine ⟨c, Submonoid.prod_mem _ fun x _ => (m x).2, fun x hx => ?_⟩
  have key : I ≤ LinearMap.ker (LinearMap.mulLeft A c) := by
    rw [← hG]
    refine Ideal.span_le.mpr fun y hy => ?_
    have hy0 : c * y = 0 := by
      rw [hc, ← Finset.mul_prod_erase G _ hy, mul_comm ((m y : A)), mul_assoc, hm y hy, mul_zero]
    simpa [LinearMap.mem_ker] using hy0
  exact key hx

/-- Let `S` be an `R`-algebra of finite presentation, let `T` be an `R`-algebra and let `Tₘ` be
the localization of `T` at a submonoid `M`. Every `R`-algebra map `S → Tₘ` factors through the
localization of `T` away from a single element `t ∈ M`, compatibly with `T → Tₘ`. -/
public theorem exists_mem_algHom_localizationAway_of_finitePresentation {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] {T : Type*}
    [CommRing T] [Algebra R T] {M : Submonoid T} {Tm : Type*} [CommRing Tm] [Algebra T Tm]
    [IsLocalization M Tm] [Algebra R Tm] [IsScalarTower R T Tm] (φ : S →ₐ[R] Tm) :
    ∃ t ∈ M,
      ∃ (ψ : S →ₐ[R] Localization.Away t) (f : Localization.Away t →ₐ[R] Tm),
        (∀ x : T, f (algebraMap T (Localization.Away t) x) = algebraMap T Tm x) ∧
          f.comp ψ = φ := by
  classical
  obtain ⟨n, π, hπ, hfg⟩ := Algebra.FinitePresentation.out (R := R) (A := S)
  obtain ⟨s, hs⟩ := hfg
  set ρ : MvPolynomial (Fin n) R →ₐ[R] Tm := φ.comp π with hρ
  have hρzero : ∀ r ∈ s, ρ r = 0 := fun r hr => by
    have hmem : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
    have hker : π r = 0 := hmem
    simp [hρ, hker]
  obtain ⟨b, hbint⟩ :=
    IsLocalization.exist_integer_multiples M Finset.univ (fun i : Fin n => ρ (MvPolynomial.X i))
  choose c hc using fun i : Fin n => hbint i (Finset.mem_univ i)
  have hbu : IsUnit (algebraMap T Tm (b : T)) := IsLocalization.map_units Tm b
  set T1 := Localization.Away (b : T)
  set ψ1 : MvPolynomial (Fin n) R →ₐ[R] T1 :=
    MvPolynomial.aeval
      (fun i => IsLocalization.mk' T1 (c i) ⟨(b : T), Submonoid.mem_powers _⟩) with
    hψ1
  let f1 : T1 →ₐ[T] Tm :=
    IsLocalization.Away.liftAlgHom (A := T) (b : T) (f := Algebra.ofId T Tm) hbu
  have hf1 : ((f1.restrictScalars R).comp ψ1) = ρ := by
    refine MvPolynomial.algHom_ext fun i => hbu.mul_right_cancel ?_
    simp only [hψ1, AlgHom.comp_apply, MvPolynomial.aeval_X, AlgHom.restrictScalars_apply]
    rw [mk'_mul_algebraMap (N := Submonoid.powers (b : T)) f1 (c i)
        ⟨(b : T), Submonoid.mem_powers _⟩,
      hc i, Algebra.smul_def, mul_comm]
  let algT1Tm : Algebra T1 Tm := f1.toRingHom.toAlgebra
  have : IsScalarTower T T1 Tm := IsScalarTower.of_algebraMap_eq fun x => (f1.commutes x).symm
  have : IsLocalization (M.map (algebraMap T T1)) Tm :=
    IsLocalization.isLocalization_of_submonoid_le T1 Tm (Submonoid.powers (b : T)) M
      (Submonoid.powers_le.mpr b.2)
  obtain ⟨m, hmM, hann⟩ :=
    exists_mem_mul_eq_zero_of_fg (M.map (algebraMap T T1)) Tm (I := Ideal.span (ψ1 '' s))
      (Submodule.fg_span (s.finite_toSet.image _))
      (Ideal.span_le.mpr
        (by
          rintro _ ⟨r, hr, rfl⟩
          exact
            ((congrArg (fun g : MvPolynomial (Fin n) R →ₐ[R] Tm => g r) hf1).trans (hρzero r hr) :
              f1 (ψ1 r) = 0)))
  obtain ⟨m₀, hm₀, rfl⟩ := hmM
  refine ⟨(b : T) * m₀, M.mul_mem b.2 hm₀, ?_⟩
  set t : T := (b : T) * m₀ with ht
  set Lt := Localization.Away t
  have hbt : (b : T) ∣ t := by
    rw [ht]; exact dvd_mul_right _ _
  have hmt : m₀ ∣ t := by
    rw [ht]; exact dvd_mul_left _ _
  have hbLt : IsUnit (algebraMap T Lt (b : T)) := isUnit_algebraMap_of_dvd hbt Lt
  have hmLt : IsUnit (algebraMap T Lt m₀) := isUnit_algebraMap_of_dvd hmt Lt
  let h : T1 →ₐ[T] Lt :=
    IsLocalization.Away.liftAlgHom (A := T) (b : T) (f := Algebra.ofId T Lt) hbLt
  let f2 : Lt →ₐ[T] Tm :=
    IsLocalization.Away.liftAlgHom (A := T) t (f := Algebra.ofId T Tm)
      (IsLocalization.map_units Tm ⟨t, M.mul_mem b.2 hm₀⟩)
  set ψP : MvPolynomial (Fin n) R →ₐ[R] Lt := (h.restrictScalars R).comp ψ1
  have hψPzero : ∀ r ∈ s, ψP r = 0 := fun r hr => by
    refine hmLt.mul_right_eq_zero.mp ?_
    have hrel : ψP r = h (ψ1 r) := rfl
    rw [hrel, ← h.commutes m₀, ← map_mul, hann (ψ1 r) (Ideal.subset_span ⟨r, hr, rfl⟩), map_zero]
  obtain ⟨ψ, hψ⟩ :=
    exists_algHom_comp_eq π hπ ψP
      (by
        rw [← hs, Ideal.span_le]
        exact fun x hx => hψPzero x hx)
  refine ⟨ψ, f2.restrictScalars R, fun x => f2.commutes x, ?_⟩
  have hcomp : ∀ x : T1, f2 (h x) = f1 x :=
    localization_apply_eq_of_comp_eq (Submonoid.powers (b : T))
      (j := (f2.comp h : T1 →ₐ[T] Tm).toRingHom) (k := f1.toRingHom) (by ext x; simp)
  ext x
  obtain ⟨a, rfl⟩ := hπ x
  show (f2.restrictScalars R) (ψ (π a)) = φ (π a)
  rw [AlgHom.restrictScalars_apply,
    show ψ (π a) = ψP a from by
      rw [← hψ]; rfl,
    show f2 (ψP a) = f1 (ψ1 a) from hcomp (ψ1 a),
    show f1 (ψ1 a) = ρ a from congrArg (fun g => g a) hf1]
  rfl

/-- If `T` is the localization of `S'` away from `g' : S'` and `a : T` avoids the prime `Q ⊆ T`,
then the localization of `T` away from `a` is the localization of `S'` away from a single element
`r ∈ S'`, and `r` avoids the contraction of `Q` to `S'`. -/
public theorem exists_notMem_comap_isLocalization_away {S' : Type v'} [CommRing S'] {T : Type w}
    [CommRing T] [Algebra S' T] (g' : S') [IsLocalization.Away g' T] (Q : Ideal T) [hQ : Q.IsPrime]
    {a : T} (ha : a ∉ Q) :
    ∃ r ∉ Q.comap (algebraMap S' T), IsLocalization.Away r (Localization.Away a) := by
  obtain ⟨⟨x, m⟩, hx⟩ := IsLocalization.surj (M := Submonoid.powers g') (S := T) a
  have hassoc : Associated a (algebraMap S' T x) :=
    ⟨(IsLocalization.map_units T m).unit, by
      rw [IsUnit.unit_spec]; exact hx⟩
  have : IsLocalization.Away (algebraMap S' T x) (Localization.Away a) :=
    IsLocalization.Away.of_associated hassoc
  refine ⟨g' * x, ?_, IsLocalization.Away.mul' T (Localization.Away a) g' x⟩
  have hg'Q : algebraMap S' T g' ∉ Q :=
    Q.notMem_of_isUnit (IsLocalization.Away.algebraMap_isUnit g')
  have hxQ : algebraMap S' T x ∉ Q := by
    obtain ⟨u, hu⟩ := hassoc
    rw [← hu]
    exact fun hmem => (hQ.mem_or_mem hmem).elim ha (Q.notMem_of_isUnit u.isUnit)
  exact fun hmem => (hQ.mem_or_mem (by rwa [Ideal.mem_comap, map_mul] at hmem)).elim hg'Q hxQ

/-- If `L` is the localization of `S` at a prime `q` and `T` is the localization of `S` at a
submonoid `M₀` disjoint from `q`, sitting between `S` and `L`, then `L` is the localization of `T`
at the prime `qT`. -/
public theorem isLocalization_atPrime_map {S : Type*} [CommRing S] (M₀ : Submonoid S) (T : Type*)
    [CommRing T] [Algebra S T] [IsLocalization M₀ T] (L : Type*) [CommRing L] [Algebra S L]
    [Algebra T L] [IsScalarTower S T L] (q : Ideal S) [q.IsPrime] [IsLocalization.AtPrime L q]
    (hdisj : Disjoint (M₀ : Set S) (q : Set S)) [hQ : (q.map (algebraMap S T)).IsPrime] :
    IsLocalization.AtPrime L (q.map (algebraMap S T)) := by
  have hcomap : (q.map (algebraMap S T)).comap (algebraMap S T) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M₀ T ‹q.IsPrime› hdisj
  have hnotMem : ∀ x : S, x ∉ q → algebraMap S T x ∉ q.map (algebraMap S T) := fun x hx hmem =>
    hx (hcomap ▸ Ideal.mem_comap.mpr hmem)
  have : IsLocalization (q.primeCompl.map (algebraMap S T)) L :=
    IsLocalization.isLocalization_of_submonoid_le T L M₀ q.primeCompl fun x hx =>
      Set.disjoint_left.mp hdisj hx
  refine
    IsLocalization.isLocalization_of_is_exists_mul_mem L (q.primeCompl.map (algebraMap S T))
      (q.map (algebraMap S T)).primeCompl (fun x hx => ?_) fun x => ?_
  · obtain ⟨y, hy, rfl⟩ := hx
    exact hnotMem y hy
  · obtain ⟨⟨y, d⟩, hy⟩ := IsLocalization.surj M₀ (x : T)
    refine ⟨algebraMap S T (d : S), ?_⟩
    rw [mul_comm, hy]
    refine ⟨y, fun hyq => ?_, rfl⟩
    rcases hQ.mem_or_mem (hy ▸ Ideal.mem_map_of_mem _ hyq) with hmem | hmem
    · exact x.2 hmem
    · exact hnotMem d (Set.disjoint_left.mp hdisj d.2) hmem

/-- Let `A` be a `B`-algebra of finite presentation and let `L` be at once the localization of
`B` at a prime `p` and, compatibly with the scalar tower, the localization of `A` at a prime `Q`,
so that the induced map `B_p → A_Q` is an isomorphism. Then there are `f ∈ B`, `f ∉ p` and
`a ∈ A`, `a ∉ Q` with `A_a ≅ B_f` as `B`-algebras. -/
public theorem exists_notMem_algEquiv_localizationAway_of_isLocalization_atPrime {B : Type u}
    [CommRing B] {A : Type v} [CommRing A] [Algebra B A] [Algebra.FinitePresentation B A]
    {L : Type w} [CommRing L] [Algebra B L] [Algebra A L] [IsScalarTower B A L] (p : Ideal B)
    [p.IsPrime] [IsLocalization.AtPrime L p] (Q : Ideal A) [Q.IsPrime]
    [IsLocalization.AtPrime L Q] :
    ∃ f ∉ p, ∃ a ∉ Q, Nonempty (Localization.Away a ≃ₐ[B] Localization.Away f) := by
  classical
  have : IsLocalRing L := IsLocalization.AtPrime.isLocalRing L p
  have hmem : ∀ b : B, b ∈ p ↔ algebraMap B A b ∈ Q := fun b => by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff L p b, ←
      IsLocalization.AtPrime.to_map_mem_maximal_iff L Q (algebraMap B A b), ←
      IsScalarTower.algebraMap_apply B A L]
  obtain ⟨f₀, hf₀, σ, hl, hl_map, hσ⟩ :=
    exists_mem_algHom_localizationAway_of_finitePresentation (R := B) (S := A) (T := B) (M :=
      p.primeCompl) (Tm := L) (IsScalarTower.toAlgHom B A L)
  set Bf := Localization.Away f₀ with hBf
  set u : A := algebraMap B A f₀ with hu
  have huQ : u ∉ Q := fun hc => hf₀ ((hmem f₀).mpr hc)
  set A' := Localization.Away u with hA'
  let algBfA' : Algebra Bf A' := (Localization.awayMap (algebraMap B A) f₀).toAlgebra
  have htower : IsScalarTower B Bf A' := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show algebraMap B A' x = (Localization.awayMap (algebraMap B A) f₀) (algebraMap B Bf x)
    rw [IsScalarTower.algebraMap_apply B A A']
    exact (IsLocalization.map_eq _ _).symm
  have : Algebra.FinitePresentation Bf A' :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation B Bf A'
  have hunit : IsUnit (σ u) := by
    rw [hu, σ.commutes]; exact IsLocalization.Away.algebraMap_isUnit f₀
  set σ' : A' →ₐ[B] Bf := IsLocalization.Away.liftAlgHom (S := A') u (f := σ) hunit with hσ'def
  have hσ'_apply : ∀ x : A, σ' (algebraMap A A' x) = σ x := by
    intro x; simp [hσ'def, IsLocalization.Away.liftAlgHom, IsLocalization.Away.lift]
  have hcom : ∀ y : Bf, σ' (algebraMap Bf A' y) = y :=
    localization_apply_eq_of_comp_eq (Submonoid.powers f₀)
      (j := σ'.toRingHom.comp (algebraMap Bf A')) (k := RingHom.id Bf) (by
        ext x
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [← IsScalarTower.algebraMap_apply B Bf A', σ'.commutes])
  have hsurj : Function.Surjective σ' := fun y => ⟨algebraMap Bf A' y, hcom y⟩
  set σ2 : A' →ₐ[Bf] Bf := { σ'.toRingHom with commutes' := hcom } with hσ2def
  have hker : (RingHom.ker σ2.toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective σ2 (fun y => ⟨_, hcom y⟩)
  have hunit2 : IsUnit (algebraMap A L u) := by
    rw [hu, ← IsScalarTower.algebraMap_apply B A L]
    exact IsLocalization.map_units L (⟨f₀, hf₀⟩ : p.primeCompl)
  set τ : A' →ₐ[B] L :=
    IsLocalization.Away.liftAlgHom (S := A') u (f := IsScalarTower.toAlgHom B A L) hunit2 with
    hτdef
  have hτ_apply : ∀ x : A, τ (algebraMap A A' x) = algebraMap A L x := by
    intro x; simp [hτdef, IsLocalization.Away.liftAlgHom, IsLocalization.Away.lift]
  have hlσ' : ∀ x : A', hl (σ' x) = τ x :=
    localization_apply_eq_of_comp_eq (Submonoid.powers u)
      (j := hl.toRingHom.comp σ'.toRingHom) (k := τ.toRingHom) (by
        ext x
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe]
        rw [hσ'_apply x, hτ_apply x]
        exact congrArg (fun g : A →ₐ[B] L => g x) hσ)
  let algA'L : Algebra A' L := τ.toRingHom.toAlgebra
  have : IsScalarTower A A' L := IsScalarTower.of_algebraMap_eq fun x => (hτ_apply x).symm
  have : IsLocalization (Submonoid.map (algebraMap A A') Q.primeCompl) L :=
    IsLocalization.isLocalization_of_submonoid_le A' L (Submonoid.powers u) Q.primeCompl
      (Submonoid.powers_le.mpr huQ)
  obtain ⟨a, hamem, hann⟩ :=
    exists_mem_mul_eq_zero_of_fg (Submonoid.map (algebraMap A A') Q.primeCompl) L hker fun x hx =>
      show algebraMap A' L x = 0 by
        show τ x = 0
        rw [← hlσ' x, show σ' x = 0 from hx, map_zero]
  obtain ⟨s, hs, rfl⟩ := hamem
  set a : A' := algebraMap A A' s with hadef
  have hbij : Function.Bijective (Localization.awayMap σ2.toRingHom a) := by
    constructor
    · rw [Localization.awayMap_injective_iff]
      intro x hx
      exact
        ⟨1, by
          rw [pow_one]; exact hann x hx⟩
    · rw [Localization.awayMap_surjective_iff]
      intro y
      obtain ⟨b, hb⟩ := hsurj y
      exact
        ⟨b, 0, by
          rw [pow_zero, one_mul]; exact hb⟩
  have hcomm :
    ∀ x : B,
      Localization.awayMap σ2.toRingHom a (algebraMap B (Localization.Away a) x) =
        algebraMap B (Localization.Away (σ2 a)) x := by
    intro x
    have hmapcomp :
      ∀ y : A',
        Localization.awayMap σ2.toRingHom a (algebraMap A' (Localization.Away a) y) =
          algebraMap Bf (Localization.Away (σ2 a)) (σ2 y) :=
      fun y => IsLocalization.map_eq _ y
    rw [IsScalarTower.algebraMap_apply B A' (Localization.Away a), hmapcomp,
      IsScalarTower.algebraMap_apply B Bf (Localization.Away (σ2 a))]
    congr 1
    show σ' (algebraMap B A' x) = algebraMap B Bf x
    exact σ'.commutes x
  let φ : Localization.Away a →ₐ[B] Localization.Away (σ2 a) :=
    { Localization.awayMap σ2.toRingHom a with commutes' := hcomm }
  have e1 : Localization.Away a ≃ₐ[B] Localization.Away (σ2 a) := AlgEquiv.ofBijective φ hbij
  have hdisj : Disjoint (Submonoid.powers f₀ : Set B) (p : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := p) f₀).mpr hf₀
  have hPprime : (Ideal.map (algebraMap B Bf) p).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) Bf p ‹p.IsPrime› hdisj
  have hσ2aP : σ2 a ∉ Ideal.map (algebraMap B Bf) p := by
    intro hc
    have h1 : hl (σ2 a) ∈ Ideal.map (algebraMap B L) p := by
      have := Ideal.mem_map_of_mem hl.toRingHom hc
      rwa [Ideal.map_map,
        show hl.toRingHom.comp (algebraMap B Bf) = algebraMap B L from hl.comp_algebraMap] at this
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal] at h1
    have h2 : IsUnit (hl (σ2 a)) := by
      rw [show hl (σ2 a) = algebraMap A L s from by
          rw [show hl (σ2 a) = hl (σ' a) from rfl, hlσ' a, hadef, hτ_apply s]]
      exact IsLocalization.map_units L (⟨s, hs⟩ : Q.primeCompl)
    exact IsLocalRing.notMem_maximalIdeal.mpr h2 h1
  obtain ⟨r, hr, hrloc⟩ :=
    exists_notMem_comap_isLocalization_away (S' := B) (T := Bf) f₀ (Ideal.map (algebraMap B Bf) p)
      hσ2aP
  have hcomap : Ideal.comap (algebraMap B Bf) (Ideal.map (algebraMap B Bf) p) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f₀) Bf ‹p.IsPrime› hdisj
  have hrp : r ∉ p := by rwa [hcomap] at hr
  have e2 : Localization.Away (σ2 a) ≃ₐ[B] Localization.Away r :=
    IsLocalization.algEquiv (Submonoid.powers r) _ _
  have e3 : Localization.Away a ≃ₐ[B] Localization.Away (u * s) :=
    (IsLocalization.algEquiv (Submonoid.powers (u * s)) (Localization.Away a)
          (Localization.Away (u * s))).restrictScalars
      B
  refine
    ⟨r, hrp, u * s, fun hc => (‹Q.IsPrime›.mem_or_mem hc).elim huQ hs,
      ⟨e3.symm.trans (e1.trans e2)⟩⟩

/-- Let `S` and `S'` be `R`-algebras of finite presentation and `q ⊆ S`, `q' ⊆ S'` primes. If the
local rings `S_q` and `S'_{q'}` are isomorphic as `R`-algebras, then `S_g ≅ S'_{g'}` as
`R`-algebras for some `g ∉ q` and `g' ∉ q'`. -/
public theorem solution {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] {S' : Type v'} [CommRing S'] [Algebra R S']
    [Algebra.FinitePresentation R S'] (q : Ideal S) [q.IsPrime] (q' : Ideal S') [q'.IsPrime]
    (Sq : Type w) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q] [Algebra R Sq]
    [IsScalarTower R S Sq] (Sq' : Type w') [CommRing Sq'] [Algebra S' Sq']
    [IsLocalization.AtPrime Sq' q'] [Algebra R Sq'] [IsScalarTower R S' Sq'] (e : Sq ≃ₐ[R] Sq') :
    ∃ g ∉ q, ∃ g' ∉ q', Nonempty (Localization.Away g ≃ₐ[R] Localization.Away g') := by
  classical
  obtain ⟨g', hg', ψ, fT, hfT, hcomp⟩ :=
    exists_mem_algHom_localizationAway_of_finitePresentation (M := q'.primeCompl) (Tm := Sq')
      (e.toAlgHom.comp (IsScalarTower.toAlgHom R S Sq))
  set T := Localization.Away g' with hTdef
  let algST : Algebra S T := ψ.toRingHom.toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  have : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T
  let algSSq' : Algebra S Sq' := (e.toRingEquiv.toRingHom.comp (algebraMap S Sq)).toAlgebra
  have : IsLocalization.AtPrime Sq' q :=
    (IsLocalization.isLocalization_iff_of_ringEquiv (M := q.primeCompl) (S := Sq) e.toRingEquiv).mp
      inferInstance
  let algTSq' : Algebra T Sq' := fT.toRingHom.toAlgebra
  have htower : IsScalarTower S' T Sq' := IsScalarTower.of_algebraMap_eq fun x => (hfT x).symm
  set Q : Ideal T := Ideal.map (algebraMap S' T) q' with hQdef
  have hdisj : Disjoint (Submonoid.powers g' : Set S') (q' : Set S') :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := q') g').mpr hg'
  have hQp : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g') T q' ‹q'.IsPrime› hdisj
  have hQc : Ideal.comap (algebraMap S' T) Q = q' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g') T ‹q'.IsPrime› hdisj
  have : IsLocalization.AtPrime Sq' Q :=
    isLocalization_atPrime_map (Submonoid.powers g') T Sq' q' hdisj
  have : IsScalarTower S T Sq' := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show algebraMap S Sq' x = fT (ψ x)
    exact (congrArg (fun g : S →ₐ[R] Sq' => g x) hcomp).symm
  obtain ⟨f, hf, a, haQ, ⟨e1⟩⟩ :=
    exists_notMem_algEquiv_localizationAway_of_isLocalization_atPrime (B := S) (A := T) (L := Sq')
      q Q
  obtain ⟨r, hr, hrloc⟩ := exists_notMem_comap_isLocalization_away (T := T) g' Q haQ
  refine ⟨f, hf, r, hQc ▸ hr, ⟨?_⟩⟩
  have e2 : Localization.Away r ≃ₐ[S'] Localization.Away a :=
    IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) (Localization.Away a)
  refine ((e2.restrictScalars R).trans ?_).symm
  refine AlgEquiv.ofRingEquiv (f := e1.toRingEquiv) fun x => ?_
  show e1 (algebraMap R (Localization.Away a) x) = algebraMap R (Localization.Away f) x
  rw [IsScalarTower.algebraMap_apply R S (Localization.Away a),
    IsScalarTower.algebraMap_apply R S (Localization.Away f), e1.commutes]

end Stacks.SpreadingOut.LocalIsoSplitting

end

@[expose] public section

namespace Algebra.FinitePresentation

/-- Let `R` be a ring, let `S` and `S'` be `R`-algebras of finite presentation,
and let `q ⊆ S`, `q' ⊆ S'` be primes. If the local rings `S_q` and `S'_{q'}` are isomorphic as
`R`-algebras, then there are `g ∈ S`, `g ∉ q` and `g' ∈ S'`, `g' ∉ q'` such that `S_g` and
`S'_{g'}` are isomorphic as `R`-algebras. -/
@[stacks 00QS "The local rings `S_q`, `S'_{q'}` are abstract (`IsLocalization.AtPrime Sq q` with
`IsScalarTower R S Sq`, so that the `R`-algebra structure is the composite `R → S → Sq`), which
makes the hypothesis available for any model; the localizations `S_g`, `S'_{g'}` of the
conclusion are the models `Localization.Away g`, `Localization.Away g'`, a choice that costs no
strength by uniqueness of localizations. As in the source only the existence of an `R`-algebra
isomorphism is claimed, not the compatibility with the given isomorphism of local rings that the
proof also produces. See the module docstring."]
public theorem exists_algEquiv_localizationAway_of_algEquiv_atPrime {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] {S' : Type v'}
    [CommRing S'] [Algebra R S'] [Algebra.FinitePresentation R S'] (q : Ideal S) [q.IsPrime]
    (q' : Ideal S') [q'.IsPrime] (Sq : Type w) [CommRing Sq] [Algebra S Sq]
    [IsLocalization.AtPrime Sq q] [Algebra R Sq] [IsScalarTower R S Sq] (Sq' : Type w')
    [CommRing Sq'] [Algebra S' Sq'] [IsLocalization.AtPrime Sq' q'] [Algebra R Sq']
    [IsScalarTower R S' Sq'] (e : Sq ≃ₐ[R] Sq') :
    ∃ g ∉ q, ∃ g' ∉ q', Nonempty (Localization.Away g ≃ₐ[R] Localization.Away g') :=
  Stacks.SpreadingOut.LocalIsoSplitting.solution q q' Sq Sq' e

end Algebra.FinitePresentation

end
