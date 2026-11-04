module

public import Mathlib
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import Mathlib.Topology.UniformSpace.Completion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.FormallySmooth.RegularLocal
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.Kaehler.SmoothRingMapsInTheNoetherianCase
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import Mathlib.RingTheory.MvPowerSeries.Ideal

/-!
# Formally smooth maps of local rings: square-zero lifting

This file starts the proof of the local lifting criterion for formal smoothness of a local
homomorphism for the maximal-ideal-adic topologies. It collects auxiliary facts about
continuous maps from adic to discrete rings, nilpotent maximal ideals, square-zero kernels,
Artinian rings and small extensions, and proves that formal smoothness for the adic topologies
is equivalent to lifting through residually trivial square-zero quotients whose source has
nilpotent maximal ideal.

The definitions and the statement of the criterion are in
`StacksFrontier.RingTheory.FormallySmooth.LocalRings.LiftingCriterion`.

## References

* [Stacks Project, Tag 0DYG](https://stacks.math.columbia.edu/tag/0DYG)
-/

@[expose] public section

/-! ### The local lifting criterion -/

section

section

open InfinitesimalLifting

/-- The discrete topology on a ring is the adic topology of the zero ideal. -/
private theorem bot_topology_eq_adicTopology_bot (B : Type*) [CommRing B] :
    (⊥ : TopologicalSpace B) = (⊥ : Ideal B).adicTopology := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  have : IsTopologicalRing B := inferInstance
  exact (is_bot_adic_iff (A := B)).2 inferInstance

/-- A continuous map from an adic local ring to a discrete ring kills a power of the maximal
ideal. -/
private theorem exists_maximalIdeal_pow_forall_map_eq_zero
    {S B : Type*} [CommRing S] [IsLocalRing S] [CommRing B] [TopologicalSpace B]
    [DiscreteTopology B] (f : S →+* B)
    (hf : @Continuous S B (IsLocalRing.maximalIdeal S).adicTopology _ f) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ IsLocalRing.maximalIdeal S ^ n, f x = 0 := by
  have hfdisc : @Continuous S B (IsLocalRing.maximalIdeal S).adicTopology
      (⊥ : TopologicalSpace B) f := by
    rwa [(inferInstance : DiscreteTopology B).eq_bot] at hf
  rw [bot_topology_eq_adicTopology_bot] at hfdisc
  obtain ⟨n, hn, hker⟩ := (RingHom.continuous_adic_iff f _ ⊥).mp hfdisc
  exact ⟨n, hn, fun x hx => Ideal.mem_bot.1 (hker x hx)⟩

/-- If a surjection of local rings kills `𝔪 ^ n`, then the target has `𝔪 ^ n = ⊥`. -/
private theorem maximalIdeal_pow_eq_bot_of_surjective_of_forall_eq_zero
    {S T : Type*} [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]
    (g : S →+* T) (hg : Function.Surjective g) {n : ℕ}
    (h : ∀ x ∈ IsLocalRing.maximalIdeal S ^ n, g x = 0) :
    IsLocalRing.maximalIdeal T ^ n = ⊥ := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective g hg, ← Ideal.map_pow]
  apply bot_unique
  rw [Ideal.map_le_iff_le_comap]
  exact fun x hx => Ideal.mem_bot.2 (h x hx)

private theorem continuous_adic_to_discrete_of_local
    {R A : Type*} [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    (f : R →+* A) [IsLocalHom f]
    (h : ∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥) :
    @Continuous R A (IsLocalRing.maximalIdeal R).adicTopology
      (⊥ : TopologicalSpace A) f := by
  obtain ⟨n, hn, hpow⟩ := h
  have hmap : Ideal.map f (IsLocalRing.maximalIdeal R) ≤ IsLocalRing.maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit f x hx
  rw [bot_topology_eq_adicTopology_bot]
  apply (RingHom.continuous_adic_iff f _ ⊥).2
  refine ⟨n, hn, ?_⟩
  intro x hx
  have hxmap : f x ∈ Ideal.map f (IsLocalRing.maximalIdeal R ^ n) :=
    Ideal.mem_map_of_mem f hx
  rw [Ideal.map_pow] at hxmap
  have : f x ∈ IsLocalRing.maximalIdeal A ^ n := (Ideal.pow_right_mono hmap n) hxmap
  simpa [hpow] using this

theorem quotient_maximalIdeal_nilpotent
    {A : Type*} [CommRing A] [IsLocalRing A] (J : Ideal A)
    [IsLocalRing (A ⧸ J)]
    (h : ∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥) :
    ∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal (A ⧸ J) ^ n = ⊥ := by
  obtain ⟨n, hn, hpow⟩ := h
  refine ⟨n, hn, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, ← Ideal.map_pow, hpow]
  simp

private theorem localHom_of_surjective_squareZero_ker
    {P Q : Type*} [CommRing P] [CommRing Q] (f : P →+* Q)
    (hsurj : Function.Surjective f) (hker : (RingHom.ker f) ^ 2 = ⊥) :
    IsLocalHom f := by
  refine ⟨?_⟩
  intro x hx
  obtain ⟨u, hu⟩ := hx
  obtain ⟨y, hy⟩ := hsurj (↑u⁻¹)
  have hmem : x * y - 1 ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, map_mul, ← hu, hy]
    simp
  have hzero : (x * y - 1) ^ 2 = 0 := by
    have := Ideal.pow_mem_pow hmem 2
    simpa [hker] using this
  have hun : IsUnit (x * y) := by
    have hn : IsNilpotent (x * y - 1) := ⟨2, hzero⟩
    have := hn.isUnit_one_add
    simpa using this
  exact ((Commute.all x y).isUnit_mul_iff.mp hun).1

private theorem maximalIdeal_pow_eq_bot_of_surjective_squareZero_ker
    {P Q : Type*} [CommRing P] [IsLocalRing P] [CommRing Q] [IsLocalRing Q]
    (f : P →+* Q) (hsurj : Function.Surjective f)
    (hker : (RingHom.ker f) ^ 2 = ⊥)
    {n : ℕ} (hQ : IsLocalRing.maximalIdeal Q ^ n = ⊥) :
    IsLocalRing.maximalIdeal P ^ (n * 2) = ⊥ := by
  have hmap : Ideal.map f (IsLocalRing.maximalIdeal P) =
      IsLocalRing.maximalIdeal Q :=
    IsLocalRing.map_maximalIdeal_of_surjective f hsurj
  have hle : IsLocalRing.maximalIdeal P ^ n ≤ RingHom.ker f := by
    intro x hx
    rw [RingHom.mem_ker]
    have hxmap : f x ∈ Ideal.map f (IsLocalRing.maximalIdeal P ^ n) :=
      Ideal.mem_map_of_mem f hx
    rw [Ideal.map_pow, hmap, hQ] at hxmap
    simpa using hxmap
  apply bot_unique
  rw [pow_mul]
  exact (Ideal.pow_right_mono hle 2).trans_eq hker

/-- The quotient map `A → A ⧸ J` restricted to the preimage of a subring `T`, as a map to `T`. -/
private def comapQuotientRestrict {A : Type*} [CommRing A] (J : Ideal A)
    (T : Subring (A ⧸ J)) : T.comap (Ideal.Quotient.mk J) →+* T :=
  ((Ideal.Quotient.mk J).comp (T.comap (Ideal.Quotient.mk J)).subtype).codRestrict T
    fun x => x.property

private theorem comapQuotientRestrict_surjective {A : Type*} [CommRing A] (J : Ideal A)
    (T : Subring (A ⧸ J)) : Function.Surjective (comapQuotientRestrict J T) := by
  intro y
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (y : A ⧸ J)
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  show (Ideal.Quotient.mk J) x ∈ T
  rw [hx]
  exact y.property

private theorem ker_comapQuotientRestrict_sq {A : Type*} [CommRing A] (J : Ideal A)
    (T : Subring (A ⧸ J)) (hJ : J ^ 2 = ⊥) :
    (RingHom.ker (comapQuotientRestrict J T)) ^ 2 = ⊥ := by
  let P : Subring A := T.comap (Ideal.Quotient.mk J)
  have hmap : Ideal.map P.subtype (RingHom.ker (comapQuotientRestrict J T)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [RingHom.mem_ker] at hx
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
      (show (Ideal.Quotient.mk J) (x : A) = 0 from congrArg Subtype.val hx)
  apply bot_unique
  intro x hx
  have hxmap : (x : A) ∈ Ideal.map P.subtype ((RingHom.ker (comapQuotientRestrict J T)) ^ 2) :=
    Ideal.mem_map_of_mem P.subtype hx
  rw [Ideal.map_pow] at hxmap
  have hxJ : (x : A) ∈ J ^ 2 := (Ideal.pow_right_mono hmap 2) hxmap
  have hx0 : (x : A) = 0 := by simpa [hJ] using hxJ
  exact show x = 0 from Subtype.ext hx0

theorem isLocalRing_comap_quotient_squareZero
    {A : Type*} [CommRing A] (J : Ideal A) (T : Subring (A ⧸ J))
    [IsLocalRing T] (hJ : J ^ 2 = ⊥) :
    IsLocalRing (T.comap (Ideal.Quotient.mk J)) := by
  let : IsLocalHom (comapQuotientRestrict J T) :=
    localHom_of_surjective_squareZero_ker _ (comapQuotientRestrict_surjective J T)
      (ker_comapQuotientRestrict_sq J T hJ)
  exact RingHom.domain_isLocalRing (comapQuotientRestrict J T)

theorem residueField_map_bijective_of_surjective
    {P Q : Type*} [CommRing P] [IsLocalRing P] [CommRing Q] [IsLocalRing Q]
    (f : P →+* Q) [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Bijective (IsLocalRing.ResidueField.map f) := by
  constructor
  · exact (IsLocalRing.ResidueField.map f).injective
  · intro y
    obtain ⟨q, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨p, rfl⟩ := hf q
    exact ⟨IsLocalRing.residue P p, IsLocalRing.ResidueField.map_residue f p⟩

private theorem isArtinianRing_range_of_continuous_adic
    {S B : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [CommRing B] [TopologicalSpace B] [DiscreteTopology B] [Nontrivial B]
    (f : S →+* B)
    (hf : @Continuous S B (IsLocalRing.maximalIdeal S).adicTopology _ f) :
    IsArtinianRing f.range := by
  let T : Subring B := f.range
  let fT : S →+* T := f.rangeRestrict
  let : IsLocalRing T := IsLocalRing.of_surjective' fT f.rangeRestrict_surjective
  let : IsNoetherianRing T :=
    isNoetherianRing_of_surjective S T fT f.rangeRestrict_surjective
  obtain ⟨n, _, hker⟩ := exists_maximalIdeal_pow_forall_map_eq_zero f hf
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal T).2 ⟨n,
    maximalIdeal_pow_eq_bot_of_surjective_of_forall_eq_zero fT f.rangeRestrict_surjective
      fun x hx => Subtype.ext (hker x hx)⟩

theorem isSemisimpleModule_ideal_of_maximalIdeal_mul_eq_bot
    {A : Type*} [CommRing A] [IsLocalRing A] (J : Ideal A)
    (hJ : IsLocalRing.maximalIdeal A * J = ⊥) :
    IsSemisimpleModule A J := by
  have ht : Module.IsTorsionBySet A J (IsLocalRing.maximalIdeal A) := by
    intro x a
    apply Subtype.ext
    have hx : (a : A) * (x : A) ∈ IsLocalRing.maximalIdeal A * J :=
      Ideal.mul_mem_mul a.property x.property
    simpa [hJ] using hx
  let : Module (A ⧸ IsLocalRing.maximalIdeal A) J := ht.module
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  exact ht.isSemisimpleModule_iff.mp inferInstance

private theorem isArtinianRing_of_artinian_quotient_of_artinian_ideal
    {A : Type*} [CommRing A] (J : Ideal A)
    [IsArtinianRing (A ⧸ J)] [IsArtinian A J] : IsArtinianRing A := by
  apply isArtinianRing_iff.mpr
  apply (isArtinian_iff_submodule_quotient J).mpr
  refine ⟨inferInstance, ?_⟩
  exact isArtinian_of_surjective_algebraMap (R := A ⧸ J) (S := A)
    (M := A ⧸ J) Ideal.Quotient.mk_surjective

theorem isSmallExtension_of_surjective_simple_ker.{u}
    {B C : Type u} [CommRing B] [IsLocalRing B]
    [CommRing C] [IsLocalRing C] [IsArtinianRing C]
    (p : B →+* C) (hp : Function.Surjective p)
    [IsSimpleModule B (RingHom.ker p)] :
    IsSmallExtension (CommRingCat.ofHom p) := by
  let e : B ⧸ RingHom.ker p ≃+* C := p.quotientKerEquivOfSurjective hp
  let : IsArtinianRing (B ⧸ RingHom.ker p) := e.symm.isArtinianRing
  have : IsArtinian B (RingHom.ker p) := inferInstance
  let : IsArtinianRing B :=
    isArtinianRing_of_artinian_quotient_of_artinian_ideal (RingHom.ker p)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    hp, Module.length_eq_one B (RingHom.ker p)⟩

theorem formallySmooth_lifts_local_squareZero.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ]
    (hfs : @IsFormallySmooth.{u, v, w} R S _
      (IsLocalRing.maximalIdeal R).adicTopology
      (IsLocalRing.maximalIdeal R).ringFilterBasis.isTopologicalRing
      (IsLocalRing.maximalIdeal R).isLinearTopology _
      (IsLocalRing.maximalIdeal S).adicTopology
      (IsLocalRing.maximalIdeal S).ringFilterBasis.isTopologicalRing
      (IsLocalRing.maximalIdeal S).isLinearTopology φ) :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] (J : Ideal A)
      [IsLocalRing (A ⧸ J)], J ^ 2 = ⊥ →
      (∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥) →
      ∀ (f : R →+* A) [IsLocalHom f] (gbar : S →+* A ⧸ J) [IsLocalHom gbar],
        gbar.comp φ = (Ideal.Quotient.mk J).comp f →
        Function.Bijective (IsLocalRing.ResidueField.map gbar) →
        ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
          (Ideal.Quotient.mk J).comp g = gbar := by
  intro A _ _ J _ hJ hnil f _ gbar _ hcomm _
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : DiscreteTopology (A ⧸ J) :=
    QuotientAddGroup.discreteTopology (isOpen_discrete (J : Set A))
  have hfcont : @Continuous R A (IsLocalRing.maximalIdeal R).adicTopology _ f :=
    continuous_adic_to_discrete_of_local f hnil
  have hgcont : @Continuous S (A ⧸ J) (IsLocalRing.maximalIdeal S).adicTopology
      _ gbar := by
    have htarget := continuous_adic_to_discrete_of_local gbar
      (quotient_maximalIdeal_nilpotent J hnil)
    rw [(inferInstance : DiscreteTopology (A ⧸ J)).eq_bot]
    exact htarget
  obtain ⟨g, hgcont, hgφ, hgg⟩ := hfs.2 A J hJ f hfcont gbar hgcont hcomm
  refine ⟨g, ?_, hgφ, hgg⟩
  have : IsLocalHom ((Ideal.Quotient.mk J).comp g) := hgg ▸ inferInstance
  exact isLocalHom_of_comp g (Ideal.Quotient.mk J)

theorem lifts_localSquareZero_formallySmooth.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ]
    (hls : ∀ (A : Type u) [CommRing A] [IsLocalRing A] (J : Ideal A)
      [IsLocalRing (A ⧸ J)], J ^ 2 = ⊥ →
      (∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal A ^ n = ⊥) →
      ∀ (f : R →+* A) [IsLocalHom f] (gbar : S →+* A ⧸ J) [IsLocalHom gbar],
        gbar.comp φ = (Ideal.Quotient.mk J).comp f →
        Function.Bijective (IsLocalRing.ResidueField.map gbar) →
        ∃ g : S →+* A, IsLocalHom g ∧ g.comp φ = f ∧
          (Ideal.Quotient.mk J).comp g = gbar) :
    @IsFormallySmooth.{u, v, w} R S _
      (IsLocalRing.maximalIdeal R).adicTopology
      (IsLocalRing.maximalIdeal R).ringFilterBasis.isTopologicalRing
      (IsLocalRing.maximalIdeal R).isLinearTopology _
      (IsLocalRing.maximalIdeal S).adicTopology
      (IsLocalRing.maximalIdeal S).ringFilterBasis.isTopologicalRing
      (IsLocalRing.maximalIdeal S).isLinearTopology φ := by
  constructor
  · apply (RingHom.continuous_adic_iff φ _ _).2
    refine ⟨1, le_rfl, ?_⟩
    intro x hx
    simpa using map_nonunit φ x (by simpa using hx)
  · intro A _ _ _ J hJ f hf gbar hgbar hcomm
    let : TopologicalSpace S := (IsLocalRing.maximalIdeal S).adicTopology
    by_cases hA : Nontrivial A
    · let : Nontrivial A := hA
      have hJne : J ≠ ⊤ := by
        intro heq
        have hbot : (⊤ : Ideal A) = ⊥ := by simp [heq, Ideal.top_pow] at hJ
        have hone : (1 : A) ∈ (⊥ : Ideal A) := hbot ▸ (show (1 : A) ∈ (⊤ : Ideal A) from trivial)
        exact (one_ne_zero : (1 : A) ≠ 0) (by simp at hone)
      let : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
      let T : Subring (A ⧸ J) := gbar.range
      let gT : S →+* T := gbar.rangeRestrict
      let : IsLocalRing T := IsLocalRing.of_surjective' gT gbar.rangeRestrict_surjective
      let P : Subring A := T.comap (Ideal.Quotient.mk J)
      let : IsLocalRing P := isLocalRing_comap_quotient_squareZero J T hJ
      let qP : P →+* T := comapQuotientRestrict J T
      have hqP : Function.Surjective qP := comapQuotientRestrict_surjective J T
      let K : Ideal P := RingHom.ker qP
      have hK : K ^ 2 = ⊥ := ker_comapQuotientRestrict_sq J T hJ
      let e : P ⧸ K ≃+* T := qP.quotientKerEquivOfSurjective hqP
      let : IsLocalRing (P ⧸ K) := e.symm.isLocalRing
      let : IsLocalHom qP := IsLocalHom.of_surjective qP hqP
      let : IsLocalHom gT := IsLocalHom.of_surjective gT gbar.rangeRestrict_surjective
      let fP : R →+* P := f.codRestrict P (by
        intro r
        show (Ideal.Quotient.mk J) (f r) ∈ T
        rw [← RingHom.comp_apply, ← hcomm]
        exact ⟨φ r, rfl⟩)
      have : IsLocalHom fP := by
        have : qP.comp fP = gT.comp φ := by
          exact RingHom.ext fun r => Subtype.ext (congrArg (fun h : R →+* A ⧸ J => h r) hcomm).symm
        have : IsLocalHom (qP.comp fP) := by rw [this]; infer_instance
        exact isLocalHom_of_comp fP qP
      let gP : S →+* P ⧸ K := e.symm.toRingHom.comp gT
      let : IsLocalHom e.symm.toRingHom :=
        IsLocalHom.of_surjective e.symm.toRingHom e.symm.surjective
      have : IsLocalHom gP := by
        dsimp [gP]
        infer_instance
      have hgPsurj : Function.Surjective gP := e.symm.surjective.comp gbar.rangeRestrict_surjective
      have hgbij : Function.Bijective (IsLocalRing.ResidueField.map gP) :=
        residueField_map_bijective_of_surjective gP hgPsurj
      have hcommP : gP.comp φ = (Ideal.Quotient.mk K).comp fP := by
        rw [← qP.quotientKerEquivOfSurjective_symm_comp hqP]
        exact RingHom.ext fun r => congrArg e.symm <|
          Subtype.ext (congrArg (fun h : R →+* A ⧸ J => h r) hcomm)
      have hnilP : ∃ n : ℕ, 0 < n ∧ IsLocalRing.maximalIdeal P ^ n = ⊥ := by
        let : DiscreteTopology (A ⧸ J) :=
          QuotientAddGroup.discreteTopology (isOpen_discrete (J : Set A))
        obtain ⟨m, hm, hker⟩ := exists_maximalIdeal_pow_forall_map_eq_zero gbar hgbar
        have hTm := maximalIdeal_pow_eq_bot_of_surjective_of_forall_eq_zero gT
          gbar.rangeRestrict_surjective fun x hx => Subtype.ext (hker x hx)
        refine ⟨m * 2, by lia, ?_⟩
        exact maximalIdeal_pow_eq_bot_of_surjective_squareZero_ker qP hqP hK hTm
      obtain ⟨g, hg, hgφ, hgq⟩ := hls P K hK hnilP fP gP hcommP hgbij
      refine ⟨P.subtype.comp g, ?_, ?_, ?_⟩
      · let : TopologicalSpace P := ⊥
        let : DiscreteTopology P := ⟨rfl⟩
        have hgc : @Continuous S P (IsLocalRing.maximalIdeal S).adicTopology _ g :=
          continuous_adic_to_discrete_of_local g hnilP
        have hs : @Continuous P A (⊥ : TopologicalSpace P) _ P.subtype :=
          continuous_of_discreteTopology
        exact hs.comp hgc
      · exact (RingHom.comp_assoc ..).trans (by rw [hgφ]; rfl)
      · apply RingHom.ext
        intro s
        have he : e ((Ideal.Quotient.mk K) (g s)) = e (gP s) :=
          congrArg e (congrArg (fun h : S →+* P ⧸ K => h s) hgq)
        have hq : qP (g s) = gT s := by
          have hmk : e ((Ideal.Quotient.mk K) (g s)) = qP (g s) :=
            qP.quotientKerEquivOfSurjective_apply_mk hqP (g s)
          have hsec : e (gP s) = gT s := by
            show e (e.symm (gT s)) = gT s
            exact e.apply_symm_apply _
          rwa [hmk, hsec] at he
        exact congrArg Subtype.val hq
    · let : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
      let g : S →+* A :=
        { toFun := fun _ => 0
          map_one' := Subsingleton.elim _ _
          map_mul' := fun _ _ => Subsingleton.elim _ _
          map_zero' := rfl
          map_add' := fun _ _ => Subsingleton.elim _ _ }
      have : Subsingleton (A ⧸ J) := inferInstance
      refine ⟨g, ?_, ?_, ?_⟩
      · exact (show @Continuous S A (IsLocalRing.maximalIdeal S).adicTopology _ g from
          continuous_const)
      · exact RingHom.ext fun _ => Subsingleton.elim _ _
      · exact RingHom.ext fun _ => Subsingleton.elim _ _

end

end

end
