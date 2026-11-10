module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.Separation.Connected
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.FormallySmooth.AdicLifting
public import StacksFrontier.RingTheory.FormallySmooth.Algebraic
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.RegularLocalRing.Colimit
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import StacksFrontier.RingTheory.AdicCompletion.EndomorphismCongruentToIdentity
public import StacksFrontier.RingTheory.MvPowerSeries.RegularLocal
public import StacksFrontier.RingTheory.RegularLocalRing.Colimit
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Adic formal smoothness implies regularity

A Noetherian local algebra over a field is a regular local ring if its structure
map is formally smooth for the topology defined by its maximal ideal.

## Main definitions

No new definitions are introduced.

## Main results

* `RingHom.FormallySmoothTop.isRegularLocalRing_of_maximalIdeal`: a Noetherian
  local algebra over a field that is formally smooth for its maximal-ideal adic
  topology is regular.

## Implementation notes

The base field carries the discrete topology, while the algebra carries the
adic topology associated to its canonical maximal ideal.

## References

* [Stacks Project, Tag 07EI](https://stacks.math.columbia.edu/tag/07EI)
-/

@[expose] public section

namespace RingHom.FormallySmoothTop

open IsLocalRing

open Stacks.CompleteLocalRing.CohenStructure

open Stacks.CompleteLocalRing.RegularSubring

open Stacks.RegularLocalRing.SpanFinrank

/-- Compatibility of maps into a surjective quotient presentation `π : P → S` can be checked
after composing with the quotient map `P → P ⧸ ker π`. -/
private theorem comp_eq_iff_mk_comp_eq_quotientKerEquiv_symm_comp
    {P S T : Type*} [CommRing P] [CommRing S] [CommRing T]
    {π : P →+* S} (hπ : Function.Surjective π) (u : T →+* P) (v : T →+* S) :
    π.comp u = v ↔ (Ideal.Quotient.mk (RingHom.ker π)).comp u =
      (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom.comp v := by
  rw [← RingHom.quotientKerEquivOfSurjective_symm_comp hπ, RingHom.comp_assoc]
  exact ⟨fun h => h ▸ rfl, fun h => RingHom.ext fun x =>
    (RingHom.quotientKerEquivOfSurjective hπ).symm.injective (congrArg (· x) h)⟩

/-- A formally smooth map lifts a quotient presentation to a section when the
presentation ring is adically complete. -/
private theorem exists_section_of_formallySmooth_of_quotient.{u, v, w}
    {R : Type u} {S : Type v} {P : Type w}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [CommRing P] [TopologicalSpace P] [IsTopologicalRing P]
    (f : R →+* S) (n : Ideal S) (hn : IsAdic n)
    (hf : RingHom.FormallySmoothTop.{w} f)
    (I : Ideal P) (hI : IsAdic I) [IsAdicComplete I P]
    (π : P →+* S) (hπ : Function.Surjective π)
    (hJ : IsClosed (RingHom.ker π : Set P))
    (hJI : RingHom.ker π ≤ I)
    (g : R →+* P) (hg : Continuous g)
    (hπg : π.comp g = f)
    (hψ : Continuous
      ((RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom :
        S →+* P ⧸ RingHom.ker π)) :
    ∃ s : S →+* P, Continuous s ∧ s.comp f = g ∧ π.comp s = RingHom.id S := by
  let J := RingHom.ker π
  let ψ : S →+* P ⧸ J := (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  obtain ⟨s, hs, hsf, hsq⟩ :=
    RingHom.FormallySmoothTop.exists_continuous_lift_of_isAdic
      f n hn hf I hI J hJ 1 (by omega)
      (show J ^ 1 ≤ I from by simpa only [pow_one, J] using hJI)
      g hg ψ hψ
      (((comp_eq_iff_mk_comp_eq_quotientKerEquiv_symm_comp hπ g f).1 hπg).symm)
  exact ⟨s, hs, hsf, (comp_eq_iff_mk_comp_eq_quotientKerEquiv_symm_comp hπ s _).2 hsq⟩

/-- A complete local ring containing a field has a coefficient field: a ring map from its residue
field splitting the residue map. By the Cohen structure theorem the coefficient ring `Λ` of `R`
has maximal ideal generated by the residue characteristic, which vanishes in `R` because `R`
contains a field; so `Λ` is a field mapping isomorphically onto the residue field. -/
private theorem exists_ringHom_residue_comp_eq_id.{u, v} (R : Type u)
    [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (F : Type v) [Field F] [Algebra F R] :
    ∃ f : ResidueField R →+* R, (residue R).comp f = RingHom.id (ResidueField R) := by
  obtain ⟨Λ, hΛ⟩ :=
    (IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries R).1
  have := hΛ.isLocalHom
  -- the residue characteristic vanishes in `R`, because `R` contains a field
  let _ : Algebra F (ResidueField R) := ((residue R).comp (algebraMap F R)).toAlgebra
  have : CharP (ResidueField R) (ringChar F) :=
    charP_of_injective_algebraMap
      (RingHom.injective (algebraMap F (ResidueField R))) (ringChar F)
  have hchar : (ringChar (ResidueField R) : R) = 0 := by
    rw [CharP.eq (ResidueField R) (ringChar.charP (ResidueField R)) ‹_›,
      ← map_natCast (algebraMap F R) (ringChar F), ringChar.Nat.cast_ringChar, map_zero]
  -- hence the coefficient ring is a field
  have hbot : maximalIdeal Λ.toSubring = ⊥ := by
    rw [← IsLocalRing.maximalIdeal_comap Λ.toSubring.subtype,
      hΛ.comap_maximalIdeal_eq_span_ringChar, Ideal.span_singleton_eq_bot]
    exact Subtype.ext (by push_cast; exact hchar)
  let _ : Field Λ.toSubring := (isField_iff_maximalIdeal_eq.2 hbot).toField
  -- and it maps isomorphically onto the residue field of `R`, so its inverse splits `R → R/𝔪`
  have hbij : Function.Bijective ((residue R).comp Λ.toSubring.subtype) := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨x, hx⟩ := hΛ.residueField_map_surjective y
    obtain ⟨z, hz⟩ : ∃ z, residue Λ.toSubring z = x := Ideal.Quotient.mk_surjective x
    exact ⟨z, by rw [RingHom.comp_apply, ← ResidueField.map_residue Λ.toSubring.subtype z, hz, hx]⟩
  exact ⟨Λ.toSubring.subtype.comp (RingEquiv.ofBijective _ hbij).symm.toRingHom,
    RingHom.ext fun x => (RingEquiv.ofBijective _ hbij).apply_symm_apply x⟩

/-- A split quotient of a complete Noetherian local ring is an isomorphism when
the quotient kernel has no nonzero linear term. -/
private def ringEquiv_of_split_surjective_of_ker_le_maximalIdeal_sq
    {P A : Type*} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    [IsAdicComplete (IsLocalRing.maximalIdeal P) P] [CommRing A]
    (π : P →+* A) (s : A →+* P)
    (hπs : π.comp s = RingHom.id A)
    (hker : RingHom.ker π ≤ (IsLocalRing.maximalIdeal P) ^ 2) : P ≃+* A := by
  have hφ : ∀ x : P, (s.comp π) x - x ∈ (IsLocalRing.maximalIdeal P) ^ 2 := by
    intro x
    apply hker
    rw [RingHom.mem_ker, map_sub, RingHom.comp_apply]
    have := congrArg (fun f : A →+* A => f (π x)) hπs
    simpa only [RingHom.comp_apply, RingHom.id_apply, sub_self] using congrArg
      (fun y : A => y - π x) this
  have hsurj := surjective_of_sub_id_mem_maximalIdeal_sq P (s.comp π) hφ
  have hφid : ∀ x : P, (s.comp π) x = x := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    have hidem := congrArg (fun f : A →+* A => f (π y)) hπs
    simpa only [RingHom.comp_apply, RingHom.id_apply] using congrArg s hidem
  exact
    { toFun := π
      invFun := s
      left_inv := hφid
      right_inv := fun x => congrArg (fun f : A →+* A => f x) hπs
      map_mul' := π.map_mul
      map_add' := π.map_add }

/-- A surjective map of local rings is a quotient map for the maximal-ideal
adic topologies. -/
private theorem isQuotientMap_of_surjective_local
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [WithIdeal R] [WithIdeal S]
    (hR : WithIdeal.i = maximalIdeal R) (hS : WithIdeal.i = maximalIdeal S)
    (f : R →+* S) (hf : Function.Surjective f) : Topology.IsQuotientMap f := by
  have hm : Ideal.map f (WithIdeal.i : Ideal R) = WithIdeal.i := by
    rw [hR, hS, map_maximalIdeal_of_surjective f hf]
  have hc := (WithIdeal.uniformContinuous_of_map_le hm.le).continuous
  refine IsOpenMap.isQuotientMap ?_ hc hf
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
  apply ((WithIdeal.i : Ideal R).hasBasis_nhds_zero_adic.map f).ge_iff.mpr
  intro n _
  have he : f '' (((WithIdeal.i : Ideal R) ^ n : Ideal R) : Set R) =
      (((WithIdeal.i : Ideal S) ^ n : Ideal S) : Set S) := by
    rw [← hm, ← Ideal.map_pow]
    ext x
    exact (Ideal.mem_map_iff_of_surjective f hf).symm
  rw [he]
  exact (WithIdeal.i : Ideal S).hasBasis_nhds_zero_adic.mem_of_mem trivial

/-- A map carrying an ideal into an ideal of completeness extends to the
adic completion. -/
private theorem exists_ringHom_from_adicCompletion
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) [IsAdicComplete J S]
    (f : R →+* S) (hf : I.map f ≤ J) :
    ∃ F : AdicCompletion I R →+* S,
      ∀ n x, Ideal.Quotient.mk (J ^ n) (F x) =
        Ideal.quotientMap (J ^ n) f
          (Ideal.map_le_iff_le_comap.mp (by
            rw [Ideal.map_pow]; exact Ideal.pow_right_mono hf n))
          (AdicCompletion.evalₐ I n x) := by
  have hle : ∀ n, I ^ n ≤ (J ^ n).comap f := fun n =>
    Ideal.map_le_iff_le_comap.mp (by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono hf n)
  let fs := fun n => (Ideal.quotientMap (J ^ n) f (hle n)).comp
    (AdicCompletion.evalₐ I n).toRingHom
  have hfs : ∀ {m n} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J hmn).comp (fs n) = fs m := by
    intro m n hmn
    have hq : (Ideal.Quotient.factorPow J hmn).comp
        (Ideal.quotientMap (J ^ n) f (hle n)) =
        (Ideal.quotientMap (J ^ m) f (hle m)).comp (Ideal.Quotient.factorPow I hmn) := by
      ext a
      simp
    ext x
    change ((Ideal.Quotient.factorPow J hmn).comp
      (Ideal.quotientMap (J ^ n) f (hle n))) _ = _
    rw [hq, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AdicCompletion.factorPow_evalₐ]
    rfl
  exact ⟨IsAdicComplete.liftRingHom J fs hfs,
    fun n x => IsAdicComplete.mk_liftRingHom J fs hfs n x⟩

/-- An element of the completion is congruent to an element of the original
ring modulo each power of the extended ideal. -/
private theorem exists_sub_algebraMap_mem_pow_adicCompletion
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    (x : AdicCompletion I R) (n : ℕ) :
    ∃ a : R, x - algebraMap R (AdicCompletion I R) a ∈
      (I.map (algebraMap R (AdicCompletion I R))) ^ n ∧
      AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a := by
  induction x using AdicCompletion.induction_on with
  | h a =>
    refine ⟨a n, ?_, AdicCompletion.evalₐ_mk I n a⟩
    rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub, sub_eq_zero]
    rfl

/-- A formally smooth local algebra over a prime field is regular. Uniqueness
of maps from the base field makes the coefficient-field presentation compatible
with the base. -/
private theorem isRegularLocalRing_of_formallySmooth_of_subsingleton_hom.{u, v, w}
    {F : Type u} {A : Type w} [Field F] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : F →+* A)
    [Subsingleton (F →+* AdicCompletion (maximalIdeal A) A)]
    (h : let : WithIdeal F := ⟨⊥⟩
         let : WithIdeal A := ⟨maximalIdeal A⟩
         RingHom.FormallySmoothTop.{max v w} f) : IsRegularLocalRing A := by
  let B := AdicCompletion (maximalIdeal A) A
  let j : A →+* B := algebraMap A B
  let : Algebra F B := (j.comp f).toAlgebra
  obtain ⟨c, hc⟩ := exists_ringHom_residue_comp_eq_id B F
  let K := ULift.{v} (ResidueField B)
  let e : K ≃+* ResidueField B := ULift.ringEquiv
  let n := (maximalIdeal B).spanFinrank
  obtain ⟨y, hy⟩ := Stacks.CompleteLocalRing.PowerSeriesRing.exists_fin_generating_family
    (IsNoetherian.noetherian (maximalIdeal B)) (n := n) rfl
  obtain ⟨π, hπ, hπX, hπC⟩ := exists_surjective_eval₂Hom
    (maximalIdeal B) y hy (c.comp e.toRingHom) (by
      intro b
      change ResidueField B at b
      refine ⟨e.symm b, ?_⟩
      change residue B (c (e (e.symm b))) = b
      rw [e.apply_symm_apply]
      exact congrArg (fun f : ResidueField B →+* ResidueField B => f b) hc)
  let P := MvPowerSeries (Fin n) K
  have : IsRegularLocalRing P := MvPowerSeries.isRegularLocalRing K n
  have : IsAdicComplete (maximalIdeal K) K := by
    rw [show maximalIdeal K = ⊥ from (isField_iff_maximalIdeal_eq.mp (Field.toIsField K))]
    infer_instance
  have : IsAdicComplete (maximalIdeal P) P :=
    Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_mvPowerSeries K n
  have hd : (maximalIdeal P).spanFinrank = (maximalIdeal B).spanFinrank := by
    have heq : ((maximalIdeal P).spanFinrank : WithBot ℕ∞) = (n : WithBot ℕ∞) :=
      IsRegularLocalRing.spanFinrank_maximalIdeal.trans
        (le_antisymm (MvPowerSeries.ringKrullDim_le K n)
          (MvPowerSeries.natCast_le_ringKrullDim K n))
    exact_mod_cast heq
  have hker :=
    Stacks.RegularLocalRing.SpanFinrank.ker_le_maximalIdeal_sq_of_surjective_of_spanFinrank_eq
      π hπ hd
  let : WithIdeal F := ⟨⊥⟩
  let : WithIdeal A := ⟨maximalIdeal A⟩
  let : WithIdeal B := ⟨maximalIdeal B⟩
  let : WithIdeal P := ⟨maximalIdeal P⟩
  have : DiscreteTopology F := is_bot_adic_iff.mp rfl
  have : T2Space B := (IsAdic.isHausdorff_iff (I := maximalIdeal B) rfl).mp inferInstance
  have hπq := isQuotientMap_of_surjective_local rfl rfl π hπ
  let E : P ⧸ RingHom.ker π ≃+* B := RingHom.quotientKerEquivOfSurjective hπ
  let ψ := E.symm.toRingHom.comp j
  have hψ : Continuous ψ := by
    have he : Continuous E.symm := hπq.continuous_iff.mpr (by
      have := RingHom.quotientKerEquivOfSurjective_symm_comp hπ
      change Continuous ⇑(E.symm.toRingHom.comp π)
      rw [this]
      exact continuous_quot_mk)
    exact he.comp ((WithIdeal.uniformContinuous_of_map_le
      (map_maximalIdeal_le j)).continuous)
  let g : F →+* P := MvPowerSeries.C.comp
    (e.symm.toRingHom.comp ((residue B).comp (j.comp f)))
  have hπg : π.comp g = j.comp f := Subsingleton.elim _ _
  have hcomm : ψ.comp f = (Ideal.Quotient.mk (RingHom.ker π)).comp g :=
    ((comp_eq_iff_mk_comp_eq_quotientKerEquiv_symm_comp hπ g (j.comp f)).1 hπg).symm
  obtain ⟨s, hs, hsf, hsq⟩ :=
    RingHom.FormallySmoothTop.exists_continuous_lift_of_isAdic
      f (maximalIdeal A) rfl h (maximalIdeal P) rfl (RingHom.ker π)
      (isClosed_singleton.preimage hπq.continuous) 1 (by omega)
      (by simpa using IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π))
      g continuous_of_discreteTopology ψ hψ hcomm
  have hπs : π.comp s = j := (comp_eq_iff_mk_comp_eq_quotientKerEquiv_symm_comp hπ s j).2 hsq
  have hsm : (maximalIdeal A).map s ≤ maximalIdeal P := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    have hjx : j x ∈ maximalIdeal B :=
      (Ideal.map_le_iff_le_comap.mp (map_maximalIdeal_le j)) hx
    have he : π (s x) = j x := congrArg (fun f : A →+* B => f x) hπs
    rw [← he, mem_maximalIdeal, mem_nonunits_iff] at hjx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hjx (hu.map π)
  obtain ⟨S, hS⟩ := exists_ringHom_from_adicCompletion
    (maximalIdeal A) (maximalIdeal P) s hsm
  have hπS : π.comp S = RingHom.id B := by
    refine DFunLike.coe_injective (IsHausdorff.funext' (maximalIdeal B) fun t x => ?_)
    obtain ⟨a, ha, ha'⟩ := exists_sub_algebraMap_mem_pow_adicCompletion
      (maximalIdeal A) (IsNoetherian.noetherian _) x t
    have hSa : S x - s a ∈ maximalIdeal P ^ t := by
      apply Ideal.Quotient.eq.mp
      rw [hS, ha', Ideal.quotientMap_mk]
    have hπSa : π (S x) - j a ∈ maximalIdeal B ^ t := by
      rw [← show π (s a) = j a from congrArg (fun f : A →+* B => f a) hπs,
        ← map_sub]
      apply (Ideal.map_le_iff_le_comap.mp ?_) hSa
      rw [Ideal.map_pow, map_maximalIdeal_of_surjective π hπ]
    apply Ideal.Quotient.eq.mpr
    change π (S x) - x ∈ maximalIdeal B ^ t
    have haB : x - j a ∈ maximalIdeal B ^ t := by
      rwa [AdicCompletion.maximalIdeal_eq_map]
    simpa only [sub_sub_sub_cancel_right] using (maximalIdeal B ^ t).sub_mem hπSa haB
  have : IsRegularLocalRing B := IsRegularLocalRing.of_ringEquiv
    (ringEquiv_of_split_surjective_of_ker_le_maximalIdeal_sq π S hπS hker)
  have : Module.Flat A B := AdicCompletion.flat_of_isNoetherian (maximalIdeal A)
  exact IsRegularLocalRing.of_flat_of_isLocalHom B

/-- A Noetherian local algebra over a field is regular if its structure map
is formally smooth for the maximal-ideal adic topology. -/
@[stacks 07EI, ega "0 19.6.5" "A regular (k'=k)", ega "0 22.5.8" "a) ⇒ A regular"]
theorem isRegularLocalRing_of_maximalIdeal.{v, w}
    {k : Type v} {A : Type w} [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A]
    (h :
      let m := IsLocalRing.maximalIdeal A
      let : TopologicalSpace k := ⊥
      let : DiscreteTopology k := ⟨rfl⟩
      let : TopologicalSpace A := m.adicTopology
      let : IsTopologicalRing A := m.ringFilterBasis.isTopologicalRing
      let : IsLinearTopology A A := m.isLinearTopology
      RingHom.FormallySmoothTop.{max v w} (algebraMap k A)) :
    IsRegularLocalRing A := by
  have H (F : Type) [Field F] [PerfectField F] [Algebra F k]
      [Subsingleton (F →+* AdicCompletion (maximalIdeal A) A)] :
      IsRegularLocalRing A := by
    let : WithIdeal F := ⟨⊥⟩
    let : TopologicalSpace k := ⊥
    have : DiscreteTopology k := ⟨rfl⟩
    let : WithIdeal A := ⟨maximalIdeal A⟩
    have : DiscreteTopology F := is_bot_adic_iff.mp rfl
    have hFk : RingHom.FormallySmoothTop.{max v w} (algebraMap F k) := by
      let : Algebra F k := (algebraMap F k).toAlgebra
      exact RingHom.FormallySmoothTop.of_formallySmooth_of_isAdic
        (algebraMap F k) ⊥ (is_bot_adic_iff.mpr inferInstance)
        (Algebra.formallySmooth_of_perfectField F k)
    exact isRegularLocalRing_of_formallySmooth_of_subsingleton_hom.{0, v, w}
      ((algebraMap k A).comp (algebraMap F k))
      (hFk.comp h continuous_of_discreteTopology)
  obtain _ | ⟨p, _, _⟩ := CharP.exists' k
  · exact H ℚ
  · let : Algebra (ZMod p) k := (ZMod.castHom (dvd_refl p) k).toAlgebra
    exact H (ZMod p)

end RingHom.FormallySmoothTop

end
