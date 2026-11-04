module

public import Mathlib.Data.ENat.SuccOrder
public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Separation.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.Henselian.Pair.Operations
public import StacksFrontier.RingTheory.Jacobson.Nullstellensatz
public import StacksFrontier.RingTheory.KrullAkizuki
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.RingTheory.Spectrum.Prime.DimensionTwoOpens
public import StacksFrontier.RingTheory.Spectrum.Prime.Integral
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.NeighbourhoodRestrictionEquivalence
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RigPointCriterion
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RelativeCriterion

/-!
# Lifting rig points and completed principal localizations

The lifting criterion for rig points along a flat adic morphism of topologically finite type,
and the extension of a prime to the completed principal localization `A[1/f]^` of an
`I`-adically complete Noetherian ring.
-/

@[expose] public section

namespace Rig

section

open Filter
open scoped Topology

private lemma isAdic_le_topologicalNilradical
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (I : Ideal R) (hI : IsAdic I) :
    I ≤ topologicalNilradical R :=
  isIdealOfDefinition_le_topologicalNilradical I (isIdealOfDefinition_of_isAdic hI)

/-- Every element of the topological nilradical has a power in any open ideal. -/
private lemma exists_pow_mem_of_mem_topologicalNilradical
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R]
    (K : Ideal R) (hK : IsOpen (K : Set R)) {x : R} (hx : x ∈ topologicalNilradical R) :
    ∃ n, x ^ n ∈ K :=
  IsTopologicallyNilpotent.exists_pow_mem_of_mem_nhds
    (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx)
    (hK.mem_nhds (Ideal.zero_mem K))

private lemma rigPointLocalCondition_of_closedPointAway_topologicalNilradical
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] [IsNoetherianRing R]
    (hweak : TopologicalRing.IsWeaklyAdmissible R)
    (hadic : ∃ I : Ideal R, IsAdic I) (p : Ideal R) [p.IsPrime]
    (hp : Ideal.IsClosedPointAwayFrom (topologicalNilradical R) p) :
    Ideal.IsRigPointLocalCondition p := by
  let : @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) := hweak.2.1
  let : T2Space R := hweak.2.2
  exact rigPointLocalCondition_of_isClosedPointAwayFrom hadic p hp

/-- A rig-closed prime lifts along a flat adic map of topologically finite type
if and only if the closed point of its quotient is in the image on special
fibres. -/
@[stacks 0GGD "lifting criterion"]
public theorem rigPoint_lifts_iff_maximalIdeal_mem_specialFibre_image
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (hadic : RingHom.IsAdic φ)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (hflat : φ.Flat)
    (p : Ideal A) [p.IsPrime]
    (hp : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical A) p) :
    ( (∃ hlocal : IsLocalRing (A ⧸ p),
          letI : IsLocalRing (A ⧸ p) := hlocal
          ∃ r : Ideal B, r.IsPrime ∧
            topologicalNilradical B ≤ r ∧
            r.comap φ = (IsLocalRing.maximalIdeal (A ⧸ p)).comap
              (Ideal.Quotient.mk p)) ↔
      (∃ q : Ideal B, ∃ hqprime : q.IsPrime,
        letI : q.IsPrime := hqprime
        Ideal.IsClosedPointAwayFrom
          (topologicalNilradical B) q ∧ q.comap φ = p) ) := by
  constructor
  · intro hspecial
    let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    let : CompleteSpace A := hA.2.1
    let : T2Space A := hA.2.2
    let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
    let : CompleteSpace B := hB.2.1
    let : T2Space B := hB.2.2
    rcases hadic with ⟨I, hIadic, hKadic⟩
    let K : Ideal B := I.map φ
    have haDef : TopologicalRing.IsIdealOfDefinition (topologicalNilradical A) :=
      isIdealOfDefinition_topologicalNilradical_of_isAdic I hIadic
    have hbDef : TopologicalRing.IsIdealOfDefinition (topologicalNilradical B) :=
      isIdealOfDefinition_topologicalNilradical_of_isAdic (I.map φ) hKadic
    have htfaeA := rigPoint_tfae ⟨I, hIadic⟩ p
    have hclosedEx : ∃ J : Ideal A, TopologicalRing.IsIdealOfDefinition J ∧
        Ideal.IsClosedPointAwayFrom J p :=
      ⟨topologicalNilradical A, haDef, hp⟩
    have hmaxAall := (htfaeA.out 2 3).mp hclosedEx
    have hmaxA := hmaxAall (topologicalNilradical A) haDef
    have hlocalACond := rigPointLocalCondition_of_closedPointAway_topologicalNilradical
      hA ⟨I, hIadic⟩ p hp
    rcases hlocalACond with ⟨_, hdimA, _, _, _, _, _⟩
    rcases hspecial with ⟨hlocal, r, hrprime, hb_le_r, hrcomap⟩
    let : IsLocalRing (A ⧸ p) := hlocal
    let : r.IsPrime := hrprime
    have hmaxAne : IsLocalRing.maximalIdeal (A ⧸ p) ≠ ⊥ := by
      intro hzero
      have hfield : IsField (A ⧸ p) :=
        IsLocalRing.isField_iff_maximalIdeal_eq.mpr hzero
      have hdimzero := ringKrullDim_eq_zero_of_isField hfield
      rw [hdimA] at hdimzero
      norm_num at hdimzero
    have hple : p ≤ (IsLocalRing.maximalIdeal (A ⧸ p)).comap
        (Ideal.Quotient.mk p) := by
      intro x hx
      show Ideal.Quotient.mk p x ∈ IsLocalRing.maximalIdeal (A ⧸ p)
      have hxzero : Ideal.Quotient.mk p x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
      rw [hxzero]
      exact Ideal.zero_mem _
    have hneq : p ≠ (IsLocalRing.maximalIdeal (A ⧸ p)).comap
        (Ideal.Quotient.mk p) := by
      intro heq
      have hmap := congrArg (fun J : Ideal A => J.map (Ideal.Quotient.mk p)) heq
      have hmapMax : ((IsLocalRing.maximalIdeal (A ⧸ p)).comap
          (Ideal.Quotient.mk p)).map (Ideal.Quotient.mk p) =
          IsLocalRing.maximalIdeal (A ⧸ p) :=
        Ideal.map_comap_of_surjective (Ideal.Quotient.mk p)
          (fun y => Ideal.Quotient.mk_surjective y) _
      rw [hmapMax] at hmap
      have hbot : p.map (Ideal.Quotient.mk p) = ⊥ := by simp
      rw [hbot] at hmap
      have : (⊥ : Ideal (A ⧸ p)) = IsLocalRing.maximalIdeal (A ⧸ p) := by
        simpa using hmap
      exact hmaxAne this.symm
    have hltA : p < (IsLocalRing.maximalIdeal (A ⧸ p)).comap
        (Ideal.Quotient.mk p) := lt_of_le_of_ne hple hneq
    have hlt : p < r.comap φ := by rw [hrcomap]; exact hltA
    let : Algebra A B := φ.toAlgebra
    let : Module.Flat A B := hflat
    have hgd : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
    obtain ⟨q₀, hq₀r, hq₀prime, hq₀over⟩ :=
      hgd.exists_ideal_le_liesOver_of_lt r hlt
    have hq₀comap : q₀.comap φ = p := by
      have h := Ideal.over_def q₀ p
      simpa [Ideal.under_def, RingHom.algebraMap_toAlgebra] using h.symm
    have hbnotq₀ : ¬ topologicalNilradical B ≤ q₀ := by
      intro hbq₀
      apply hmaxA.1
      intro x hx
      rw [← hq₀comap]
      show φ x ∈ q₀
      apply hbq₀
      exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
        ((IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx).map hφ)
    let S : Set (Ideal B) := {s | q₀ ≤ s ∧ s.IsPrime ∧
      ¬ topologicalNilradical B ≤ s}
    have hS : S.Nonempty := ⟨q₀, le_rfl, hq₀prime, hbnotq₀⟩
    have hwf : WellFounded ((· > ·) : Ideal B → Ideal B → Prop) := IsWellFounded.wf
    obtain ⟨q, hqS, hqmax⟩ := hwf.has_min S hS
    rcases hqS with ⟨hq₀q, hqprime, hbnotq⟩
    have hmaxAvoid : Ideal.IsMaximalAmongPrimesAvoiding
        (topologicalNilradical B) q := by
      refine ⟨hbnotq, ?_⟩
      intro s hsprime hqs hbnotS
      have hsS : s ∈ S := ⟨le_trans hq₀q hqs, hsprime, hbnotS⟩
      have hnotlt : ¬ q < s := hqmax s hsS
      apply le_antisymm ?_ hqs
      by_contra hnot
      exact hnotlt (lt_iff_le_not_ge.mpr ⟨hqs, hnot⟩)
    have htfaeB := rigPoint_tfae ⟨I.map φ, hKadic⟩ q
    have hmaxEx : ∃ J : Ideal B, TopologicalRing.IsIdealOfDefinition J ∧
        Ideal.IsMaximalAmongPrimesAvoiding J q :=
      ⟨topologicalNilradical B, hbDef, hmaxAvoid⟩
    have hclosedAll := (htfaeB.out 1 4).mp hmaxEx
    have hqclosed := hclosedAll (topologicalNilradical B) hbDef
    have hqcomaple : p ≤ q.comap φ := by
      rw [← hq₀comap]
      exact Ideal.comap_mono hq₀q
    have hbnotcomap : ¬ topologicalNilradical A ≤ q.comap φ := by
      intro haq
      apply hbnotq
      have hIleA : I ≤ topologicalNilradical A := isAdic_le_topologicalNilradical I hIadic
      have hIleq : I ≤ q.comap φ := le_trans hIleA haq
      have hKleq : K ≤ q := by
        show I.map φ ≤ q
        exact Ideal.map_le_iff_le_comap.mpr hIleq
      have hbrad : topologicalNilradical B ≤ K.radical := fun x hx ↦
        Ideal.mem_radical_iff.mpr
          (exists_pow_mem_of_mem_topologicalNilradical K
            (isIdealOfDefinition_of_isAdic hKadic).1 hx)
      have hradq : K.radical ≤ q := by
        intro x hx
        obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
        exact hqprime.mem_of_pow_mem n (hKleq hn)
      exact le_trans hbrad hradq
    have hqcomap : q.comap φ = p := by
      have hprime : (q.comap φ).IsPrime := by infer_instance
      exact hmaxA.2 (q.comap φ) hprime hqcomaple hbnotcomap
    exact ⟨q, hqprime, hqclosed, hqcomap⟩
  · rintro ⟨q, hqprime, hq, hqp⟩
    let : q.IsPrime := hqprime
    rcases hadic with ⟨I, hIadic, hKadic⟩
    have hlocalACond := rigPointLocalCondition_of_closedPointAway_topologicalNilradical
      hA ⟨I, hIadic⟩ p hp
    have hlocalBCond := rigPointLocalCondition_of_closedPointAway_topologicalNilradical
      hB ⟨I.map φ, hKadic⟩ q hq
    rcases hlocalACond with ⟨hlocalA, _, _, _, _, _, hforallA⟩
    rcases hlocalBCond with ⟨hlocalB, _, _, _, _, _, hforallB⟩
    let : IsLocalRing (A ⧸ p) := hlocalA
    let : IsLocalRing (B ⧸ q) := hlocalB
    let K : Ideal B := I.map φ
    let f : (A ⧸ p) →+* (B ⧸ q) :=
      Ideal.quotientMap q φ (by simpa only [hqp] using (le_rfl : p ≤ p))
    have hIdef : TopologicalRing.IsIdealOfDefinition I := isIdealOfDefinition_of_isAdic hIadic
    have hKdef : TopologicalRing.IsIdealOfDefinition K := isIdealOfDefinition_of_isAdic hKadic
    have hradA : (I.map (Ideal.Quotient.mk p)).radical =
        IsLocalRing.maximalIdeal (A ⧸ p) := hforallA I hIdef
    have hradB : (K.map (Ideal.Quotient.mk q)).radical =
        IsLocalRing.maximalIdeal (B ⧸ q) := hforallB K hKdef
    let r : Ideal B := (IsLocalRing.maximalIdeal (B ⧸ q)).comap
      (Ideal.Quotient.mk q)
    refine ⟨hlocalA, ?_⟩
    refine ⟨r, ?_, ?_, ?_⟩
    · show (IsLocalRing.maximalIdeal (B ⧸ q)).comap
        (Ideal.Quotient.mk q) |>.IsPrime
      infer_instance
    · intro x hx
      show Ideal.Quotient.mk q x ∈ IsLocalRing.maximalIdeal (B ⧸ q)
      obtain ⟨n, hn⟩ := exists_pow_mem_of_mem_topologicalNilradical K hKdef.1 hx
      have hradmem : Ideal.Quotient.mk q (x ^ n) ∈
          (K.map (Ideal.Quotient.mk q)).radical :=
        Ideal.le_radical (Ideal.mem_map_of_mem (Ideal.Quotient.mk q) hn)
      have hpow : (Ideal.Quotient.mk q x) ^ n ∈
          IsLocalRing.maximalIdeal (B ⧸ q) := by
        simpa only [map_pow, hradB] using hradmem
      have hprime : (IsLocalRing.maximalIdeal (B ⧸ q)).IsPrime := by infer_instance
      exact hprime.mem_of_pow_mem n hpow
    · have hcomp : f.comp (Ideal.Quotient.mk p) =
          (Ideal.Quotient.mk q).comp φ := by
        ext x
        rfl
      let hmap : (I.map (Ideal.Quotient.mk p)).map f ≤
          (K.map (Ideal.Quotient.mk q)) := by
        rw [Ideal.map_map, Ideal.map_map, hcomp]
      have hmaxmap : (IsLocalRing.maximalIdeal (A ⧸ p)).map f ≤
          IsLocalRing.maximalIdeal (B ⧸ q) := by
        rw [← hradA]
        calc
          ((I.map (Ideal.Quotient.mk p)).radical).map f ≤
              ((I.map (Ideal.Quotient.mk p)).map f).radical :=
            Ideal.map_radical_le (f := f) (I := I.map (Ideal.Quotient.mk p))
          _ ≤ (K.map (Ideal.Quotient.mk q)).radical := Ideal.radical_mono hmap
          _ = IsLocalRing.maximalIdeal (B ⧸ q) := hradB
      have hlocalMap :=
        ((IsLocalRing.local_hom_TFAE f).out 3 5).mp hmaxmap
      show ((IsLocalRing.maximalIdeal (B ⧸ q)).comap
        (Ideal.Quotient.mk q)).comap φ =
        (IsLocalRing.maximalIdeal (A ⧸ p)).comap (Ideal.Quotient.mk p)
      calc
        ((IsLocalRing.maximalIdeal (B ⧸ q)).comap (Ideal.Quotient.mk q)).comap φ =
            (IsLocalRing.maximalIdeal (B ⧸ q)).comap
              ((Ideal.Quotient.mk q).comp φ) := by rw [Ideal.comap_comap]
        _ = (IsLocalRing.maximalIdeal (B ⧸ q)).comap
            (f.comp (Ideal.Quotient.mk p)) := by rw [hcomp]
        _ = ((IsLocalRing.maximalIdeal (B ⧸ q)).comap f).comap
            (Ideal.Quotient.mk p) := by rw [Ideal.comap_comap]
        _ = (IsLocalRing.maximalIdeal (A ⧸ p)).comap
            (Ideal.Quotient.mk p) := by rw [hlocalMap]

/-- At a rig-closed lift, the induced map from the reduction of `A` to the
residue field of `B / q` is finite. -/
@[stacks 0GGD "relative residue-field finiteness"]
public theorem rigPoint_residueFieldMap_finite_of_lift
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (hadic : RingHom.IsAdic φ)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (p : Ideal A) [p.IsPrime]
    (hp : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical A) p)
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical B) q)
    (hqp : q.comap φ = p) :
    ∃ hlocal : IsLocalRing (B ⧸ q),
      letI : IsLocalRing (B ⧸ q) := hlocal
      ∃ ψ : (A ⧸ topologicalNilradical A) →+*
          IsLocalRing.ResidueField (B ⧸ q),
        ψ.comp (Ideal.Quotient.mk (topologicalNilradical A)) =
            (IsLocalRing.residue (B ⧸ q)).comp
              ((Ideal.Quotient.mk q).comp φ) ∧ ψ.Finite := by
  subst hqp
  exact ((rigPoint_relative_tfae hA hB φ hφ hadic hft q hq).out 2 1).mp hp

/-- At a rig-closed lift, the induced map on the quotients by the two primes
is finite. -/
@[stacks 0GGD "relative quotient finiteness"]
public theorem rigPoint_quotientMap_finite_of_lift
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (hadic : RingHom.IsAdic φ)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (p : Ideal A) [p.IsPrime]
    (hp : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical A) p)
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical B) q)
    (hqp : q.comap φ = p) :
    (Ideal.quotientMap (I := p) q φ (by simpa only [← hqp] using le_rfl)).Finite := by
  subst hqp
  exact ((rigPoint_relative_tfae hA hB φ hφ hadic hft q hq).out 2 3).mp hp

end

noncomputable section

open scoped TensorProduct

universe u

variable {A : Type u} [CommRing A]

variable {A : Type u} [CommRing A]

private noncomputable def tensorToIdealMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) :
    S ⊗[R] p →ₗ[S] p.map (algebraMap R S) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c ↦
        { toFun := fun x ↦ ⟨algebraMap R S x.1 * c,
            Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ x.2)⟩
          map_add' := by simp [add_mul]
          map_smul' := by intro; simp [Algebra.smul_def, mul_comm, mul_left_comm] }
      map_add' := by intro x y; ext z; simp [mul_add]
      map_smul' := by intro c x; ext z; simp [mul_assoc, mul_comm] }

private theorem tensorToIdealMap_bijective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (p : Ideal R) : Function.Bijective (tensorToIdealMap (S := S) p) := by
  let g := tensorToIdealMap (S := S) p
  constructor
  · intro x y hxy
    have hi := Module.Flat.lTensor_preserves_injective_linearMap
      (M := S) p.subtype Subtype.val_injective
    apply hi
    apply (TensorProduct.rid R S).injective
    have heq : (TensorProduct.rid R S).toLinearMap.comp (p.subtype.lTensor S) =
        (p.map (algebraMap R S)).subtype.comp g := by
      ext c x
      simp [g, tensorToIdealMap, Algebra.smul_def, mul_comm]
    calc
      (TensorProduct.rid R S) ((p.subtype.lTensor S) x) =
          ((p.map (algebraMap R S)).subtype.comp g) x := congrArg (fun h ↦ h x) heq
      _ = ((p.map (algebraMap R S)).subtype.comp g) y := congrArg Subtype.val hxy
      _ = (TensorProduct.rid R S) ((p.subtype.lTensor S) y) :=
        (congrArg (fun h ↦ h y) heq).symm
  · intro y
    suffices ∃ z, (g z : S) = y.1 by
      obtain ⟨z, hz⟩ := this
      exact ⟨z, Subtype.ext hz⟩
    have hy := y.property
    change y.1 ∈ Submodule.span S ((algebraMap R S) '' (p : Set R)) at hy
    let h : S ⊗[R] p →ₗ[S] S := (p.map (algebraMap R S)).subtype.comp g
    have hle : Submodule.span S ((algebraMap R S) '' (p : Set R)) ≤ LinearMap.range h :=
      Submodule.span_le.mpr fun z ⟨x, hx, hzx⟩ ↦ by
        subst z
        exact ⟨1 ⊗ₜ[R] ⟨x, hx⟩, by simp [h, g, tensorToIdealMap]⟩
    exact hle hy

private noncomputable def tensorIdealMapEquiv
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (p : Ideal R) : S ⊗[R] p ≃ₗ[S] p.map (algebraMap R S) :=
  LinearEquiv.ofBijective (tensorToIdealMap (S := S) p) (tensorToIdealMap_bijective p)

/-- The completion of the principal localization `A[1/f]` for the extension of `I`. -/
public abbrev CompletedAway (I : Ideal A) (f : A) : Type u :=
  AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f)

/-- The extension of an ideal of `A` to its completed principal localization. -/
public abbrev extendedIdeal (I p : Ideal A) (f : A) : Ideal (CompletedAway I f) :=
  p.map (algebraMap A (CompletedAway I f))

private noncomputable def awayQuotientMap (p : Ideal A) (f : A)
    (hf : IsUnit (Ideal.Quotient.mk p f)) :
    Localization.Away f ⧸ (p.map (algebraMap A (Localization.Away f))) →+* A ⧸ p := by
  let q : Localization.Away f →+* A ⧸ p := IsLocalization.Away.lift f hf
  have hq : p.map (algebraMap A (Localization.Away f)) ≤ RingHom.ker q := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change IsLocalization.Away.lift f hf (algebraMap A (Localization.Away f) a) = 0
    rw [IsLocalization.Away.lift_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  exact Ideal.Quotient.lift _ q (fun _ hx => RingHom.mem_ker.mp (hq hx))

private theorem awayQuotientMap_surjective (p : Ideal A) (f : A)
    (hf : IsUnit (Ideal.Quotient.mk p f)) :
    Function.Surjective (awayQuotientMap p f hf) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.Quotient.mk _ (algebraMap A (Localization.Away f) a), ?_⟩
  show (Ideal.Quotient.lift _ (IsLocalization.Away.lift f hf) _)
      (Ideal.Quotient.mk _ (algebraMap A (Localization.Away f) a) :
        Localization.Away f ⧸ (p.map (algebraMap A (Localization.Away f)))) = _
  rw [Ideal.Quotient.lift_mk, IsLocalization.Away.lift_eq]

private theorem awayQuotientMap_injective (p : Ideal A) (f : A)
    (hf : IsUnit (Ideal.Quotient.mk p f)) :
    Function.Injective (awayQuotientMap p f hf) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  let q : Localization.Away f →+* A ⧸ p := IsLocalization.Away.lift f hf
  have hq : q x = q y := by
    simpa [awayQuotientMap, q] using hxy
  have hzq : q (x - y) = 0 := by rw [map_sub, hq, sub_self]
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f (x - y)
  have hqa : Ideal.Quotient.mk p a = 0 := by
    calc
      Ideal.Quotient.mk p a = q (algebraMap A (Localization.Away f) a) := by
        simp [q, IsLocalization.Away.lift_eq]
      _ = q ((x - y) * algebraMap A (Localization.Away f) f ^ n) := by rw [ha]
      _ = 0 := by rw [map_mul, hzq, zero_mul]
  have haP : a ∈ p := Ideal.Quotient.eq_zero_iff_mem.mp hqa
  have hamem : algebraMap A (Localization.Away f) a ∈
      p.map (algebraMap A (Localization.Away f)) := Ideal.mem_map_of_mem _ haP
  have hmul : (x - y) * algebraMap A (Localization.Away f) f ^ n ∈
      p.map (algebraMap A (Localization.Away f)) := by simpa [ha] using hamem
  have hu : IsUnit (algebraMap A (Localization.Away f) f ^ n) :=
    IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit f)
  rwa [mul_comm, Ideal.unit_mul_mem_iff_mem _ hu] at hmul

private noncomputable def awayQuotientEquiv (p : Ideal A) (f : A)
    (hf : IsUnit (Ideal.Quotient.mk p f)) :
    (Localization.Away f ⧸ (p.map (algebraMap A (Localization.Away f))) ≃+* A ⧸ p) :=
  RingEquiv.ofBijective (awayQuotientMap p f hf)
    ⟨awayQuotientMap_injective p f hf, awayQuotientMap_surjective p f hf⟩

private theorem quotient_isAdicComplete (I p : Ideal A) [IsNoetherianRing A]
    [IsAdicComplete I A] : IsAdicComplete I (A ⧸ p) :=
  isAdicComplete_of_iInf_smul_eq_bot I
    (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I (IsAdicComplete.le_jacobson_bot I))

private theorem qoutMapEquivTensorQout_mk_one
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) :
    Ideal.qoutMapEquivTensorQout (S := S) (I := I)
      (Ideal.Quotient.mk (I.map (algebraMap R S)) (1 : S)) =
        (1 : S) ⊗ₜ[R] Ideal.Quotient.mk I (1 : R) := by
  show (TensorProduct.tensorQuotEquivQuotSMul S I).symm
    (((Submodule.quotEquivOfEq (I • (⊤ : Submodule R S))
        (Submodule.restrictScalars R (I.map (algebraMap R S))) (by simp)).symm)
      ((Submodule.Quotient.restrictScalarsEquiv R (I.map (algebraMap R S))).symm
        (Submodule.Quotient.mk (1 : S)))) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  have hq :
      ((Submodule.quotEquivOfEq (I • (⊤ : Submodule R S))
        (Submodule.restrictScalars R (I.map (algebraMap R S))) (by simp)).symm
        (Submodule.Quotient.mk (1 : S))) = Submodule.Quotient.mk (1 : S) := by
    apply (Submodule.quotEquivOfEq (I • (⊤ : Submodule R S))
      (Submodule.restrictScalars R (I.map (algebraMap R S))) (by simp)).symm_apply_eq.mpr
    exact (Submodule.quotEquivOfEq_mk _ _ (by simp) (1 : S)).symm
  rw [hq]
  simp

private theorem qoutMapEquivTensorQout_one
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) :
    Ideal.qoutMapEquivTensorQout (S := S) (I := I) (1 : S ⧸ I.map (algebraMap R S)) =
      (1 : S) ⊗ₜ[R] Ideal.Quotient.mk I (1 : R) := by
  simpa using qoutMapEquivTensorQout_mk_one (R := R) (S := S) I

private theorem qoutMapEquivTensorQout_symm_unit
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) :
    (Ideal.qoutMapEquivTensorQout (S := S) (I := I)).symm
      ((1 : S) ⊗ₜ[R] (1 : R ⧸ I)) = (1 : S ⧸ I.map (algebraMap R S)) := by
  show (Ideal.qoutMapEquivTensorQout (S := S) (I := I)).symm
    ((1 : S) ⊗ₜ[R] Ideal.Quotient.mk I (1 : R)) = _
  rw [← qoutMapEquivTensorQout_one]
  exact (Ideal.qoutMapEquivTensorQout (S := S) (I := I)).symm_apply_apply _

private noncomputable def completedQuotientModuleEquiv
    (I p : Ideal A) (f : A) [IsNoetherianRing A] [IsAdicComplete I A]
    (hf : IsUnit (Ideal.Quotient.mk p f)) :
    (CompletedAway I f ⧸ extendedIdeal I p f) ≃ₗ[A] A ⧸ p := by
  let Af := Localization.Away f
  let J := I.map (algebraMap A Af)
  let pf := p.map (algebraMap A Af)
  let B := CompletedAway I f
  let C := Af ⧸ pf
  let eC := awayQuotientEquiv p f hf
  let K := I.map (algebraMap A (A ⧸ p))
  have he (x : Af) : eC (algebraMap Af C x) = IsLocalization.Away.lift f hf x := by
    change awayQuotientMap p f hf (Ideal.Quotient.mk pf x) = _
    rw [awayQuotientMap, Ideal.Quotient.lift_mk]
  have hI : IsAdicComplete I (A ⧸ p) := quotient_isAdicComplete I p
  have hK : IsAdicComplete K (A ⧸ p) := by rwa [IsAdicComplete.map_algebraMap_iff]
  have hmap : K.map eC.symm.toRingHom = J.map (algebraMap Af C) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    apply eC.injective
    simpa [IsLocalization.Away.lift_eq] using (he (algebraMap A Af a)).symm
  have hC' : IsAdicComplete (K.map eC.symm.toRingHom) C :=
    (IsAdicComplete.congr_ringEquiv K eC.symm).mpr hK
  rw [hmap] at hC'
  have hC : IsAdicComplete J C :=
    (IsAdicComplete.map_algebraMap_iff (R := Af) (S := C) (M := C) J).mp hC'
  letI : IsAdicComplete J C := hC
  let qE : (B ⧸ extendedIdeal I p f) ≃ₗ[B] B ⊗[A] (A ⧸ p) :=
    p.qoutMapEquivTensorQout B
  let eBase : B ⊗[A] (A ⧸ p) ≃ₗ[B]
      B ⊗[Af] (Af ⊗[A] (A ⧸ p)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A Af B B (A ⧸ p)).symm
  let eLoc : B ⊗[Af] (Af ⊗[A] (A ⧸ p)) ≃ₗ[B] B ⊗[Af] C :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (p.qoutMapEquivTensorQout Af).symm
  let eComp : B ⊗[Af] C ≃ₗ[B] AdicCompletion J C :=
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J C
  let eComplete : C ≃ₗ[Af] AdicCompletion J C := AdicCompletion.ofLinearEquiv J C
  let q : Af →+* A ⧸ p := IsLocalization.Away.lift f hf
  letI : Algebra Af (A ⧸ p) := q.toAlgebra
  letI : IsScalarTower A Af (A ⧸ p) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change Ideal.Quotient.mk p a = q (algebraMap A Af a)
      rw [IsLocalization.Away.lift_eq])
  let eCA : C ≃ₗ[Af] A ⧸ p :=
    { eC.toEquiv with
      map_add' := eC.map_add
      map_smul' := by
        intro a x
        simp only [Algebra.smul_def]
        change eC (algebraMap Af C a * x) = q a * eC x
        calc
          eC (algebraMap Af C a * x) = eC (algebraMap Af C a) * eC x := eC.map_mul _ _
          _ = q a * eC x := by rw [he] }
  let eFirst : (B ⧸ extendedIdeal I p f) ≃ₗ[Af] AdicCompletion J C :=
    ((qE.trans eBase).trans (eLoc.trans eComp)).restrictScalars Af
  exact (eFirst.trans (eComplete.symm.trans eCA)).restrictScalars A

private theorem completedQuotientModuleEquiv_apply
    (I p : Ideal A) (f a : A) [IsNoetherianRing A] [IsAdicComplete I A]
    (hf : IsUnit (Ideal.Quotient.mk p f)) :
    completedQuotientModuleEquiv I p f hf
      (Ideal.Quotient.mk (extendedIdeal I p f)
        (algebraMap A (CompletedAway I f) a)) = Ideal.Quotient.mk p a := by
  let B := CompletedAway I f
  let e := completedQuotientModuleEquiv I p f hf
  have h1 : e (Ideal.Quotient.mk (extendedIdeal I p f) (1 : B)) =
      Ideal.Quotient.mk p (1 : A) := by
    rw [← e.apply_symm_apply (Ideal.Quotient.mk p (1 : A))]
    apply congrArg e
    simp [e, completedQuotientModuleEquiv,
      qoutMapEquivTensorQout_one, qoutMapEquivTensorQout_symm_unit,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  have hsmul : Ideal.Quotient.mk (extendedIdeal I p f) (algebraMap A B a) =
      a • Ideal.Quotient.mk (extendedIdeal I p f) (1 : B) := by
    let : IsScalarTower A B (B ⧸ extendedIdeal I p f) :=
      IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
    rw [Algebra.smul_def]
    calc
      Ideal.Quotient.mk (extendedIdeal I p f) (algebraMap A B a) =
          algebraMap B (B ⧸ extendedIdeal I p f) (algebraMap A B a) :=
        by rw [Ideal.Quotient.algebraMap_eq]
      _ = algebraMap A (B ⧸ extendedIdeal I p f) a :=
        (IsScalarTower.algebraMap_apply A B (B ⧸ extendedIdeal I p f) a).symm
      _ = algebraMap A (B ⧸ extendedIdeal I p f) a *
          Ideal.Quotient.mk (extendedIdeal I p f) 1 := by
        simp [← Ideal.Quotient.algebraMap_eq]
  rw [hsmul, map_smul, h1]
  simp [Algebra.smul_def]

private noncomputable def completedQuotientRingMap
    (I p : Ideal A) (f : A) (_hf : IsUnit (Ideal.Quotient.mk p f)) :
    (A ⧸ p) →+* (CompletedAway I f ⧸ extendedIdeal I p f) :=
  Ideal.Quotient.lift p
    ((Ideal.Quotient.mk (extendedIdeal I p f)).comp
      (algebraMap A (CompletedAway I f)))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (algebraMap A (CompletedAway I f)) ha))

private noncomputable def completedQuotientRingEquiv
    (I p : Ideal A) (f : A) [IsNoetherianRing A] [IsAdicComplete I A]
    (hf : IsUnit (Ideal.Quotient.mk p f)) :
    (A ⧸ p) ≃+* (CompletedAway I f ⧸ extendedIdeal I p f) := by
  let e := completedQuotientModuleEquiv I p f hf
  have hcompat (x : A ⧸ p) : e (completedQuotientRingMap I p f hf x) = x := by
    refine Quotient.inductionOn' x ?_
    intro a
    change e (Ideal.Quotient.mk (extendedIdeal I p f)
      (algebraMap A (CompletedAway I f) a)) = Ideal.Quotient.mk p a
    exact completedQuotientModuleEquiv_apply I p f a hf
  apply RingEquiv.ofBijective (completedQuotientRingMap I p f hf)
  constructor
  · intro x y hxy
    simpa only [hcompat] using congrArg e hxy
  · intro y
    refine ⟨e y, ?_⟩
    apply e.injective
    simp only [hcompat]

/-- Extension of scalars of `p` to the completed principal localization is canonically its
extended ideal. -/
@[stacks 0GGF "tensor-product description"]
public theorem tensorProduct_equiv_extendedIdeal
    (I p : Ideal A) (f : A) [IsNoetherianRing A] :
    ∃ e : (CompletedAway I f ⊗[A] p) ≃ₗ[CompletedAway I f] extendedIdeal I p f,
      ∀ (x : p) (c : CompletedAway I f),
        ((e (c ⊗ₜ[A] x) : extendedIdeal I p f) : CompletedAway I f) =
          algebraMap A (CompletedAway I f) (x : A) * c := by
  let A_f := Localization.Away f
  let : Module.Flat A (CompletedAway I f) :=
    Module.Flat.trans A A_f (CompletedAway I f)
  exact ⟨tensorIdealMapEquiv (S := CompletedAway I f) p, fun x c => rfl⟩

/-- Completing the localized ideal `p A[1/f]` gives its extension to the completed principal
localization, compatibly with the canonical maps. -/
@[stacks 0GGF "completion description"]
public theorem adicCompletion_localizedIdeal_equiv_extendedIdeal
    (I p : Ideal A) (f : A) [IsNoetherianRing A] :
    let A_f := Localization.Away f
    let J := I.map (algebraMap A A_f)
    let p_f := p.map (algebraMap A A_f)
    ∃ e : AdicCompletion J p_f ≃ₗ[A_f] extendedIdeal I p f,
      ∀ x : p_f,
        ((e (AdicCompletion.of J p_f x) : extendedIdeal I p f) : CompletedAway I f) =
          algebraMap A_f (CompletedAway I f) (x : A_f) := by
  dsimp only
  let A_f := Localization.Away f
  let J := I.map (algebraMap A A_f)
  let p_f := p.map (algebraMap A A_f)
  let B := AdicCompletion J A_f
  let e₀ : B ⊗[A_f] p_f ≃ₗ[B] AdicCompletion J p_f :=
    LinearEquiv.ofBijective (AdicCompletion.ofTensorProduct J p_f)
      (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian J p_f)
  let e₁ := tensorIdealMapEquiv (S := B) p_f
  have hideal : p_f.map (algebraMap A_f B) = extendedIdeal I p f := by
    rw [Ideal.map_map]
    rfl
  let e₂ : p_f.map (algebraMap A_f B) ≃ₗ[B] extendedIdeal I p f :=
    LinearEquiv.ofEq _ _ hideal
  let e : AdicCompletion J p_f ≃ₗ[A_f] extendedIdeal I p f :=
    (e₀.symm.restrictScalars A_f).trans
      ((e₁.trans e₂).restrictScalars A_f)
  refine ⟨e, ?_⟩
  intro x
  have hx : e₀.symm (AdicCompletion.of J p_f x) = (1 : B) ⊗ₜ[A_f] x := by
    rw [e₀.symm_apply_eq]
    show AdicCompletion.of J p_f x = AdicCompletion.ofTensorProduct J p_f
      ((1 : B) ⊗ₜ[A_f] x)
    rw [AdicCompletion.ofTensorProduct_tmul, one_smul]
  rw [show e (AdicCompletion.of J p_f x) =
      e₂ (e₁ (e₀.symm (AdicCompletion.of J p_f x))) by rfl, hx]
  show algebraMap A_f B (x : A_f) * 1 = algebraMap A_f B (x : A_f)
  simp

/-- The extension of `p` to the completed principal localization is prime. -/
@[stacks 0GGF "primality"]
public theorem extendedIdeal_isPrime
    (I p : Ideal A) (f : A) [IsNoetherianRing A] [IsAdicComplete I A]
    (hp : p.IsPrime)
    (hf : IsUnit (Ideal.Quotient.mk p f)) :
    (extendedIdeal I p f).IsPrime := by
  let : p.IsPrime := hp
  let e := completedQuotientRingEquiv I p f hf
  have hdom : IsDomain (CompletedAway I f ⧸ extendedIdeal I p f) :=
    (e.isDomain_iff).mp inferInstance
  exact (Ideal.Quotient.isDomain_iff_prime (extendedIdeal I p f)).mp hdom

/-- Quotienting the completed principal localization by the extended prime canonically recovers
`A / p`. -/
@[stacks 0GGF "quotient"]
public theorem quotient_extendedIdeal_equiv
    (I p : Ideal A) (f : A) [IsNoetherianRing A] [IsAdicComplete I A]
    (hf : IsUnit (Ideal.Quotient.mk p f)) :
    ∃ e : (A ⧸ p) ≃+* (CompletedAway I f ⧸ extendedIdeal I p f),
      ∀ a : A,
        e (Ideal.Quotient.mk p a) =
          Ideal.Quotient.mk (extendedIdeal I p f)
            (algebraMap A (CompletedAway I f) a) :=
  ⟨completedQuotientRingEquiv I p f hf,
    fun a => by simp [completedQuotientRingEquiv, completedQuotientRingMap]⟩

/-- **Completing the principal localization at a unit of the residue ring does not move the
prime.**  If `f` is a unit modulo `p`, then the extension of `p` to the completed principal
localization of `A` at `f` contracts back to `p`: the two quotients are identified compatibly
with the structure maps, so an element of `A` lies in the extended ideal exactly when it lies
in `p`. -/
public theorem comap_extendedIdeal_eq (I p : Ideal A) (f : A) [IsNoetherianRing A]
    [IsAdicComplete I A] (hf : IsUnit (Ideal.Quotient.mk p f)) :
    (extendedIdeal I p f).comap (algebraMap A (CompletedAway I f)) = p := by
  obtain ⟨e, he⟩ := quotient_extendedIdeal_equiv I p f hf
  ext a
  show algebraMap A (CompletedAway I f) a ∈ extendedIdeal I p f ↔ a ∈ p
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← he, map_eq_zero_iff e e.injective,
    Ideal.Quotient.eq_zero_iff_mem]

-- This existing equivalence is the source's equality
-- `(A / p) ⊗ₐ CompletedAway I f = CompletedAway I f / p CompletedAway I f`.
add_to_stacks 0GGF "tensor-product description of the quotient"
  Ideal.qoutMapEquivTensorQout

-- This is the equality between direct extension to the completion and extension first to the
-- principal localization and then to its completion.
add_to_stacks 0GGF "transitivity of ideal extension" Ideal.map_map

end

end Rig

end
