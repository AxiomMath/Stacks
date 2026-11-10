module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Completion
public import Mathlib.Topology.Algebra.Ring.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Adic ring maps

A homomorphism `φ : A →+* B` of topological rings is *adic* when some ideal defining the
topology of `A` extends along `φ` to an ideal defining the topology of `B`.  This file defines
the predicate, proves it is stable under composition and satisfies the two cancellation
properties, and relates it to tautness: an adic map is taut, and over adic rings the two
notions agree.

## References

* [Stacks Project, Tag 0GBR](https://stacks.math.columbia.edu/tag/0GBR)
* [Stacks Project, Tag 0APU](https://stacks.math.columbia.edu/tag/0APU)
* [Stacks Project, Tag 0GXA](https://stacks.math.columbia.edu/tag/0GXA)
* [Stacks Project, Tag 0GXB](https://stacks.math.columbia.edu/tag/0GXB)
* [Stacks Project, Tag 0GBS](https://stacks.math.columbia.edu/tag/0GBS)
-/

@[expose] public section

namespace RingHom

section

/-- A ring homomorphism `φ : A →+* B` is adic if some ideal defining the
topology of `A` extends along `φ` to an ideal defining the topology of `B`. -/
@[stacks 0GBR]
public abbrev IsAdic {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] (φ : A →+* B) : Prop :=
  ∃ I : Ideal A, _root_.IsAdic I ∧ _root_.IsAdic (I.map φ)

end

section

private lemma exists_fg_map_isAdic
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B]
    (φ : A →+* B) (hTaut : RingHom.IsTaut φ)
    (hA : ∃ I : Ideal A, I.FG ∧ _root_.IsAdic I)
    [hComplete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)] [T2Space B] :
    ∃ I : Ideal A, I.FG ∧ _root_.IsAdic I ∧ _root_.IsAdic (I.map φ) := by
  classical
  obtain ⟨I, hIfg, hIadic⟩ := hA
  let K : Ideal B := I.map φ
  let L : Ideal (ULift.{0} B) := K.comap (ULift.ringEquiv (R := B))
  have hLmap : Ideal.map (ULift.ringEquiv (R := B)) L = K := by
    simpa [L] using Ideal.map_comap_eq_self_of_equiv (ULift.ringEquiv (R := B)) K
  have hLpow (n : ℕ) : Ideal.map (ULift.ringEquiv (R := B)) (L ^ n) = K ^ n := by
    rw [Ideal.map_pow, hLmap]
  have hmem (n : ℕ) (x : ULift.{0} B) : ULift.ringEquiv (R := B) x ∈ K ^ n ↔ x ∈ L ^ n := by
    rw [← hLpow n]
    exact Ideal.apply_mem_of_equiv_iff
  let Khat : Ideal (AdicCompletion K B) := K.map (algebraMap B (AdicCompletion K B))
  let : WithIdeal (ULift.{0} B) := ⟨L⟩
  let : WithIdeal (AdicCompletion K B) := ⟨Khat⟩
  let : TopologicalSpace (ULift.{0} B) := WithIdeal.instTopologicalSpace (ULift.{0} B)
  let : UniformSpace (ULift.{0} B) := WithIdeal.instUniformSpace (ULift.{0} B)
  let : TopologicalSpace (AdicCompletion K B) :=
    WithIdeal.instTopologicalSpace (AdicCompletion K B)
  let : UniformSpace (AdicCompletion K B) := WithIdeal.instUniformSpace (AdicCompletion K B)
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  let : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have hKfg : K.FG := by simpa [K] using hIfg.map φ
  have hKhatAdic : _root_.IsAdic Khat := rfl
  have hKhatCompleteTopo := (hKhatAdic.isAdicComplete_iff).mp
    ((IsAdicComplete.map_algebraMap_iff K (AdicCompletion K B)).mpr
      (AdicCompletion.isAdicComplete hKfg))
  let : CompleteSpace (AdicCompletion K B) := hKhatCompleteTopo.1
  let : T2Space (AdicCompletion K B) := hKhatCompleteTopo.2
  have hKhatBasis := hKhatAdic.hasBasis_nhds_zero
  have hLBasis := (show _root_.IsAdic L from rfl).hasBasis_nhds_zero
  have hkerPow : ∀ n : ℕ,
      Khat ^ n = RingHom.ker (AdicCompletion.evalₐ K n).toRingHom := by
    intro n; ext x
    change x ∈ ((K.map (algebraMap B (AdicCompletion K B))) ^ n) ↔ _
    rw [← Ideal.map_pow]
    change x ∈ Submodule.restrictScalars B (Ideal.map (algebraMap B _) (K ^ n)) ↔ _
    rw [← Ideal.smul_top_eq_map]
    change x ∈ K ^ n • (⊤ : Submodule B (AdicCompletion K B)) ↔ _
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hKfg, RingHom.mem_ker]
    have hpow : (K ^ n • (⊤ : Ideal B) : Ideal B) = K ^ n := by
      ext y; simp
    let q := Ideal.quotientEquivAlgOfEq B hpow
    change (AdicCompletion.eval K B n x = 0) ↔
      (q (AdicCompletion.eval K B n x) = 0)
    exact (map_eq_zero_iff q.toRingHom q.injective).symm
  let coeB : ULift.{0} B →+* AdicCompletion K B :=
    (algebraMap B (AdicCompletion K B)).comp (ULift.ringEquiv (R := B)).toRingHom
  have hpre : ∀ n : ℕ,
      coeB ⁻¹' ((Khat ^ n : Ideal (AdicCompletion K B)) : Set (AdicCompletion K B)) =
        ((L ^ n : Ideal (ULift.{0} B)) : Set (ULift.{0} B)) := by
    intro n; ext x
    change coeB x ∈ Khat ^ n ↔ x ∈ L ^ n
    rw [hkerPow n, RingHom.mem_ker]
    change AdicCompletion.evalₐ K n (coeB x) = 0 ↔ x ∈ L ^ n
    change AdicCompletion.evalₐ K n
        (algebraMap B (AdicCompletion K B) (ULift.ringEquiv (R := B) x)) = 0 ↔
      x ∈ L ^ n
    simp only [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmem n x
  have htopInd : Topology.IsInducing coeB := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    apply hLBasis.ext (hKhatBasis.comap coeB)
    · rintro n -
      exact ⟨n, trivial, by rw [hpre n]⟩
    · rintro n -
      exact ⟨n, trivial, by rw [hpre n]⟩
  have huni : IsUniformInducing coeB := AddMonoidHom.isUniformInducing_of_isInducing htopInd
  have hdense : DenseRange coeB := by
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_iff_forall.mpr
    intro x
    rw [mem_closure_iff_nhds]
    intro U hU
    rcases (hKhatAdic.hasBasis_nhds x).mem_iff.mp hU with ⟨n, -, hn⟩
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ K n x)
    refine ⟨coeB (ULift.up b), ?_, ⟨ULift.up b, rfl⟩⟩
    have hdiff : coeB (ULift.up b) - x ∈ (Khat ^ n : Ideal (AdicCompletion K B)) := by
      rw [hkerPow n, RingHom.mem_ker]
      rw [map_sub, sub_eq_zero]
      simpa [coeB, AdicCompletion.algebraMap_apply, ULift.ringEquiv] using hb
    exact hn ⟨coeB (ULift.up b) - x, hdiff, by simp⟩
  let pkg : AbstractCompletion (ULift.{0} B) := {
    space := AdicCompletion K B
    coe := coeB
    uniformStruct := IsTopologicalAddGroup.rightUniformSpace (AdicCompletion K B)
    complete := inferInstance
    separation := inferInstance
    isUniformInducing := huni
    dense := hdense }
  let cmp : UniformSpace.Completion (ULift.{0} B) ≃ᵤ AdicCompletion K B :=
    AbstractCompletion.compareEquiv (UniformSpace.Completion.cPkg (α := ULift.{0} B)) pkg
  let liftToHat : UniformSpace.Completion (ULift.{0} B) →+* AdicCompletion K B :=
    UniformSpace.Completion.extensionHom coeB pkg.continuous_coe
  have hlift_eq_cmp : liftToHat = cmp.toEquiv.toFun := by
    exact (UniformSpace.Completion.cPkg (α := ULift.{0} B)).funext
      (f := liftToHat) (g := cmp.toEquiv.toFun)
      (UniformSpace.Completion.continuous_extension (f := coeB))
      cmp.uniformContinuous_toFun.continuous fun x => by
        change UniformSpace.Completion.extensionHom coeB pkg.continuous_coe
            (x : UniformSpace.Completion (ULift.{0} B)) =
          AbstractCompletion.compareEquiv (UniformSpace.Completion.cPkg (α := ULift.{0} B)) pkg
            (x : UniformSpace.Completion (ULift.{0} B))
        rw [UniformSpace.Completion.extensionHom_coe coeB pkg.continuous_coe x]
        change coeB x =
          AbstractCompletion.compareEquiv (UniformSpace.Completion.cPkg (α := ULift.{0} B)) pkg
            ((UniformSpace.Completion.cPkg (α := ULift.{0} B)).coe x)
        exact (AbstractCompletion.compare_coe
          (UniformSpace.Completion.cPkg (α := ULift.{0} B)) pkg x).symm
  let liftToHatEquiv : UniformSpace.Completion (ULift.{0} B) ≃+* AdicCompletion K B :=
    RingEquiv.ofBijective liftToHat (by
      rw [hlift_eq_cmp]
      exact cmp.bijective)
  have hKbasisB : (nhds (0 : B)).HasBasis (fun n : ℕ => True)
      (fun n => Ideal.closure (K ^ n)) := by
    refine Filter.HasBasis.mk fun U => ?_
    constructor
    · intro hU
      rcases hTaut.2.mem_iff.mp hU with ⟨M, hMo, hsub⟩
      rcases hIadic.hasBasis_nhds_zero.mem_iff.mp
          (hMo.mem_nhds M.zero_mem) with ⟨n, -, hn⟩
      refine ⟨n, trivial, ?_⟩
      have hm : Ideal.closure (K ^ n) ≤ Ideal.closure (M.map φ) := by
        rw [← Ideal.map_pow]
        exact closure_mono (Ideal.map_mono hn)
      exact Set.Subset.trans hm hsub
    · rintro ⟨n, -, hsub⟩
      exact hTaut.2.mem_iff.mpr ⟨I ^ n,
        (isAdic_iff.mp hIadic).1 n, by
          rw [Ideal.map_pow]
          exact hsub⟩
  have heCont : Continuous (ULift.ringEquiv (R := B)).toRingHom := by
    apply continuous_of_continuousAt_zero (ULift.ringEquiv (R := B)).toRingHom.toAddMonoidHom
    rw [ContinuousAt]
    intro U hU
    rcases hKbasisB.mem_iff.mp hU with ⟨n, -, hn⟩
    exact Filter.mem_of_superset (hLBasis.mem_iff.mpr ⟨n, trivial, by
      intro x hx
      have hx' : (ULift.ringEquiv (R := B)) x ∈ K ^ n := (hmem n x).mpr hx
      exact hn (subset_closure hx')⟩) (by intro x hx; exact hx)
  let toB : UniformSpace.Completion (ULift.{0} B) →+* B :=
    UniformSpace.Completion.extensionHom (ULift.ringEquiv (R := B)).toRingHom heCont
  let ψ : AdicCompletion K B →+* B := toB.comp liftToHatEquiv.symm.toRingHom
  let intoCompletion : B →+* UniformSpace.Completion (ULift.{0} B) :=
    UniformSpace.Completion.coeRingHom.comp (ULift.ringEquiv (R := B)).symm.toRingHom
  have hcoe : liftToHatEquiv.toRingHom.comp intoCompletion =
      algebraMap B (AdicCompletion K B) := by
    apply RingHom.ext
    intro b
    change liftToHat ((ULift.up b : ULift.{0} B) : UniformSpace.Completion (ULift.{0} B)) =
      algebraMap B (AdicCompletion K B) b
    rw [hlift_eq_cmp]
    change (UniformSpace.Completion.cPkg (α := ULift.{0} B)).compare pkg
        ((UniformSpace.Completion.cPkg (α := ULift.{0} B)).coe (ULift.up b)) = _
    rw [AbstractCompletion.compare_coe
      (UniformSpace.Completion.cPkg (α := ULift.{0} B)) pkg (ULift.up b)]
    change algebraMap B (AdicCompletion K B)
        (ULift.ringEquiv (R := B) (ULift.up b : ULift.{0} B)) =
      algebraMap B (AdicCompletion K B) b
    exact congrArg (algebraMap B (AdicCompletion K B)) rfl
  have hsection : ψ.comp (algebraMap B (AdicCompletion K B)) = RingHom.id B := by
    apply RingHom.ext
    intro b
    change toB (liftToHatEquiv.symm (algebraMap B (AdicCompletion K B) b)) = b
    have hcoe_b : liftToHatEquiv (intoCompletion b) = algebraMap B (AdicCompletion K B) b :=
      congrArg (fun f : B →+* AdicCompletion K B => f b) hcoe
    rw [← hcoe_b, RingEquiv.symm_apply_apply]
    change toB ((ULift.up b : ULift.{0} B) : UniformSpace.Completion (ULift.{0} B)) = b
    simp only [toB, UniformSpace.Completion.extensionHom_coe]
    change ULift.ringEquiv (R := B) (ULift.up b : ULift.{0} B) = b
    rfl
  have hψsurj : Function.Surjective ψ := by
    intro b
    exact ⟨algebraMap B (AdicCompletion K B) b,
      by simpa using congrArg (fun f : B →+* B => f b) hsection⟩
  have hmapKhat : Khat.map ψ = K := by
    change Ideal.map ψ (K.map (algebraMap B (AdicCompletion K B))) = K
    rw [Ideal.map_map, hsection, Ideal.map_id]
  have hmapKhatPow (n : ℕ) : Ideal.map ψ (Khat ^ n) = K ^ n := by
    rw [Ideal.map_pow, hmapKhat]
  have hKhatPowOpen (n : ℕ) :
      IsOpen ((Khat ^ n : Ideal (AdicCompletion K B)) : Set (AdicCompletion K B)) :=
    (Khat ^ n).toAddSubgroup.isOpen_of_mem_nhds (hKhatBasis.mem_iff.mpr ⟨n, trivial, subset_rfl⟩)
  have hψbasis : (nhds (0 : B)).HasBasis
      (fun U : Ideal (AdicCompletion K B) => IsOpen (U : Set (AdicCompletion K B)))
      (fun U => Ideal.closure (U.map ψ)) := by
    refine Filter.HasBasis.mk fun V => ?_
    constructor
    · intro hV
      rcases hKbasisB.mem_iff.mp hV with ⟨n, -, hn⟩
      refine ⟨Khat ^ n, ?_, ?_⟩
      · exact hKhatPowOpen n
      · rw [hmapKhatPow n]
        exact hn
    · rintro ⟨U, hUopen, hUsub⟩
      have hUnhds : (U : Set (AdicCompletion K B)) ∈ nhds 0 :=
        hUopen.mem_nhds U.zero_mem
      rcases hKhatBasis.mem_iff.mp hUnhds with ⟨n, -, hn⟩
      have hmap : K ^ n ≤ U.map ψ := by
        rw [← hmapKhatPow n]
        exact Ideal.map_mono hn
      have hcl : Ideal.closure (K ^ n) ≤ Ideal.closure (U.map ψ) := by
        exact closure_mono hmap
      exact Filter.mem_of_superset (hKbasisB.mem_iff.mpr ⟨n, trivial, hcl⟩) hUsub
  have hψtaut : RingHom.IsTaut ψ := by
    refine ⟨?_, hψbasis⟩
    intro U hU
    exact (Ideal.closure (U.map ψ)).toAddSubgroup.isOpen_of_mem_nhds
      (hψbasis.mem_iff.mpr ⟨U, hU, subset_rfl⟩)
  have hψcont : Continuous ψ := by
    have hInv : ⇑liftToHatEquiv.symm = cmp.symm := by
      funext x
      apply cmp.injective
      calc
        cmp (liftToHatEquiv.symm x) = liftToHat (liftToHatEquiv.symm x) := by
          exact (congrFun hlift_eq_cmp (liftToHatEquiv.symm x)).symm
        _ = x := by
          exact liftToHatEquiv.apply_symm_apply x
        _ = cmp (cmp.symm x) := (cmp.apply_symm_apply x).symm
    exact (UniformSpace.Completion.continuous_extension
      (f := (ULift.ringEquiv (R := B)).toRingHom)).comp (by
        change Continuous (fun x => liftToHatEquiv.symm x)
        rw [hInv]
        exact cmp.uniformContinuous_invFun.continuous)
  have hopen := RingHom.isOpenMap_of_isTaut_of_denseRange ψ hψcont inferInstance
    (hKhatBasis.isCountablyGenerated) hψtaut hψsurj.denseRange
  have hKpowOpen : ∀ n : ℕ, IsOpen ((K ^ n : Ideal B) : Set B) := by
    intro n
    have himage :
        ψ '' ((Khat ^ n : Ideal (AdicCompletion K B)) : Set (AdicCompletion K B)) =
          ((K ^ n : Ideal B) : Set B) := by
      rw [← Ideal.map_eq_image_of_surjective ψ hψsurj, hmapKhatPow n]
    rw [← himage]
    exact hopen _ (hKhatPowOpen n)
  have hKadic : _root_.IsAdic K := by
    rw [isAdic_iff]
    refine ⟨hKpowOpen, ?_⟩
    intro U hU
    rcases hKbasisB.mem_iff.mp hU with ⟨n, -, hn⟩
    exact ⟨n, Set.Subset.trans subset_closure hn⟩
  exact ⟨I, hIfg, hIadic, by simpa [K] using hKadic⟩

/-- The target of a taut continuous homomorphism from a pre-adic ring with a finitely generated
ideal of definition is itself adic with a finitely generated ideal of definition, provided that
the target is complete. -/
@[stacks 0APU "the target is adic with a finitely generated ideal of definition"]
public theorem exists_fg_ideal_isAdic_of_isTaut
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B]
    (φ : A →+* B) (hTaut : RingHom.IsTaut φ)
    (hA : ∃ I : Ideal A, I.FG ∧ _root_.IsAdic I)
    [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)] [T2Space B] :
    ∃ J : Ideal B, J.FG ∧ _root_.IsAdic J := by
  rcases exists_fg_map_isAdic φ hTaut hA with ⟨I, hIfg, -, hKadic⟩
  exact ⟨I.map φ, hIfg.map φ, by simpa using hKadic⟩

section

/-- A taut continuous homomorphism from a pre-adic ring with a finitely generated ideal of
definition to a complete linearly topologized ring is adic. -/
@[stacks 0APU "the homomorphism is adic"]
public theorem isAdic_of_isTaut
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B]
    (φ : A →+* B) (hTaut : RingHom.IsTaut φ)
    (hA : ∃ I : Ideal A, I.FG ∧ _root_.IsAdic I)
    [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)] [T2Space B] :
    RingHom.IsAdic φ := by
  rcases exists_fg_map_isAdic φ hTaut hA with ⟨I, -, hIadic, hKadic⟩
  exact ⟨I, hIadic, by simpa using hKadic⟩

end

end

section

section

private theorem isAdic_map_of_isAdic_map {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] (f : R →+* S) (I J : Ideal R)
    (hI : _root_.IsAdic I) (hJ : _root_.IsAdic J)
    (hJmap : _root_.IsAdic (J.map f)) : _root_.IsAdic (I.map f) := by
  let : IsTopologicalRing R := hI ▸ inferInstance
  let : IsTopologicalRing S := hJmap ▸ inferInstance
  rw [isAdic_iff] at hI hJ hJmap ⊢
  constructor
  · intro n
    obtain ⟨m, hm⟩ := hJ.2 _ ((hI.1 n).mem_nhds (I ^ n).zero_mem)
    apply Ideal.isOpen_of_isOpen_subideal _ (hJmap.1 m)
    simpa only [Ideal.map_pow] using (Ideal.map_mono hm : (J ^ m).map f ≤ (I ^ n).map f)
  · intro U hU
    obtain ⟨n, hn⟩ := hJmap.2 U hU
    obtain ⟨m, hm⟩ := hI.2 _ ((hJ.1 n).mem_nhds (J ^ n).zero_mem)
    refine ⟨m, Set.Subset.trans ?_ hn⟩
    change (I.map f) ^ m ≤ (J.map f) ^ n
    simpa only [Ideal.map_pow] using (Ideal.map_mono hm : (I ^ m).map f ≤ (J ^ n).map f)

/-- The composite of two continuous adic ring homomorphisms is adic. -/
@[stacks 0GXA]
public theorem isAdic_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : A →+* B) (g : B →+* C) (hf : RingHom.IsAdic f)
    (hg : RingHom.IsAdic g) :
    RingHom.IsAdic (g.comp f) := by
  obtain ⟨I, hI, hIf⟩ := hf
  obtain ⟨J, hJ, hJg⟩ := hg
  refine ⟨I, hI, ?_⟩
  simpa only [Ideal.map_map] using isAdic_map_of_isAdic_map g (I.map f) J hIf hJ hJg

end

end

section

section

/-- If a composite of continuous ring homomorphisms is adic and the middle ring is
pre-adic, then the second homomorphism is adic. -/
@[stacks 0GXB]
public theorem isAdic_of_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : A →+* B) (g : B →+* C) (hf_continuous : Continuous f)
    (hg_continuous : Continuous g) (hB : TopologicalRing.IsPreAdic B)
    (hgf : RingHom.IsAdic (g.comp f)) :
    RingHom.IsAdic g := by
  rcases hgf with ⟨I, hIA, hAC⟩
  rcases hB with ⟨K, hKdef, hKB⟩
  let L : Ideal C := Ideal.map g (Ideal.map f I)
  let M : Ideal C := Ideal.map g K
  have hLC : _root_.IsAdic L := by simpa only [L, Ideal.map_map] using hAC
  have hKB' := hKB
  change (inferInstance : TopologicalSpace A) = I.adicTopology at hIA
  cases hIA
  change (inferInstance : TopologicalSpace B) = K.adicTopology at hKB
  cases hKB
  change (inferInstance : TopologicalSpace C) = L.adicTopology at hLC
  cases hLC
  -- The ambient topology on `C` is now the adic topology, whose ring structure
  -- is supplied by the ideal's ring filter basis.
  let : TopologicalSpace C := L.adicTopology
  let : IsTopologicalRing C := L.ringFilterBasis.isTopologicalRing
  have hLcharacterization := (_root_.isAdic_iff.mp (show _root_.IsAdic L from rfl))
  obtain ⟨m, -, hfm⟩ := (RingHom.continuous_adic_iff f I K).mp hf_continuous
  obtain ⟨n, -, hgn⟩ := (RingHom.continuous_adic_iff g K L).mp hg_continuous
  have hfm' : Ideal.map f (I ^ m) ≤ K := Ideal.map_le_iff_le_comap.mpr hfm
  have hgn' : Ideal.map g (K ^ n) ≤ L := Ideal.map_le_iff_le_comap.mpr hgn
  have hLM : L ^ m ≤ M := by simpa only [L, M, Ideal.map_pow] using Ideal.map_mono (f := g) hfm'
  have hML : M ^ n ≤ L := by simpa only [M, L, Ideal.map_pow] using hgn'
  refine ⟨K, hKB', _root_.isAdic_iff.mpr ⟨?_, ?_⟩⟩
  · intro k
    exact Ideal.isOpen_of_isOpen_subideal
      (by simpa only [pow_mul] using Ideal.pow_right_mono hLM k)
      (hLcharacterization.1 (m * k))
  · intro U hU
    obtain ⟨k, hk⟩ := hLcharacterization.2 U hU
    refine ⟨n * k, ?_⟩
    intro x hx
    apply hk
    exact (show M ^ (n * k) ≤ L ^ k from by
      simpa only [pow_mul] using Ideal.pow_right_mono hML k) hx

end

end

section

section

/-- A continuous adic homomorphism of linearly topologized rings is taut. -/
@[stacks 0GBS "part (1)", stacks 0GXC "adic implies taut"]
public theorem isTaut_of_isAdic
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B]
    (φ : A →+* B) (hAdic : RingHom.IsAdic φ) :
    RingHom.IsTaut φ := by
  obtain ⟨I, hI, hJ⟩ := hAdic
  let J : Ideal B := I.map φ
  have hpowOpen (n : ℕ) : IsOpen ((J ^ n : Ideal B) : Set B) := (isAdic_iff.mp hJ).1 n
  have hopen (K : Ideal A) (hK : IsOpen (K : Set A)) :
      IsOpen (Ideal.closure (K.map φ) : Set B) := by
    obtain ⟨n, -, hn⟩ := hI.hasBasis_nhds_zero.mem_iff.mp (hK.mem_nhds K.zero_mem)
    exact (K.map φ).closure.toAddSubgroup.isOpen_of_mem_nhds
      (Filter.mem_of_superset ((hpowOpen n).mem_nhds (J ^ n).zero_mem) (by
        rw [← Ideal.map_pow]; exact (Ideal.map_mono hn).trans subset_closure))
  refine ⟨hopen, Filter.hasBasis_iff.mpr fun s ↦ ?_⟩
  constructor
  · intro hs; obtain ⟨n, -, hn⟩ := hJ.hasBasis_nhds_zero.mem_iff.mp hs
    refine ⟨I ^ n, (isAdic_iff.mp hI).1 n, ?_⟩
    have hclosed : IsClosed ((J ^ n : Ideal B) : Set B) :=
      (J ^ n).toAddSubgroup.isClosed_of_isOpen (hpowOpen n)
    simpa [Ideal.map_pow, Ideal.closure_eq_of_isClosed _ hclosed] using hn
  · rintro ⟨K, hK, hsub⟩; exact Filter.mem_of_superset
      ((hopen K hK).mem_nhds (K.map φ).closure.zero_mem) hsub

add_to_stacks 0GBS "part (2)" RingHom.isAdic_of_isTaut

/-- Adicness and tautness are equivalent for a continuous homomorphism from a linearly
topologized ring with a finitely generated ideal of definition to a complete separated linearly
topologized ring. In particular, this applies to morphisms in `WAdm^{adic*}`. -/
@[stacks 0GBS "on WAdm^{adic*}"]
public theorem isAdic_iff_isTaut
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B]
    (φ : A →+* B)
    (hA : ∃ I : Ideal A, I.FG ∧ _root_.IsAdic I)
    [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)] [T2Space B] :
    RingHom.IsAdic φ ↔ RingHom.IsTaut φ := by
  exact ⟨isTaut_of_isAdic φ, (RingHom.isAdic_of_isTaut φ · hA)⟩

end

end

end RingHom

end
