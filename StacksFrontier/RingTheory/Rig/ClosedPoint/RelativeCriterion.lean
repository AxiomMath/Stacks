module

public import Mathlib.Order.SuccPred.ENat
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

/-!
# Rig points along an adic morphism

Finiteness of the residue field at a rig point over the reduction of the source, the relative
criterion `Rig.rigPoint_relative_tfae` for rig-closedness of `q.comap φ`, and descent of
rig-closedness over a Jacobson reduction.
-/

@[expose] public section

namespace Rig

section

private lemma topologicallyNilpotent_mem_maximalIdeal_quotient
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (q : Ideal B)
    [IsLocalRing (B ⧸ q)] [T2Space (B ⧸ q)]
    {x : B} (hx : IsTopologicallyNilpotent x) :
    Ideal.Quotient.mk q x ∈ IsLocalRing.maximalIdeal (B ⧸ q) := by
  by_contra hnot
  have hxunit : IsUnit (Ideal.Quotient.mk q x) :=
    IsLocalRing.notMem_maximalIdeal.mp hnot
  have hxquot : IsTopologicallyNilpotent (Ideal.Quotient.mk q x) :=
    IsTopologicallyNilpotent.map continuous_quot_mk hx
  have hzeroOpen : ∀ U : Set (B ⧸ q), IsOpen U → (0 : B ⧸ q) ∈ U → U = Set.univ := by
    intro U hU h0
    obtain ⟨J, hJopen, hJpre⟩ :=
      (IsLinearTopology.hasBasis_open_ideal (R := B)).mem_iff.mp
        ((hU.preimage continuous_quot_mk).mem_nhds
          (show (0 : B) ∈ (Ideal.Quotient.mk q) ⁻¹' U from by simpa using h0))
    have hJimageOpen : IsOpen ((J.map (Ideal.Quotient.mk q) : Ideal (B ⧸ q)) : Set (B ⧸ q)) := by
      rw [Ideal.map_eq_image_of_surjective (Ideal.Quotient.mk q)
        Ideal.Quotient.mk_surjective]
      exact (QuotientRing.isOpenMap_coe (N := q)) (J : Set B) hJopen
    obtain ⟨n, hpowmem⟩ := hxquot.exists_pow_mem_of_mem_nhds
      (hJimageOpen.mem_nhds (Ideal.zero_mem _))
    have hJtop := (J.map (Ideal.Quotient.mk q)).eq_top_of_isUnit_mem
      hpowmem (hxunit.pow n)
    have hJsubset :
        ((J.map (Ideal.Quotient.mk q) : Ideal (B ⧸ q)) : Set (B ⧸ q)) ⊆ U := by
      intro y hy
      obtain ⟨z, hzJ, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk q)
          Ideal.Quotient.mk_surjective).mp hy
      exact hJpre hzJ
    simpa [hJtop] using hJsubset
  obtain ⟨U, V, hUopen, hVopen, h0U, h1V, hUV⟩ :=
    t2_separation (show (0 : B ⧸ q) ≠ 1 from zero_ne_one)
  exact (Set.disjoint_left.mp hUV (by rw [hzeroOpen U hUopen h0U]; trivial)) h1V

/-- The residue field at a rig-closed point is of finite type over the quotient
of the source by its ideal of topologically nilpotent elements. -/
@[stacks 0GGA]
public lemma exists_residueFieldMap_finiteType_of_rigPoint
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsRigPointLocalCondition q)
    (φ : A →+* B) (hφ : Continuous φ)
    (hfiniteType : (Ideal.quotientMap (I := topologicalNilradical A)
      (topologicalNilradical B) φ
      (by
        intro x hx
        exact IsTopologicallyNilpotent.map hφ
          (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx))).FiniteType) :
    let _ : IsLocalRing (B ⧸ q) := hq.choose
    ∃ ψ : (A ⧸ topologicalNilradical A) →+* IsLocalRing.ResidueField (B ⧸ q),
      ψ.comp (Ideal.Quotient.mk (topologicalNilradical A)) =
        (IsLocalRing.residue (B ⧸ q)).comp ((Ideal.Quotient.mk q).comp φ) ∧
      ψ.FiniteType := by
  let : IsLocalRing (B ⧸ q) := hq.choose
  rcases hq with ⟨_, _, _, _, _, hT2, _⟩
  let rmap : B →+* IsLocalRing.ResidueField (B ⧸ q) :=
    (IsLocalRing.residue (B ⧸ q)).comp (Ideal.Quotient.mk q)
  have hkill : ∀ x : B, x ∈ topologicalNilradical B → rmap x = 0 := by
    intro x hx
    exact (IsLocalRing.residue_eq_zero_iff _).2
      (topologicallyNilpotent_mem_maximalIdeal_quotient q
        (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx))
  let g : (B ⧸ topologicalNilradical B) →+* IsLocalRing.ResidueField (B ⧸ q) :=
    Ideal.Quotient.lift (topologicalNilradical B) rmap hkill
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨z, hz⟩ := IsLocalRing.residue_surjective (R := B ⧸ q) y
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨Ideal.Quotient.mk (topologicalNilradical B) w, ?_⟩
    simp [g, rmap, hw, hz]
  let f : (A ⧸ topologicalNilradical A) →+* (B ⧸ topologicalNilradical B) :=
    Ideal.quotientMap (topologicalNilradical B) φ (by
      intro x hx
      exact IsTopologicallyNilpotent.map hφ
        (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx))
  refine ⟨g.comp f, ?_, RingHom.FiniteType.comp_surjective hfiniteType hg⟩
  apply RingHom.ext
  intro x
  simp [f, g, rmap, Ideal.quotientMap]

end

section

open Filter
open PrimeSpectrum
open scoped Topology

private lemma moduleFinite_of_isFiniteLength_over_local
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing S]
    [AddCommGroup M] [Module S M] [Algebra R S]
    [Algebra R (IsLocalRing.ResidueField S)]
    (hTower : IsScalarTower R S (IsLocalRing.ResidueField S))
    (hres : Module.Finite R (IsLocalRing.ResidueField S))
    (hM : IsFiniteLength S M) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    Module.Finite R M := by
  let : IsScalarTower R S (IsLocalRing.ResidueField S) := hTower
  refine IsFiniteLength.rec (R := S)
    (motive := fun M' _ _ _ =>
      let : Module R M' := Module.compHom M' (algebraMap R S)
      Module.Finite R M') ?_ ?_ hM
  · intro M' _ _ _
    let : Module R M' := Module.compHom M' (algebraMap R S)
    exact Module.Finite.of_surjective (0 : R →ₗ[R] M') (by
      intro x
      exact ⟨0, Subsingleton.elim _ _⟩)
  · intro M' _ _ N _ hN ih
    let : Module R M' := Module.compHom M' (algebraMap R S)
    let : IsScalarTower R S M' := IsScalarTower.of_compHom R S M'
    let : Module R N := Module.compHom N (algebraMap R S)
    let : IsScalarTower R S N := IsScalarTower.of_compHom R S N
    let : Module R (M' ⧸ N) := Module.compHom (M' ⧸ N) (algebraMap R S)
    let : IsScalarTower R S (M' ⧸ N) :=
      IsScalarTower.of_compHom R S (M' ⧸ N)
    have hsimple : IsSimpleModule S (M' ⧸ N) := inferInstance
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    rw [IsLocalRing.eq_maximalIdeal hm] at e
    have hquotS : Module.Finite R (M' ⧸ N) := by
      simpa only [IsLocalRing.ResidueField] using
        hres.equiv (e.symm.restrictScalars R)
    let NR : Submodule R M' := N.restrictScalars R
    let eN : N ≃ₗ[R] NR := {
      toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl
    }
    let : Module.Finite R NR := ih.equiv eN
    let eQ : (M' ⧸ NR) ≃ₗ[R] (M' ⧸ N) :=
      Submodule.Quotient.restrictScalarsEquiv R N
    let : Module.Finite R (M' ⧸ NR) := hquotS.equiv eQ.symm
    exact Module.Finite.of_submodule_quotient NR

lemma rigPointLocalCondition_of_isClosedPointAwayFrom
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] [IsNoetherianRing R]
    [@CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R)] [T2Space R]
    (hadic : ∃ I : Ideal R, IsAdic I)
    (q : Ideal R) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom (topologicalNilradical R) q) :
    Ideal.IsRigPointLocalCondition q := by
  rcases hadic with ⟨I, hI⟩
  have h2 : ∃ J : Ideal R,
      TopologicalRing.IsIdealOfDefinition J ∧ Ideal.IsClosedPointAwayFrom J q :=
    ⟨topologicalNilradical R, isIdealOfDefinition_topologicalNilradical_of_isAdic I hI, hq⟩
  exact ((rigPoint_tfae ⟨I, hI⟩ q).out 2 8).mp h2

/-- For an adic, topologically finite type morphism of Noetherian weakly
admissible rings, a rig-closed prime upstairs satisfies the relative
rig-closed point criterion. -/
@[stacks 0GGB]
public lemma rigPoint_relative_tfae {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (hadic : RingHom.IsAdic φ)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical B) q) :
    let a := topologicalNilradical A
    let p := q.comap φ
    List.TFAE
      [ ∃ hlocal : IsLocalRing (B ⧸ q),
          letI : IsLocalRing (B ⧸ q) := hlocal
          ∃ ψ : (A ⧸ a) →+* IsLocalRing.ResidueField (B ⧸ q),
            ψ.comp (Ideal.Quotient.mk a) =
                (IsLocalRing.residue (B ⧸ q)).comp
                  ((Ideal.Quotient.mk q).comp φ) ∧
              ψ.Finite,
        Ideal.IsClosedPointAwayFrom a p,
        (Ideal.quotientMap (I := p) q φ le_rfl).Finite ] := by
  let a := topologicalNilradical A
  let p := q.comap φ
  let : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := hA.2.1
  let : T2Space A := hA.2.2
  let : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B) := hB.2.1
  let : T2Space B := hB.2.2
  rcases hadic with ⟨I, hI, hJ⟩
  have hlocal := rigPointLocalCondition_of_isClosedPointAwayFrom ⟨I.map φ, hJ⟩ q hq
  have hIdefB : TopologicalRing.IsIdealOfDefinition (I.map φ) :=
    isIdealOfDefinition_of_isAdic hJ
  have hIleA : I ≤ a := fun x hx =>
    IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
      (isTopologicallyNilpotent_of_mem_isIdealOfDefinition (isIdealOfDefinition_of_isAdic hI) hx)
  have hIavoid : ¬ I.map φ ≤ q := by
    have hB6 := ((rigPoint_tfae ⟨I.map φ, hJ⟩ q).out 8 6).mp hlocal
    exact hB6.2 (I.map φ) hIdefB
  tfae_have 1 → 3 := by
    intro h1
    rcases h1 with ⟨hLS, ψ, hψcomp, hψfinite⟩
    let : IsLocalRing (B ⧸ q) := hLS
    let S := B ⧸ q
    let f : A →+* S := (Ideal.Quotient.mk q).comp φ
    let : Algebra A S := f.toAlgebra
    have : IsScalarTower A S S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let J : Ideal S := a.map f
    let T := S ⧸ J
    rcases hlocal with ⟨hLocalB, hdimB, hNoethB, hDomainB, hCompB, hT2B, hradB⟩
    let : IsNoetherianRing S := hNoethB
    let : IsDomain S := hDomainB
    have hRadIB : ((I.map φ).map (Ideal.Quotient.mk q)).radical =
        IsLocalRing.maximalIdeal S := hradB (I.map φ) hIdefB
    have haRadI : a ≤ I.radical :=
      topologicalNilradical_le_radical_of_isIdealOfDefinition I
        (isIdealOfDefinition_of_isAdic hI)
    have hmapI : (I.map φ).map (Ideal.Quotient.mk q) = I.map f := by
      rw [Ideal.map_map]
    have hRadMapI : (I.map f).radical = IsLocalRing.maximalIdeal S := by
      rw [← hmapI]
      exact hRadIB
    have hIBne : (I.map φ).map (Ideal.Quotient.mk q) ≠ ⊥ := by
      intro hbot
      have hle : (I.map φ).map (Ideal.Quotient.mk q) ≤ (⊥ : Ideal S) := by
        rw [hbot]
      have hle' : I.map φ ≤ (⊥ : Ideal S).comap (Ideal.Quotient.mk q) :=
        (Ideal.map_le_iff_le_comap).mp hle
      have hleq : I.map φ ≤ q := by
        rw [← RingHom.ker_eq_comap_bot] at hle'
        rw [Ideal.mk_ker] at hle'
        exact hle'
      exact hIavoid hleq
    have hIBleJ : (I.map f) ≤ J := by
      exact Ideal.map_mono (f := f) hIleA
    have hJleRadIB : J ≤ (I.map f).radical :=
      (Ideal.map_mono haRadI).trans (Ideal.map_radical_le f)
    have hRadJ : J.radical = IsLocalRing.maximalIdeal S := by
      apply le_antisymm
      · calc
          J.radical ≤ (I.map f).radical := by
            simpa using Ideal.radical_mono hJleRadIB
          _ = IsLocalRing.maximalIdeal S := hRadMapI
      · calc
          IsLocalRing.maximalIdeal S = (I.map f).radical := hRadMapI.symm
          _ ≤ J.radical := Ideal.radical_mono hIBleJ
    have hJleMax : J ≤ IsLocalRing.maximalIdeal S := by
      rw [← hRadJ]
      exact Ideal.le_radical
    have hJproper : J ≠ ⊤ := by
      intro htop
      have htopmax : (⊤ : Ideal S) ≤ IsLocalRing.maximalIdeal S := by
        simpa [htop] using hJleMax
      exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_le_iff.mp htopmax)
    let fS : A →+* S := f
    let ρ : A →+* IsLocalRing.ResidueField S :=
      (IsLocalRing.residue S).comp fS
    have hρfinite : ρ.Finite := by
      change ((IsLocalRing.residue (B ⧸ q)).comp
        ((Ideal.Quotient.mk q).comp φ)).Finite
      rw [← hψcomp]
      exact RingHom.Finite.comp hψfinite
        (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
    let : Algebra S (IsLocalRing.ResidueField S) := (IsLocalRing.residue S).toAlgebra
    let : Algebra A (IsLocalRing.ResidueField S) := ρ.toAlgebra
    have : IsScalarTower A S (IsLocalRing.ResidueField S) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hres : Module.Finite A (IsLocalRing.ResidueField S) := hρfinite
    have hIBne' : (I.map f : Submodule S S) ≠ ⊥ := by
      simpa [hmapI] using hIBne
    obtain ⟨x, hxIB, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIBne'
    have hxJ : x ∈ J := hIBleJ hxIB
    have hdimLE : Ring.KrullDimLE 1 S :=
      Ring.krullDimLE_iff.mpr (by rw [hdimB]; norm_num)
    have hlengthPrincipal : IsFiniteLength S (S ⧸ Ideal.span {x}) :=
      isFiniteLength_quotient_span_singleton S (mem_nonZeroDivisors_of_ne_zero hx0)
    have hspanleJ : Ideal.span {x} ≤ J :=
      Ideal.span_le.mpr (by
        rintro y ⟨rfl⟩
        exact hxJ)
    have hlength : IsFiniteLength S T := by
      let g : (S ⧸ Ideal.span {x}) →ₐ[S] T := Ideal.Quotient.factorₐ S hspanleJ
      exact IsFiniteLength.of_surjective (f := g.toLinearMap) hlengthPrincipal
        (Ideal.Quotient.factor_surjective hspanleJ)
    let : Algebra S T := (Ideal.Quotient.mk J).toAlgebra
    let : Algebra A T := ((Ideal.Quotient.mk J).comp fS).toAlgebra
    have : IsScalarTower A S T := by
      apply IsScalarTower.of_algebraMap_smul
      intro r t
      obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective J t
      change Submodule.Quotient.mk (algebraMap A S r • t) =
        Submodule.Quotient.mk (algebraMap A S r • t)
      rfl
    have hfiniteA : Module.Finite A T :=
      moduleFinite_of_isFiniteLength_over_local
        (hTower := IsScalarTower.of_algebraMap_eq (fun _ => rfl)) hres hlength
    have hfiniteRed : Module.Finite (A ⧸ a) (S ⧸ (a • (⊤ : Submodule A S))) := by
      have hrestrict :
          Submodule.restrictScalars A J = a • (⊤ : Submodule A S) := by
        have hfalg : f = algebraMap A S := by ext x; rfl
        simp [J, hfalg]
      have hfiniteAq : Module.Finite A (S ⧸ (a • (⊤ : Submodule A S))) := by
        rw [← hrestrict]
        exact hfiniteA.equiv (Submodule.Quotient.restrictScalarsEquiv A J).symm
      let : Module.Finite A (S ⧸ (a • (⊤ : Submodule A S))) := hfiniteAq
      have hTors : Module.IsTorsionBySet A (S ⧸ (a • (⊤ : Submodule A S))) (a : Set A) := by
        intro x r
        refine Quotient.inductionOn x ?_
        intro y
        change Submodule.Quotient.mk (r.val • y) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul r.2 Submodule.mem_top
      let : Module (A ⧸ a) (S ⧸ (a • (⊤ : Submodule A S))) := hTors.module
      have : IsScalarTower A (A ⧸ a) (S ⧸ (a • (⊤ : Submodule A S))) :=
        hTors.isScalarTower
      exact Module.Finite.of_restrictScalars_finite A (A ⧸ a)
        (S ⧸ (a • (⊤ : Submodule A S)))
    let : IsPrecomplete a A := by
      let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
      let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup (G := A)
      have haDef := isIdealOfDefinition_topologicalNilradical_of_isAdic I hI
      have haAdic : IsAdic a :=
        (isIdealOfDefinition_iff_isAdic ⟨I, hI⟩ a).mp haDef
      exact (haAdic.isAdicComplete_iff.mpr ⟨hA.2.1, hA.2.2⟩).toIsPrecomplete
    have hsep : ⨅ n : ℕ, a ^ n • (⊤ : Submodule A S) = ⊥ := by
      have hHausJ : IsHausdorff J S := by
        rw [isHausdorff_iff]
        intro x hx
        have hx' : ∀ n : ℕ, x ∈ J ^ n • (⊤ : Submodule S S) :=
          fun n => SModEq.zero.mp (hx n)
        have hx'' : x ∈ ⨅ n : ℕ, J ^ n • (⊤ : Submodule S S) := by
          rw [← SetLike.mem_coe, Submodule.coe_iInf, Set.mem_iInter]
          exact hx'
        rw [J.iInf_pow_smul_eq_bot_of_isLocalRing hJproper] at hx''
        change x = 0 at hx''
        exact hx''
      have hHausA : IsHausdorff a S := by
        have hfalg : f = algebraMap A S := by ext x; rfl
        rw [← IsHausdorff.map_algebraMap_iff (R := A) (S := S) (M := S) (I := a)]
        simpa [J, hfalg] using hHausJ
      exact hHausA.iInf_pow_smul
    have hfiniteS : Module.Finite A S :=
      Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
        a hsep hfiniteRed
    let fbar : (A ⧸ p) →+* S := Ideal.quotientMap q φ le_rfl
    have hfcomp : fbar.comp (Ideal.Quotient.mk p) = fS := by
      simpa [fbar, fS, f] using
        (Ideal.quotientMap_comp_mk (J := p) (I := q) (f := φ) (H := le_rfl))
    have hcompFinite : (fbar.comp (Ideal.Quotient.mk p)).Finite := by
      rw [hfcomp]
      exact hfiniteS
    exact RingHom.Finite.of_comp_finite hcompFinite
  tfae_have 3 → 2 := by
    intro hfinite
    let f : (A ⧸ p) →+* (B ⧸ q) := Ideal.quotientMap q φ le_rfl
    have hfinite' : f.Finite := by simpa [f] using hfinite
    have hsurj : Function.Surjective (PrimeSpectrum.comap f) :=
      integral_overring_surjective f hfinite'.to_isIntegral Ideal.quotientMap_injective
    have hBTFAE := rigPoint_tfae ⟨I.map φ, hJ⟩ q
    have hB1 := (hBTFAE.out 8 1).mp hlocal
    obtain ⟨J, hJdef, hJmax⟩ := hB1
    have haB_radJ := topologicalNilradical_le_radical_of_isIdealOfDefinition J hJdef
    have hpAvoid : ¬ a ≤ p := by
      intro ha
      apply hIavoid
      exact Ideal.map_le_iff_le_comap.mpr (hIleA.trans ha)
    have hpMax : Ideal.IsMaximalAmongPrimesAvoiding a p := by
      refine ⟨hpAvoid, ?_⟩
      intro r hr hpr har
      have hrbarPrime : (r.map (Ideal.Quotient.mk p)).IsPrime :=
        Ideal.isPrime_map_quotientMk_of_isPrime hpr
      let rbar : Ideal (A ⧸ p) := r.map (Ideal.Quotient.mk p)
      let : rbar.IsPrime := hrbarPrime
      have hrbar_comap : rbar.comap (Ideal.Quotient.mk p) = r := by
        simp [rbar, sup_eq_right.mpr hpr]
      obtain ⟨s, hs⟩ := hsurj ⟨rbar, hrbarPrime⟩
      have hsIdeal : s.asIdeal.comap f = rbar := by
        simpa using congrArg PrimeSpectrum.asIdeal hs
      let Q : Ideal B := s.asIdeal.comap (Ideal.Quotient.mk q)
      have hQprime : Q.IsPrime :=
        Ideal.comap_isPrime (f := Ideal.Quotient.mk q) (K := s.asIdeal)
      have hqQ : q ≤ Q := by
        intro x hx
        change Ideal.Quotient.mk q x ∈ s.asIdeal
        have hxq : Ideal.Quotient.mk q x = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hx
        rw [hxq]
        exact s.asIdeal.zero_mem
      have hQr : Q.comap φ = r := by
        ext x
        change Ideal.Quotient.mk q (φ x) ∈ s.asIdeal ↔ x ∈ r
        have hcomp : f (Ideal.Quotient.mk p x) = Ideal.Quotient.mk q (φ x) := by
          simp [f]
        rw [← hcomp, ← Ideal.mem_comap, hsIdeal, ← Ideal.mem_comap, hrbar_comap]
      have hJnotQ : ¬ J ≤ Q := by
        intro hJQ
        apply har
        intro x hx
        have hφx : φ x ∈ topologicalNilradical B := by
          exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
            ((IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx).map hφ)
        have hφQ : φ x ∈ Q := by
          obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (haB_radJ hφx)
          exact hQprime.mem_of_pow_mem n (hJQ hn)
        rw [← hQr]
        exact hφQ
      have hQeq : Q = q := hJmax.2 Q hQprime hqQ hJnotQ
      have hpr : p = r := by
        calc
          p = q.comap φ := rfl
          _ = Q.comap φ := by rw [hQeq]
          _ = r := hQr
      simpa [p] using hpr.symm
    have hATFAE := rigPoint_tfae ⟨I, hI⟩ p
    have hA1 : ∃ J : Ideal A,
        TopologicalRing.IsIdealOfDefinition J ∧
          Ideal.IsMaximalAmongPrimesAvoiding J p :=
      ⟨a, isIdealOfDefinition_topologicalNilradical_of_isAdic I hI, hpMax⟩
    have hclosed : ∀ J : Ideal A, TopologicalRing.IsIdealOfDefinition J →
        Ideal.IsClosedPointAwayFrom J p :=
      (hATFAE.out 1 4).mp hA1
    exact hclosed a (isIdealOfDefinition_topologicalNilradical_of_isAdic I hI)
  tfae_have 2 → 1 := by
    intro hpclosed
    let : IsLocalRing (B ⧸ q) := hlocal.choose
    have htaut := RingHom.isTaut_of_isAdic φ ⟨I, hI, hJ⟩
    have hred := isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType
      φ hφ hA.1 htaut hft
    obtain ⟨ψ, hψcomp, hψft⟩ :=
      exists_residueFieldMap_finiteType_of_rigPoint q hlocal φ hφ hred
    have hpLocal := rigPointLocalCondition_of_isClosedPointAwayFrom ⟨I, hI⟩ p hpclosed
    rcases hpLocal with ⟨hLocalA, hdimA, hNoethA, hDomainA, hCompA, hT2A, hRadA⟩
    let : IsLocalRing (A ⧸ p) := hLocalA
    let : IsNoetherianRing (A ⧸ p) := hNoethA
    let : IsDomain (A ⧸ p) := hDomainA
    let f : (A ⧸ p) →+* (B ⧸ q) := Ideal.quotientMap q φ le_rfl
    let kA := IsLocalRing.ResidueField (A ⧸ p)
    let kB := IsLocalRing.ResidueField (B ⧸ q)
    let IA : Ideal (A ⧸ p) := I.map (Ideal.Quotient.mk p)
    let IB : Ideal (B ⧸ q) := (I.map φ).map (Ideal.Quotient.mk q)
    have hIAdef := isIdealOfDefinition_of_isAdic hI
    have hIBdef := isIdealOfDefinition_of_isAdic hJ
    have hRadIA : IA.radical = IsLocalRing.maximalIdeal (A ⧸ p) := by
      exact hRadA I hIAdef
    have hRadIB : IB.radical = IsLocalRing.maximalIdeal (B ⧸ q) := by
      rcases hlocal with ⟨_, _, _, _, _, _, hRadB⟩
      exact hRadB (I.map φ) hIBdef
    have hmapI : Ideal.map f IA = IB := by
      have hfcomp : f.comp (Ideal.Quotient.mk p) =
          (Ideal.Quotient.mk q).comp φ := by
        ext x
        simp [f]
      change (I.map (Ideal.Quotient.mk p)).map f =
        (I.map φ).map (Ideal.Quotient.mk q)
      rw [Ideal.map_map, hfcomp, Ideal.map_map]
    have hmapMax :
        Ideal.map f (IsLocalRing.maximalIdeal (A ⧸ p)) ≤
          IsLocalRing.maximalIdeal (B ⧸ q) := by
      rw [← hRadIA, ← hRadIB, ← hmapI]
      exact Ideal.map_radical_le f
    have : IsLocalHom f := ((IsLocalRing.local_hom_TFAE f).out 3 1).mp hmapMax
    let θ : kA →+* kB := IsLocalRing.ResidueField.map f
    let g : A →+* kA := (IsLocalRing.residue (A ⧸ p)).comp (Ideal.Quotient.mk p)
    have haRad : a ≤ I.radical :=
      topologicalNilradical_le_radical_of_isIdealOfDefinition I hIAdef
    have hker' : ∀ x ∈ a, g x = 0 := by
      intro x hx
      apply (IsLocalRing.residue_eq_zero_iff (Ideal.Quotient.mk p x)).2
      rw [← hRadIA]
      exact Ideal.map_radical_le (Ideal.Quotient.mk p) (Ideal.mem_map_of_mem _ (haRad hx))
    let τ : (A ⧸ a) →+* kA := Ideal.Quotient.lift a g hker'
    have hτcomp : τ.comp (Ideal.Quotient.mk a) = g := by
      ext x
      change (Ideal.Quotient.lift a g hker') (Ideal.Quotient.mk a x) = g x
      rw [Ideal.Quotient.lift_mk]
    have hτsurj : Function.Surjective τ := by
      intro y
      obtain ⟨z, hz⟩ := IsLocalRing.residue_surjective (R := A ⧸ p) y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      refine ⟨Ideal.Quotient.mk a x, ?_⟩
      change IsLocalRing.residue (A ⧸ p) (Ideal.Quotient.mk p x) = y
      exact hz
    have hθg : θ.comp g =
        (IsLocalRing.residue (B ⧸ q)).comp ((Ideal.Quotient.mk q).comp φ) := by
      ext x
      rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalRing.ResidueField.map_residue]
      rfl
    have hfactor : ψ = θ.comp τ := by
      apply RingHom.ext
      intro x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hcomp := hθg.trans hψcomp.symm
      have hτval : τ (Ideal.Quotient.mk a y) = g y :=
        congrArg (fun F : A →+* kA => F y) hτcomp
      calc
        ψ (Ideal.Quotient.mk a y) = (ψ.comp (Ideal.Quotient.mk a)) y := rfl
        _ = (θ.comp g) y := (congrArg (fun F : A →+* kB => F y) hcomp).symm
        _ = (θ.comp τ) (Ideal.Quotient.mk a y) := by
          change θ (g y) = θ (τ (Ideal.Quotient.mk a y))
          exact congrArg θ hτval.symm
    have hθft : θ.FiniteType := by
      have hcompft : (θ.comp τ).FiniteType := by
        simpa [hfactor] using hψft
      exact RingHom.FiniteType.of_comp_finiteType (f := τ) (g := θ) hcompft
    let : Algebra kA kB := θ.toAlgebra
    have : Algebra.FiniteType kA kB := by
      exact hθft
    have hAlgebraic : Algebra.IsAlgebraic kA kB := Algebra.IsAlgebraic.of_finiteType
    have : Algebra.IsIntegral kA kB :=
      (Algebra.isAlgebraic_iff_isIntegral).mp hAlgebraic
    have hθfiniteMod : Module.Finite kA kB := Algebra.IsIntegral.finite
    have hθfinite : θ.Finite := hθfiniteMod
    have hτfinite : τ.Finite := RingHom.Finite.of_surjective τ hτsurj
    have hψfinite : ψ.Finite := by
      rw [hfactor]
      exact hθfinite.comp hτfinite
    exact ⟨hlocal.choose, ⟨ψ, hψcomp, hψfinite⟩⟩
  tfae_finish

end

section

/-- Whether a prime is closed away from the vanishing locus of an ideal only depends on the
radical of that ideal. -/
public lemma isClosedPointAwayFrom_congr_radical
    {A : Type*} [CommRing A] (I J q : Ideal A) [q.IsPrime]
    (hIJ : I.radical = J.radical) :
    Ideal.IsClosedPointAwayFrom I q ↔
      Ideal.IsClosedPointAwayFrom J q := by
  have hzero : PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) := by
    rw [← PrimeSpectrum.zeroLocus_radical I, hIJ, PrimeSpectrum.zeroLocus_radical]
  constructor <;> intro h
  · change ∃ hq : _, IsClosed _ at h
    change ∃ hq : _, IsClosed _
    rw [hzero] at h
    exact h
  · change ∃ hq : _, IsClosed _ at h
    change ∃ hq : _, IsClosed _
    rw [hzero.symm] at h
    exact h

/-- Under a Jacobson reduction of the source, the inverse image of a rig-closed
prime along an adic topologically finite type morphism is rig-closed. -/
@[stacks 0GGC]
public theorem isRigPointLocalCondition_comap_of_isJacobsonRing_quotient
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (hadic : RingHom.IsAdic φ)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsRigPointLocalCondition q)
    (hJacobson : ∃ I : Ideal A,
      TopologicalRing.IsIdealOfDefinition I ∧ IsJacobsonRing (A ⧸ I)) :
    Ideal.IsRigPointLocalCondition (q.comap φ) := by
  rcases hadic with ⟨Iadic, hIadicA, hIadicB⟩
  let : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := hA.2.1
  let : T2Space A := hA.2.2
  let : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B) := hB.2.1
  let : T2Space B := hB.2.2
  have hAadic : ∃ J : Ideal A, _root_.IsAdic J := ⟨Iadic, hIadicA⟩
  have hBadic : ∃ J : Ideal B, _root_.IsAdic J := ⟨Iadic.map φ, hIadicB⟩
  have hIdefA : TopologicalRing.IsIdealOfDefinition Iadic :=
    (isIdealOfDefinition_iff_isAdic hAadic Iadic).2 hIadicA
  have hIdefB : TopologicalRing.IsIdealOfDefinition (Iadic.map φ) :=
    (isIdealOfDefinition_iff_isAdic hBadic (Iadic.map φ)).2 hIadicB
  have htaut := RingHom.isTaut_of_isAdic φ ⟨Iadic, hIadicA, hIadicB⟩
  have hfiniteRed :=
    isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType
      φ hφ hA.1 htaut hft
  have hclosedB : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical B) q := by
    have hTFAE := rigPoint_tfae hBadic q
    have hall : ∀ J : Ideal B, TopologicalRing.IsIdealOfDefinition J →
        Ideal.IsClosedPointAwayFrom J q :=
      (hTFAE.out 8 4 (by rfl) (by rfl) (by decide) (by decide)).mp hq
    have hclosed := hall (Iadic.map φ) hIdefB
    have hrad := radical_eq_topologicalNilradical_of_isIdealOfDefinition
      (Iadic.map φ) hIdefB
    exact (isClosedPointAwayFrom_congr_radical
      (Iadic.map φ) (topologicalNilradical B) q
      (hrad.trans TopologicalRing.topologicalNilradical_isRadical.radical.symm)).mp hclosed
  have hrelative := rigPoint_relative_tfae
    hA hB φ hφ ⟨Iadic, hIadicA, hIadicB⟩ hft q hclosedB
  rcases hJacobson with ⟨J, hJdef, hJjac⟩
  have hJle : J ≤ topologicalNilradical A :=
    isIdealOfDefinition_le_topologicalNilradical J hJdef
  let ψ₀ : (A ⧸ J) →+*
      (A ⧸ topologicalNilradical A) := Ideal.quotientMap (topologicalNilradical A)
        (RingHom.id A) hJle
  have hψ₀surj : Function.Surjective ψ₀ :=
    Ideal.quotientMap_surjective (f := RingHom.id A) (H := hJle)
      (RingHom.surjective _)
  let : IsJacobsonRing (A ⧸ J) := hJjac
  let : IsJacobsonRing (A ⧸ topologicalNilradical A) :=
    isJacobsonRing_of_surjective ⟨ψ₀, hψ₀surj⟩
  let : IsLocalRing (B ⧸ q) := hq.choose
  obtain ⟨ψ, hψcomp, hψft⟩ :=
    exists_residueFieldMap_finiteType_of_rigPoint
      q hq φ hφ hfiniteRed
  let K := IsLocalRing.ResidueField (B ⧸ q)
  let : Field K := inferInstance
  let : Algebra (A ⧸ topologicalNilradical A) K := ψ.toAlgebra
  have hψfinite : ψ.Finite := by
    let : Algebra.FiniteType (A ⧸ topologicalNilradical A) K := by
      change RingHom.FiniteType ψ at hψft
      change RingHom.FiniteType (algebraMap (A ⧸ topologicalNilradical A) K)
      simpa only [RingHom.algebraMap_toAlgebra] using hψft
    change (algebraMap (A ⧸ topologicalNilradical A) K).Finite
    exact RingHom.finite_algebraMap.mpr
      (finite_of_finite_type_of_isJacobsonRing _ _)
  have hfirst :
      ∃ hlocal : IsLocalRing (B ⧸ q),
        let : IsLocalRing (B ⧸ q) := hlocal
        ∃ ψ : (A ⧸ topologicalNilradical A) →+* K,
          ψ.comp (Ideal.Quotient.mk (topologicalNilradical A)) =
              (IsLocalRing.residue (B ⧸ q)).comp
                ((Ideal.Quotient.mk q).comp φ) ∧ ψ.Finite :=
    ⟨hq.choose, ψ, hψcomp, hψfinite⟩
  have hclosedP : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical A) (q.comap φ) :=
    (hrelative.out 1 2 (by rfl) (by rfl) (by decide) (by decide)).mp hfirst
  have hradA := radical_eq_topologicalNilradical_of_isIdealOfDefinition Iadic hIdefA
  have hclosedP' :=
    (isClosedPointAwayFrom_congr_radical
      (topologicalNilradical A) Iadic (q.comap φ)
      (TopologicalRing.topologicalNilradical_isRadical.radical.trans hradA.symm)).mp hclosedP
  have hclosed_iff_rig :
      (∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
        Ideal.IsClosedPointAwayFrom I (q.comap φ)) ↔
        Ideal.IsRigPointLocalCondition (q.comap φ) :=
    (rigPoint_tfae hAadic (q.comap φ)).out 2 8
      (by rfl) (by rfl) (by decide) (by decide)
  exact hclosed_iff_rig.mp ⟨Iadic, hIdefA, hclosedP'⟩

end

end Rig

end
