module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.GeometricBranchCount
public import StacksFrontier.AlgebraicGeometry.Variety.Branches.Wedge
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.MaximalSpectrum
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.Length.Comparison
public import StacksFrontier.RingTheory.NoetherNormalization.Basic
public import StacksFrontier.RingTheory.Nagata.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The delta invariant bounds the number of geometric branches

For a strictly henselian reduced Nagata local ring the delta invariant is at least one less than
the number of geometric branches, and a one-dimensional such ring attaining the bound is a wedge
of strictly henselian discrete valuation rings.

## Main results

* `Ring.deltaInvariant_ge_numberOfGeometricBranches_sub_one_of_strictlyHenselian`: the lower
  bound on the delta invariant in terms of the number of geometric branches.
* `Ring.exists_isWedge_of_deltaInvariant_eq_numberOfGeometricBranches_sub_one`: equality in
  that bound forces the ring to be a wedge of strictly henselian discrete valuation rings.

## References

* [Stacks Project, Tag 0C42](https://stacks.math.columbia.edu/tag/0C42)
-/

@[expose] public section

universe u v

namespace Ring

open IsLocalRing

/-- A linear map out of the base field has range of rank at most one. -/
private theorem rank_le_one_of_surjective_of_field (k : Type u) [Field k] (M : Type u)
    [AddCommGroup M] [Module k M] (f : k →ₗ[k] M) (hf : Function.Surjective f) :
    Module.rank k M ≤ 1 := by
  simpa using LinearMap.rank_le_of_surjective f hf

/-- If every factor of a product of vector spaces has a nonzero vector and `N` is a subspace of
rank at most one, then the number of factors is at most the rank of the quotient by `N` plus
one. -/
private theorem card_le_toENat_rank_quotient_add_one (k : Type u) [Field k] {ι : Type u}
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (v : ∀ i, V i) (hv : ∀ i, v i ≠ 0)
    (N : Submodule k (∀ i, V i)) (hN : Module.rank k N ≤ 1) :
    ENat.card ι ≤ Cardinal.toENat (Module.rank k ((∀ i, V i) ⧸ N)) + 1 := by
  classical
  have hli : LinearIndependent k
      (fun j : Σ _ : ι, Unit => Pi.single (M := V) j.1 (v j.1)) := by
    exact Pi.linearIndependent_single (ιs := fun _ : ι => Unit) (Ms := V) (v := fun i _ => v i)
      fun i => (linearIndependent_unique_iff (R := k) (v := fun _ : Unit => v i)).2 (hv i)
  have hprod : Cardinal.mk ι ≤ Module.rank k (∀ i, V i) := by
    convert hli.cardinal_le_rank using 1
    exact (Equiv.sigmaPUnit ι).cardinal_eq.symm
  rw [← rank_quotient_add_rank_of_divisionRing N] at hprod
  simpa [ENat.card, map_add] using
    Cardinal.enat_gc.monotone_u (hprod.trans (add_le_add_right hN _))

/-- The delta invariant of a strictly henselian reduced Nagata
local ring is at least the number of its geometric branches minus one. -/
@[stacks 0C42 "delta_ge_branches_sub_one"]
public lemma deltaInvariant_ge_numberOfGeometricBranches_sub_one_of_strictlyHenselian
    (A : Type u) [CommRing A] [IsReduced A]
    [StrictlyHenselianLocalRing A]
    (hA : IsNagataRing A) :
    Ring.deltaInvariant A ≥
      numberOfGeometricBranchesOfLocalRing A - 1 := by
  classical
  let B := integralClosure A (FractionRing A)
  let D := strictHenselizationData A
  let Ash := D.carrier
  let : CommRing Ash := D.commRing
  let : IsLocalRing Ash := D.isLocalRing
  let : Algebra A Ash := D.algebra
  let : IsLocalRing.IsHenselization A (SeparableClosure (ResidueField A)) Ash :=
    D.isHenselization
  have hbranches :=
    Ring.numberOfGeometricBranches_eq_encard_maximalSpectrum_integralClosure
      A (SeparableClosure (ResidueField A)) Ash hA
  have hcount : numberOfGeometricBranchesOfLocalRing A =
      Set.encard (Set.univ : Set (MaximalSpectrum B)) := by
    rw [numberOfGeometricBranchesOfLocalRing_eq_encard_minimalPrimes]
    change (minimalPrimes Ash).encard = _
    exact hbranches
  let p : Type u := (m : MaximalSpectrum B) → B ⧸ m.asIdeal
  let f := Ring.normalizationResidueProductMap A
  let g := f.comp (Algebra.linearMap A B)
  have hmax (m : MaximalSpectrum B) :
      maximalIdeal A = m.asIdeal.comap (algebraMap A B) :=
    (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) m.asIdeal)).symm
  let k := A ⧸ maximalIdeal A
  let : Field k := Ideal.Quotient.field (maximalIdeal A)
  have hcomponent (m : MaximalSpectrum B) :
      Module.IsTorsionBySet A (B ⧸ m.asIdeal) (maximalIdeal A : Set A) := by
    intro x r
    have hrm : algebraMap A B r ∈ m.asIdeal := by
      rw [← Ideal.mem_comap, ← hmax m]
      exact r.property
    change (r : A) • x = 0
    rw [Algebra.smul_def]
    change Ideal.Quotient.mk m.asIdeal (algebraMap A B r) * x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hrm, zero_mul]
  let : ∀ m : MaximalSpectrum B, Module k (B ⧸ m.asIdeal) :=
    fun m => (hcomponent m).module
  let : Module k p := inferInstance
  let : IsScalarTower A k p := by infer_instance
  have hmk (a : A) (x : p) :
      Ideal.Quotient.mk (maximalIdeal A) a • x = a • x := by
    ext m
    exact Module.IsTorsionBySet.mk_smul (hcomponent m) a (x m)
  let N : Submodule k p :=
    { carrier := LinearMap.range g
      zero_mem' := (LinearMap.range g).zero_mem
      add_mem' := fun hx hy => (LinearMap.range g).add_mem hx hy
      smul_mem' := by
        rintro r _ ⟨y, rfl⟩
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact ⟨a • y, by rw [LinearMap.map_smul, hmk]⟩ }
  have hone (m : MaximalSpectrum B) : (1 : B ⧸ m.asIdeal) ≠ 0 := by
    let : m.asIdeal.IsMaximal := m.isMaximal
    let : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    exact one_ne_zero
  have hRankN : Module.rank k N ≤ 1 := by
    let y : N := ⟨g 1, ⟨1, rfl⟩⟩
    have hsurj : Function.Surjective (LinearMap.toSpanSingleton k N y) := by
      intro x
      rcases x.2 with ⟨a, ha⟩
      refine ⟨Ideal.Quotient.mk (maximalIdeal A) a, Subtype.ext ?_⟩
      change Ideal.Quotient.mk (maximalIdeal A) a • (y : p) = (x : p)
      rw [hmk]
      calc
        a • g 1 = g (a • (1 : A)) := (g.map_smul a (1 : A)).symm
        _ = g a := by simp
        _ = (x : p) := ha
    exact rank_le_one_of_surjective_of_field k N _ hsurj
  let Q := p ⧸ N
  let : IsScalarTower A k Q := by infer_instance
  have hdimQ : ENat.card (MaximalSpectrum B) ≤ Cardinal.toENat (Module.rank k Q) + 1 :=
    card_le_toENat_rank_quotient_add_one k (fun m : MaximalSpectrum B => B ⧸ m.asIdeal)
      (fun _ => 1) hone N hRankN
  have hmap : Function.Surjective (algebraMap A k) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, by simp [k]⟩
  have hlenQ : Module.length A Q = Cardinal.toENat (Module.rank k Q) := by
    rw [Module.length_eq_of_surjective (S := A) (R := k) (M := Q) hmap,
      Module.length_eq_rank]
  have htarget : numberOfGeometricBranchesOfLocalRing A - 1 ≤
      Module.length A Q := by
    rw [hcount, Set.encard_univ, hlenQ]
    exact tsub_le_iff_right.2 hdimQ
  let M := B ⧸ LinearMap.range (Algebra.linearMap A B)
  change Module.length A M ≥ numberOfGeometricBranchesOfLocalRing A - 1
  exact htarget.trans (Module.length_le_of_surjective
    (Ring.normalizationResidueQuotientMap A)
    (Ring.normalizationResidueQuotientMap_surjective A hA))

/-- Each factor of a normal finite product of rings is normal. -/
private theorem isNormalRing_of_pi_factor {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] (hR : IsNormalRing (∀ i, R i)) (i : ι) :
    IsNormalRing (R i) := by
  intro q hq
  let p : Ideal (∀ j, R j) := q.comap (Pi.evalRingHom R i)
  have : p.IsPrime := hq.comap _
  let e : Localization.AtPrime p ≃+* Localization.AtPrime q :=
    RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q)
      (Localization.AtPrime.mapPiEvalRingHom_bijective q)
  obtain ⟨_, _⟩ := hR p
  exact ⟨Function.Injective.isDomain e.symm.toRingHom e.symm.injective,
    IsIntegrallyClosed.of_equiv e⟩

/-- A finite local domain algebra over a strictly henselian local ring is henselian with
separably closed residue field. -/
private theorem strictHenselian_of_finite_domain (A B : Type u) [CommRing A] [CommRing B]
    [StrictlyHenselianLocalRing A] [IsLocalRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] :
    HenselianLocalRing B ∧ IsSepClosed (ResidueField B) := by
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  obtain ⟨hB, _, hsep⟩ := RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain
    (algebraMap A B) (Algebra.IsIntegral.isIntegral (R := A))
  let : IsLocalRing B := hB.toIsLocalRing
  exact ⟨hB, (hsep inferInstance).1⟩

/-- A one-dimensional Noetherian integrally closed local domain is a discrete valuation ring. -/
@[ega "IV 6.7.5" "partial"]
private theorem isDVR_of_normal_local_dim_one (B : Type u) [CommRing B]
    [IsNoetherianRing B] [IsLocalRing B] [IsDomain B] [IsIntegrallyClosed B]
    (hdim : ringKrullDim B = 1) : IsDiscreteValuationRing B := by
  have hcrit : IsNoetherianRing B ∧ IsLocalRing B ∧ IsDomain B ∧
      IsIntegrallyClosed B ∧ ringKrullDim B = 1 :=
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim⟩
  obtain ⟨_, hDVR⟩ := ((isDiscreteValuationRing_tfae B).out 5 1).mp hcrit
  exact hDVR

/-- A finite local algebra over a local ring has a local structure map. -/
private theorem isLocalHom_algebraMap_of_finite (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [Module.Finite A B] :
    IsLocalHom (algebraMap A B) := by
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hmax : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (maximalIdeal B))
  refine ⟨fun a hu => ?_⟩
  by_contra hna
  have hmap : algebraMap A B a ∈ maximalIdeal B := by
    rw [← Ideal.mem_comap, hmax]
    exact (mem_maximalIdeal a).2 (mem_nonunits_iff.mpr hna)
  exact (notMem_maximalIdeal.mpr hu) hmap

/-- The structure map of the normalization of the fraction ring of `A` is injective. -/
private theorem algebraMap_integralClosure_injective (A : Type u) [CommRing A] :
    Function.Injective (algebraMap A (integralClosure A (FractionRing A))) := fun a b hab =>
  IsFractionRing.injective A (FractionRing A)
    (by simpa using congrArg (fun x : integralClosure A (FractionRing A) =>
      (x : FractionRing A)) hab)

/-- If the normalization of a one-dimensional reduced henselian Nagata local ring `A` is a finite
product of local domains finite over `A`, then every factor has dimension one. -/
private theorem normalization_factor_dim_one (A : Type u) [CommRing A]
    [HenselianLocalRing A] [IsReduced A] (hA : IsNagataRing A) (hdim : ringKrullDim A = 1)
    {ι : Type v} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, IsLocalRing (B i)] [∀ i, IsDomain (B i)] [∀ i, Algebra A (B i)]
    [∀ i, Module.Finite A (B i)]
    (e : integralClosure A (FractionRing A) ≃ₐ[A] ∀ i, B i) :
    ∀ i, ringKrullDim (B i) = 1 := by
  classical
  let C := integralClosure A (FractionRing A)
  let : IsNoetherianRing A := hA.1
  let : Module.Finite A C := module_finite_integralClosure_fractionRing hA
  let : IsIntegralClosure C A (FractionRing A) := integralClosure.isIntegralClosure A _
  let : Algebra.IsIntegral A C := ⟨fun x => IsIntegralClosure.isIntegral A (FractionRing A) x⟩
  obtain ⟨f, hf, hrad⟩ := IsLocalRing.exists_radical_span_eq_maximalIdeal hdim
  have havoid :=
    (IsLocalRing.radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes hdim hf).mp hrad
  have hdepth := IsLocalRing.depth_eq_one_of_isReduced hdim
  have hfreg :=
    (IsLocalRing.notMem_minimalPrimes_iff_mem_nonZeroDivisors_of_depth_eq_one
      hdim hdepth f).mp havoid
  have hfunit : IsUnit (algebraMap A (FractionRing A) f) :=
    IsLocalization.map_units (FractionRing A) ⟨f, hfreg⟩
  have hdimC : ringKrullDim C = 1 := (ringKrullDim_eq_of_injective_isIntegral (algebraMap A C)
    (algebraMap_integralClosure_injective A)
    (Algebra.IsIntegral.isIntegral (R := A))).symm.trans hdim
  intro i
  let g : C →+* B i := (Pi.evalRingHom B i).comp e.toRingEquiv.toRingHom
  have hsurj : Function.Surjective g := fun b => ⟨e.symm (Pi.single i b), by simp [g]⟩
  have hdim_le : ringKrullDim (B i) ≤ 1 := (ringKrullDim_le_of_surjective g hsurj).trans hdimC.le
  have hfi : algebraMap A (B i) f ≠ 0 := by
    intro hzero
    let z : C := e.symm (Pi.single i (1 : B i))
    have hz : z ≠ 0 := by
      intro hz
      have hsingle : Pi.single i (1 : B i) = 0 := by
        simpa [z] using congrArg e hz
      simpa using congrFun hsingle i
    have hmul : algebraMap A C f * z = 0 := by
      apply e.injective
      ext j
      by_cases hji : j = i
      · subst j
        rw [map_mul, e.commutes]
        simp [z, hzero]
      · rw [map_mul, e.commutes]
        simp [z, hji]
    have hmulQ : (algebraMap A (FractionRing A) f) * (z : FractionRing A) = 0 := by
      simpa using congrArg (fun x : C => (x : FractionRing A)) hmul
    have hzQ : (z : FractionRing A) = 0 :=
      hfunit.mul_left_cancel (by simpa using hmulQ)
    exact hz (Subtype.ext hzQ)
  have hnotField : ¬ IsField (B i) := by
    intro hfield
    let : Field (B i) := hfield.toField
    let : IsLocalHom (algebraMap A (B i)) := isLocalHom_algebraMap_of_finite A (B i)
    have hfiMax : algebraMap A (B i) f ∈ maximalIdeal (B i) :=
      map_nonunit (algebraMap A (B i)) f hf
    have hu : IsUnit (algebraMap A (B i) f) := IsUnit.mk0 _ hfi
    exact (notMem_maximalIdeal.mpr hu) hfiMax
  have hnotle0 : ¬ ringKrullDim (B i) ≤ 0 := by
    intro hle
    let : Ring.KrullDimLE 0 (B i) := Ring.krullDimLE_iff.mpr hle
    exact hnotField (Ring.KrullDimLE.isField_of_isDomain)
  have hpositive : 0 < ringKrullDim (B i) := lt_of_not_ge hnotle0
  have hone : (1 : WithBot ℕ∞) ≤ ringKrullDim (B i) := by
    exact_mod_cast (Order.succ_le_of_lt hpositive)
  exact le_antisymm hdim_le hone

/-- A finite product of local rings has one maximal ideal for each factor. -/
private noncomputable def maximalSpectrum_pi_equiv_fin (m : ℕ) (B : Fin m → Type u)
    [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)] :
    MaximalSpectrum (∀ i, B i) ≃ Fin m := by
  classical
  let f : Fin m → MaximalSpectrum (∀ i, B i) := fun i =>
    ⟨(maximalIdeal (B i)).comap (Pi.evalRingHom B i),
      Ideal.IsMaximal.comap_piEvalRingHom (inferInstance : (maximalIdeal (B i)).IsMaximal)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hsig : PrimeSpectrum.sigmaToPi B
          ⟨i, (⟨maximalIdeal (B i), (inferInstance : (maximalIdeal (B i)).IsPrime)⟩ :
            PrimeSpectrum (B i))⟩ =
          PrimeSpectrum.sigmaToPi B
            ⟨j, (⟨maximalIdeal (B j), (inferInstance : (maximalIdeal (B j)).IsPrime)⟩ :
              PrimeSpectrum (B j))⟩ := by
        apply PrimeSpectrum.ext
        simpa [f] using congrArg (fun M : MaximalSpectrum (∀ i, B i) => M.asIdeal) hij
      exact congrArg Sigma.fst (PrimeSpectrum.sigmaToPi_injective B hsig)
    · intro M
      obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
        M.toPrimeSpectrum
      let eval : (∀ j, B j) →+* B i := Pi.evalRingHom B i
      have heval : Function.Surjective eval := Function.surjective_eval _
      have hqmax : q.asIdeal.IsMaximal := by
        have hmap := Ideal.map_eq_top_or_isMaximal_of_surjective (f := eval)
          (I := M.asIdeal) heval M.2
        have hMideal : M.asIdeal = Ideal.comap eval q.asIdeal := by
          simpa [eval, MaximalSpectrum.toPrimeSpectrum] using
            (congrArg PrimeSpectrum.asIdeal hq).symm
        rw [hMideal, Ideal.map_comap_of_surjective eval heval] at hmap
        exact hmap.resolve_left q.2.ne_top
      have hqeq : q.asIdeal = maximalIdeal (B i) := eq_maximalIdeal hqmax
      refine ⟨i, ?_⟩
      apply MaximalSpectrum.ext
      have hq' := congrArg PrimeSpectrum.asIdeal hq
      change q.asIdeal.comap eval = M.asIdeal at hq'
      rw [hqeq] at hq'
      simpa [f] using hq'
  exact (Equiv.ofBijective f hf).symm

/-- A strictly henselian, reduced, one-dimensional Nagata local ring attaining the lower bound
for its delta invariant is a wedge of a nonempty finite family of strictly henselian discrete
valuation rings. -/
@[stacks 0C42 "equality_implies_wedge"]
public theorem exists_isWedge_of_deltaInvariant_eq_numberOfGeometricBranches_sub_one
    (A : Type u) [CommRing A] [IsReduced A]
    [StrictlyHenselianLocalRing A]
    (hA : IsNagataRing A) (hdim : ringKrullDim A = 1)
    (hdelta : Ring.deltaInvariant A =
      numberOfGeometricBranchesOfLocalRing A - 1) :
    ∃ (n : ℕ) (B : Fin (n + 1) → Type u)
      (_ : ∀ i, CommRing (B i)) (_ : ∀ i, IsDomain (B i))
      (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, IsDiscreteValuationRing (B i))
      (_ : ∀ i, StrictlyHenselianLocalRing (B i)),
      IsLocalRing.IsWedge A B := by
  classical
  let C := integralClosure A (FractionRing A)
  let : IsNoetherianRing A := hA.1
  let : Module.Finite A C := module_finite_integralClosure_fractionRing hA
  obtain ⟨m, B, hBcomm, hBalgebra, hBlocal, hBfinite, ⟨e⟩⟩ :=
    exists_algEquiv_pi_isLocalRing A C
  let : ∀ i : Fin m, CommRing (B i) := hBcomm
  let : ∀ i : Fin m, Algebra A (B i) := hBalgebra
  let : ∀ i : Fin m, IsLocalRing (B i) := hBlocal
  let : ∀ i : Fin m, Module.Finite A (B i) := hBfinite
  have hnormalC : IsNormalRing C := isNormalRing_integralClosure_fractionRing (A := A)
  have hnormalProd : IsNormalRing (∀ i : Fin m, B i) :=
    IsNormalRing.congr e.toRingEquiv hnormalC
  let hnormalFactor : ∀ i : Fin m, IsNormalRing (B i) :=
    isNormalRing_of_pi_factor B hnormalProd
  let : ∀ i : Fin m, IsDomain (B i) := fun i => (hnormalFactor i).of_isLocalRing.1
  let : ∀ i : Fin m, IsIntegrallyClosed (B i) := fun i =>
    (hnormalFactor i).of_isLocalRing.2
  have hdimFactor : ∀ i : Fin m, ringKrullDim (B i) = 1 :=
    normalization_factor_dim_one A hA hdim B e
  have hnonemptyIndex : m ≠ 0 := by
    intro hm
    subst m
    have heq : e (algebraMap A C 0) = e (algebraMap A C 1) := Subsingleton.elim _ _
    have hzeroone : (0 : A) = 1 := by
      apply (IsFractionRing.injective A (FractionRing A))
      have h := congrArg (fun x : C => (x : FractionRing A)) (e.injective heq)
      simp at h
    exact zero_ne_one hzeroone
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnonemptyIndex
  let : ∀ i : Fin (n + 1), IsNoetherianRing (B i) := fun i =>
    IsNoetherianRing.of_finite A (B i)
  have hDVR : ∀ i : Fin (n + 1), IsDiscreteValuationRing (B i) := fun i =>
    isDVR_of_normal_local_dim_one (B i) (hdimFactor i)
  let hstrict : ∀ i : Fin (n + 1),
      HenselianLocalRing (B i) ∧ IsSepClosed (ResidueField (B i)) := fun i =>
    strictHenselian_of_finite_domain A (B i)
  let : ∀ i : Fin (n + 1), HenselianLocalRing (B i) := fun i => (hstrict i).1
  let : ∀ i : Fin (n + 1), IsSepClosed (ResidueField (B i)) := fun i => (hstrict i).2
  let : ∀ i : Fin (n + 1), StrictlyHenselianLocalRing (B i) := fun _ => ⟨⟩
  let : ∀ i : Fin (n + 1), IsLocalHom (algebraMap A (B i)) := fun i =>
    isLocalHom_algebraMap_of_finite A (B i)
  let κ := ResidueField A
  let P := ∀ i : Fin (n + 1), ResidueField (B i)
  let : ∀ i : Fin (n + 1), Algebra κ (ResidueField (B i)) := inferInstance
  let : ∀ i : Fin (n + 1), IsScalarTower A κ (ResidueField (B i)) := inferInstance
  let : Algebra κ P := inferInstance
  let : Algebra A P := inferInstance
  let : IsScalarTower A κ P := inferInstance
  let : Module.Finite κ P := inferInstance
  let rhoA : A →ₗ[A] P := Algebra.linearMap A P
  let rhoC : C →ₗ[A] P :=
    { toFun := fun c i => IsLocalRing.residue (B i) ((e c) i)
      map_add' := by
        intro x y
        ext i
        rw [map_add]
        rfl
      map_smul' := by
        intro a x
        ext i
        rw [map_smul]
        simp only [Pi.smul_apply, Algebra.smul_def]
        have hres : algebraMap A (ResidueField (B i)) a =
            IsLocalRing.residue (B i) (algebraMap A (B i) a) :=
          (IsScalarTower.algebraMap_apply A κ (ResidueField (B i)) a).symm.trans
            (IsLocalRing.ResidueField.algebraMap_residue a)
        change IsLocalRing.residue (B i)
            (algebraMap A (B i) a * (e x) i) =
          algebraMap A (ResidueField (B i)) a * IsLocalRing.residue (B i) ((e x) i)
        rw [map_mul, ← hres] }
  have hrhoC_surj : Function.Surjective rhoC := by
    intro y
    choose b hb using fun i : Fin (n + 1) => IsLocalRing.residue_surjective (y i)
    refine ⟨e.symm b, ?_⟩
    ext i
    simp [rhoC, hb]
  have hrhoC_alg : rhoC.comp (Algebra.linearMap A C) = rhoA := by
    apply LinearMap.ext
    intro a
    funext i
    change IsLocalRing.residue (B i) (e (algebraMap A C a) i) = algebraMap A P a i
    rw [e.commutes, Pi.algebraMap_apply]
    rfl
  let Q : Type u := C ⧸ LinearMap.range (Algebra.linearMap A C)
  let T : Type u := P ⧸ LinearMap.range rhoA
  let rhoQ : Q →ₗ[A] T := Submodule.mapQ _ _ rhoC (by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (hrhoC_alg ▸ rfl)⟩)
  have hrhoQ_surj : Function.Surjective rhoQ := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range rhoA) y
    obtain ⟨c, rfl⟩ := hrhoC_surj z
    exact ⟨Submodule.mkQ (LinearMap.range (Algebra.linearMap A C)) c, rfl⟩
  let D := strictHenselizationData A
  let Ash := D.carrier
  let : CommRing Ash := D.commRing
  let : IsLocalRing Ash := D.isLocalRing
  let : Algebra A Ash := D.algebra
  let Ksep := SeparableClosure κ
  let : IsSepClosure κ Ksep := inferInstance
  let : IsHenselization A Ksep Ash := D.isHenselization
  have hbranches :=
    Ring.numberOfGeometricBranches_eq_encard_maximalSpectrum_integralClosure
      A Ksep Ash hA
  let maxEquiv := (MaximalSpectrum.congr e.toRingEquiv).trans
    (maximalSpectrum_pi_equiv_fin (n + 1) B)
  have hmaxCount : (Set.univ : Set (MaximalSpectrum C)).encard = (n + 1 : ℕ∞) := by
    let : Finite (MaximalSpectrum C) := Finite.of_equiv (Fin (n + 1)) maxEquiv.symm
    simpa using (ENat.card_congr maxEquiv)
  have hbranchCount : numberOfGeometricBranchesOfLocalRing A =
      (Set.univ : Set (MaximalSpectrum C)).encard := by
    change numberOfGeometricBranches A Ksep Ash = _
    exact hbranches
  have hdeltaN : Ring.deltaInvariant A = (n : ℕ∞) := by
    rw [hdelta, hbranchCount, hmaxCount]
    rfl
  have hlengthQ : Module.length A Q = n := by
    simpa [Q, Ring.deltaInvariant] using hdeltaN
  have hlengthP : Module.length A P = ∑ i : Fin (n + 1),
      Module.finrank κ (ResidueField (B i)) := by
    rw [Module.length_eq_of_surjective (S := A) (R := κ) (M := P)
      (by simpa [κ] using IsLocalRing.residue_surjective (R := A)), Module.length_pi_of_fintype]
    simp_rw [Module.length_eq_finrank]
    simp
  let resA : A →ₗ[A] κ := Algebra.linearMap A κ
  let fK : κ →ₗ[A] P := (Algebra.linearMap κ P).restrictScalars A
  have hresAsurj : Function.Surjective resA := by
    change Function.Surjective (IsLocalRing.residue A)
    exact IsLocalRing.residue_surjective (R := A)
  have hfactor : rhoA = fK.comp resA := by
    apply LinearMap.ext
    intro a
    funext i
    change algebraMap A P a i = algebraMap κ P (algebraMap A κ a) i
    rw [IsScalarTower.algebraMap_apply A κ P a, Pi.algebraMap_apply]
  have hfKinj : Function.Injective fK := by
    intro x y hxy
    have hlast := congrFun hxy (Fin.last n)
    change algebraMap κ P x (Fin.last n) = algebraMap κ P y (Fin.last n) at hlast
    rw [Pi.algebraMap_apply] at hlast
    exact RingHom.injective (algebraMap κ (ResidueField (B (Fin.last n)))) hlast
  have hker : LinearMap.ker rhoA = LinearMap.ker resA := by
    rw [hfactor]
    ext a
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    exact ⟨fun h => hfKinj (by simpa using h), fun h => by simp [h]⟩
  let eRange : κ ≃ₗ[A] LinearMap.range rhoA :=
    (resA.quotKerEquivOfSurjective hresAsurj).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker.symm).trans rhoA.quotKerEquivRange)
  have hlengthκ : Module.length A κ = 1 := by
    rw [Module.length_eq_of_surjective (S := A) (R := κ) (M := κ) hresAsurj]
    simp
  have hlengthRange : Module.length A (LinearMap.range rhoA) = 1 :=
    eRange.symm.length_eq.trans hlengthκ
  have hlengthExact : Module.length A P =
      Module.length A (LinearMap.range rhoA) + Module.length A T :=
    Module.length_eq_add_of_exact (LinearMap.range rhoA).subtype
      (LinearMap.range rhoA).mkQ (Submodule.subtype_injective _)
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  let d : Fin (n + 1) → ℕ := fun i => Module.finrank κ (ResidueField (B i))
  have hlengthP_eq : ∑ i : Fin (n + 1), (d i : ℕ∞) = 1 + Module.length A T := by
    calc
      _ = Module.length A P := by simpa [d] using hlengthP.symm
      _ = Module.length A (LinearMap.range rhoA) + Module.length A T := hlengthExact
      _ = 1 + Module.length A T := by rw [hlengthRange]
  have hlengthT_le : Module.length A T ≤ n :=
    (Module.length_le_of_surjective rhoQ hrhoQ_surj).trans hlengthQ.le
  have hd_lower (i : Fin (n + 1)) : 1 ≤ d i := by
    have hpos : 0 < d i := Module.finrank_pos
    omega
  have hsum_le : (∑ i : Fin (n + 1), d i) ≤ n + 1 := by
    have hle : (∑ i : Fin (n + 1), d i : ℕ∞) ≤ (n + 1 : ℕ∞) := by
      rw [hlengthP_eq]
      simpa [add_comm] using add_le_add_left hlengthT_le 1
    exact ENat.natCast_le_natCast.mp (by simpa [d, Nat.cast_add] using hle)
  have hsum_ge : n + 1 ≤ ∑ i : Fin (n + 1), d i := by
    calc
      n + 1 = ∑ _i : Fin (n + 1), 1 := by simp
      _ ≤ ∑ i : Fin (n + 1), d i :=
        Finset.sum_le_sum fun i _ => hd_lower i
  have hsum_eq : (∑ i : Fin (n + 1), d i) = n + 1 := by omega
  have hdegree : ∀ i : Fin (n + 1), d i = 1 := by
    intro i
    have hrest : n ≤ ∑ j ∈ Finset.univ.erase i, d j := by
      calc
        n = ∑ j ∈ Finset.univ.erase i, 1 := by simp
        _ ≤ ∑ j ∈ Finset.univ.erase i, d j :=
          Finset.sum_le_sum fun j _ => hd_lower j
    have hsplit : d i + ∑ j ∈ Finset.univ.erase i, d j = n + 1 := by
      rw [Finset.add_sum_erase Finset.univ d (Finset.mem_univ i)]
      exact hsum_eq
    have := hd_lower i
    omega
  have hlengthT : Module.length A T = n := by
    have hsumLen : (1 : ℕ∞) + n = 1 + Module.length A T := by
      rw [← hlengthP_eq, add_comm]
      exact_mod_cast hsum_eq.symm
    exact (WithTop.add_left_cancel ENat.one_ne_top hsumLen).symm
  have hlengthKerQ : Module.length A (LinearMap.ker rhoQ) = 0 := by
    have hseq := Module.length_eq_add_of_exact (LinearMap.ker rhoQ).subtype rhoQ
      (Submodule.subtype_injective _) hrhoQ_surj (LinearMap.exact_subtype_ker_map rhoQ)
    simpa [hlengthQ, hlengthT] using hseq.symm
  have hrhoQ_inj : Function.Injective rhoQ := by
    apply LinearMap.ker_eq_bot.mp
    have : Subsingleton (LinearMap.ker rhoQ) := Module.length_eq_zero_iff.mp hlengthKerQ
    exact (Submodule.eq_bot_iff _).2 fun x hx =>
      congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker rhoQ) 0)
  have hresidueZero_in_A : ∀ c : C, rhoC c = 0 →
      c ∈ LinearMap.range (Algebra.linearMap A C) := by
    intro c hc
    have hqzero : rhoQ ((LinearMap.range (Algebra.linearMap A C)).mkQ c) = rhoQ 0 := by
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, hc]
      simp
    have hq : (LinearMap.range (Algebra.linearMap A C)).mkQ c = 0 := hrhoQ_inj hqzero
    exact (Submodule.Quotient.mk_eq_zero _).mp hq
  let eRes : ∀ i : Fin (n + 1), κ ≃+* ResidueField (B i) := fun i =>
    RingEquiv.ofBijective (algebraMap κ (ResidueField (B i)))
      ((Algebra.finrank_eq_one_iff_bijective_algebraMap).mp (hdegree i))
  let eW : ∀ i : Fin n,
      ResidueField (B i.castSucc) ≃+* ResidueField (B (Fin.last n)) := fun i =>
    (eRes i.castSucc).symm.trans (eRes (Fin.last n))
  let f : A →+* ∀ i : Fin (n + 1), B i :=
    e.toRingEquiv.toRingHom.comp (algebraMap A C)
  have hf_mem (a : A) : f a ∈ IsLocalRing.wedgeSubring B eW := by
    intro i
    have hri := IsLocalRing.ResidueField.algebraMap_residue
      (R := A) (S := B i.castSucc) a
    have hlast := IsLocalRing.ResidueField.algebraMap_residue
      (R := A) (S := B (Fin.last n)) a
    change eW i (IsLocalRing.residue (B i.castSucc) (f a i.castSucc)) =
      IsLocalRing.residue (B (Fin.last n)) (f a (Fin.last n))
    rw [show f a = algebraMap A (∀ i : Fin (n + 1), B i) a by
      ext j
      simp [f, e.commutes]]
    rw [Pi.algebraMap_apply, Pi.algebraMap_apply]
    calc
      eW i (IsLocalRing.residue (B i.castSucc)
          (algebraMap A (B i.castSucc) a)) =
          eW i (algebraMap κ (ResidueField (B i.castSucc)) (IsLocalRing.residue A a)) := by
        rw [hri]
      _ = algebraMap κ (ResidueField (B (Fin.last n))) (IsLocalRing.residue A a) := by
        change (eRes (Fin.last n)) ((eRes i.castSucc).symm
          ((eRes i.castSucc) (IsLocalRing.residue A a))) =
          (eRes (Fin.last n)) (IsLocalRing.residue A a)
        simp
      _ = IsLocalRing.residue (B (Fin.last n))
          (algebraMap A (B (Fin.last n)) a) := hlast
  let fW : A →+* IsLocalRing.wedgeSubring B eW :=
    f.codRestrict _ hf_mem
  have hfW_inj : Function.Injective fW := fun a b hab =>
    algebraMap_integralClosure_injective A (e.toRingEquiv.injective (congrArg Subtype.val hab))
  have hfW_surj : Function.Surjective fW := by
    intro y
    let b : ∀ i : Fin (n + 1), B i := y.1
    let c : C := e.symm b
    let xκ : κ := (eRes (Fin.last n)).symm
      (IsLocalRing.residue (B (Fin.last n)) (b (Fin.last n)))
    obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (R := A) xκ
    have hcommon (i : Fin (n + 1)) :
        (eRes i).symm (IsLocalRing.residue (B i) (b i)) = xκ := by
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have h := congrArg (eRes (Fin.last n)).symm (y.2 j)
        simpa [eW, xκ, RingEquiv.trans_apply] using h
      · simp [xκ]
    have hcoords : rhoC c = rhoA a₀ := by
      ext i
      have hbi := congrArg (eRes i) (hcommon i)
      have hres := IsLocalRing.ResidueField.algebraMap_residue
        (R := A) (S := B i) a₀
      have hbi' : IsLocalRing.residue (B i) (b i) =
          IsLocalRing.residue (B i) (algebraMap A (B i) a₀) := by
        calc
          IsLocalRing.residue (B i) (b i) = eRes i xκ := by
            simpa using hbi
          _ = eRes i (IsLocalRing.residue A a₀) := by rw [ha₀]
          _ = IsLocalRing.residue (B i) (algebraMap A (B i) a₀) := by
            change algebraMap κ (ResidueField (B i)) (IsLocalRing.residue A a₀) = _
            exact hres
      change IsLocalRing.residue (B i) (e c i) = algebraMap A P a₀ i
      rw [show e c = b by simp [c], Pi.algebraMap_apply]
      exact hbi'
    have hmapA : rhoC (Algebra.linearMap A C a₀) = rhoA a₀ :=
      congrArg (fun g => g a₀) hrhoC_alg
    have hzero : rhoC (c - Algebra.linearMap A C a₀) = 0 := by
      rw [map_sub, hcoords, hmapA, sub_self]
    rcases hresidueZero_in_A (c - Algebra.linearMap A C a₀) hzero with
      ⟨a₁, ha₁⟩
    have hc : Algebra.linearMap A C (a₀ + a₁) = c := by
      rw [map_add, ha₁, add_comm, sub_add_cancel]
    refine ⟨a₀ + a₁, ?_⟩
    apply Subtype.ext
    change f (a₀ + a₁) = b
    rw [show f (a₀ + a₁) = e (Algebra.linearMap A C (a₀ + a₁)) by rfl, hc]
    simp [c]
  exact ⟨n, B, hBcomm, fun _ => inferInstance, hBlocal, hDVR, fun _ => inferInstance,
    ⟨eW, ⟨RingEquiv.ofBijective fW ⟨hfW_inj, hfW_surj⟩⟩⟩⟩

end Ring

end
