module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.BaseChangeDelta
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.RingEquivTransport
public import StacksFrontier.AlgebraicGeometry.Variety.MulticrossBranches.BranchBound
public import StacksFrontier.AlgebraicGeometry.Variety.MulticrossBranches.MulticrossDelta
public import StacksFrontier.AlgebraicGeometry.Variety.MulticrossBranches.WedgeMinimalPrimes
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.DeltaBranchBound
public import StacksFrontier.RingTheory.Branches.Completion
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.Henselian.Criteria
import all StacksFrontier.RingTheory.Branches.Completion

/-!
# Equality in the branch bound characterizes the multicross completion

For a reduced one-dimensional Nagata local algebra over a separably closed field, equality in the
bound of the delta invariant by the number of branches holds exactly when the completed local
algebra is a multicross ring with one branch for each branch of the algebra.

## Main results

* `Ring.adicCompletion_algEquiv_multicross_of_deltaInvariant_eq` produces the multicross
  description of the completion in the equality case.
* `Ring.deltaInvariant_eq_numberOfBranches_sub_one_of_adicCompletion_algEquiv_multicross` is the
  converse: a coefficient-compatible multicross description with the right number of branches
  forces equality.

## References

* [Stacks Project, Tag 0C1V](https://stacks.math.columbia.edu/tag/0C1V)
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.Curves

universe u v

namespace Ring

/-- **If equality holds in the branch bound, the completed local algebra is the multicross
algebra with one power-series factor for each branch.** -/
@[stacks 0C1V "equality case"]
theorem adicCompletion_algEquiv_multicross_of_deltaInvariant_eq
    (k : Type u) (A : Type v) [Field k] [IsSepClosed k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsReduced A] (hNagata : IsNagataRing A)
    (hdim : ringKrullDim A = 1) (_hres : Nonempty (ResidueField A ≃ₐ[k] k))
    (heq : Ring.deltaInvariant A = numberOfBranchesOfLocalRing A - 1) :
    ∃ n : ℕ, numberOfBranchesOfLocalRing A = n ∧
      ∃ e : AdicCompletion (maximalIdeal A) A ≃+* multicross k n,
        e.toRingHom.comp (algebraMap k (AdicCompletion (maximalIdeal A) A)) =
          (RingHom.pi fun _ : Fin n ↦ PowerSeries.C).codRestrict
            (multicross k n) (by
              intro a
              rw [mem_multicross]
              simp) := by
  let : IsNoetherianRing A := hNagata.1
  let Ahat := AdicCompletion (maximalIdeal A) A
  let : IsLocalRing Ahat := AdicCompletion.isLocalRing_of_fg
    (maximalIdeal A).fg_of_isNoetherianRing
  let : IsAdicComplete (maximalIdeal Ahat) Ahat :=
    AdicCompletion.isAdicComplete_of_fg (maximalIdeal A).fg_of_isNoetherianRing
  let : HenselianLocalRing Ahat :=
    henselianLocalRing_of_isAdicComplete_maximalIdeal Ahat
  let hresA := Classical.choice _hres
  let : IsSepClosed (ResidueField A) :=
    IsSepClosed.of_ringEquiv hresA.toRingEquiv
  let eK := residueFieldAlgEquiv_completion A
  let : IsSepClosed (ResidueField Ahat) :=
    IsSepClosed.of_ringEquiv eK.symm.toRingEquiv
  let : StrictlyHenselianLocalRing Ahat := {}
  have hhatNagata : IsNagataRing Ahat :=
    IsLocalRing.isNagataRing_adicCompletion_maximalIdeal
  have hhatReduced : IsReduced Ahat :=
    IsLocalRing.isReduced_adicCompletion_maximalIdeal_of_isNagataRing hNagata
  have hhatDim : ringKrullDim Ahat = 1 :=
    IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal.trans hdim
  let Dh := henselizationData A
  let H := Dh.carrier
  let : CommRing H := Dh.commRing
  let : IsLocalRing H := Dh.isLocalRing
  let : Algebra A H := Dh.algebra
  let : IsHenselization A (ResidueField A) H := Dh.isHenselization
  let DhatH := henselizationData Ahat
  let Hhat := DhatH.carrier
  let : CommRing Hhat := DhatH.commRing
  let : IsLocalRing Hhat := DhatH.isLocalRing
  let : Algebra Ahat Hhat := DhatH.algebra
  let : IsHenselization Ahat (ResidueField Ahat) Hhat := DhatH.isHenselization
  let Dsh := strictHenselizationData A
  let Sh := Dsh.carrier
  let : CommRing Sh := Dsh.commRing
  let : IsLocalRing Sh := Dsh.isLocalRing
  let : Algebra A Sh := Dsh.algebra
  let : IsHenselization A (SeparableClosure (ResidueField A)) Sh := Dsh.isHenselization
  let DhatSh := strictHenselizationData Ahat
  let HhatSh := DhatSh.carrier
  let : CommRing HhatSh := DhatSh.commRing
  let : IsLocalRing HhatSh := DhatSh.isLocalRing
  let : Algebra Ahat HhatSh := DhatSh.algebra
  let : IsHenselization Ahat (SeparableClosure (ResidueField Ahat)) HhatSh :=
    DhatSh.isHenselization
  have hbranches :=
    calc
      numberOfBranchesOfLocalRing A = numberOfGeometricBranchesOfLocalRing A :=
        numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed A
      _ = numberOfGeometricBranchesOfLocalRing Ahat :=
        (numberOfBranches_and_numberOfGeometricBranches_eq_adicCompletion_of_dimension_one
          A H Hhat Sh HhatSh (SeparableClosure (ResidueField A))
          (SeparableClosure (ResidueField Ahat)) hdim).2
      _ = numberOfBranchesOfLocalRing Ahat :=
        (numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed Ahat).symm
  have hdeltaHatEq : Ring.deltaInvariant Ahat =
      numberOfGeometricBranchesOfLocalRing Ahat - 1 :=
    calc
      Ring.deltaInvariant Ahat = Ring.deltaInvariant A :=
        deltaInvariant_adicCompletion_maximalIdeal A hNagata hdim
      _ = numberOfBranchesOfLocalRing A - 1 := heq
      _ = numberOfBranchesOfLocalRing Ahat - 1 := congrArg (· - 1) hbranches
      _ = numberOfGeometricBranchesOfLocalRing Ahat - 1 := by
        rw [numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed Ahat]
  obtain ⟨m, B, hBcomm, hBdom, hBloc, hBDVR, hBstrict, hWedge⟩ :=
    Ring.exists_isWedge_of_deltaInvariant_eq_numberOfGeometricBranches_sub_one
      Ahat hhatNagata hhatDim hdeltaHatEq
  let : ∀ i, CommRing (B i) := hBcomm
  let : ∀ i, IsDomain (B i) := hBdom
  let : ∀ i, IsLocalRing (B i) := hBloc
  let : ∀ i, IsDiscreteValuationRing (B i) := hBDVR
  let : ∀ i, StrictlyHenselianLocalRing (B i) := hBstrict
  rcases hWedge with ⟨eRes, ⟨wEquiv⟩⟩
  let S := wedgeSubring B eRes
  let : IsLocalRing S := wEquiv.isLocalRing
  let : IsHenselization Ahat (ResidueField Ahat) Ahat := isHenselization_self Ahat
  obtain ⟨eH⟩ := exists_algEquiv_of_isHenselization Ahat Hhat Ahat
    (ResidueField Ahat) (ResidueField Ahat) AlgEquiv.refl
  have hcount : numberOfBranchesOfLocalRing A = (m + 1 : ℕ∞) :=
    calc
      numberOfBranchesOfLocalRing A = numberOfBranchesOfLocalRing Ahat := hbranches
      _ = (minimalPrimes Ahat).encard := by
        rw [numberOfBranchesOfLocalRing_eq_encard_minimalPrimes]
        exact encard_minimalPrimes_eq_of_ringEquiv eH.toRingEquiv
      _ = (minimalPrimes S).encard := encard_minimalPrimes_eq_of_ringEquiv wEquiv
      _ = (m + 1 : ℕ∞) := encard_minimalPrimes_wedgeSubring B eRes
  refine ⟨m + 1, hcount, ?_⟩
  let eResKA : ResidueField A ≃ₐ[k] ResidueField Ahat :=
    { eK.toRingEquiv with
      commutes' := fun x => by
        show eK (algebraMap k (ResidueField A) x) =
          algebraMap k (ResidueField Ahat) x
        rw [IsScalarTower.algebraMap_apply k A (ResidueField A) x,
          eK.commutes,
          ← IsScalarTower.algebraMap_apply k A (ResidueField Ahat) x] }
  let hresHat : ResidueField Ahat ≃ₐ[k] k := eResKA.symm.trans hresA
  have hbijHat : Function.Bijective ((residue Ahat).comp (algebraMap k Ahat)) := by
    refine ⟨fun x y h => ?_, fun y => ⟨hresHat y, ?_⟩⟩
    · change algebraMap k (ResidueField Ahat) x =
        algebraMap k (ResidueField Ahat) y at h
      simpa using congrArg hresHat h
    · show algebraMap k (ResidueField Ahat) (hresHat y) = y
      apply hresHat.injective
      rw [hresHat.commutes]
      simp
  let ψ (i : Fin (m + 1)) : Ahat →+* B i :=
    (wedgeProjection B eRes i).comp wEquiv.toRingHom
  have hψsurj (i : Fin (m + 1)) : Function.Surjective (ψ i) :=
    (wedgeProjection_surjective B eRes i).comp wEquiv.surjective
  have (i : Fin (m + 1)) : IsLocalHom (ψ i) := IsLocalHom.of_surjective _ (hψsurj i)
  let (i : Fin (m + 1)) : Algebra k (B i) :=
    ((ψ i).comp (algebraMap k Ahat)).toAlgebra
  have hresMapBijective (i : Fin (m + 1)) :
      Function.Bijective (ResidueField.map (ψ i)) := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := hψsurj i b
    exact ⟨residue Ahat a, by simp [ha]⟩
  have hbijB (i : Fin (m + 1)) :
      Function.Bijective ((residue (B i)).comp (algebraMap k (B i))) := by
    have hcomp : (residue (B i)).comp (algebraMap k (B i)) =
        (ResidueField.map (ψ i)).comp ((residue Ahat).comp (algebraMap k Ahat)) := by
      ext x
      show residue (B i) (ψ i (algebraMap k Ahat x)) =
        ResidueField.map (ψ i) (residue Ahat (algebraMap k Ahat x))
      simp [IsLocalRing.ResidueField.map_residue]
    rw [hcomp]
    exact (hresMapBijective i).comp hbijHat
  let hAhatNCL : IsNoetherianCompleteLocalRing Ahat :=
    ⟨hhatNagata.1, inferInstance, inferInstance⟩
  have hBiComplete (i : Fin (m + 1)) :
      IsAdicComplete (maximalIdeal (B i)) (B i) := by
    let J := RingHom.ker (ψ i)
    let Q := Ahat ⧸ J
    have hQ := quotient_isNoetherianCompleteLocalRing hAhatNCL J (RingHom.ker_ne_top _)
    let : IsLocalRing Q := hQ.isLocal
    let eQ : Q ≃+* B i := RingHom.quotientKerEquivOfSurjective (hψsurj i)
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal eQ]
    exact (IsAdicComplete.congr_ringEquiv (maximalIdeal Q) eQ).mpr hQ.isComplete
  have hregdim (i : Fin (m + 1)) :
      IsRegularLocalRing (B i) ∧ ringKrullDim (B i) = 1 := by
    have hinput : ∃ _ : IsDomain (B i), IsDiscreteValuationRing (B i) :=
      ⟨hBdom i, hBDVR i⟩
    exact ((isDiscreteValuationRing_tfae (B i)).out 1 3).mp hinput
  have hfinrank (i : Fin (m + 1)) :
      Module.finrank (ResidueField (B i)) (CotangentSpace (B i)) = 1 := by
    let : IsRegularLocalRing (B i) := (hregdim i).1
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (B i)).mp (hregdim i).1
    rw [(hregdim i).2] at h
    exact_mod_cast h
  have hseries (i : Fin (m + 1)) :
      Nonempty (B i ≃ₐ[k] PowerSeries k) := by
    let : IsRegularLocalRing (B i) := (hregdim i).1
    let : IsAdicComplete (maximalIdeal (B i)) (B i) := hBiComplete i
    obtain ⟨e⟩ := (IsRegularLocalRing.nonempty_ringEquiv_and_algEquiv_mvPowerSeries.{v, v, u}
      (B i) 1 (hfinrank i)).2 k (hbijB i)
    exact ⟨e.trans (MvPowerSeries.renameEquiv k finOneEquiv)⟩
  let E : ∀ i : Fin (m + 1), B i ≃ₐ[k] PowerSeries k :=
    fun i => Classical.choice (hseries i)
  let κ (i : Fin (m + 1)) : k ≃+* ResidueField (B i) :=
    RingEquiv.ofBijective (algebraMap k (ResidueField (B i))) (by
      rw [IsScalarTower.algebraMap_eq k (B i) (ResidueField (B i))]
      exact hbijB i)
  have hconst (i : Fin (m + 1)) (b : B i) :
      PowerSeries.constantCoeff (E i b) = (κ i).symm (residue (B i) b) := by
    let c := (κ i).symm (residue (B i) b)
    have hres : residue (B i) (b - algebraMap k (B i) c) = 0 := by
      have hc : residue (B i) (algebraMap k (B i) c) = residue (B i) b := by
        show κ i c = residue (B i) b
        exact (κ i).apply_symm_apply _
      rw [map_sub, hc, sub_self]
    have hmem : b - algebraMap k (B i) c ∈ maximalIdeal (B i) :=
      (IsLocalRing.residue_eq_zero_iff _).mp hres
    have hmemE : E i (b - algebraMap k (B i) c) ∈ maximalIdeal (PowerSeries k) := by
      rw [← IsLocalRing.map_ringEquiv_maximalIdeal (E i).toRingEquiv]
      exact Ideal.mem_map_of_mem (E i).toRingHom hmem
    have hzero : PowerSeries.constantCoeff (E i (b - algebraMap k (B i) c)) = 0 := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff] at hmemE
      simpa [isUnit_iff_ne_zero] using hmemE
    have hmap : E i (b - algebraMap k (B i) c) = E i b - PowerSeries.C c := by
      rw [map_sub, (E i).commutes]
      simp
    have hcoeff := congrArg PowerSeries.constantCoeff hmap
    rw [hzero, map_sub, PowerSeries.constantCoeff_C] at hcoeff
    have hsub : PowerSeries.constantCoeff (E i b) - c = 0 := by
      simpa using hcoeff.symm
    exact sub_eq_zero.mp hsub
  let f : S →+* (Fin (m + 1) → PowerSeries k) :=
    RingHom.pi fun i => (E i).toRingHom.comp (wedgeProjection B eRes i)
  have hcompat (i : Fin m) :
      (eRes i).toRingHom.comp (κ i.castSucc).toRingHom =
        (κ (Fin.last m)).toRingHom := by
    ext a
    show eRes i (residue (B i.castSucc) (ψ i.castSucc (algebraMap k Ahat a))) =
      residue (B (Fin.last m)) (ψ (Fin.last m) (algebraMap k Ahat a))
    have hz := (wEquiv (algebraMap k Ahat a)).property
    rw [mem_wedgeSubring] at hz
    simpa [ψ, wedgeProjection] using hz i
  have hcompatEq (i : Fin m) (r : ResidueField (B i.castSucc)) :
      eRes i r = (κ (Fin.last m)) ((κ i.castSucc).symm r) := by
    simpa using congrArg (fun g : k →+* ResidueField (B (Fin.last m)) =>
      g ((κ i.castSucc).symm r)) (hcompat i)
  have hcompatSymm (i : Fin m) (r : ResidueField (B i.castSucc)) :
      (κ (Fin.last m)).symm (eRes i r) = (κ i.castSucc).symm r := by
    rw [hcompatEq]
    exact (κ _).symm_apply_apply _
  have hEqLast (x : S) (i : Fin m) :
      PowerSeries.constantCoeff (E i.castSucc (x.1 i.castSucc)) =
        PowerSeries.constantCoeff (E (Fin.last m) (x.1 (Fin.last m))) := by
    have hx := (mem_wedgeSubring B eRes x.1).mp x.2 i
    calc
      PowerSeries.constantCoeff (E i.castSucc (x.1 i.castSucc)) =
          (κ i.castSucc).symm (residue (B i.castSucc) (x.1 i.castSucc)) :=
        hconst i.castSucc _
      _ = (κ (Fin.last m)).symm (residue (B (Fin.last m)) (x.1 (Fin.last m))) := by
        rw [← hcompatSymm i (residue (B i.castSucc) (x.1 i.castSucc)), hx]
      _ = PowerSeries.constantCoeff (E (Fin.last m) (x.1 (Fin.last m))) :=
        (hconst (Fin.last m) _).symm
  have hfmem (x : S) : f x ∈ multicross k (m + 1) := by
    rw [mem_multicross]
    intro i j
    induction i using Fin.lastCases with
    | last =>
        induction j using Fin.lastCases with
        | last => rfl
        | cast j => exact (hEqLast x j).symm
    | cast i =>
        induction j using Fin.lastCases with
        | last => exact hEqLast x i
        | cast j => exact (hEqLast x i).trans (hEqLast x j).symm
  let fC : S →+* multicross k (m + 1) :=
    f.codRestrict (multicross k (m + 1)) hfmem
  have hfCbij : Function.Bijective fC := by
    constructor
    · intro x y h
      refine Subtype.ext <| funext fun i => ?_
      simpa [fC, f, wedgeProjection] using congrFun (congrArg Subtype.val h) i
    · intro y
      let g : ∀ i : Fin (m + 1), B i := fun i => (E i).symm (y.1 i)
      have hg : g ∈ S := by
        rw [mem_wedgeSubring]
        intro i
        have hy := (mem_multicross y.1).mp y.2 i.castSucc (Fin.last m)
        have hyg (j : Fin (m + 1)) : (κ j).symm (residue (B j) (g j)) =
            PowerSeries.constantCoeff (y.1 j) := by
          simpa [g] using (hconst j ((E j).symm (y.1 j))).symm
        calc
          eRes i (residue (B i.castSucc) (g i.castSucc)) =
              (κ (Fin.last m)) ((κ i.castSucc).symm
                (residue (B i.castSucc) (g i.castSucc))) := hcompatEq i _
          _ = (κ (Fin.last m)) ((κ (Fin.last m)).symm
                (residue (B (Fin.last m)) (g (Fin.last m)))) := by
            rw [hyg, hyg, hy]
          _ = residue (B (Fin.last m)) (g (Fin.last m)) :=
            (κ (Fin.last m)).apply_symm_apply _
      refine ⟨⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      funext i
      simp [fC, f, g, wedgeProjection]
  let fEquiv : S ≃+* multicross k (m + 1) :=
    RingEquiv.ofBijective fC hfCbij
  let e : Ahat ≃+* multicross k (m + 1) := wEquiv.trans fEquiv
  refine ⟨e, RingHom.ext fun a => Subtype.ext <| funext fun i => ?_⟩
  show E i (algebraMap k (B i) a) = PowerSeries.C a
  exact (E i).commutes a

/-- **A coefficient-compatible multicross description of the completion, with one factor for
each branch, forces equality in the delta-invariant bound.** -/
@[stacks 0C1V "converse equality case"]
theorem deltaInvariant_eq_numberOfBranches_sub_one_of_adicCompletion_algEquiv_multicross
    (k : Type u) (A : Type v) [Field k] [IsSepClosed k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsReduced A] (hNagata : IsNagataRing A)
    (hdim : ringKrullDim A = 1) (_hres : Nonempty (ResidueField A ≃ₐ[k] k))
    (n : ℕ) (hn : numberOfBranchesOfLocalRing A = n)
    (e : AdicCompletion (maximalIdeal A) A ≃+* multicross k n)
    (_he : e.toRingHom.comp (algebraMap k (AdicCompletion (maximalIdeal A) A)) =
      (RingHom.pi fun _ : Fin n ↦ PowerSeries.C).codRestrict
        (multicross k n) (by
          intro a
          rw [mem_multicross]
          simp)) :
    Ring.deltaInvariant A = numberOfBranchesOfLocalRing A - 1 :=
  calc
    Ring.deltaInvariant A = Ring.deltaInvariant (AdicCompletion (maximalIdeal A) A) :=
      (deltaInvariant_adicCompletion_maximalIdeal A hNagata hdim).symm
    _ = Ring.deltaInvariant (multicross k n) :=
      Ring.deltaInvariant_eq_of_ringEquiv _ _ e
    _ = (n : ℕ∞) - 1 := deltaInvariant_multicross_eq_sub_one k n
    _ = numberOfBranchesOfLocalRing A - 1 := by rw [hn]

end Ring

end
