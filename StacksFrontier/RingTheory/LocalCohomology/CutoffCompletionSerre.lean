module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
import StacksFrontier.RingTheory.Depth.UnqualifiedDepth
public import StacksFrontier.RingTheory.LocalCohomology.CutoffCompletion
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.Depth.AlgebraMap

/-!
# The local cohomology cutoff after completion

Let `A` be a universally catenary Noetherian local ring, `I` an ideal, and
`M` a finite `A`-module. If every formal fibre of `A` satisfies Serre's
condition `(Sₙ)`, then completion can lower the local cohomology finiteness
cutoff only as far as `n + 1`.

## Main definitions

* `Stacks.LocalCohomology.FormalFibersHavePropertySk`
  says that the formal fibres of a local ring satisfy `(Sₖ)`.

## Main results

* `Stacks.LocalCohomology.min_succ_le_localCohomologyCutoff_adicCompletion` is the lower
  bound for the cutoff of the completed module.

## Implementation notes

The completion of `A` is represented by
`AdicCompletion (IsLocalRing.maximalIdeal A) A`, and the completion of the
finite module `M` by `AdicCompletion (IsLocalRing.maximalIdeal A) M`. A formal
fibre at `p` is the tensor product of the completed ring with the residue field
`κ(p)`. The Noetherian condition is included explicitly in the formal-fibre
predicate because `PropertySkRing` is defined for Noetherian rings.

## References

* [Stacks Project, Tag 0BJT](https://stacks.math.columbia.edu/tag/0BJT)
-/

@[expose] public section

namespace Stacks.LocalCohomology

universe u v

open scoped TensorProduct

private lemma ringDepth_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) : ringDepth A = ringDepth B := by
  rw [ringDepth_eq_depth_maximalIdeal, ringDepth_eq_depth_maximalIdeal,
    Module.depth_self_eq_of_ringEquiv e]

/-- Every formal fibre of the local ring `A` satisfies Serre's condition `(Sₖ)`.
The existence of a Noetherian-ring structure records that the fibre is
Noetherian, as required by the definition of `PropertySkRing`. -/
public def FormalFibersHavePropertySk (A : Type u) [CommRing A] [IsLocalRing A]
    (k : ℕ) : Prop :=
  ∀ (p : Ideal A), ∀ [_hp : p.IsPrime],
    let F := TensorProduct A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A) p.ResidueField
    ∃ hF : IsNoetherianRing F,
      @PropertySkRing F (inferInstance : CommRing F) hF k

private lemma formalFiber_depth_lower_bound
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ) (hformal : FormalFibersHavePropertySk A n)
    (p' : PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let p := PrimeSpectrum.comap (algebraMap A Ahat) p'
    let Ap' := Localization.AtPrime p'.asIdeal
    let Fp := Ap' ⧸ p.asIdeal.map (algebraMap A Ap')
    let mp := (IsLocalRing.maximalIdeal Ap').map
      (Ideal.Quotient.mk (p.asIdeal.map (algebraMap A Ap')))
    min (n : ℕ∞) mp.height ≤ Module.depth Fp mp Fp := by
  classical
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let p := PrimeSpectrum.comap (algebraMap A Ahat) p'
  let K := p.asIdeal.ResidueField
  let F := TensorProduct A Ahat K
  let E : F ≃ₐ[A] p.asIdeal.Fiber Ahat := Algebra.TensorProduct.comm A Ahat K
  let qOver : p.asIdeal.primesOver Ahat := ⟨p'.asIdeal, p'.isPrime, ⟨rfl⟩⟩
  set Q : PrimeSpectrum (p.asIdeal.Fiber Ahat) :=
    PrimeSpectrum.primesOverOrderIsoFiber A Ahat p.asIdeal qOver with hQdef
  let q0 : PrimeSpectrum F := ⟨Q.asIdeal.comap E.toRingHom, Ideal.IsPrime.comap _⟩
  have hq0 : q0.asIdeal = Q.asIdeal.comap E.toRingHom := rfl
  obtain ⟨hNF, hSk⟩ := hformal p.asIdeal
  let : IsNoetherianRing F := hNF
  let : CommRing (Localization.AtPrime q0.asIdeal) := inferInstance
  let : CommRing (Localization.AtPrime Q.asIdeal) := inferInstance
  let eLoc : Localization.AtPrime q0.asIdeal ≃+* Localization.AtPrime Q.asIdeal :=
    Localization.localRingEquiv q0.asIdeal Q.asIdeal E.toRingEquiv (by
      rw [hq0]
      rfl)
  have hsk := hSk q0.asIdeal
  rw [ringDepth_eq_of_ringEquiv (A := Localization.AtPrime q0.asIdeal)
    (B := Localization.AtPrime Q.asIdeal) eLoc, ringDepth_eq_depth_maximalIdeal,
    IsLocalization.AtPrime.ringKrullDim_eq_height q0.asIdeal] at hsk
  have hheight : q0.asIdeal.height = Q.asIdeal.height := by
    rw [hq0]
    exact E.toRingEquiv.height_comap Q.asIdeal
  have hskQ : min (n : ℕ∞) Q.asIdeal.height ≤
      Module.depth (Localization.AtPrime Q.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal))
        (Localization.AtPrime Q.asIdeal) := by
    simpa [hheight] using hsk
  have hQ : Q.asIdeal.comap (Algebra.TensorProduct.includeRight :
      Ahat →ₐ[A] p.asIdeal.Fiber Ahat) = p'.asIdeal := by
    rw [hQdef, ← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply,
      OrderIso.symm_apply_apply]
  let e2 : Localization.AtPrime (Q.asIdeal.comap (Algebra.TensorProduct.includeRight :
    Ahat →ₐ[A] p.asIdeal.Fiber Ahat)) ≃ₐ[Ahat] Localization.AtPrime p'.asIdeal :=
    Localization.localAlgEquiv _ p'.asIdeal (AlgEquiv.refl : Ahat ≃ₐ[Ahat] Ahat)
      (by rw [hQ]; exact (Ideal.comap_id p'.asIdeal).symm)
  let q := Q.asIdeal.comap (Algebra.TensorProduct.includeRight :
      Ahat →ₐ[A] p.asIdeal.Fiber Ahat)
  let Lq := Localization.AtPrime q
  have hmapE : Ideal.map e2.toRingHom
        (Ideal.map (algebraMap Ahat Lq)
          (Ideal.map (algebraMap A Ahat) p.asIdeal)) =
      p.asIdeal.map (algebraMap A (Localization.AtPrime p'.asIdeal)) := by
    rw [Ideal.map_map, Ideal.map_map]
    have hcomp : e2.toRingHom.comp (algebraMap Ahat Lq) =
        algebraMap Ahat (Localization.AtPrime p'.asIdeal) := by
      ext x
      exact e2.commutes x
    rw [hcomp, ← IsScalarTower.algebraMap_eq A Ahat (Localization.AtPrime p'.asIdeal)]
  let Efp : Localization.AtPrime Q.asIdeal ≃+*
      (Localization.AtPrime p'.asIdeal ⧸
        p.asIdeal.map (algebraMap A (Localization.AtPrime p'.asIdeal))) :=
    (Ideal.Fiber.algEquivAux₂ p.asIdeal Q.asIdeal).toRingEquiv.trans
      (Ideal.quotientEquiv _ _ e2.toRingEquiv hmapE.symm)
  let Ap' := Localization.AtPrime p'.asIdeal
  let J := p.asIdeal.map (algebraMap A Ap')
  let Fp := Ap' ⧸ J
  let mp := (IsLocalRing.maximalIdeal Ap').map (Ideal.Quotient.mk J)
  have hple : p.asIdeal.map (algebraMap A Ahat) ≤ p'.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    rfl
  have hJle : J ≤ IsLocalRing.maximalIdeal Ap' := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    calc
      J = Ideal.map (algebraMap Ahat Ap') (Ideal.map (algebraMap A Ahat) p.asIdeal) := by
        rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A Ahat Ap']
      _ ≤ Ideal.map (algebraMap Ahat Ap') p'.asIdeal := Ideal.map_mono hple
  have hJne : J ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal Ap').ne_top hJle
  let : Nontrivial Fp := Ideal.Quotient.nontrivial_iff.mpr hJne
  let : IsLocalRing Fp := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  have hmax : (IsLocalRing.maximalIdeal Ap').map (Ideal.Quotient.mk J) =
      IsLocalRing.maximalIdeal Fp :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hQloc : Q.asIdeal.height =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal)).height := by
    have hunder : (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal)).under
        (p.asIdeal.Fiber Ahat) = Q.asIdeal :=
      IsLocalization.AtPrime.under_maximalIdeal
        (R := p.asIdeal.Fiber Ahat) (S := Localization.AtPrime Q.asIdeal)
        (I := Q.asIdeal)
    exact (congrArg Ideal.height hunder).symm.trans
      (IsLocalization.height_under (R := p.asIdeal.Fiber Ahat)
        Q.asIdeal.primeCompl (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal)))
  have hEfpmax : Ideal.map Efp.toRingHom
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal)) =
        IsLocalRing.maximalIdeal Fp := IsLocalRing.map_ringEquiv_maximalIdeal Efp
  have hEfpheight :
      (Ideal.map Efp.toRingHom
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal))).height =
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal)).height :=
    RingEquiv.height_map Efp
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal))
  have hdim : Q.asIdeal.height = mp.height := by
    rw [hQloc, ← hEfpheight, hEfpmax, ← hmax]
  have hdepth : Module.depth (Localization.AtPrime Q.asIdeal)
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal))
      (Localization.AtPrime Q.asIdeal) = Module.depth Fp mp Fp := by
    calc
      _ = Module.depth Fp (IsLocalRing.maximalIdeal Fp) Fp :=
        Module.depth_self_eq_of_ringEquiv Efp
      _ = Module.depth Fp mp Fp := by rw [← hmax]
  simpa only [hdim, hdepth] using hskQ

private lemma depth_localized_adicCompletion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : Ideal A) [p.IsPrime]
    (p' : Ideal (AdicCompletion I A)) [p'.IsPrime] [p'.LiesOver p] :
    Module.depth (Localization.AtPrime p')
        (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
        (LocalizedModule p'.primeCompl (AdicCompletion I M)) =
      Module.depth (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (LocalizedModule p.primeCompl M) +
        Module.depth (Localization.AtPrime p')
          (IsLocalRing.maximalIdeal (Localization.AtPrime p'))
          ((Localization.AtPrime p') ⧸
            p.map (algebraMap A (Localization.AtPrime p'))) := by
  let := Localization.AtPrime.algebraOfLiesOver p p'
  let B := AdicCompletion I A
  let R := Localization.AtPrime p
  let S := Localization.AtPrime p'
  let N := LocalizedModule p.primeCompl M
  let N' := LocalizedModule p'.primeCompl (AdicCompletion I M)
  have : IsNoetherianRing B := inferInstance
  have : IsNoetherianRing S := inferInstance
  have : Module.Flat A B := AdicCompletion.flat_of_isNoetherian I
  have : Module.Flat A S := Module.Flat.trans A B S
  have : Module.Flat R S :=
    (Module.flat_iff_of_isLocalization R p.primeCompl S).mpr inferInstance
  have hcompletion : IsBaseChange B (AdicCompletion.of I M) := by
    let : Small.{u} M := Module.Finite.small A M
    let M₀ := Shrink.{u} M
    let eM : M₀ ≃ₗ[A] M := Shrink.linearEquiv A M
    have hsmall : IsBaseChange B (AdicCompletion.of I M₀) :=
      IsBaseChange.of_equiv (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M₀)
        (by intro x
            change (AdicCompletion.ofTensorProduct I M₀) (1 ⊗ₜ[A] x) = _
            rw [AdicCompletion.ofTensorProduct_tmul, one_smul])
    exact (IsBaseChange.iff_of_equiv_comm eM (AdicCompletion.congr I eM)
      (LinearMap.ext fun x => (AdicCompletion.map_of I eM.toLinearMap x).symm)).mp hsmall
  have hlocalization : IsBaseChange S
      (LocalizedModule.mkLinearMap p'.primeCompl (AdicCompletion I M)) :=
    IsLocalizedModule.isBaseChange p'.primeCompl S _
  have hA : IsBaseChange S
      (((LocalizedModule.mkLinearMap p'.primeCompl (AdicCompletion I M)).restrictScalars A).comp
        (AdicCompletion.of I M)) := hcompletion.comp hlocalization
  have hR : IsBaseChange R (LocalizedModule.mkLinearMap p.primeCompl M) :=
    IsLocalizedModule.isBaseChange p.primeCompl R _
  let e : S ⊗[R] N ≃ₗ[S] N' :=
    (hR.equiv.symm.baseChange R S) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S M ≪≫ₗ hA.equiv
  have : Module.Finite R N := inferInstance
  have : Module.Finite S S := inferInstance
  have h' : Module.depth S (IsLocalRing.maximalIdeal S) N' =
      Module.depth R (IsLocalRing.maximalIdeal R) N +
        Module.depth S (IsLocalRing.maximalIdeal S)
          (S ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
            (⊤ : Submodule S S))) := by
    rw [← Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal S) e]
    exact Module.depth_tensorProduct_of_flat (R := R) (S := S) (M := N) (N := S)
  have hid : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
      p.map (algebraMap A S) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p R, Ideal.map_map]
    exact congrArg (fun f => p.map f) (IsScalarTower.algebraMap_eq A R S).symm
  have hquot : p.map (algebraMap A S) • (⊤ : Submodule S S) =
      (p.map (algebraMap A S) : Submodule S S) :=
    (Ideal.smul_eq_mul _ _).trans (Ideal.mul_top _)
  rwa [hid, hquot] at h'

private lemma completed_module_depth_formula
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p' : PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let p := PrimeSpectrum.comap (algebraMap A Ahat) p'
    let Ap' := Localization.AtPrime p'.asIdeal
    let Fp := Ap' ⧸ p.asIdeal.map (algebraMap A Ap')
    let mp := (IsLocalRing.maximalIdeal Ap').map
      (Ideal.Quotient.mk (p.asIdeal.map (algebraMap A Ap')))
    Module.depth Ap' (IsLocalRing.maximalIdeal Ap')
        (LocalizedModule p'.asIdeal.primeCompl
          (AdicCompletion (IsLocalRing.maximalIdeal A) M)) =
      Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) + Module.depth Fp mp Fp := by
  classical
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let p := PrimeSpectrum.comap (algebraMap A Ahat) p'
  let Ap' := Localization.AtPrime p'.asIdeal
  let J := p.asIdeal.map (algebraMap A Ap')
  let Fp := Ap' ⧸ J
  let mp := (IsLocalRing.maximalIdeal Ap').map (Ideal.Quotient.mk J)
  let : p.asIdeal.IsPrime := p.isPrime
  have hsurj : Function.Surjective (algebraMap Ap' Fp) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  have hdepthmap : Module.depth Ap' (IsLocalRing.maximalIdeal Ap') Fp =
      Module.depth Fp mp Fp := by
    rw [Module.depth_eq_depth_map_algebraMap hsurj]
    change Module.depth Fp
      ((IsLocalRing.maximalIdeal Ap').map (algebraMap Ap' Fp)) Fp = _
    rw [show (IsLocalRing.maximalIdeal Ap').map (algebraMap Ap' Fp) = mp by
      rw [Ideal.Quotient.algebraMap_eq]]
  have h' : Module.depth Ap' (IsLocalRing.maximalIdeal Ap')
      (LocalizedModule p'.asIdeal.primeCompl
        (AdicCompletion (IsLocalRing.maximalIdeal A) M)) =
      Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) +
        Module.depth Ap' (IsLocalRing.maximalIdeal Ap') Fp := by
    simpa only [Ap', Fp, J] using depth_localized_adicCompletion (A := A)
      (I := IsLocalRing.maximalIdeal A) (M := M) p.asIdeal p'.asIdeal
  rwa [hdepthmap] at h'

/-- If the formal fibres of a universally catenary Noetherian local ring
satisfy `(Sₙ)`, the cutoff after completion is at least the minimum of the
original cutoff and `n + 1`. -/
@[stacks 0BJT "cutoff_completion_lower_bound_of_serre"]
public lemma min_succ_le_localCohomologyCutoff_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (n : ℕ) (hcatenary : Ring.IsUniversallyCatenary A)
    (hformal : FormalFibersHavePropertySk A n) :
    min ((n + 1 : ℕ) : ℕ∞) (localCohomologyCutoff A I M) ≤
      localCohomologyCutoff
        (AdicCompletion (IsLocalRing.maximalIdeal A) A)
        (I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
        (AdicCompletion (IsLocalRing.maximalIdeal A) M) := by
  classical
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  rw [le_localCohomologyCutoff_iff]
  intro p' q' hp' hq' hpq'
  let p := PrimeSpectrum.comap (algebraMap A Ahat) p'
  let q := PrimeSpectrum.comap (algebraMap A Ahat) q'
  let Ap := Localization.AtPrime p.asIdeal
  let Aq := Localization.AtPrime q.asIdeal
  let Ap' := Localization.AtPrime p'.asIdeal
  let Aq' := Localization.AtPrime q'.asIdeal
  let Fp := Ap' ⧸ p.asIdeal.map (algebraMap A Ap')
  let Fq := Aq' ⧸ q.asIdeal.map (algebraMap A Aq')
  let mp := (IsLocalRing.maximalIdeal Ap').map
    (Ideal.Quotient.mk (p.asIdeal.map (algebraMap A Ap')))
  let mq := (IsLocalRing.maximalIdeal Aq').map
    (Ideal.Quotient.mk (q.asIdeal.map (algebraMap A Aq')))
  have hcut : localCohomologyCutoff A I M ≤
      Module.depth Ap (IsLocalRing.maximalIdeal Ap)
          (LocalizedModule p.asIdeal.primeCompl M) +
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height :=
    localCohomologyCutoff_le A I M p q (fun h => hp' (Ideal.map_le_iff_le_comap.mpr h))
      (Ideal.map_le_iff_le_comap.mp hq') (Ideal.comap_mono hpq')
  have hdepthTensor :
      Module.depth Ap' (IsLocalRing.maximalIdeal Ap')
          (LocalizedModule p'.asIdeal.primeCompl (Ahat ⊗[A] M)) =
        Module.depth Ap' (IsLocalRing.maximalIdeal Ap')
          (LocalizedModule p'.asIdeal.primeCompl
            (AdicCompletion (IsLocalRing.maximalIdeal A) M)) :=
    Module.depth_eq_depth_of_linearEquiv _ (localizedEquiv p'.asIdeal.primeCompl
      (FormalGlueing.adicCompletionTensorEquiv A (IsLocalRing.maximalIdeal A) M))
  have hpair :
      Module.depth Ap' (IsLocalRing.maximalIdeal Ap')
          (LocalizedModule p'.asIdeal.primeCompl
            (AdicCompletion (IsLocalRing.maximalIdeal A) M)) +
        (q'.asIdeal.map (Ideal.Quotient.mk p'.asIdeal)).height =
      Module.depth Ap (IsLocalRing.maximalIdeal Ap)
          (LocalizedModule p.asIdeal.primeCompl M) +
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height +
        mq.height + Module.depth Fp mp Fp - mp.height := by
    rw [← hdepthTensor]
    simpa only [p, q, Ap, Aq, Ap', Aq', Fp, Fq, mp, mq,
      PrimeSpectrum.asIdeal] using
        (pairwiseCutoffValue_eq_under_completion A hcatenary I M
          p' q' hp' hq' hpq')
  have hdepth : Module.depth Ap' (IsLocalRing.maximalIdeal Ap')
      (LocalizedModule p'.asIdeal.primeCompl
        (AdicCompletion (IsLocalRing.maximalIdeal A) M)) =
      Module.depth Ap (IsLocalRing.maximalIdeal Ap)
          (LocalizedModule p.asIdeal.primeCompl M) + Module.depth Fp mp Fp := by
    simpa only [p, Ap, Ap', Fp, mp, PrimeSpectrum.asIdeal] using
      completed_module_depth_formula A M p'
  have hdepthSerre : min (n : ℕ∞) mp.height ≤ Module.depth Fp mp Fp := by
    simpa only [p, Ap', Fp, mp, PrimeSpectrum.asIdeal] using
      formalFiber_depth_lower_bound A n hformal p'
  have hrel : 1 ≤ (q'.asIdeal.map (Ideal.Quotient.mk p'.asIdeal)).height := by
    let P := q'.asIdeal.map (Ideal.Quotient.mk p'.asIdeal)
    have : P.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq'
    have hne : p'.asIdeal ≠ q'.asIdeal := fun h => hp' (by rwa [h])
    have hP : P ≠ ⊥ := fun h => hne (le_antisymm hpq' (by
      simpa only [Ideal.mk_ker] using (Ideal.map_eq_bot_iff_le_ker _).mp h))
    have hstrict : (⊥ : Ideal (Ahat ⧸ p'.asIdeal)).height < P.height :=
      Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne bot_le hP.symm)
    have hpos : 0 < P.height := by simpa only [Ideal.height_bot] using hstrict
    exact Order.one_le_iff_ne_zero.2 hpos.ne'
  have key : ∀ {c t x y d m m' h : ℕ∞}, c ≤ x + y → min (n : ℕ∞) m ≤ d → 1 ≤ h →
      t = x + d → t + h = x + y + m' + d - m → min ((n + 1 : ℕ) : ℕ∞) c ≤ t + h := by
    intro c t x y d m m' h hc hd hh ht hpair
    subst ht
    by_cases hm : m ≤ n
    · refine (min_le_right _ _).trans (hc.trans ?_)
      have hmd : m ≤ m' + d := ((min_eq_right hm).symm.trans_le hd).trans le_add_self
      rw [hpair, add_assoc (x + y)]
      exact ((ENat.addLECancellable_of_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top n) hm)
        ).le_tsub_iff_right (hmd.trans le_add_self)).2 (add_le_add le_rfl hmd)
    · refine (min_le_left _ _).trans ?_
      rw [Nat.cast_add, Nat.cast_one, add_assoc x]
      exact (add_le_add ((min_eq_left (not_le.mp hm).le).symm.trans_le hd) hh).trans le_add_self
  exact key hcut hdepthSerre hrel hdepth hpair

end Stacks.LocalCohomology

end
