module

public import StacksFrontier.Deformation.Formal.MinimalVersal.Basic

/-!
# The projection of the descended levels onto the stage tower

The base of the `n`-th level of the descended formal object projects onto the `n`-th term of the
stage tower, and the `n`-th component of the morphism to the original formal object lies over that
projection followed by the inclusion of the tower. This identifies the image subalgebra of each
component, which is what the minimality statement of Stacks 06T2 records.

## Main definitions

* `Deformation.stageBaseTowerFormalLevelProjection`: the projection from the base of the `n`-th
  level of `stageBaseTowerFormalObject` onto the `n`-th term of the tower.

## Main results

* `Deformation.stageBaseTowerFormalObjectApp_projection_fac`: the image of the `n`-th component of
  the morphism out of `stageBaseTowerFormalObject` is the projection onto the `n`-th term of the
  tower followed by its inclusion.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- The projection from the base of the `n`-th level of `stageBaseTowerFormalObject` onto the
`n`-th term of the tower. -/
noncomputable def stageBaseTowerFormalLevelProjection
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    p.obj ((stageBaseTowerFormalObject hp hS1 ξ hbound).level n) ⟶
      stageBaseTower hp hS1 ξ n := by
  let F := stageBaseTowerFormalObject hp hS1 ξ hbound
  let R := F.base
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  let S := inverseLimit A f
  letI : IsLocalRing S :=
    (Classical.choose (stageBaseTower_cotangent_bounded hp hS1 ξ hbound)).isLocal
  let π := inverseLimitProj A f n
  have hπ : Function.Surjective π := stageBaseTowerProjection_surjective hp hS1 ξ n
  have hmax : (maximalIdeal S).map π.toRingHom = maximalIdeal (A n) :=
    IsLocalRing.map_maximalIdeal_of_surjective π.toRingHom hπ
  have hpow : maximalIdeal S ^ (n + 1) ≤ RingHom.ker π := by
    apply (Ideal.map_eq_bot_iff_le_ker _).mp
    change Ideal.map π.toRingHom (maximalIdeal S ^ (n + 1)) = ⊥
    rw [Ideal.map_pow, hmax, stageBaseTower_maximalIdeal_pow_eq_bot hp hS1 ξ n]
  have hI : ∀ x : S, x ∈ maximalIdeal S ^ (n + 1) → (π : S →+* A n) x = 0 :=
    fun _ hx => RingHom.mem_ker.mp (hpow hx)
  let q : AdicTruncation.obj R n →ₐ[Λ] A n := by
    change (S ⧸ maximalIdeal S ^ (n + 1)) →ₐ[Λ] A n
    exact Ideal.Quotient.liftₐ (maximalIdeal S ^ (n + 1)) π hI
  have hcomp : q.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = π := by
    change (Ideal.Quotient.liftₐ (maximalIdeal S ^ (n + 1)) π hI).comp
      (Ideal.Quotient.mkₐ Λ (maximalIdeal S ^ (n + 1))) = π
    exact Ideal.Quotient.liftₐ_comp _ _ hI
  have hqmk (x : S) :
      q (Ideal.Quotient.mk (AdicTruncation.ideal R n) x : AdicTruncation.obj R n) = π x :=
    DFunLike.congr_fun hcomp x
  have hq : Function.Surjective q.toRingHom := fun y =>
    let ⟨x, hx⟩ := hπ y
    ⟨Ideal.Quotient.mk _ x, (hqmk x).trans hx⟩
  let q₀ : AdicTruncation.obj R n ⟶ A n :=
    { hom := q
      isLocal := IsLocalHom.of_surjective q.toRingHom hq
      residue_comm := by
        intro x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [hqmk r]
        exact (stageBaseTowerProjection_residue hp hS1 ξ hbound r n).trans
          (AdicTruncation.residueEquiv_residue_mk R n r).symm }
  exact eqToHom (F.level_eq n) ≫ q₀

/-- Transporting an element along `eqToHom h` and then back along `eqToHom h.symm` is the
identity. -/
private theorem eqToHom_symm_hom_apply {X Y : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : X = Y)
    (z : X) : (eqToHom h.symm).hom ((eqToHom h).hom z) = z := by
  subst h
  rfl

/-- The image of the `n`-th component of the morphism out of `stageBaseTowerFormalObject` is the
projection onto the `n`-th term of the tower followed by its inclusion. -/
theorem stageBaseTowerFormalObjectApp_projection_fac
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    stageBaseTowerFormalLevelProjection hp hS1 ξ hbound n ≫
        stageBaseTowerInclusion hp hS1 ξ n =
      p.map (stageBaseTowerFormalObjectApp hp hS1 ξ hbound n) := by
  classical
  let F := stageBaseTowerFormalObject hp hS1 ξ hbound
  let R := stageBaseTowerCompleteLocal hp hS1 ξ hbound
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  let S := inverseLimit A f
  let : IsLocalRing S := R.completeLocal.isLocal
  let π := inverseLimitProj A f n
  let β := (AdicTruncation.functor n).map (stageBaseTowerBaseHom hp hS1 ξ hbound)
  let q := stageBaseTowerFormalLevelProjection hp hS1 ξ hbound n
  let i := stageBaseTowerInclusion hp hS1 ξ n
  have hbaseEq : F.base = R := rfl
  let hbaseObjEq := congrArg (fun B : CompleteLocalAlgCat.{u, v, w} Λ k =>
    AdicTruncation.obj B n) hbaseEq
  let e0 := eqToHom (F.level_eq n)
  let eBase := eqToHom hbaseObjEq
  let eBaseInv := eqToHom hbaseObjEq.symm
  let hsrcR := (F.level_eq n).trans hbaseObjEq
  let eR := e0 ≫ eBase
  let eRinv := eBaseInv ≫ eqToHom (F.level_eq n).symm
  refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun z => ?_)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (eR.hom z)
  let rS : S := r
  have hbase := congrArg (fun g : R →ₐ[Λ] AdicTruncation.obj ξ.base n => g r)
    (stageBaseTowerBaseHom_quotient hp hS1 ξ hbound n)
  have hq : q.hom z = π rS := by
    have hcast : eBaseInv.hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R n) r) =
        Ideal.Quotient.mk (AdicTruncation.ideal F.base n) r := by
      cases hbaseEq
      rfl
    have he0 : e0.hom z = eBaseInv.hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R n) r) := by
      rw [hr]
      exact (eqToHom_symm_hom_apply hbaseObjEq (e0.hom z)).symm
    dsimp [q, stageBaseTowerFormalLevelProjection]
    rw [he0, hcast]
    change Ideal.Quotient.lift (maximalIdeal S ^ (n + 1))
        (π : S →+* A n) _ (Ideal.Quotient.mk (maximalIdeal S ^ (n + 1)) rS) =
      π.toRingHom rS
    rw [Ideal.Quotient.lift_mk]
    rfl
  have happ :
      (eqToHom (ξ.level_eq n)).hom ((p.map (stageBaseTowerFormalObjectApp
        hp hS1 ξ hbound n)).hom z) =
        β.hom (Ideal.Quotient.mk (AdicTruncation.ideal R n) r) := by
    let := stageBaseTowerFormalObjectApp_lift hp hS1 ξ hbound n
    have hsrc : IsHomLift.domain_eq p β
        (stageBaseTowerFormalObjectApp hp hS1 ξ hbound n) = hsrcR :=
      rfl
    have hfac := IsHomLift.fac p β
      (stageBaseTowerFormalObjectApp hp hS1 ξ hbound n)
    rw [hsrc] at hfac
    have hv := congrArg (fun g => g.hom (eR.hom z)) hfac
    have hcancel : eRinv.hom (eR.hom z) = z := by
      change (eqToHom (F.level_eq n).symm).hom (eBaseInv.hom (eBase.hom (e0.hom z))) = z
      rw [eqToHom_symm_hom_apply hbaseObjEq, eqToHom_symm_hom_apply (F.level_eq n)]
    have happ0 : (eqToHom (ξ.level_eq n)).hom
        ((p.map (stageBaseTowerFormalObjectApp hp hS1 ξ hbound n)).hom z) =
        β.hom (eR.hom z) := by
      have hv' : β.hom (eR.hom z) = (eqToHom (ξ.level_eq n)).hom
          ((p.map (stageBaseTowerFormalObjectApp hp hS1 ξ hbound n)).hom
            (eRinv.hom (eR.hom z))) :=
        hv
      rw [hcancel] at hv'
      exact hv'.symm
    exact happ0.trans (congrArg β.hom hr).symm
  have hbase' : (eqToHom (ξ.level_eq n)).hom (i.hom (π rS)) =
      β.hom (Ideal.Quotient.mk (AdicTruncation.ideal R n) r) := by
    have hcoord : (eqToHom (ξ.level_eq n)).hom (i.hom (π rS)) =
        (formalInverseLimitCoordinate ξ n) (stageBaseInverseLimitMap hp hS1 ξ r) := by
      change (eqToHom (ξ.level_eq n)).hom
          ((stageBaseTowerInclusion hp hS1 ξ n).hom
            (inverseLimitProj (stageBaseTower hp hS1 ξ)
              (stageBaseTowerTransition hp hS1 ξ) n r)) = _
      rfl
    have hquot : β.hom (Ideal.Quotient.mk (AdicTruncation.ideal R n) r) =
        ((Ideal.Quotient.mkₐ Λ (maximalIdeal ξ.base ^ (n + 1))).comp
          (stageBaseTowerBaseHom hp hS1 ξ hbound).hom) r := by
      simpa [β] using adicTruncationMap_mk
        (stageBaseTowerBaseHom hp hS1 ξ hbound) n r
    exact hcoord.trans (hbase.symm.trans hquot.symm)
  have hEq : (eqToHom (ξ.level_eq n)).hom (i.hom (π rS)) =
      (eqToHom (ξ.level_eq n)).hom
        ((p.map (stageBaseTowerFormalObjectApp hp hS1 ξ hbound n)).hom z) :=
    hbase'.trans happ.symm
  rw [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply, hq]
  exact artinianHom_injective_of_isIso (eqToHom (ξ.level_eq n)) hEq

end Deformation

end
