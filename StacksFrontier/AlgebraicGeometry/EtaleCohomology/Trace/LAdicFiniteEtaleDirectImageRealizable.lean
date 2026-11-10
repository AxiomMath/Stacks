module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IotaRealizableSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseFiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ContinuousModuleScalarAction

/-!
# Frobenius traces and realizability of the direct image along a finite étale morphism

Let `π : X ⟶ Y` be a finite étale morphism of schemes of finite type over a finite field and `F`
an ℓ-adic sheaf on `X` whose levels are locally constant of finite type. At a closed point `v` of
`Y` and for `n ≥ 1`,

  `Tr(π_v ^ n | (π_* F)_v̄ ⊗ ℚ_ℓ) = ∑_{x̄ ↦ v̄, π_v ^ n x̄ = x̄} Tr(π_v ^ n | F_x̄ ⊗ ℚ_ℓ)`,

the sum running over the lifts of `v̄` fixed by `π_v ^ n`
(`Stacks.EtaleCohomology.trace_pow_eq_sum_of_permutedBlocks`); and at such a lift, over the
point `u` of `X`, the term is `Tr(π_u ^ (m + 1) | F_ū ⊗ ℚ_ℓ)` with `#κ(u) ^ (m + 1) = #κ(v) ^ n`
(`Stacks.EtaleCohomology.LAdicSheaf.trace_directImageRationalBlock_eq`), the exponent `m` not
depending on `F`.

Consequently `ι`-realizability (Weil II 1.5, in trace form,
`Stacks.EtaleCohomology.LAdicSheaf.IsIotaRealizable`) passes from `F` to `π_* F`, with witness the
direct image of a witness.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse`:
  the levels of a lisse ℓ-adic sheaf are locally constant of finite type.
* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow`: the trace of
  `π_v ^ n` on `(π_* F)_v̄ ⊗ ℚ_ℓ` is the sum of the traces of its diagonal blocks at the fixed
  lifts.
* `Stacks.EtaleCohomology.LAdicSheaf.trace_directImageRationalBlock_eq`: the diagonal block at a
  fixed lift has the trace of a Frobenius power at the point under it.
* `Stacks.EtaleCohomology.LAdicSheaf.IsIotaRealizable.directImage`: `ι`-realizability passes to
  the direct image along a finite étale morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (π : X ⟶ Y) [IsFinite (B.inclusion.map π)]
  [AlgebraicGeometry.Etale (B.inclusion.map π)] {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- The levels of a lisse ℓ-adic sheaf are locally constant of finite type. -/
public theorem LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse
    (G : LAdicSheaf.{u, u + 1} B X ℓ) (hG : G.IsLisse) (n : ℕ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (SmallEtale.topology B X.1 X.property) (G.level n) := by
  intro U
  obtain ⟨I, V, f, hcov, htriv⟩ :=
    (LAdicSheaf.isFiniteLocallyConstant_level_of_isLisse G hG n).exists_finite_cover U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨E, hE, he⟩ := htriv i
  exact ⟨E, (Stacks.GroupCohomology.moduleCat_isFG_iff_finite (ZMod (ℓ ^ (n + 1))) E).mpr hE, he⟩

section Trace

variable (G : LAdicSheaf.{u, u + 1} B X ℓ)
  (hG : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
    (SmallEtale.topology B X.1 X.property) (G.level n))
  (v : Y.1) [Finite (Y.1.residueField v)]
  [Fintype (GeometricLifts B π (geometricPointAt Y.1 v))]
  [DecidableEq (GeometricLifts B π (geometricPointAt Y.1 v))]

/-- The trace of a Frobenius power on the rational stalk of `π_* G` at `v` is the sum, over the
lifts of `v̄` fixed by that power, of the traces of the diagonal blocks. -/
public theorem LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow (n : ℕ) :
    haveI := isIso_frobeniusPointHom_hom Y.1 v
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B Y ℓ
        (SmallEtale.LAdicSheaf.directImage π G hG) v ‹_› ^ n) =
      ∑ x ∈ Finset.univ.filter
          (fun x => ((geometricLiftsPerm π (frobeniusPointHom Y.1 v)) ^ n) x = x),
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.directImageRationalPr π G hG _ x ∘ₗ
          (LAdicSheaf.rationalStalkFrobenius B Y ℓ
            (SmallEtale.LAdicSheaf.directImage π G hG) v ‹_› ^ n) ∘ₗ
          LAdicSheaf.directImageRationalInc π G hG _ x) :=
  have := isIso_frobeniusPointHom_hom Y.1 v
  trace_pow_eq_sum_of_permutedBlocks (LAdicSheaf.directImageRationalPr π G hG _)
    (LAdicSheaf.directImageRationalInc π G hG _) (LAdicSheaf.directImageRational_sum π G hG _)
    (LAdicSheaf.directImageRational_pr_inc_self π G hG _)
    (fun i j h => LAdicSheaf.directImageRational_pr_inc_of_ne π G hG _ j i h)
    (geometricLiftsPerm π (frobeniusPointHom Y.1 v)) _
    (LAdicSheaf.rationalStalkEnd_directImage_comp_inc_comp_pr π G hG _) n

omit [Fintype (GeometricLifts B π (geometricPointAt Y.1 v))] in
/-- If `π_v ^ (e + 1)` fixes the lift `x̄` over `u`, and `#κ(u) ^ (m + 1) = #κ(v) ^ (e + 1)`, then
the trace of the diagonal block of `π_v ^ (e + 1)` at `x̄` is `Tr(π_u ^ (m + 1) | G_ū ⊗ ℚ_ℓ)`. -/
public theorem LAdicSheaf.trace_directImageRationalBlock_eq
    (x : GeometricLifts B π (geometricPointAt Y.1 v)) (e : ℕ)
    (hx : haveI := isIso_frobeniusPointHom_hom Y.1 v
      ((geometricLiftsPerm π (frobeniusPointHom Y.1 v)) ^ (e + 1)) x = x)
    [Finite (X.1.residueField (geometricLiftPoint B π v x))] (m : ℕ)
    (hm : Nat.card (X.1.residueField (geometricLiftPoint B π v x)) ^ (m + 1) =
      Nat.card (Y.1.residueField v) ^ (e + 1)) :
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.directImageRationalPr π G hG _ x ∘ₗ
        (LAdicSheaf.rationalStalkFrobenius B Y ℓ
          (SmallEtale.LAdicSheaf.directImage π G hG) v ‹_› ^ (e + 1)) ∘ₗ
        LAdicSheaf.directImageRationalInc π G hG _ x) =
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ G
        (geometricLiftPoint B π v x) ‹_› ^ (m + 1)) := by
  have := isIso_frobeniusPointHom_hom Y.1 v
  set a := frobeniusPointHom Y.1 v
  have hfix : (a.iterate e).hom ≫ x.1 = x.1 := by
    have := congrArg Subtype.val hx
    rwa [geometricLiftsPerm_pow_succ_apply] at this
  let b : GeometricPoint.Hom (geometricPointLift (B.inclusion.map π) (geometricPointAt Y.1 v) x)
      (geometricPointLift (B.inclusion.map π) (geometricPointAt Y.1 v) x) :=
    ⟨(a.iterate e).hom, hfix⟩
  change LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.directImageRationalPr π G hG _ x ∘ₗ
      (LAdicSheaf.rationalStalkEnd B Y ℓ (SmallEtale.LAdicSheaf.directImage π G hG) a ^ (e + 1)) ∘ₗ
      LAdicSheaf.directImageRationalInc π G hG _ x) =
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkEnd B X ℓ G
      (frobeniusPointHom X.1 (geometricLiftPoint B π v x)) ^ (m + 1))
  rw [LAdicSheaf.directImageRationalPr_comp_rationalStalkEnd_pow_comp_inc π G hG a x e hx b rfl,
    ← LAdicSheaf.rationalStalkEnd_iterate]
  exact LAdicSheaf.trace_rationalStalkEnd_eq_of_comm B X ℓ G (geometricLiftPointHom B π v x) b _
    (geometricLiftPointHom_comp_frobenius_iterate B π v x m e hm b rfl)

end Trace

/-! ### Realizability -/

variable (F : LAdicSheaf.{u, u + 1} B X ℓ)
  (hF : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
    (SmallEtale.topology B X.1 X.property) (F.level n))
  {k : Type u} [Field k] [Finite k] (fV : Y.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fV]

/-- If `F` is `ι`-realizable, then so is its direct image `π_* F` along the finite étale
morphism `π`, with witness the direct image of a witness for `F`. -/
public theorem LAdicSheaf.IsIotaRealizable.directImage {ι : ℚ_[ℓ] →+* ℂ}
    (hFr : LAdicSheaf.IsIotaRealizable B X ℓ (B.inclusion.map π ≫ fV) F ι) :
    LAdicSheaf.IsIotaRealizable B Y ℓ fV (SmallEtale.LAdicSheaf.directImage π F hF) ι := by
  classical
  obtain ⟨F', hF'l, hreal⟩ := hFr
  have hF' := LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse F' hF'l
  refine ⟨SmallEtale.LAdicSheaf.directImage π F' hF',
    SmallEtale.LAdicSheaf.directImage_isLisse π F' hF', fun v n hn => ?_⟩
  have hv : Finite (Y.1.residueField v.1) := finite_residueField fV v.1 v.2
  have := finite_geometricLifts B π (geometricPointAt Y.1 v.1)
  let : Fintype (GeometricLifts B π (geometricPointAt Y.1 v.1)) := Fintype.ofFinite _
  have := isIso_frobeniusPointHom_hom Y.1 v.1
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  rw [LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow π F hF v.1,
    LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow π F' hF' v.1, ← Finset.sum_add_distrib,
    map_sum]
  have hmem : ∀ x ∈ Finset.univ.filter (fun x =>
      ((geometricLiftsPerm π (frobeniusPointHom Y.1 v.1)) ^ (e + 1)) x = x),
      ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.directImageRationalPr π F hF _ x ∘ₗ
          (LAdicSheaf.rationalStalkFrobenius B Y ℓ
            (SmallEtale.LAdicSheaf.directImage π F hF) v.1 ‹_› ^ (e + 1)) ∘ₗ
          LAdicSheaf.directImageRationalInc π F hF _ x) +
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.directImageRationalPr π F' hF' _ x ∘ₗ
          (LAdicSheaf.rationalStalkFrobenius B Y ℓ
            (SmallEtale.LAdicSheaf.directImage π F' hF') v.1 ‹_› ^ (e + 1)) ∘ₗ
          LAdicSheaf.directImageRationalInc π F' hF' _ x)) ∈ (Complex.ofRealHom).range := by
    intro x hx
    have hx' := (Finset.mem_filter.1 hx).2
    have : Finite (X.1.residueField (geometricLiftPoint B π v.1 x)) :=
      finite_residueField_geometricLiftPoint B π v.1 x
    have hfix : ((frobeniusPointHom Y.1 v.1).iterate e).hom ≫ x.1 = x.1 := by
      have := congrArg Subtype.val hx'
      rwa [geometricLiftsPerm_pow_succ_apply] at this
    obtain ⟨m, hm⟩ := exists_natCard_pow_eq_of_iterate_fixed B π v.1 x e hfix
    have huc : IsClosed ({geometricLiftPoint B π v.1 x} : Set X.1) := by
      have : Finite ((B.inclusion.obj X).residueField (geometricLiftPoint B π v.1 x)) :=
        ‹Finite (X.1.residueField (geometricLiftPoint B π v.1 x))›
      exact isClosed_singleton_of_module_finite_residueField (B.inclusion.map π ≫ fV) _ (by
        let : Algebra k ((B.inclusion.obj X).residueField (geometricLiftPoint B π v.1 x)) :=
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (B.inclusion.map π ≫ fV).appTop ≫
            (B.inclusion.obj X).Γevaluation (geometricLiftPoint B π v.1 x)).hom.toAlgebra
        exact Module.Finite.of_finite)
    rw [LAdicSheaf.trace_directImageRationalBlock_eq π F hF v.1 x e hx' m hm,
      LAdicSheaf.trace_directImageRationalBlock_eq π F' hF' v.1 x e hx' m hm]
    exact hreal ⟨geometricLiftPoint B π v.1 x, huc⟩ (m + 1) (Nat.succ_pos m)
  exact RingHom.mem_range.1 (Subring.sum_mem _ hmem)

end Stacks.EtaleCohomology

end
