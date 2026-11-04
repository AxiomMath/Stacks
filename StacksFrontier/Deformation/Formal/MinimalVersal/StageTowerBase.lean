module

public import StacksFrontier.Deformation.Formal.MinimalVersal.StageTower

/-!
# The inverse limit of the stage tower inside the base

The inverse limit of the stage tower maps to the base of the formal object: the bases of the
levels have the adic truncations of that base as inverse limit, and the inclusions of the tower
are compatible with the transitions. The resulting map is injective, so the inverse limit is a
subalgebra of the base.

## Main definitions

* `Deformation.stageBaseInverseLimitMap`: the map from the inverse limit of `stageBaseTower` to
  the inverse limit of the bases of the levels, induced by the inclusions.
* `Deformation.formalInverseLimitCoordinate`: the `n`-th coordinate of the inverse limit of the
  bases of the levels of a formal object, valued in the `n`-th adic truncation of its base.
* `Deformation.formalLimitQuotientMap`: the map from the base of a formal object to the base of
  its `n`-th level.
* `Deformation.formalInverseLimitQuotientSystem`: the map from the base of a formal object into
  the inverse limit of the bases of its levels.
* `Deformation.formalInverseLimitToBase`: the inverse of `formalInverseLimitQuotientSystem`: the
  identification of the inverse limit of the bases of the levels with the base of the formal
  object.
* `Deformation.stageBaseTowerBaseMap`: the map from the inverse limit of `stageBaseTower` to the
  base of the formal object.

## Main results

* `Deformation.formalInverseLimitCoordinate_fac`: the coordinates of the inverse limit of the
  bases of the levels are compatible with the truncation transitions.
* `Deformation.formalLimitQuotientMap_fac`: `formalLimitQuotientMap` is the projection onto the
  `n`-th adic truncation followed by the identification of that truncation with the base of the
  `n`-th level.
* `Deformation.formalLimitQuotientMap_compatible`: the maps `formalLimitQuotientMap` are
  compatible with the transition maps of the levels.
* `Deformation.formalInverseLimitQuotientSystem_compatible`: `formalInverseLimitQuotientSystem` is
  compatible with the coordinates of the inverse limit.
* `Deformation.formalInverseLimitToBase_quotient`: `formalInverseLimitToBase` is compatible with
  the projections onto the adic truncations.
* `Deformation.stageBaseTowerBaseMap_quotient`: `stageBaseTowerBaseMap` is compatible with the
  projections onto the adic truncations.
* `Deformation.stageBaseTowerBaseMap_injective`: `stageBaseTowerBaseMap` is injective, so the
  inverse limit of `stageBaseTower` is a subalgebra of the base of the formal object.

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


section
variable [IsNoetherianRing Λ] [Module.Finite Λ k]
/-- The map from the inverse limit of `stageBaseTower` to the inverse limit of the bases of the
levels, induced by the inclusions. -/
noncomputable def stageBaseInverseLimitMap
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) :
    inverseLimit (stageBaseTower hp hS1 ξ)
        (stageBaseTowerTransition hp hS1 ξ) →ₐ[Λ]
      inverseLimit (fun n => p.obj (ξ.level n))
        (fun n => p.map (ξ.transition n)) := by
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  let B : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k := fun n => p.obj (ξ.level n)
  let g : ∀ n, B (n + 1) ⟶ B n := fun n => p.map (ξ.transition n)
  let i : ∀ n, A n ⟶ B n := stageBaseTowerInclusion hp hS1 ξ
  refine
    { toFun := fun x => ⟨fun n => (i n).hom (x.1 n), ?_⟩
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · intro n
    have hfac := congrArg (fun q : A (n + 1) ⟶ B n => q.hom (x.1 (n + 1)))
      (stageBaseTowerInclusion_fac hp hS1 ξ n)
    rw [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply,
      ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply] at hfac
    change (g n).hom ((i (n + 1)).hom (x.1 (n + 1))) =
      (i n).hom (x.1 n)
    rw [← hfac]
    rw [x.2 n]
  · apply Subtype.ext
    funext n
    simp
  · intro x y
    apply Subtype.ext
    funext n
    simp
  · apply Subtype.ext
    funext n
    simp
  · intro x y
    apply Subtype.ext
    funext n
    simp
  · intro r
    apply Subtype.ext
    funext n
    simp [A, B, i, stageBaseTowerInclusion]


/-- The `n`-th coordinate of the inverse limit of the bases of the levels of a formal object,
valued in the `n`-th adic truncation of its base. -/
noncomputable def formalInverseLimitCoordinate
    (ξ : FormalObject p) (n : ℕ) :
    inverseLimit (fun j => p.obj (ξ.level j))
      (fun j => p.map (ξ.transition j)) →ₐ[Λ] AdicTruncation.obj ξ.base n :=
  (eqToHom (ξ.level_eq n)).hom.comp
    (inverseLimitProj (fun j => p.obj (ξ.level j))
      (fun j => p.map (ξ.transition j)) n)

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- The coordinates of the inverse limit of the bases of the levels are compatible with the
truncation transitions. -/
theorem formalInverseLimitCoordinate_fac
    (ξ : FormalObject p) (n : ℕ) :
    (AdicTruncation.transition ξ.base n).hom.comp
        (formalInverseLimitCoordinate ξ (n + 1)) =
      formalInverseLimitCoordinate ξ n := by
  apply AlgHom.ext
  intro x
  let z : inverseLimit (fun j => p.obj (ξ.level j))
      (fun j => p.map (ξ.transition j)) := x
  have hcoord := z.2 n
  change (p.map (ξ.transition n)).hom
      ((inverseLimitProj (fun j => p.obj (ξ.level j))
        (fun j => p.map (ξ.transition j)) (n + 1)) z) =
    (inverseLimitProj (fun j => p.obj (ξ.level j))
      (fun j => p.map (ξ.transition j)) n) z at hcoord
  let : p.IsHomLift ((AdicTruncation.transitionNat n).app ξ.base)
      (ξ.transition n) := by
    simpa only [AdicTruncation.transitionNat] using ξ.transition_lift n
  have hfac := IsHomLift.fac p
    ((AdicTruncation.transitionNat n).app ξ.base) (ξ.transition n)
  have hfac' : eqToHom (ξ.level_eq (n + 1)) ≫
      AdicTruncation.transition ξ.base n =
        p.map (ξ.transition n) ≫ eqToHom (ξ.level_eq n) := by
    calc
      _ = eqToHom (ξ.level_eq (n + 1)) ≫
          (eqToHom (ξ.level_eq (n + 1)).symm ≫
            p.map (ξ.transition n) ≫ eqToHom (ξ.level_eq n)) := by
              simpa only [AdicTruncation.transitionNat] using
                congrArg (fun f => eqToHom (ξ.level_eq (n + 1)) ≫ f) hfac
      _ = _ := by simp
  change (AdicTruncation.transition ξ.base n).hom
      ((formalInverseLimitCoordinate ξ (n + 1)) x) =
    (formalInverseLimitCoordinate ξ n) x
  change (AdicTruncation.transition ξ.base n).hom
      ((eqToHom (ξ.level_eq (n + 1))).hom
        ((inverseLimitProj (fun j => p.obj (ξ.level j))
          (fun j => p.map (ξ.transition j)) (n + 1)) z)) = _
  have hval := congrArg (fun f : ArtinianLocalAlgCat.Hom _ _ =>
      f.hom ((inverseLimitProj (fun j => p.obj (ξ.level j))
        (fun j => p.map (ξ.transition j)) (n + 1)) z)) hfac'
  rw [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply,
    ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply] at hval
  rw [hval, hcoord]
  rfl

/-- The map from the base of a formal object to the base of its `n`-th level. -/
noncomputable def formalLimitQuotientMap
    (ξ : FormalObject p) (n : ℕ) :
    inverseLimit (fun j => p.obj (ξ.level j))
      (fun j => p.map (ξ.transition j)) →ₐ[Λ]
      ξ.base ⧸ maximalIdeal ξ.base ^ (n + 1) := by
  change inverseLimit (fun j => p.obj (ξ.level j))
      (fun j => p.map (ξ.transition j)) →ₐ[Λ] AdicTruncation.obj ξ.base n
  exact formalInverseLimitCoordinate ξ n

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `formalLimitQuotientMap` is the projection onto the `n`-th adic truncation followed by the
identification of that truncation with the base of the `n`-th level. -/
theorem formalLimitQuotientMap_fac
    (ξ : FormalObject p) (n : ℕ) :
    (Ideal.Quotient.factorₐ Λ
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).comp
        (formalLimitQuotientMap ξ (n + 1)) = formalLimitQuotientMap ξ n :=
  formalInverseLimitCoordinate_fac ξ n

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- The maps `formalLimitQuotientMap` are compatible with the transition maps of the levels. -/
theorem formalLimitQuotientMap_compatible
    (ξ : FormalObject p) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ Λ
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).comp
        (formalLimitQuotientMap ξ n) = formalLimitQuotientMap ξ m := by
  induction n, h using Nat.le_induction with
  | base =>
      simp only [Ideal.Quotient.factorₐ_refl, AlgHom.id_comp]
  | succ n h ih =>
      let h01 : maximalIdeal ξ.base ^ (n + 2) ≤
          maximalIdeal ξ.base ^ (n + 1) :=
        Ideal.pow_le_pow_right (Nat.le_succ (n + 1))
      let h12 : maximalIdeal ξ.base ^ (n + 1) ≤
          maximalIdeal ξ.base ^ (m + 1) :=
        Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)
      let h02 : maximalIdeal ξ.base ^ (n + 2) ≤
          maximalIdeal ξ.base ^ (m + 1) := h01.trans h12
      calc
        (Ideal.Quotient.factorₐ Λ h02).comp (formalLimitQuotientMap ξ (n + 1)) =
            (Ideal.Quotient.factorₐ Λ h12).comp
              ((Ideal.Quotient.factorₐ Λ h01).comp
                (formalLimitQuotientMap ξ (n + 1))) := by
                  rw [← AlgHom.comp_assoc, ← Ideal.Quotient.factorₐ_comp Λ h01 h12]
        _ = (Ideal.Quotient.factorₐ Λ h12).comp
              (formalLimitQuotientMap ξ n) := by
                rw [formalLimitQuotientMap_fac]
        _ = formalLimitQuotientMap ξ m := ih

/-- The map from the base of a formal object into the inverse limit of the bases of its levels. -/
noncomputable def formalInverseLimitQuotientSystem
    (ξ : FormalObject p) (n : ℕ) :
    inverseLimit (fun j => p.obj (ξ.level j))
      (fun j => p.map (ξ.transition j)) →ₐ[Λ]
      ξ.base ⧸ maximalIdeal ξ.base ^ n := by
  cases n with
  | zero =>
      letI : Subsingleton (ξ.base ⧸ maximalIdeal ξ.base ^ 0) := by
        rw [pow_zero]
        exact Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact
        { toFun := fun _ => 0
          map_one' := Subsingleton.elim _ _
          map_mul' := fun _ _ => Subsingleton.elim _ _
          map_zero' := Subsingleton.elim _ _
          map_add' := fun _ _ => Subsingleton.elim _ _
          commutes' := fun _ => Subsingleton.elim _ _ }
  | succ n => exact formalLimitQuotientMap ξ n

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `formalInverseLimitQuotientSystem` is compatible with the coordinates of the inverse limit. -/
theorem formalInverseLimitQuotientSystem_compatible
    (ξ : FormalObject p) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp
      (formalInverseLimitQuotientSystem ξ n) =
        formalInverseLimitQuotientSystem ξ m := by
  cases m with
  | zero =>
      apply AlgHom.ext
      intro x
      let : Subsingleton (ξ.base ⧸ maximalIdeal ξ.base ^ 0) := by
        rw [pow_zero]
        exact Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact Subsingleton.elim _ _
  | succ m =>
      cases n with
      | zero => omega
      | succ n =>
          simpa only [formalInverseLimitQuotientSystem] using
            formalLimitQuotientMap_compatible ξ
              (Nat.le_of_succ_le_succ hle)

/-- The inverse of `formalInverseLimitQuotientSystem`: the identification of the inverse limit of
the bases of the levels with the base of the formal object. -/
noncomputable def formalInverseLimitToBase
    (ξ : FormalObject p) :
    inverseLimit (fun j => p.obj (ξ.level j))
      (fun j => p.map (ξ.transition j)) →ₐ[Λ] ξ.base := by
  let S := inverseLimit (fun j => p.obj (ξ.level j))
    (fun j => p.map (ξ.transition j))
  let ψ := AdicCompletion.liftAlgHom (R := Λ) (A := S)
    (maximalIdeal ξ.base) (formalInverseLimitQuotientSystem ξ)
    (formalInverseLimitQuotientSystem_compatible ξ)
  let u := (AdicCompletion.ofAlgEquiv (maximalIdeal ξ.base)).symm
  letI : IsScalarTower Λ ξ.base
      (AdicCompletion (maximalIdeal ξ.base) ξ.base) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact
    { toFun := fun x => u (ψ x)
      map_one' := by simp [ψ, u]
      map_mul' := by simp [ψ, u]
      map_zero' := by simp [ψ, u]
      map_add' := by simp [ψ, u]
      commutes' := by
        intro r
        change u (ψ (algebraMap Λ S r)) = algebraMap Λ ξ.base r
        rw [ψ.commutes]
        rw [IsScalarTower.algebraMap_apply Λ ξ.base
          (AdicCompletion (maximalIdeal ξ.base) ξ.base) r]
        exact u.commutes (algebraMap Λ ξ.base r) }

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `formalInverseLimitToBase` is compatible with the projections onto the adic truncations. -/
theorem formalInverseLimitToBase_quotient
    (ξ : FormalObject p) (n : ℕ) :
    (Ideal.Quotient.mkₐ Λ (maximalIdeal ξ.base ^ (n + 1))).comp
      (formalInverseLimitToBase ξ) = formalLimitQuotientMap ξ n := by
  apply AlgHom.ext
  intro x
  let ψ := AdicCompletion.liftAlgHom (R := Λ)
    (A := inverseLimit (fun j => p.obj (ξ.level j))
      (fun j => p.map (ξ.transition j))) (maximalIdeal ξ.base)
    (formalInverseLimitQuotientSystem ξ)
    (formalInverseLimitQuotientSystem_compatible ξ)
  let u := (AdicCompletion.ofAlgEquiv (maximalIdeal ξ.base)).symm
  change (Ideal.Quotient.mkₐ Λ (maximalIdeal ξ.base ^ (n + 1)))
      ((fun x => u (ψ x)) x) = _
  change Ideal.Quotient.mk (maximalIdeal ξ.base ^ (n + 1))
      (u (ψ x)) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm]
  rw [AdicCompletion.evalₐ_liftAlgHom]
  rfl

/-- The map from the inverse limit of `stageBaseTower` to the base of the formal object. -/
noncomputable def stageBaseTowerBaseMap
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) :
    inverseLimit (stageBaseTower hp hS1 ξ)
      (stageBaseTowerTransition hp hS1 ξ) →ₐ[Λ] ξ.base :=
  (formalInverseLimitToBase ξ).comp
    (stageBaseInverseLimitMap hp hS1 ξ)

/-- `stageBaseTowerBaseMap` is compatible with the projections onto the adic truncations. -/
theorem stageBaseTowerBaseMap_quotient
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    (Ideal.Quotient.mkₐ Λ (maximalIdeal ξ.base ^ (n + 1))).comp
      (stageBaseTowerBaseMap hp hS1 ξ) =
    (formalInverseLimitCoordinate ξ n).comp (stageBaseInverseLimitMap hp hS1 ξ) := by
  rw [stageBaseTowerBaseMap, ← AlgHom.comp_assoc,
    formalInverseLimitToBase_quotient]
  rfl

/-- `stageBaseTowerBaseMap` is injective, so the inverse limit of `stageBaseTower` is a subalgebra
of the base of the formal object. -/
theorem stageBaseTowerBaseMap_injective
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) :
    Function.Injective (stageBaseTowerBaseMap hp hS1 ξ) := by
  intro x y hxy
  apply Subtype.ext
  funext n
  apply stageBaseTowerInclusion_injective hp hS1 ξ n
  rw [stageBaseTowerBaseMap] at hxy
  have hq := congrArg
    (fun z : ξ.base => Ideal.Quotient.mk (maximalIdeal ξ.base ^ (n + 1)) z) hxy
  change ((Ideal.Quotient.mkₐ Λ (maximalIdeal ξ.base ^ (n + 1))).comp
      (formalInverseLimitToBase ξ)) (stageBaseInverseLimitMap hp hS1 ξ x) =
    ((Ideal.Quotient.mkₐ Λ (maximalIdeal ξ.base ^ (n + 1))).comp
      (formalInverseLimitToBase ξ)) (stageBaseInverseLimitMap hp hS1 ξ y) at hq
  rw [formalInverseLimitToBase_quotient] at hq
  change (eqToHom (ξ.level_eq n)).hom
      ((stageBaseTowerInclusion hp hS1 ξ n).hom (x.1 n)) =
    (eqToHom (ξ.level_eq n)).hom
      ((stageBaseTowerInclusion hp hS1 ξ n).hom (y.1 n)) at hq
  exact artinianHom_injective_of_isIso (eqToHom (ξ.level_eq n)) hq

end

end Deformation

end
