module

public import StacksFrontier.Deformation.Formal.MinimalVersal.StageTowerCotangent

/-!
# The stage tower limit as a complete local algebra

Under the bound on the cotangent dimensions, the inverse limit of the stage tower is an object of
the category of Noetherian complete local `Λ`-algebras with residue field `k`, and its projections
onto the terms of the tower respect the chosen identifications of the residue fields. This file
builds that object together with its injective morphism to the base of the formal object.

## Main definitions

* `Deformation.stageBaseTowerResidueMapEquiv`: the identification of the residue field of the
  inverse limit of `stageBaseTower` with the residue field of its zeroth term.
* `Deformation.stageBaseTowerResidueEquiv`: the identification of the residue field of the inverse
  limit of `stageBaseTower` with `k`.
* `Deformation.stageBaseTowerCompleteLocal`: the inverse limit of `stageBaseTower` as an object of
  the category of Noetherian complete local `Λ`-algebras with residue field `k`.
* `Deformation.stageBaseTowerBaseHom`: the morphism of complete local algebras from
  `stageBaseTowerCompleteLocal` to the base of the formal object.

## Main results

* `Deformation.stageBaseTowerProjection_zero_isLocal`: the projection of the inverse limit of
  `stageBaseTower` onto its zeroth term is local.
* `Deformation.stageBaseTowerResidueMapEquiv_residue`: `stageBaseTowerResidueMapEquiv` carries a
  residue class to the residue class of its zeroth coordinate.
* `Deformation.stageBaseTowerProjection_residue`: the projections of `stageBaseTowerCompleteLocal`
  onto the terms of the tower respect the chosen identifications of the residue fields with `k`.
* `Deformation.stageBaseTowerBaseHom_injective`: `stageBaseTowerBaseHom` is injective, so
  `stageBaseTowerCompleteLocal` is a complete local subalgebra of the base of the formal object.
* `Deformation.stageBaseTowerBaseHom_quotient`: `stageBaseTowerBaseHom` is compatible with the
  projections onto the adic truncations.

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
/-- The projection of the inverse limit of `stageBaseTower` onto its zeroth term is local. -/
theorem stageBaseTowerProjection_zero_isLocal
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) :
    IsLocalHom (inverseLimitProj (stageBaseTower hp hS1 ξ)
      (stageBaseTowerTransition hp hS1 ξ) 0).toRingHom := by
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  let π (n : ℕ) := inverseLimitProj A f n
  refine ⟨fun x hx => ?_⟩
  have hunit : ∀ n, IsUnit (π n x) := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih =>
        refine isUnit_of_map_unit (f n).hom.toRingHom _ ?_
        change IsUnit ((f n).hom (π (n + 1) x))
        rwa [show (f n).hom (π (n + 1) x) = π n x from x.2 n]
  refine isUnit_iff_exists_inv.mpr ⟨⟨fun n => ↑((hunit n).unit⁻¹), fun n => ?_⟩,
    Subtype.ext (funext fun n => (hunit n).unit.mul_inv)⟩
  change (f n).hom (↑((hunit (n + 1)).unit⁻¹)) = ↑((hunit n).unit⁻¹)
  apply Units.eq_inv_of_mul_eq_one_left
  change π n x * (f n).hom (↑((hunit (n + 1)).unit⁻¹)) = 1
  rw [show π n x = (f n).hom (π (n + 1) x) from (x.2 n).symm, ← map_mul,
    (hunit (n + 1)).mul_val_inv, map_one]

/-- The identification of the residue field of the inverse limit of `stageBaseTower` with the
residue field of its zeroth term. -/
noncomputable def stageBaseTowerResidueMapEquiv
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d) :
    (let A := stageBaseTower hp hS1 ξ
     let f := stageBaseTowerTransition hp hS1 ξ
     let S := inverseLimit A f
     letI : IsLocalRing S :=
       (Classical.choose (stageBaseTower_cotangent_bounded hp hS1 ξ hbound)).isLocal
     ResidueField S ≃ₐ[Λ] ResidueField (A 0)) := by
  classical
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  let S := inverseLimit A f
  letI : IsLocalRing S :=
    (Classical.choose (stageBaseTower_cotangent_bounded hp hS1 ξ hbound)).isLocal
  let π (n : ℕ) := inverseLimitProj A f n
  let t : ∀ n, A (n + 1) →ₗ[ℤ] A n := fun n =>
    (f n).hom.toRingHom.toAddMonoidHom.toIntLinearMap
  letI : IsLocalHom (π 0) := ⟨(stageBaseTowerProjection_zero_isLocal hp hS1 ξ).map_nonunit⟩
  let e₀ := ResidueField.mapAlgHom (π 0)
  refine AlgEquiv.ofBijective e₀ ⟨e₀.toRingHom.injective, fun z => ?_⟩
  obtain ⟨a, rfl⟩ := residue_surjective z
  obtain ⟨x, hx⟩ := invLimit.proj_surjective (M := fun n => A n) (t := t)
    (stageBaseTowerTransition_surjective hp hS1 ξ) 0 a
  exact ⟨residue S ⟨x.1, x.2⟩, (ResidueField.mapAlgHom_residue _ _).trans
    (congrArg (residue (A 0)) hx)⟩

/-- The identification of the residue field of the inverse limit of `stageBaseTower` with `k`. -/
noncomputable def stageBaseTowerResidueEquiv
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d) :
    (let A := stageBaseTower hp hS1 ξ
     let f := stageBaseTowerTransition hp hS1 ξ
     let S := inverseLimit A f
     letI : IsLocalRing S :=
       (Classical.choose (stageBaseTower_cotangent_bounded hp hS1 ξ hbound)).isLocal
     ResidueField S ≃ₐ[Λ] k) :=
  (stageBaseTowerResidueMapEquiv hp hS1 ξ hbound).trans
    (stageBaseTower hp hS1 ξ 0).residueEquiv

/-- The inverse limit of `stageBaseTower` as an object of the category of Noetherian complete local
`Λ`-algebras with residue field `k`. -/
noncomputable def stageBaseTowerCompleteLocal
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d) :
    CompleteLocalAlgCat.{u, v, w} Λ k := by
  let h := Classical.choose (stageBaseTower_cotangent_bounded hp hS1 ξ hbound)
  let S := inverseLimit (stageBaseTower hp hS1 ξ)
    (stageBaseTowerTransition hp hS1 ξ)
  exact
    { carrier := S
      completeLocal := h
      residueEquiv := stageBaseTowerResidueEquiv hp hS1 ξ hbound }

/-- `stageBaseTowerResidueMapEquiv` carries a residue class to the residue class of its zeroth
coordinate. -/
theorem stageBaseTowerResidueMapEquiv_residue
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    [IsLocalRing (inverseLimit (stageBaseTower hp hS1 ξ)
      (stageBaseTowerTransition hp hS1 ξ))]
    (x : stageBaseTowerCompleteLocal hp hS1 ξ hbound) :
    stageBaseTowerResidueMapEquiv hp hS1 ξ hbound (residue _ x) =
      residue (stageBaseTower hp hS1 ξ 0)
        (inverseLimitProj (stageBaseTower hp hS1 ξ)
          (stageBaseTowerTransition hp hS1 ξ) 0 x) := by
  let : IsLocalHom (inverseLimitProj (stageBaseTower hp hS1 ξ)
      (stageBaseTowerTransition hp hS1 ξ) 0) :=
    ⟨fun x hx => (stageBaseTowerProjection_zero_isLocal hp hS1 ξ).map_nonunit x hx⟩
  change ResidueField.mapAlgHom
      (inverseLimitProj (stageBaseTower hp hS1 ξ)
        (stageBaseTowerTransition hp hS1 ξ) 0) (residue _ x) = _
  exact ResidueField.mapAlgHom_residue _ _

/-- The projections of `stageBaseTowerCompleteLocal` onto the terms of the tower respect the chosen
identifications of the residue fields with `k`. -/
theorem stageBaseTowerProjection_residue
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    [IsLocalRing (inverseLimit (stageBaseTower hp hS1 ξ)
      (stageBaseTowerTransition hp hS1 ξ))]
    (x : stageBaseTowerCompleteLocal hp hS1 ξ hbound) (n : ℕ) :
    (stageBaseTower hp hS1 ξ n).residueEquiv
        (residue _ (inverseLimitProj (stageBaseTower hp hS1 ξ)
          (stageBaseTowerTransition hp hS1 ξ) n x)) =
      (stageBaseTowerCompleteLocal hp hS1 ξ hbound).residueEquiv (residue _ x) := by
  let A := stageBaseTower hp hS1 ξ
  let f := stageBaseTowerTransition hp hS1 ξ
  let π := inverseLimitProj A f
  induction n with
  | zero =>
      change (A 0).residueEquiv (residue (A 0) (π 0 x)) =
        (stageBaseTowerResidueMapEquiv hp hS1 ξ hbound).trans
          (A 0).residueEquiv (residue _ x)
      rw [AlgEquiv.trans_apply,
        stageBaseTowerResidueMapEquiv_residue hp hS1 ξ hbound x]
  | succ n ih =>
      change (A (n + 1)).residueEquiv
          (residue (A (n + 1)) (π (n + 1) x)) =
        (stageBaseTowerCompleteLocal hp hS1 ξ hbound).residueEquiv (residue _ x)
      calc
        (A (n + 1)).residueEquiv (residue (A (n + 1)) (π (n + 1) x)) =
            (A n).residueEquiv (residue (A n) ((f n).hom (π (n + 1) x))) :=
              ((f n).residue_comm (π (n + 1) x)).symm
        _ = (A n).residueEquiv (residue (A n) (π n x)) := by
              rw [show (f n).hom (π (n + 1) x) = π n x from x.2 n]
        _ = (stageBaseTowerCompleteLocal hp hS1 ξ hbound).residueEquiv (residue _ x) := ih

/-- The morphism of complete local algebras from `stageBaseTowerCompleteLocal` to the base of the
formal object. -/
noncomputable def stageBaseTowerBaseHom
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d) :
    stageBaseTowerCompleteLocal hp hS1 ξ hbound ⟶ ξ.base := by
  let R := stageBaseTowerCompleteLocal hp hS1 ξ hbound
  let S := inverseLimit (stageBaseTower hp hS1 ξ)
    (stageBaseTowerTransition hp hS1 ξ)
  letI : IsLocalRing S := R.completeLocal.isLocal
  let f := stageBaseTowerBaseMap hp hS1 ξ
  let π := inverseLimitProj (stageBaseTower hp hS1 ξ)
    (stageBaseTowerTransition hp hS1 ξ) 0
  let i := stageBaseTowerInclusion hp hS1 ξ 0
  have hi : i = 𝟙 (stageBaseTower hp hS1 ξ 0) := by
    change p.map (𝟙 (ξ.level 0)) = 𝟙 (p.obj (ξ.level 0))
    exact p.map_id _
  have hq : ∀ a : S, Ideal.Quotient.mk (AdicTruncation.ideal ξ.base 0) (f a) =
      (eqToHom (ξ.level_eq 0)).hom (i.hom (π a)) := fun a =>
    congrArg (fun g : R →ₐ[Λ] ξ.base ⧸ maximalIdeal ξ.base ^ (0 + 1) => g a)
      (stageBaseTowerBaseMap_quotient hp hS1 ξ 0)
  refine
    { hom := f
      isLocal := ?_
      residue_comm := ?_ }
  · refine ⟨fun a hfa => ?_⟩
    have hmk : IsUnit (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base 0) (f a)) := hfa.map _
    have hiunit := isUnit_of_map_unit (eqToHom (ξ.level_eq 0)).hom (i.hom (π a)) (hq a ▸ hmk)
    rw [hi] at hiunit
    exact (stageBaseTowerProjection_zero_isLocal hp hS1 ξ).map_nonunit a hiunit
  · intro a
    let : Nontrivial
        (ξ.base ⧸ AdicTruncation.ideal ξ.base 0) :=
      inferInstanceAs (Nontrivial (AdicTruncation.obj ξ.base 0))
    let : IsLocalRing
        (ξ.base ⧸ AdicTruncation.ideal ξ.base 0) :=
      inferInstanceAs (IsLocalRing (AdicTruncation.obj ξ.base 0))
    have hres := congrArg
      (fun z : AdicTruncation.obj ξ.base 0 =>
        AdicTruncation.residueEquiv ξ.base 0 (residue _ z)) (hq a)
    rw [AdicTruncation.residueEquiv_residue_mk] at hres
    have htransport := (eqToHom (ξ.level_eq 0)).residue_comm (i.hom (π a))
    rw [hi] at htransport
    have hproj := stageBaseTowerProjection_residue hp hS1 ξ hbound a 0
    change (stageBaseTowerCompleteLocal hp hS1 ξ hbound).residueEquiv
        (residue (stageBaseTowerCompleteLocal hp hS1 ξ hbound) a) =
      (stageBaseTower hp hS1 ξ 0).residueEquiv (residue _ (π a)) at hproj
    have htransport' :
        (p.obj (ξ.level 0)).residueEquiv (residue _ (π a)) =
          AdicTruncation.residueEquiv ξ.base 0
            (residue _ ((eqToHom (ξ.level_eq 0)).hom (i.hom (π a)))) := by
      have hmap : i.hom (π a) = π a := by rw [hi]; rfl
      rw [hmap]
      convert htransport.symm using 1 <;>
        simp [ArtinianLocalAlgCat.id_hom, AdicTruncation.functor, AdicTruncation.obj]
      all_goals rfl
    exact hres.trans (htransport'.symm.trans hproj.symm)

/-- `stageBaseTowerBaseHom` is injective, so `stageBaseTowerCompleteLocal` is a complete local
subalgebra of the base of the formal object. -/
theorem stageBaseTowerBaseHom_injective
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d) :
    Function.Injective (stageBaseTowerBaseHom hp hS1 ξ hbound).hom := by
  change Function.Injective (stageBaseTowerBaseMap hp hS1 ξ)
  exact stageBaseTowerBaseMap_injective hp hS1 ξ

/-- `stageBaseTowerBaseHom` is compatible with the projections onto the adic truncations. -/
theorem stageBaseTowerBaseHom_quotient
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    (Ideal.Quotient.mkₐ Λ (maximalIdeal ξ.base ^ (n + 1))).comp
      (stageBaseTowerBaseHom hp hS1 ξ hbound).hom =
    (formalInverseLimitCoordinate ξ n).comp (stageBaseInverseLimitMap hp hS1 ξ) := by
  change (Ideal.Quotient.mkₐ Λ (maximalIdeal ξ.base ^ (n + 1))).comp
      (stageBaseTowerBaseMap hp hS1 ξ) = _
  exact stageBaseTowerBaseMap_quotient hp hS1 ξ n

end

end Deformation

end
