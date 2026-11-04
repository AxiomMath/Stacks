module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverFieldFunctionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverFieldDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionBaseChangeTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquareRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FirstFailureDiagramNormalization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalHigherBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeReduction
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Base change over a field (Stacks 0F1I)

[Stacks, Tag 0F1I]: let `K` be a field. For any commutative diagram

```
X  ←-p-  X'  ←-h-  Y
|        |f'       |e
Spec K ←-s- S' ←-g- T
```

of schemes over `K` with `X' = X ×_{Spec K} S'` and `Y = X' ×_{S'} T` and `g` quasi-compact and
quasi-separated, and every abelian sheaf `𝓕` on `T_étale` whose stalks are torsion of orders
invertible in `K`, the base change map `(f')⁻¹Rg_*𝓕 ⟶ Rh_*e⁻¹𝓕` is an isomorphism.

## Main results

* `Stacks.EtaleCohomology.BaseChangeOverField.derivedBaseChangeHolds_of_quasiCompact` — the case of
  `X` quasi-compact and locally of finite type over `K` and `𝓕` annihilated by `n`: the second
  and third paragraphs of the source's proof (`derivedBaseChangeHolds_of_reduction`, through
  [Stacks, Tag 0F1D] with [Stacks, Tag 0F08] and [Stacks, Tag 0F09]) and its last paragraph
  (`FunctionFieldLimit.functionFieldBaseChange_of_quasiCompact`).
* `Stacks.EtaleCohomology.BaseChangeOverField.derivedBaseChangeHolds_of_compactSpace` — `X`
  quasi-compact and quasi-separated: *"we can write `X = lim X_i` [...] of finite type over `K`
  [...] By Lemma 0EZT it suffices to prove the statement for the squares with corners
  `X_i, Y_i, S_i, T_i`"*, with [Stacks, Tag 09MV].
* `Stacks.EtaleCohomology.BaseChangeOverField.derivedBaseChangeHolds_of_affineOpens` — *"the
  question is local on `X`"*, by [Stacks, Tag 0EZR].
* `Stacks.EtaleCohomology.BaseChangeOverField.derivedBaseChangeHolds_of_isUnit` — 0F1I for every
  `X` over `K` and sheaves annihilated by an integer `n` invertible in `K`, in the form
  `DerivedBaseChangeHolds πX n` used by [Stacks, Tag 0F1J].
* `Stacks.EtaleCohomology.BaseChangeOverField.isIso_smallEtaleDerivedBaseChangeAb_of_field` —
  **[Stacks, Tag 0F1I]**: *"we may write `𝓕 = colim 𝓕[n]` [...] reduces us to the case where
  `𝓕` is a sheaf of `ℤ/nℤ`-modules"*.

## Implementation notes

The source reduces to `X` affine of finite type and to `𝓕` annihilated by `n` first, and then
replaces `K` by `K̄` and `X` by its reduction; here the reductions to `K̄` and to the reduction
are made for `X` of finite type, and the passage from finite type to arbitrary `X` comes after.
The base change map is `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` on bounded below
derived categories, `𝓕` placed in degree zero.

## References

* [Stacks Project, Tag 0F1I](https://stacks.math.columbia.edu/tag/0F1I)
* [Stacks Project, Tag 09MV](https://stacks.math.columbia.edu/tag/09MV)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 0F1D](https://stacks.math.columbia.edu/tag/0F1D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.BaseChangeOverField

-- forced by `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`
-- (BaseChangeHigher/BaseChangeCondition.lean:220), through which
-- `Stacks.EtaleCohomology.BaseChangeOverField.DerivedBaseChangeHolds`
-- (Kunneth/BaseChangeOverField.lean:98) is stated.
attribute [local instance] HasDerivedCategory.standard

/-! ### Schemes of finite type over a field -/

/-- **[Stacks, Tag 0F1I] for a quasi-compact scheme locally of finite type over `K` and a sheaf
annihilated by `n`.** This is `derivedBaseChangeHolds_of_reduction_of_locallyOfFiniteType` with
[Stacks, Tag 0F09] (`smoothLimitBaseChange_holds`), [Stacks, Tag 0F08]
(`FirstFailureDiagram.normalFailureDiagram_of_firstFailure`), and the last paragraph of the
source's proof (`FunctionFieldLimit.functionFieldBaseChange_of_quasiCompact`) for the reduction
of `X_{K̄}`. -/
theorem derivedBaseChangeHolds_of_quasiCompact (K : Type u) [Field K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX] [QuasiCompact sX] (n : ℤ)
    (hn : IsUnit (n : K)) : DerivedBaseChangeHolds sX n := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have : LocallyOfFiniteType ((pullback φ sX).nilradical.subschemeι ≫ pullback.fst φ sX) :=
    inferInstance
  have : QuasiCompact ((pullback φ sX).nilradical.subschemeι ≫ pullback.fst φ sX) :=
    inferInstance
  have hn' : IsUnit (n : AlgebraicClosure K) := by
    simpa using hn.map (algebraMap K (AlgebraicClosure K))
  exact derivedBaseChangeHolds_of_reduction_of_locallyOfFiniteType K sX
    smoothLimitBaseChange_holds
    FirstFailureDiagram.normalFailureDiagram_of_firstFailure n hn
    (FunctionFieldLimit.functionFieldBaseChange_of_quasiCompact (AlgebraicClosure K) _ n hn')

/-! ### Quasi-compact and quasi-separated schemes over a field -/

open LimitBaseChange in
/-- **[Stacks, Tag 0F1I] for a quasi-compact quasi-separated scheme over `K` and a sheaf
annihilated by `n`.** By [Stacks, Tag 09MV] `X = lim X_i` with affine transition morphisms and
`X_i` of finite presentation over `K`; then `X' = lim X_i ×_K S'` and `Y = lim X'_i ×_{S'} T`,
and base change for the squares of the `X'_i` (`derivedBaseChangeHolds_of_quasiCompact`) passes
to the limit by [Stacks, Tag 0EZT]
(`OpenProductLimit.isIso_higherBaseChangeMapAb_of_isLimit_of_fixedBase`). -/
theorem derivedBaseChangeHolds_of_compactSpace (K : Type u) [Field K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) [CompactSpace X] [QuasiSeparatedSpace X] (n : ℤ)
    (hn : IsUnit (n : K)) : DerivedBaseChangeHolds sX n := by
  obtain ⟨I, _, _, _, D, t, pc, hlim, hpt, hfp, -, haff⟩ := exists_isLimit_finitePresentation sX
  have hD : ∀ i, DerivedBaseChangeHolds (t.app i) n := fun i => by
    have : LocallyOfFinitePresentation (t.app i) := (hfp i).locallyOfFinitePresentation
    have : QuasiCompact (t.app i) := (hfp i).quasiCompact
    exact derivedBaseChangeHolds_of_quasiCompact K (t.app i) n hn
  refine (derivedBaseChangeHolds_iff sX n).2 fun q => ?_
  intro S' X' T Y s p f' hp g h e sq _ _ F hF r _
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := fun a => haff a
  let DX := baseChangeDiagram D t s
  let fX : DX ⟶ (Functor.const Iᵒᵖ).obj S' := baseChangeStructureMap D t s
  let DY := baseChangeDiagram DX fX g
  let hY : DY ⟶ DX := baseChangeHorizontal DX fX g
  let eY : DY ⟶ (Functor.const Iᵒᵖ).obj T := baseChangeStructureMap DX fX g
  have hsq : ∀ i, IsPullback (hY.app i) (eY.app i) (fX.app i)
      (((Functor.const Iᵒᵖ).map g).app i) := isPullback_baseChangeStage DX fX g
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a) :=
    fun a => isAffineHom_baseChangeDiagram_map D t s a
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a) :=
    fun a => isAffineHom_baseChangeDiagram_map DX fX g a
  -- the limits of the upper corners
  have hptj : ∀ j, pc.app j ≫ t.app j = sX := fun j => congrArg (fun φ => φ.app j) hpt
  have hw : ∀ j, (p ≫ pc.app j) ≫ t.app j = f' ≫ s := fun j => by rw [Category.assoc, hptj, hp.w]
  let pX := baseChangeProjection D t s pc p f' hw
  have hXs := baseChangeProjection_comp_structureMap D t s pc p f' hw
  have hcX : IsLimit (Cone.mk X' pX) :=
    isLimit_of_isPullback_stages (isPullback_baseChangeStage D t s) hp hptj
      hXs (baseChangeProjection_comp_horizontal D t s pc p f' hw) hlim
  have hwY : ∀ j, (h ≫ pX.app j) ≫ fX.app j = e ≫ g := fun j => by
    rw [Category.assoc, hXs, sq.w]
  let pY := baseChangeProjection DX fX g pX h e hwY
  have hYs := baseChangeProjection_comp_structureMap DX fX g pX h e hwY
  have hcY : IsLimit (Cone.mk Y pY) :=
    isLimit_of_isPullback_stages (isPullback_baseChangeStage DX fX g) sq
      hXs hYs (baseChangeProjection_comp_horizontal DX fX g pX h e hwY) hcX
  -- the levels
  have hlevel : ∀ i, IsIso ((higherBaseChangeMapAb (fX.app i) (((Functor.const Iᵒᵖ).map g).app i)
      (hY.app i) (eY.app i) (hsq i).w r).app F) := fun i => by
    have : QuasiCompact (((Functor.const Iᵒᵖ).map g).app i) := inferInstanceAs (QuasiCompact g)
    have : QuasiSeparated (((Functor.const Iᵒᵖ).map g).app i) :=
      inferInstanceAs (QuasiSeparated g)
    exact (derivedBaseChangeHolds_iff (t.app i) n).1 (hD i) r s
      ((baseChangeHorizontal D t s).app i) (fX.app i) (isPullback_baseChangeStage D t s i) _
      (hY.app i) (eY.app i) (hsq i) F hF r le_rfl
  exact OpenProductLimit.isIso_higherBaseChangeMapAb_of_isLimit_of_fixedBase g fX hY eY hsq
    hcX hcY f' h e hXs
    (fun i => (baseChangeProjection_comp_horizontal DX fX g pX h e hwY i).symm) hYs sq.w r F hlevel

/-! ### Locality on the source -/

/-- **Derived base change for sheaves annihilated by `n` is local on the source.** If it holds for
`U ⟶ X ⟶ S` for every affine open `U ⊆ X`, it holds for `f : X ⟶ S`. In a diagram over `f`, the
opens `U' = X' ×_X U` cover `X'`, and the square `U' ⟵ U' ×_{X'} Y` over `S' ⟵ T` is a diagram
over `U ⟶ S`; this is [Stacks, Tag 0EZR] (3) for that covering
(`isIso_higherBaseChangeMapAb_app_of_isIso_local`). -/
theorem derivedBaseChangeHolds_of_affineOpens {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ)
    (H : ∀ U : X.affineOpens, DerivedBaseChangeHolds (U.1.ι ≫ f) n) :
    DerivedBaseChangeHolds f n := by
  refine (derivedBaseChangeHolds_iff f n).2 fun q => ?_
  intro S' X' T Y s p f' hp g h e sq _ _ F hF r _
  have hcov : Presieve.ofArrows (fun U : X.affineOpens => pullback p U.1.ι)
      (fun U => pullback.fst p U.1.ι) ∈ Scheme.etalePrecoverage X' := by
    refine AlgebraicGeometry.ofArrows_mem_etalePrecoverage_iff.2
      ⟨fun z => ?_, fun U => inferInstance⟩
    obtain ⟨U, hU, hpz, -⟩ := exists_isAffineOpen_mem_and_subset (x := p z) (U := ⊤) trivial
    refine ⟨⟨U, hU⟩, ?_⟩
    rw [Scheme.Pullback.range_fst]
    exact ⟨⟨p z, hpz⟩, rfl⟩
  have hloc : ∀ U : X.affineOpens, IsIso ((higherBaseChangeMapAb (pullback.fst p U.1.ι ≫ f') g
      (pullback.fst (pullback.fst p U.1.ι) h) (pullback.snd (pullback.fst p U.1.ι) h ≫ e)
      ((IsPullback.of_hasPullback _ _).paste_vert sq).w r).app
        ((smallEtalePullbackAb (𝟙 T)).obj F)) := fun U => by
    have hpU : IsPullback (pullback.snd p U.1.ι) (pullback.fst p U.1.ι ≫ f') (U.1.ι ≫ f) s :=
      (IsPullback.of_hasPullback p U.1.ι).flip.paste_vert hp
    exact OpenImmersionProductSquare.isIso_app_smallEtalePullbackAb_id_obj _ F
      ((derivedBaseChangeHolds_iff _ n).1 (H U) r s (pullback.snd p U.1.ι) _ hpU g
        (pullback.fst _ _) (pullback.snd _ _ ≫ e) ((IsPullback.of_hasPullback _ _).paste_vert sq) F
        hF r le_rfl)
  let D : EtaleLocalBaseChangeData Ab.{u + 1} :=
    { X := X', Y := Y, S := S', T := T, f := f', h := h, e := e, g := g, cartesian := sq,
      I := X.affineOpens, U := fun U => pullback p U.1.ι, u := fun U => pullback.fst p U.1.ι,
      cover := hcov, V := fun _ => S', v := fun _ => 𝟙 S', etale_v := fun _ => inferInstance,
      f_i := fun U => pullback.fst p U.1.ι ≫ f', factorization := fun U => by simp,
      Y_i := fun U => pullback (pullback.fst p U.1.ι) h, h_i := fun U => pullback.fst _ _,
      toY_i := fun U => pullback.snd _ _,
      upper_cartesian := fun U => IsPullback.of_hasPullback _ _,
      T_i := fun _ => T, g_i := fun _ => g, toT_i := fun _ => 𝟙 T,
      lower_cartesian := fun _ => IsPullback.id_vert g,
      e_i := fun U => pullback.snd _ _ ≫ e, e_i_compatible := fun U => by simp,
      local_cartesian := fun U => (IsPullback.of_hasPullback _ _).paste_vert sq, F := F }
  exact isIso_higherBaseChangeMapAb_app_of_isIso_local D r hloc

/-! ### Stacks 0F1I -/

/-- **[Stacks, Tag 0F1I] for sheaves annihilated by an integer invertible in `K`.** Let `K` be a
field, `X` a scheme over `K` and `n` an integer invertible in `K`. For every diagram

```
X  ←-p-  X'  ←-h-  Y
|        |f'       |e
Spec K ←- S' ←-g-  T
```

with `X' = X ×_K S'`, `Y = X' ×_{S'} T` and `g` quasi-compact and quasi-separated, and every
abelian sheaf `𝓕` on `T_étale` annihilated by `n`, the base change map
`(f')⁻¹Rg_*𝓕 ⟶ Rh_*e⁻¹𝓕` is an isomorphism.

The question is local on `X` (`derivedBaseChangeHolds_of_affineOpens`), and an affine `X` is
quasi-compact and quasi-separated (`derivedBaseChangeHolds_of_compactSpace`). -/
theorem derivedBaseChangeHolds_of_isUnit (K : Type u) [Field K] (n : ℤ) (hn : IsUnit (n : K))
    {X : Scheme.{u}} (πX : X ⟶ Spec (.of K)) : DerivedBaseChangeHolds πX n :=
  derivedBaseChangeHolds_of_affineOpens πX n fun U => by
    have : IsAffine U.1.toScheme := U.2
    exact derivedBaseChangeHolds_of_compactSpace K (U.1.ι ≫ πX) n hn

/-- **[Stacks, Tag 0F1I].** Let `K` be a field. For any commutative diagram

```
X  ←-p-  X'  ←-h-  Y
|        |f'       |e
Spec K ←-s- S' ←-g- T
```

of schemes over `K` with `X' = X ×_{Spec K} S'` and `Y = X' ×_{S'} T` and `g` quasi-compact and
quasi-separated, and every abelian sheaf `𝓕` on `T_étale` whose stalks are torsion of orders
invertible in `K`, the base change map `(f')⁻¹Rg_*𝓕 ⟶ Rh_*e⁻¹𝓕` is an isomorphism (in
`D⁺(X'_étale)`, `𝓕` placed in degree zero).

`𝓕` is the filtered colimit of its subsheaves `𝓕[n]`, `n` invertible in `K`
(`isIso_higherBaseChangeMapAb_of_forall_annihilated`), and for those this is
`derivedBaseChangeHolds_of_isUnit`. -/
@[stacks 0F1I]
theorem isIso_smallEtaleDerivedBaseChangeAb_of_field (K : Type u) [Field K] {X : Scheme.{u}}
    (πX : X ⟶ Spec (.of K)) {S' X' T Y : Scheme.{u}} (s : S' ⟶ Spec (.of K)) (p : X' ⟶ X)
    (f' : X' ⟶ S') (hp : IsPullback p f' πX s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    (sq : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (𝓕 : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (h𝓕 : ∀ (t : GeometricPoint T) (a : (smallEtaleStalkAb t.hom).obj 𝓕),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : K) ∧ n • a = 0) :
    IsIso ((smallEtaleDerivedBaseChangeAb f' g h e sq.w).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj 𝓕)) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq.flip inferInstance
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq.flip inferInstance
  refine (isIso_smallEtaleDerivedBaseChangeAb_app_single_iff f' g h e sq.w 𝓕).2 fun q => ?_
  refine isIso_higherBaseChangeMapAb_of_forall_annihilated (Spec (.of K)) f' g h e sq.w q
    (fun n hn hu G hG => ?_) 𝓕 fun t a => ?_
  · exact (derivedBaseChangeHolds_iff πX n).1
      (derivedBaseChangeHolds_of_isUnit K n (isUnit_intCast_Γ_Spec_iff.1 hu) πX) q s p f' hp g h
      e sq G hG q le_rfl
  · obtain ⟨n, hn, hu, ha⟩ := h𝓕 t a
    exact ⟨n, hn, isUnit_intCast_Γ_Spec_iff.2 hu, ha⟩

end Stacks.EtaleCohomology.BaseChangeOverField

end
