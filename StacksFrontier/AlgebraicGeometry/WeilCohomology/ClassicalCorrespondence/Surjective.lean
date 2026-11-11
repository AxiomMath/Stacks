module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.Transport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.VarietyComparison
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilRealizationBijection

/-!
# A classical Weil cohomology theory comes from a realization `(G, F[2] ≅ G(𝟏(1)))`

The second paragraph of the proof of Stacks 0FH3. Let `H^*` be a classical Weil cohomology
theory. Its extension to all smooth projective schemes (data (D0)–(D3) with `F(1) = F`) gives the
functor `G : M_k ⥤ graded F-vector spaces` of Stacks 0FH2 / 0FHL, and `G(𝟏(1))` is a line in
degree `-2`. The data (D0)–(D3) of `G` (Stacks 0FHK) are isomorphic to the extension of `H^*`
(Stacks 0FHM); this isomorphism identifies `G(h(X))` with `H^*(X)` for every smooth projective
variety `X` with all its structure, provided `F[2] ≅ G(𝟏(1))` is chosen to match the coordinate
`F(1) = F` under the isomorphism of Tate lines: the trace of `H^*` determines the isomorphism
`F[2] ≅ G(𝟏(1))`, as in the source (where it comes from `∫_{𝐏¹} : H²(𝐏¹) → F`).

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.exists_corresponds`: every classical Weil
  cohomology theory corresponds to a realization `(G, F[2] ≅ G(𝟏(1)))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
  CategoryTheory.GradedCategory
  Stacks.Chow DirectSum
open Stacks.WeilCohomology.ChowMotiveCat (h tate)

universe u v

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

attribute [local instance] WeilRealization.braidedTK WeilRealization.monoidalTK

/-- The isomorphism `F[2] ≅ G(𝟏(1))` of a linear isomorphism `F ≅ G^{-2}(𝟏(1))` sends `1` to the
image of `1`. -/
theorem tateIsoOfLinearEquiv_hom_apply {G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F)}
    (hG : ∀ i, i ≠ -2 → IsZero ((G.obj (tate k 1)) i)) (e : F ≃ₗ[F] (G.obj (tate k 1)) (-2)) :
    ((tateIsoOfLinearEquiv hG e).hom (-2)).hom
      ((GradedObject.singleObjApplyIso (-2) (ModuleCat.of F F)).inv.hom 1) = e 1 := by
  simp only [tateIsoOfLinearEquiv, GradedObject.isoMk_hom, dite_eq_left, Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

namespace ClassicalWeilCohomologyTheory

variable (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

/-- The traces of the extension in coordinates. -/
theorem traceCoord_eq (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (a : T.toWeilData.grade X (2 * (d : ℤ))) :
    T.toWeilData.traceCoord X d hX a =
      (((tateCoordUnit (F := F))⁻¹ ^ (d : ℤ) : Fˣ) : F) * T.extTraceUntw X hX a := by
  set x := (T.toWeilData.twCoord X _ d).symm a
  have hx : a = (((tateCoordUnit (F := F)) ^ (d : ℤ) : Fˣ) : F) • twistCoord _ d x := by
    rw [← tateTwistCoordinates_smulOfUnit, ← tateLineCoordinate_eq]
    exact (LinearEquiv.apply_symm_apply _ a).symm
  change T.extTrace X d hX x = _
  rw [extTrace, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hx,
    Submodule.coe_smul, map_smul, smul_eq_mul, ← mul_assoc, ← Units.val_mul, ← mul_zpow,
    inv_mul_cancel, one_zpow, Units.val_one, one_mul]
  rfl

/-- The realization `G` of the extension (Stacks 0FH2, 0FHL). -/
abbrev weilRealization : WeilRealization k F :=
  T.toWeilDataAxioms.toWeilRealization

/-- **Stacks 0FHM for the extension**: the data of `G` (Stacks 0FHK) are isomorphic to the
extension of `H^*`. -/
theorem exists_dataIso : ∃ ψ : WeilData.Iso T.weilRealization.toWeilData T.toWeilData,
    ψ.PreservesCycleClass ∧ ψ.PreservesTrace :=
  (T.weilRealization.realizes T.weilRealization.poincareDuality T.weilRealization.kunneth
    T.weilRealization.cycleClassAxiom).isIsomorphic T.toWeilDataAxioms.realizes_toWeilRealization

variable {T} (ψ : WeilData.Iso T.weilRealization.toWeilData T.toWeilData)

/-- `H^n(X) ≅ G(h(X))^n` through the isomorphism `ψ` of data. -/
def pieceEquivOf (X : (SmoothProjective k).FullSubcategory) (n : ℤ) :
    (T.H X).piece n ≃ₗ[F] T.weilRealization.toWeilData.grade
      ((SmoothProjective.toSchemeCat k).obj X) n :=
  (T.varietyGradeEquiv X n).symm.trans
    (ψ.gradeEquiv ((SmoothProjective.toSchemeCat k).obj X) n).symm

/-- The scalar `c = u κ` of the coordinates of `F(1) = F` and of `G^{-2}(𝟏(1))` under `ψ`. -/
def scalarOf : Fˣ :=
  tateCoordUnit * ψ.coordRatio⁻¹

/-- **The realization `(G, F[2] ≅ G(𝟏(1)))` of `H^*`**, with the isomorphism `F[2] ≅ G(𝟏(1))`
matched to the coordinate `F(1) = F` through `ψ`. -/
def realizationOf : ClassicalMotiveRealization k F where
  G := T.weilRealization.functor
  braided := T.weilRealization.braided
  additive := T.weilRealization.additive
  linear := T.weilRealization.linear
  tateIso := tateIsoOfLinearEquiv T.weilRealization.tate_degree
    ((LinearEquiv.smulOfUnit (scalarOf ψ)).trans
      (tateLineCoordinate T.weilRealization.finrank_tateLine).symm)
  nonneg X i hi := by
    rw [ModuleCat.isZero_iff_subsingleton]
    have : Subsingleton ((T.H X).piece i) :=
      ⟨fun a b ↦ (T.eq_zero_of_neg X hi a).trans (T.eq_zero_of_neg X hi b).symm⟩
    exact ((pieceEquivOf ψ X i).trans
      ((T.weilRealization.cohAlg _).gradeEquiv i)).symm.toEquiv.subsingleton
  finrank_zero X := ((pieceEquivOf ψ X 0).trans
    ((T.weilRealization.cohAlg _).gradeEquiv 0)).finrank_eq.symm.trans (T.finrank_piece_zero X)

theorem tateScalar_realizationOf : (realizationOf ψ).tateScalar = scalarOf ψ := by
  apply Units.ext
  change tateLineCoordinate _ (((tateIsoOfLinearEquiv T.weilRealization.tate_degree
    ((LinearEquiv.smulOfUnit (scalarOf ψ)).trans
      (tateLineCoordinate T.weilRealization.finrank_tateLine).symm)).hom (-2)).hom
        ((GradedObject.singleObjApplyIso (-2) (ModuleCat.of F F)).inv.hom 1)) = _
  rw [tateIsoOfLinearEquiv_hom_apply, LinearEquiv.trans_apply]
  refine (LinearEquiv.apply_symm_apply (tateLineCoordinate T.weilRealization.finrank_tateLine)
    _).trans ?_
  change ((scalarOf ψ : Fˣ) : F) * 1 = _
  rw [mul_one]

/-- **The isomorphism of `H^*` with the theory of its realization** (the second paragraph of the
proof of Stacks 0FH3): `H^*(X) ≅ G(h(X))` through the isomorphism `ψ` of data, carrying the cycle
classes and traces of `H^*` to `γ(α) = G(a_α)(e_{-r})` and `x ↦ G([X])(x ⊗ e_d)`. -/
def isoOf (hγ : ψ.PreservesCycleClass) (htr : ψ.PreservesTrace) :
    Iso T (realizationOf ψ).toClassicalWeilCohomologyTheory where
  equiv X n := pieceEquivOf ψ X n
  equiv_pullback {X Y} f n a := by
    apply (ψ.gradeEquiv _ n).injective
    change ψ.gradeEquiv _ n ((ψ.gradeEquiv _ n).symm ((T.varietyGradeEquiv X n).symm
      (T.pullback f n a))) = ψ.gradeEquiv _ n (T.weilRealization.toWeilData.pullDeg
        ((SmoothProjective.toSchemeCat k).map f) n
        ((ψ.gradeEquiv _ n).symm ((T.varietyGradeEquiv Y n).symm a)))
    rw [LinearEquiv.apply_symm_apply, ψ.gradeEquiv_pullDeg, LinearEquiv.apply_symm_apply]
    apply (T.varietyGradeEquiv X n).injective
    rw [LinearEquiv.apply_symm_apply, T.varietyGradeEquiv_pullDeg]
    exact congrArg _ (LinearEquiv.apply_symm_apply _ a).symm
  equiv_one X := by
    have h1 : (T.varietyGradeEquiv X 0).symm (T.H X).one = ⟨1, SetLike.GradedOne.one_mem⟩ := by
      apply (T.varietyGradeEquiv X 0).injective
      rw [LinearEquiv.apply_symm_apply, T.varietyGradeEquiv_one]
    change (ψ.gradeEquiv _ 0).symm ((T.varietyGradeEquiv X 0).symm (T.H X).one) = _
    rw [h1]
    apply (ψ.gradeEquiv _ 0).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext (map_one (ψ.equiv _)).symm
  equiv_mul X i j a b := by
    apply (ψ.gradeEquiv _ (i + j)).injective
    apply (T.varietyGradeEquiv X (i + j)).injective
    change T.varietyGradeEquiv X (i + j) (ψ.gradeEquiv _ (i + j) ((ψ.gradeEquiv _ (i + j)).symm
      ((T.varietyGradeEquiv X (i + j)).symm ((T.H X).mul i j a b)))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have hc : ψ.gradeEquiv _ (i + j)
        ⟨((pieceEquivOf ψ X i a : _) : T.weilRealization.toWeilData.H _) *
        ((pieceEquivOf ψ X j b : _) : T.weilRealization.toWeilData.H _),
          SetLike.GradedMul.mul_mem (pieceEquivOf ψ X i a).2 (pieceEquivOf ψ X j b).2⟩ =
        T.toWeilData.cup _ i j (i + j) rfl (ψ.gradeEquiv _ i (pieceEquivOf ψ X i a))
          (ψ.gradeEquiv _ j (pieceEquivOf ψ X j b)) :=
      Subtype.ext (map_mul (ψ.equiv _) _ _)
    refine Eq.trans ?_ (congrArg (T.varietyGradeEquiv X (i + j)) hc).symm
    rw [T.varietyGradeEquiv_cup]
    simp only [pieceEquivOf, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  equiv_cycleClass X r α := by
    obtain ⟨α, rfl⟩ : ∃ α' : codimensionChowGroup k
        ((SmoothProjective.toSchemeCat k).obj X).obj.hom r, α' = α := ⟨α, rfl⟩
    change (ψ.gradeEquiv _ (2 * r)).symm ((T.varietyGradeEquiv X (2 * r)).symm
      (T.cycleClass X r α)) = ((((realizationOf ψ).tateScalar ^ (-r) : Fˣ) : F) •
        T.weilRealization.toWeilData.cycleClassCoord _ r α)
    rw [tateScalar_realizationOf]
    have h1' : (⟨T.extCycleClassUntw _ r α, T.extCycleClassUntw_mem _ r α⟩ :
        T.extGrade ((SmoothProjective.toSchemeCat k).obj X) (2 * r)) =
        (((tateCoordUnit (F := F)) ^ (-r) : Fˣ) : F) • T.toWeilData.cycleClassCoord _ r α := by
      apply Subtype.ext
      rw [SetLike.val_smul, coe_cycleClassCoord, smul_smul, ← Units.val_mul, ← zpow_add,
        neg_add_cancel, zpow_zero, Units.val_one, one_smul]
    have h1 : (T.varietyGradeEquiv X (2 * r)).symm (T.cycleClass X r α) =
        (((tateCoordUnit (F := F)) ^ (-r) : Fˣ) : F) •
          T.toWeilData.cycleClassCoord _ r α := by
      rw [← h1']
      exact (LinearEquiv.symm_apply_eq _).2 (T.varietyGradeEquiv_extCycleClassUntw X r α).symm
    have h2 : (ψ.gradeEquiv _ (2 * r)).symm (T.toWeilData.cycleClassCoord _ r α) =
        ((ψ.coordRatio ^ r : Fˣ) : F) • T.weilRealization.toWeilData.cycleClassCoord _ r α := by
      apply (ψ.gradeEquiv _ (2 * r)).injective
      rw [LinearEquiv.apply_symm_apply, map_smul, ψ.gradeEquiv_cycleClassCoord hγ, smul_smul,
        ← Units.val_mul, ← mul_zpow, mul_inv_cancel, one_zpow, Units.val_one, one_smul]
    have hs : (scalarOf ψ) ^ (-r) = tateCoordUnit ^ (-r) * ψ.coordRatio ^ r := by
      rw [scalarOf, mul_zpow, inv_zpow', neg_neg]
    rw [h1, map_smul, h2, smul_smul, ← Units.val_mul, hs]
  integration_equiv X a := by
    have hX := SmoothProjective.isNonemptyEquidimensional X (T.dimension_eq X)
    have key := ψ.traceCoord_gradeEquiv htr _ (T.dimension X) hX
      ((ψ.gradeEquiv _ _).symm ((T.varietyGradeEquiv X _).symm a))
    rw [LinearEquiv.apply_symm_apply, traceCoord_eq, extTraceUntw_eq_integration _ X hX,
      LinearEquiv.apply_symm_apply] at key
    have hdim : (realizationOf ψ).toClassicalWeilCohomologyTheory.dimension X = T.dimension X :=
      dimension_eq_dimension _ T X
    have hgen : ∀ (e e' : ℕ) (he : e = T.dimension X) (he' : e' = T.dimension X)
        (hX' : IsNonemptyEquidimensional ((SmoothProjective.toSchemeCat k).obj X) e')
        (z : T.weilRealization.toWeilData.grade ((SmoothProjective.toSchemeCat k).obj X)
          (2 * (T.dimension X : ℤ))),
        (((scalarOf ψ) ^ (e : ℤ) : Fˣ) : F) * T.weilRealization.toWeilData.traceCoord _ e'
          hX' (ExternallyGraded.degreeCast (R := F)
            (X := fun n ↦ T.weilRealization.toWeilData.grade
              ((SmoothProjective.toSchemeCat k).obj X) n)
            (by rw [he']) z) =
        (((scalarOf ψ) ^ (T.dimension X : ℤ) : Fˣ) : F) *
          T.weilRealization.toWeilData.traceCoord _ (T.dimension X) hX z := by
      rintro e e' rfl rfl hX' z
      rfl
    have hu : scalarOf ψ * ψ.coordRatio * tateCoordUnit⁻¹ = 1 := by
      simp [scalarOf]
    have hk : ((ψ.coordRatio ^ (T.dimension X : ℤ) : Fˣ) : F) *
        ((((tateCoordUnit (F := F))⁻¹ ^ (T.dimension X : ℤ) : Fˣ) : F) * T.integration X a) =
        T.weilRealization.toWeilData.traceCoord _ (T.dimension X) hX
          ((ψ.gradeEquiv _ _).symm ((T.varietyGradeEquiv X _).symm a)) := by
      rw [key, ← mul_assoc, ← Units.val_mul, ← mul_zpow, mul_inv_cancel, one_zpow,
        Units.val_one, one_mul]
    change (((realizationOf ψ).tateScalar ^
        ((realizationOf ψ).toClassicalWeilCohomologyTheory.dimension X : ℤ) : Fˣ) : F) *
      T.weilRealization.toWeilData.traceCoord _ _
        (SmoothProjective.isNonemptyEquidimensional_dim X) (ExternallyGraded.degreeCast (R := F)
          (X := fun n ↦ T.weilRealization.toWeilData.grade
            ((SmoothProjective.toSchemeCat k).obj X) n)
          (congrArg (fun d : ℕ ↦ 2 * (d : ℤ)) hdim).symm
            ((ψ.gradeEquiv _ _).symm ((T.varietyGradeEquiv X _).symm a))) = _
    rw [tateScalar_realizationOf]
    refine (hgen _ _ hdim hdim _ _).trans ?_
    rw [← hk, ← mul_assoc, ← mul_assoc, ← Units.val_mul,
      ← Units.val_mul, ← mul_zpow, ← mul_zpow, hu, one_zpow, Units.val_one, one_mul]

/-- **Every classical Weil cohomology theory corresponds to a realization**
`(G, F[2] ≅ G(𝟏(1)))` (the second paragraph of the proof of Stacks 0FH3). -/
theorem exists_corresponds (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F) :
    ∃ R : ClassicalMotiveRealization k F, T.Corresponds R := by
  obtain ⟨ψ, hγ, htr⟩ := T.exists_dataIso
  exact ⟨realizationOf ψ, (realizationOf ψ).corresponds_toClassicalWeilCohomologyTheory.of_iso
    (isoOf ψ hγ htr).symm⟩

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
