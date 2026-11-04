/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePowerSection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.GraphFibreDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPointGroup

/-!
# Degrees on `C^1` and on `C`

For a smooth proper curve `C` over an algebraically closed field `k`, the first coordinate
`e : C^1 = C ×_k Spec k ⟶ C` is an isomorphism over `k`. This file transports degrees along it:

* `Stacks.CurvePower.curveDeg_schemePullbackClass_coord`: `deg_{C^1} e^* A = deg_C A`;
* `Stacks.CurvePower.schemePullbackClass_powerTwoIso_diagonal`: the diagonal class of `C^2` is the
  pullback of `[𝒪(Δ_C)]` along the isomorphism `C^2 ≅ C ×_k C`;
* `Stacks.CurvePower.curveDeg_graph_diagClass`: `(φ, 1)^* Δ` has degree `V(φ)` on `C^1`;
* `Stacks.CurvePower.curveDeg_graph_pointClass`: `φ^*[c]` has degree `deg φ` on `C^1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open AlgebraicGeometry

universe u

namespace Stacks.CurvePower

/-- **The ideal of a closed immersion pulled back along an isomorphism** `e` is the ideal of
`i ≫ e⁻¹`. -/
theorem comap_ker_of_isIso {Z Y Y' : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (e : Y' ⟶ Y)
    [IsIso e] : i.ker.comap e = (i ≫ inv e).ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i e]
  have h : pullback.fst e i = pullback.snd e i ≫ i ≫ inv e := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [h, Scheme.Hom.ker_comp_of_isIso]

/-- **The degree of a line bundle is unchanged by pullback along an isomorphism of curves.** -/
theorem picardDegree_schemePullbackClass_of_isIso {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k)) (fZ : Z ⟶ Spec (.of k)) [IsCurve k fY] [IsProper fY] [IsCurve k fZ]
    [IsProper fZ] (hY : topologicalKrullDim Y ≤ 1) (hZ : topologicalKrullDim Z ≤ 1) (e : Y ⟶ Z)
    [IsIso e] (he : e ≫ fZ = fY) (A : Stacks.Picard.ofScheme Z) :
    picardDegree k fY hY (Stacks.GluePicard.picardModelAddEquiv Y.toRingedSpace
        (Stacks.Picard.schemePullbackClass e A)) =
      picardDegree k fZ hZ (Stacks.GluePicard.picardModelAddEquiv Z.toRingedSpace A) := by
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have hsq : IsPullback e fY fZ (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [hid]
    exact IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  exact Stacks.PicardCurve.picardDegree_schemePullbackClass_of_isPullback hsq hZ hY A

variable {k : Type u} [Field k] [IsAlgClosed k] (C : Over (Spec (.of k))) [IsCurve k C.hom]
  [Smooth C.hom] [IsProper C.hom]

attribute [local instance] smoothOfRelativeDimension_one_of_isCurve

omit [IsAlgClosed k] [Smooth C.hom] [IsProper C.hom] in
/-- A curve has dimension one. -/
theorem topologicalKrullDim_left_eq_one : topologicalKrullDim C.left = 1 :=
  IsCurve.topologicalKrullDim_eq_one (f := C.hom)

omit [IsAlgClosed k] [Smooth C.hom] [IsProper C.hom] in
/-- A curve has dimension at most one. -/
theorem topologicalKrullDim_left_le_one : topologicalKrullDim C.left ≤ 1 :=
  (topologicalKrullDim_left_eq_one C).le

/-- The coordinate `C^1 ⟶ C` is an isomorphism. -/
instance isIso_coord_one : IsIso (coord C 1 0) :=
  ⟨lift 1 (fun _ => 𝟙 C), hom_ext 1 fun i => by
      fin_cases i
      exact (Category.assoc _ _ _).trans ((congrArg _ (lift_coord (C := C) 1 _ 0)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)),
    lift_coord (C := C) 1 _ 0⟩

/-- The underlying morphism of schemes of the coordinate `C^1 ⟶ C` is an isomorphism. -/
instance isIso_coord_one_left : IsIso (coord C 1 0).left :=
  inferInstanceAs (IsIso ((Over.forget _).map (coord C 1 0)))

omit [Smooth C.hom] in
/-- **Degrees on `C^1` are degrees on `C`.** -/
theorem curveDeg_schemePullbackClass_coord (A : Stacks.Picard.ofScheme C.left) :
    curveDeg C (topologicalKrullDim_left_eq_one C)
        (Stacks.Picard.schemePullbackClass (coord C 1 0).left A) =
      picardDegree k C.hom (topologicalKrullDim_left_le_one C)
        (Stacks.GluePicard.picardModelAddEquiv C.left.toRingedSpace A) := by
  have := isCurve_power_one C (topologicalKrullDim_left_eq_one C)
  rw [curveDeg_eq_picardDegree]
  exact picardDegree_schemePullbackClass_of_isIso _ _ _ _ (coord C 1 0).left (Over.w _) A

/-- The isomorphism `C^2 ≅ C ×_k C`. -/
abbrev powerTwoIso : (power C 2).left ⟶ pullback C.hom C.hom :=
  pullback.map C.hom (power C 1).hom C.hom C.hom (𝟙 _) (coord C 1 0).left (𝟙 _)
    (by simp) (by rw [Category.comp_id]; exact Over.w (coord C 1 0))

/-- `powerTwoIso C` is an isomorphism. -/
instance isIso_powerTwoIso : IsIso (powerTwoIso C) := by
  have hw : inv (coord C 1 0).left ≫ (power C 1).hom = C.hom ≫ 𝟙 _ := by
    rw [IsIso.inv_comp_eq, Category.comp_id]
    exact (Over.w (coord C 1 0)).symm
  refine ⟨pullback.map C.hom C.hom C.hom (power C 1).hom (𝟙 _) (inv (coord C 1 0).left) (𝟙 _)
    (by simp) hw.symm, ?_, ?_⟩ <;> apply pullback.hom_ext <;> simp [powerTwoIso]

omit [IsAlgClosed k] [IsCurve k C.hom] [Smooth C.hom] [IsProper C.hom] in
/-- The first projection of `powerTwoIso C` is the first projection of `C^2`. -/
theorem powerTwoIso_fst :
    powerTwoIso C ≫ pullback.fst C.hom C.hom = pullback.fst C.hom (power C 1).hom := by
  simp [powerTwoIso]

omit [IsAlgClosed k] [IsCurve k C.hom] [Smooth C.hom] [IsProper C.hom] in
/-- The second projection of `powerTwoIso C` is the second projection of `C^2` followed by the
coordinate `C^1 ⟶ C`. -/
theorem powerTwoIso_snd :
    powerTwoIso C ≫ pullback.snd C.hom C.hom =
      pullback.snd C.hom (power C 1).hom ≫ (coord C 1 0).left := by
  simp [powerTwoIso]

omit [IsAlgClosed k] [IsCurve k C.hom] [Smooth C.hom] [IsProper C.hom] in
/-- `doubleFirst C 0` followed by `powerTwoIso C` is the coordinate `C^1 ⟶ C` followed by the
diagonal of `C`. -/
theorem doubleFirst_comp_powerTwoIso :
    (doubleFirst C 0).left ≫ powerTwoIso C =
      (coord C 1 0).left ≫
        AlgebraicGeometry.CurveGraph.graph C.hom (𝟙 C.left) (Category.id_comp _) := by
  apply pullback.hom_ext
  · rw [Category.assoc, powerTwoIso_fst, Category.assoc, CurveGraph.graph_fst, Category.comp_id]
    exact congrArg Over.Hom.left (lift_coord (C := C) 2 (Fin.cons (coord C 1 0) (coord C 1)) 0)
  · rw [Category.assoc, powerTwoIso_snd, Category.assoc, CurveGraph.graph_snd, Category.comp_id]
    exact congrArg Over.Hom.left (lift_coord (C := C) 2 (Fin.cons (coord C 1 0) (coord C 1)) 1)

/-- The pullback of `[𝒪(D)]` is `[𝒪(D')]` when the pullback of `D` along `f` is the divisor `D'`. -/
private theorem schemePullbackClass_picardClass_of_comap_eq {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)
    (D : Y.IdealSheafData) (D' : Y'.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [Stacks.Divisors.IsEffectiveCartierDivisor D'] (h : D.comap f = D') :
    Stacks.Picard.schemePullbackClass f (Stacks.Divisors.picardClass D) =
      Stacks.Divisors.picardClass D' := by
  have : Stacks.Divisors.IsPullbackDefined f D :=
    (congrArg Stacks.Divisors.IsEffectiveCartierDivisor h).mpr ‹_›
  exact (Stacks.Divisors.schemePullbackClass_picardClass _ _).trans (picardClass_congr h)

omit [IsAlgClosed k] [IsProper C.hom] in
/-- **The diagonal class of `C^2` is the pullback of `[𝒪(Δ_C)]`.** -/
theorem schemePullbackClass_powerTwoIso_diagonal :
    Stacks.Picard.schemePullbackClass (powerTwoIso C)
        (Stacks.Divisors.picardClass (CurveGraph.diagonalDivisor C.hom)) = diagClass C := by
  have hD : (CurveGraph.diagonalDivisor C.hom).comap (powerTwoIso C) =
      Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0) := by
    rw [CurveGraph.diagonalDivisor, CurveGraph.graphDivisor, comap_ker_of_isIso,
      Stacks.Hilbert.pointIdeal, pointGraph_eq_lift]
    have h : CurveGraph.graph C.hom (𝟙 C.left) (Category.id_comp _) ≫ inv (powerTwoIso C) =
        inv (coord C 1 0).left ≫ (doubleFirst C 0).left := by
      rw [IsIso.comp_inv_eq, Category.assoc, doubleFirst_comp_powerTwoIso, IsIso.inv_hom_id_assoc]
    rw [h, Scheme.Hom.ker_comp_of_isIso]
    rfl
  exact @schemePullbackClass_picardClass_of_comap_eq _ _ _ _ _ _
    (isEffectiveCartierDivisor_graph C 1 _) hD

omit [IsAlgClosed k] [IsProper C.hom] in
/-- **The diagonal of `C ×_k C` is symmetric.** -/
theorem schemePullbackClass_braid_diagonal :
    Stacks.Picard.schemePullbackClass (pullback.lift (pullback.snd C.hom C.hom)
        (pullback.fst C.hom C.hom) pullback.condition.symm)
        (Stacks.Divisors.picardClass (CurveGraph.diagonalDivisor C.hom)) =
      Stacks.Divisors.picardClass (CurveGraph.diagonalDivisor C.hom) := by
  set s := pullback.lift (pullback.snd C.hom C.hom) (pullback.fst C.hom C.hom)
    pullback.condition.symm
  have hss : s ≫ s = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp]
  have : IsIso s := ⟨s, hss, hss⟩
  have hD : (CurveGraph.diagonalDivisor C.hom).comap s = CurveGraph.diagonalDivisor C.hom := by
    refine ker_comap_of_comp_eq _ _ ?_
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, CurveGraph.graph_snd, CurveGraph.graph_fst]
    · rw [Category.assoc, pullback.lift_snd, CurveGraph.graph_fst, CurveGraph.graph_snd]
  exact schemePullbackClass_picardClass_of_comap_eq _ _ _ hD

variable (φ : C.left ⟶ C.left) (w : φ ≫ C.hom = C.hom)

/-- **`(φ, 1)^* Δ` has degree `V(φ)`** on `C^1`. -/
theorem curveDeg_graph_diagClass :
    curveDeg C (topologicalKrullDim_left_eq_one C)
        (Stacks.Picard.schemePullbackClass
          (lift 2 (Fin.cons (coord C 1 0 ≫ Over.homMk φ w) fun _ => coord C 1 0)).left
          (diagClass C)) =
      CurveGraph.fixedPointIntersection C.hom (topologicalKrullDim_left_le_one C) φ w := by
  set γ := lift 2 (Fin.cons (coord C 1 0 ≫ Over.homMk φ w) fun _ => coord C 1 0)
  have hγ : γ.left ≫ powerTwoIso C = (coord C 1 0).left ≫ CurveGraph.graph C.hom φ w ≫
      pullback.lift (pullback.snd C.hom C.hom) (pullback.fst C.hom C.hom)
        pullback.condition.symm := by
    apply pullback.hom_ext
    · rw [Category.assoc, powerTwoIso_fst, Category.assoc, Category.assoc, pullback.lift_fst,
        CurveGraph.graph_snd]
      exact congrArg Over.Hom.left (lift_coord (C := C) 2
        (Fin.cons (coord C 1 0 ≫ Over.homMk φ w) fun _ => coord C 1 0) 0)
    · rw [Category.assoc, powerTwoIso_snd, Category.assoc, Category.assoc, pullback.lift_snd,
        CurveGraph.graph_fst, Category.comp_id]
      exact congrArg Over.Hom.left (lift_coord (C := C) 2
        (Fin.cons (coord C 1 0 ≫ Over.homMk φ w) fun _ => coord C 1 0) 1)
  rw [← schemePullbackClass_powerTwoIso_diagonal, Stacks.Picard.schemePullbackClass_comp, hγ,
    ← Stacks.Picard.schemePullbackClass_comp, ← Stacks.Picard.schemePullbackClass_comp,
    schemePullbackClass_braid_diagonal, curveDeg_schemePullbackClass_coord,
    CurveGraph.fixedPointIntersection_eq_picardDegree]

/-- **`φ^*[c]` has degree `deg φ`** on `C^1`. -/
theorem curveDeg_graph_pointClass (c : power C 0 ⟶ C) :
    curveDeg C (topologicalKrullDim_left_eq_one C)
        (Stacks.Picard.schemePullbackClass (lift 1 fun _ => coord C 1 0 ≫ Over.homMk φ w).left
          (pointClass C c)) =
      CurveGraph.curveMapDegree C.hom φ w := by
  set e := (coord C 1 0).left
  set P := Stacks.Picard.schemePullbackClass (inv e) (pointClass C c)
  have hP : Stacks.Picard.schemePullbackClass e P = pointClass C c := by
    rw [Stacks.Picard.schemePullbackClass_comp, IsIso.hom_inv_id,
      Stacks.Picard.schemePullbackClass_id]
  have hφ : (lift 1 fun _ => coord C 1 0 ≫ Over.homMk φ w).left ≫ e = e ≫ φ :=
    congrArg Over.Hom.left (lift_coord (C := C) 1 _ 0)
  have h1 := curveDeg_pointClass C (topologicalKrullDim_left_eq_one C) c
  rw [← hP, curveDeg_schemePullbackClass_coord] at h1
  rw [← hP, Stacks.Picard.schemePullbackClass_comp, hφ, ← Stacks.Picard.schemePullbackClass_comp,
    curveDeg_schemePullbackClass_coord, CurveGraph.picardDegree_schemePullbackClass C.hom _ φ w,
    h1, mul_one]

end Stacks.CurvePower

end
