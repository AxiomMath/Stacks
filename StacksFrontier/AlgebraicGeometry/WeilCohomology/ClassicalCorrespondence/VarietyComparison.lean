module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.Iso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.Variety
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFunctoriality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataIsoOfGraded
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataIsoTransport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassExteriorProduct

/-!
# The extension of a classical Weil cohomology theory on varieties, with its structure

A classical Weil cohomology theory `H^*` extends to data (D0)–(D3) satisfying (A), (B), (C) on all
smooth projective schemes (`ClassicalWeilCohomologyTheory.toWeilDataAxioms`, the first step of
Stacks 0FH2), with `H^*(X) = ∏_i H^*(X_i)` over the components. On a smooth projective variety
`V`, whose unique component `V_0` is isomorphic to `V`, the extended cohomology is `H^*(V)`
(`ClassicalWeilCohomologyTheory.varietyGradeEquiv`). This file shows that this identification
carries the cycle classes and the trace of the extension, read in a coordinate of the Tate line
`F(1) = F`, to those of `H^*`:

* `γ([V]) = 1` (from Stacks 0FHF for the extension and Gysin pullback along `V ≅ V_0`), so by
  the axiom (C)(b) for the isomorphism `V_0 ≅ V` the trace is invariant: `∫_{V_0} φ^* = ∫_V`;
* in the coordinate `u` of `F(1) = F`, `γ_coord = uʳ γ` and `∫_coord = u^{-d} ∫`.

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.cycleClass_fundamental`: `γ([V]) = 1`.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.integration_pullback_compIso`.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.varietyGradeEquiv_cycleClassCoord`,
  `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.traceCoord_eq_integration`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum Stacks.Chow

universe u v

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace ClassicalWeilCohomologyTheory

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

open SmoothProjective

omit [IsAlgClosed k] in
/-- The isomorphism of a component of a variety with the variety is its inclusion. -/
theorem toSchemeCat_map_compIso_hom (V : (SmoothProjective k).FullSubcategory)
    (i : Idx ((toSchemeCat k).obj V)) :
    (toSchemeCat k).map (compIso V i).hom = compAtι ((toSchemeCat k).obj V) i :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (compIso_hom_left V i))

/-- The restriction of a cycle class of `V` to its component, pulled back along `V ≅ V_0`, is the
class itself. -/
theorem gysin_compIso_inv_restrictChow (V : (SmoothProjective k).FullSubcategory)
    (i : Idx ((toSchemeCat k).obj V)) (r : ℤ)
    (β : codimensionChowGroup k ((toSchemeCat k).obj V).obj.hom r) :
    (chowCycleData k).gysin (compIso V i).inv r (restrictChow ((toSchemeCat k).obj V) i r β) =
      β := by
  have hcomp : ((toSchemeCat k).map (compIso V i).inv ≫
      compAtι ((toSchemeCat k).obj V) i).hom.left = 𝟙 _ := by
    rw [← toSchemeCat_map_compIso_hom, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    rfl
  change codimensionGysin _ _ _ r (codimensionGysin _ _ _ r _) = _
  rw [← codimensionGysin_comp]
  exact (codimensionGysin_congr _ _ hcomp _ (Category.id_comp _) r _).trans
    (codimensionGysin_id _ r β)

/-- The coordinate of `F(1) = F` used by the data (D0)–(D3), a unit. -/
def tateCoordUnit : Fˣ :=
  Units.mk0 (tateLineCoordinate (Module.finrank_self F) 1) (by simp)

omit [IsAlgClosed k] [CharZero F] in
theorem tateLineCoordinate_eq :
    tateLineCoordinate (Module.finrank_self F) =
      (LinearEquiv.refl F F).trans (LinearEquiv.smulOfUnit (tateCoordUnit (F := F))) := by
  ext x
  change _ = (tateLineCoordinate (Module.finrank_self F) 1) • x
  rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- The cycle classes of the extension in coordinates. -/
theorem coe_cycleClassCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ)
    (α : codimensionChowGroup k X.obj.hom r) :
    (T.toWeilData.cycleClassCoord X r α : T.extH X) =
      (((tateCoordUnit (F := F)) ^ r : Fˣ) : F) • T.extCycleClassUntw X r α := by
  rw [WeilData.cycleClassCoord_apply]
  change ((tateTwistCoordinates (tateLineCoordinate (Module.finrank_self F)) r)
    ((twistCoord _ r).symm (⟨T.extCycleClassUntw X r α, T.extCycleClassUntw_mem X r α⟩ :
      T.extGrade X (2 * r))) : T.extH X) = _
  rw [tateLineCoordinate_eq, tateTwistCoordinates_smulOfUnit, LinearEquiv.apply_symm_apply]

/-- **`γ([V]) = 1`** for a classical Weil cohomology theory: by Stacks 0FHF for the extension of
`H^*` to smooth projective schemes, on the component `V_0` of `V`, and axiom (C)(a) for the
isomorphism `V ≅ V_0`. -/
theorem cycleClass_fundamental (V : (SmoothProjective k).FullSubcategory) :
    T.cycleClass V 0 ((chowCycleData k).fundamental V) =
      ExternallyGraded.degreeCast (R := F) (X := (T.H V).piece) (by norm_num) (T.H V).one := by
  set X := (toSchemeCat k).obj V
  set i : Idx X := default
  have h1 := WeilData.coe_cycleClassCoord_fundamentalClass (W := T.toWeilData)
    T.toWeilData_kunneth.kunnethIsomorphism T.cycleClassAxiom.pullback T.cycleClassAxiom.mul
    T.cycleClassAxiom.point X
  have h2 : (T.toWeilData.cycleClassCoord X 0 (fundamentalClass X) : T.extH X) =
      T.extCycleClassUntw X 0 (fundamentalClass X) := by
    rw [coe_cycleClassCoord, zpow_zero, Units.val_one, one_smul]
  rw [h2] at h1
  have h3 := congrFun h1 i
  rw [extCycleClassUntw_apply, Pi.one_apply, ExternallyGradedAlgebra.one_eq_of,
    ← lof_eq_of F] at h3
  have h4 : T.cycleClass (compAt X i) 0 (restrictChow X i 0 (fundamentalClass X)) =
      ExternallyGraded.degreeCast (R := F) (X := (T.H (compAt X i)).piece) (by norm_num)
        (T.H (compAt X i)).one :=
    DFinsupp.single_injective h3
  change T.cycleClass V 0 (fundamentalClass X) = _
  rw [← gysin_compIso_inv_restrictChow V i 0 (fundamentalClass X)]
  refine (T.cycleClass_gysin (compIso V i).inv 0 _).trans ?_
  rw [h4, Iso.degreeCast_naturality (fun n ↦ T.pullback (compIso V i).inv n), T.pullback_one]

/-- On a variety, the extended cycle class of `α` is the cycle class of `α`. -/
theorem varietyGradeEquiv_extCycleClassUntw (V : (SmoothProjective k).FullSubcategory) (r : ℤ)
    (α : codimensionChowGroup k ((toSchemeCat k).obj V).obj.hom r) :
    T.varietyGradeEquiv V (2 * r) ⟨T.extCycleClassUntw _ r α, T.extCycleClassUntw_mem _ r α⟩ =
      T.cycleClass V r α := by
  apply DFinsupp.single_injective (i := 2 * r)
  change lof F ℤ _ (2 * r) _ = lof F ℤ _ (2 * r) _
  rw [varietyGradeEquiv_apply, varietyEquiv_apply _ _ _ default]
  change T.pullTotal _ (T.extCycleClassUntw _ r α default) = _
  rw [extCycleClassUntw_apply, pullTotal_lof]
  congr 1
  exact (T.cycleClass_gysin _ r _).symm.trans
    (congrArg _ (gysin_compIso_inv_restrictChow V default r α))

/-- A product with a class equal to the unit, read in the expected degree, is the class. -/
theorem _root_.ExternallyGradedAlgebra.degreeCast_mul_eq_of_heq_one
    (A : ExternallyGradedAlgebra.{v, v} F) {i j n : ℤ} (h : i + j = n) (h' : i = n)
    (x : A.piece i) {z : A.piece j} (hz : z ≍ A.one) :
    ExternallyGraded.degreeCast (R := F) (X := A.piece) h (A.mul i j x z) =
      ExternallyGraded.degreeCast (R := F) (X := A.piece) h' x := by
  have hj : j = 0 := by omega
  subst hj
  obtain rfl := eq_of_heq hz
  exact eq_of_heq ((ExternallyGraded.degreeCast_heq _ _).trans ((A.mul_one i x).trans
    (ExternallyGraded.degreeCast_heq _ _).symm))

/-- The cycle class of a class heterogeneously equal to the fundamental class is the unit. -/
theorem cycleClass_heq_one (V : (SmoothProjective k).FullSubcategory) {r : ℤ} (hr : r = 0)
    {α : (chowCycleData k).group V r} (hα : α ≍ (chowCycleData k).fundamental V) :
    T.cycleClass V r α ≍ (T.H V).one := by
  subst hr
  obtain rfl := eq_of_heq hα
  rw [cycleClass_fundamental]
  exact ExternallyGraded.degreeCast_heq _ _

/-- The pushforward of the fundamental class along an isomorphism of varieties is the fundamental
class. -/
theorem pushforward_fundamental_heq {V C : (SmoothProjective k).FullSubcategory} (f : V ≅ C)
    (hd : T.dimension V = T.dimension C) :
    (chowCycleData k).pushforward f.hom (T.dimension V) (T.dimension C) (T.dimension_eq V)
      (T.dimension_eq C) 0 ((chowCycleData k).fundamental V) ≍
      (chowCycleData k).fundamental C := by
  have hV := SmoothProjective.isNonemptyEquidimensional V (T.dimension_eq V)
  have hC := SmoothProjective.isNonemptyEquidimensional C (T.dimension_eq C)
  have : IsIso ((toSchemeCat k).map f.hom).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (((toSchemeCat k) ⋙
      ObjectProperty.ι _).map f.hom)))
  change equidimensionalPushforward ((toSchemeCat k).map f.hom) _ _ 0 _ rfl
    (fundamentalClass _) ≍ fundamentalClass _
  rw [equidimensionalPushforward_fundamentalClass _ hV hC]
  have key : ∀ (c : ℤ) (hc : c = 0), closedSubschemeClass ((toSchemeCat k).obj C).obj.hom
      ((toSchemeCat k).map f.hom).hom.left c ≍ closedSubschemeClass
        ((toSchemeCat k).obj C).obj.hom ((toSchemeCat k).map f.hom).hom.left 0 := by
    rintro c rfl
    rfl
  exact (key _ (by omega)).trans
    (heq_of_eq (WeilData.closedSubschemeClass_of_isIso _ hC.relativeDimension))

/-- Pullback along `f` of classes heterogeneously equal in equal degrees. -/
theorem pullback_heq {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) {i j : ℤ}
    (h : i = j) {a : (T.H Y).piece i} {b : (T.H Y).piece j} (hab : a ≍ b) :
    T.pullback f i a ≍ T.pullback f j b := by
  subst h
  cases hab
  rfl

/-- **The trace is invariant under isomorphisms of varieties**: `∫_V f^*b = ∫_C b` for
`f : V ≅ C`, by axiom (C)(b) for `f` and the fundamental class, and `γ([V]) = 1`. -/
theorem integration_pullback_iso {V C : (SmoothProjective k).FullSubcategory} (f : V ≅ C)
    (hd : T.dimension V = T.dimension C) (b : (T.H C).piece (2 * (T.dimension C : ℤ))) :
    T.integration V (ExternallyGraded.degreeCast (R := F) (X := (T.H V).piece) (by rw [hd])
      (T.pullback f.hom _ b)) = T.integration C b := by
  set b' := ExternallyGraded.degreeCast (R := F) (X := (T.H C).piece)
    (show 2 * (T.dimension C : ℤ) = 2 * (T.dimension V : ℤ) - 2 * 0 by rw [hd]; ring) b
  have key := T.integration_pullback_mul_cycleClass f.hom 0 ((chowCycleData k).fundamental V) b'
  simp only [ExternallyGradedAlgebra.tracePairing, LinearMap.compr₂_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe] at key
  rw [ExternallyGradedAlgebra.degreeCast_mul_eq_of_heq_one _ _ (by omega) _
      ((ExternallyGraded.degreeCast_heq _ _).trans (T.cycleClass_heq_one V rfl HEq.rfl)),
    ExternallyGradedAlgebra.degreeCast_mul_eq_of_heq_one _ _ (by rw [hd]; ring) _
      ((ExternallyGraded.degreeCast_heq _ _).trans
        (T.cycleClass_heq_one C (by omega) (T.pushforward_fundamental_heq f hd)))] at key
  refine Eq.trans (congrArg _ ?_) (key.trans (congrArg _ ?_))
  · exact eq_of_heq ((ExternallyGraded.degreeCast_heq _ _).trans
      ((T.pullback_heq f.hom (by rw [hd]; ring) (ExternallyGraded.degreeCast_heq _ b).symm).trans
        (ExternallyGraded.degreeCast_heq _ _).symm))
  · simp only [b', Iso.degreeCast_degreeCast, Iso.degreeCast_rfl]

/-- **On a variety, the extended trace is the trace.** -/
theorem extTraceUntw_eq_integration (V : (SmoothProjective k).FullSubcategory)
    (hX : IsNonemptyEquidimensional ((toSchemeCat k).obj V) (T.dimension V))
    (y : T.extGrade ((toSchemeCat k).obj V) (2 * (T.dimension V : ℤ))) :
    T.extTraceUntw _ hX y = T.integration V (T.varietyGradeEquiv V _ y) := by
  have hd := T.dimension_compAt hX (@default (Idx ((toSchemeCat k).obj V)) Unique.instInhabited)
  rw [extTraceUntw_apply, Fintype.sum_unique]
  obtain ⟨b, hb⟩ := ((T.H (compAt _
      (@default (Idx ((toSchemeCat k).obj V)) Unique.instInhabited))).mem_grade_iff _).1
    (T.mem_extGrade.1 y.2 (@default (Idx ((toSchemeCat k).obj V)) Unique.instInhabited))
  have hvar : T.varietyGradeEquiv V _ y = T.pullback
      (compIso V (@default (Idx ((toSchemeCat k).obj V)) Unique.instInhabited)).inv _ b := by
    apply DFinsupp.single_injective (i := 2 * (T.dimension V : ℤ))
    change lof F ℤ _ _ _ = lof F ℤ _ _ _
    rw [varietyGradeEquiv_apply,
      varietyEquiv_apply _ _ _ (@default (Idx ((toSchemeCat k).obj V)) Unique.instInhabited), hb,
      ← lof_eq_of F, pullTotal_lof]
  have hc : component F ℤ (T.H (compAt ((toSchemeCat k).obj V)
      (@default (Idx ((toSchemeCat k).obj V)) Unique.instInhabited))).piece
      (2 * (T.dimension V : ℤ)) ((y : T.extH ((toSchemeCat k).obj V))
        (@default (Idx ((toSchemeCat k).obj V)) Unique.instInhabited)) = b := by
    rw [hb, ← lof_eq_of F, component.lof_self]
  have key := T.integration_pullback_iso
    (compIso V (@default (Idx ((toSchemeCat k).obj V)) Unique.instInhabited)).symm hd.symm
    (ExternallyGraded.degreeCast (R := F) (X := (T.H (compAt _
      (@default (Idx ((toSchemeCat k).obj V)) Unique.instInhabited))).piece)
      (by rw [hd]) b)
  refine Eq.trans (congrArg _ (congrArg _ hc)) (key.symm.trans (congrArg _ ?_))
  rw [hvar, Iso.symm_hom, Iso.degreeCast_naturality (fun n ↦ T.pullback
      (compIso V (@default (Idx ((toSchemeCat k).obj V)) Unique.instInhabited)).inv n),
    Iso.degreeCast_degreeCast, Iso.degreeCast_rfl]

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
