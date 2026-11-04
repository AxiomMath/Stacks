module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.PoincareDuality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFunctoriality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Axioms (C)(a), (C)(c), (C)(d) for the extension of a classical Weil cohomology theory

For the data (D0)–(D3) obtained from a classical Weil cohomology theory by taking products over
connected components (`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.toWeilData`), the
cycle class map `γ(α) = (γ(α|_{X_c}))_c` is compatible with Gysin pullback, with the
intersection product and with the class of a point, because restriction to a component is the
Gysin map of its inclusion (Stacks 0FF5 composes it with any other Gysin map, and Stacks 0FFB
makes it multiplicative), and because the classical theory satisfies the same axioms on each
component.

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.cycleClassPullback`: axiom (C)(a).
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.cycleClassMul`: axiom (C)(c).
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.cycleClassPoint`: axiom (C)(d).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum Stacks.Chow

universe u v

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace ClassicalWeilCohomologyTheory

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

/-! ### Restriction of cycles to components -/

omit [IsAlgClosed k] in
/-- **Restriction to a component commutes with Gysin pullback**: `(f^!β)|_{X_c} = f_c^!(β|_{Y_d})`
for the restriction `f_c : X_c ⟶ Y_d` of `f`, both being the Gysin map of `X_c ⟶ X ⟶ Y`
(Stacks 0FF5). -/
theorem restrictChow_codimensionGysin {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (c : Idx X) (r : ℤ) (β : codimensionChowGroup k Y.obj.hom r) :
    restrictChow X c r (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) r β) =
      codimensionGysin _ _ (Over.w ((SmoothProjective.toSchemeCat k).map (resIdx f c)).hom) r
        (restrictChow Y (idxMap f c) r β) := by
  rw [restrictChow, restrictChow]
  rw [← codimensionGysin_comp _ _ (Over.w (compAtι X c).hom) _ (Over.w f.hom),
    ← codimensionGysin_comp _ _ (Over.w ((SmoothProjective.toSchemeCat k).map (resIdx f c)).hom)
      _ (Over.w (compAtι Y (idxMap f c)).hom)]
  have h : (compAtι X c).hom.left ≫ f.hom.left =
      ((SmoothProjective.toSchemeCat k).map (resIdx f c)).hom.left ≫
        (compAtι Y (idxMap f c)).hom.left :=
    (resIdx_left_ι f c).symm
  exact codimensionGysin_congr _ _ h _ _ _ _

omit [IsAlgClosed k] in
/-- **Restriction to a component is multiplicative** (Stacks 0FFB). -/
theorem restrictChow_mul (X : (SmoothProjectiveScheme k).FullSubcategory) (c : Idx X) (i j : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j) :
    restrictChow X c (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) =
      codimensionIntersectionProduct k _ i j (restrictChow X c i α) (restrictChow X c j β) :=
  codimensionGysin_codimensionIntersectionProduct _ _ _ i j α β

/-! ### Axiom (C)(a) -/

/-- The untwisted cycle class of the extension commutes with Gysin pullback:
`γ(f^!β) = f^*γ(β)` in the untwisted cohomology. -/
theorem extCycleClassUntw_gysin {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (r : ℤ) (β : codimensionChowGroup k Y.obj.hom r) :
    T.extCycleClassUntw X r (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) r β) =
      T.extPull f (T.extCycleClassUntw Y r β) := by
  funext c
  rw [extPull_apply, extCycleClassUntw_apply, extCycleClassUntw_apply, pullTotal_lof,
    restrictChow_codimensionGysin]
  exact congrArg _ (T.cycleClass_gysin (resIdx f c) r (restrictChow Y (idxMap f c) r β))

/-- **Axiom (C)(a)** for the extension: `γ(f^!β) = f^*γ(β)`. -/
theorem cycleClassPullback : T.toWeilData.CycleClassPullback := by
  intro X Y f i β
  refine (T.twCoord X (2 * i) i).injective (Subtype.ext ?_)
  rw [coe_twistCoord_cycleClass, twistCoord_pullTw, coe_pullDeg, coe_twistCoord_cycleClass]
  exact T.extCycleClassUntw_gysin f i β

/-! ### Axiom (C)(c) -/

/-- The untwisted cycle class of the extension is multiplicative: `γ(α · β) = γ(α) * γ(β)`. -/
theorem extCycleClassUntw_mul (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j) :
    T.extCycleClassUntw X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) =
      T.extCycleClassUntw X i α * T.extCycleClassUntw X j β := by
  funext c
  have hmul : T.cycleClass (compAt X c) (i + j) (codimensionIntersectionProduct k _ i j
      (restrictChow X c i α) (restrictChow X c j β)) = (T.H (compAt X c)).evenCup i j
        (T.cycleClass _ i (restrictChow X c i α)) (T.cycleClass _ j (restrictChow X c j β)) :=
    T.cycleClass_mul _ i j _ _
  rw [Pi.mul_apply, extCycleClassUntw_apply, extCycleClassUntw_apply, extCycleClassUntw_apply,
    restrictChow_mul, hmul, ExternallyGradedAlgebra.evenCup, LinearMap.compr₂_apply,
    ExternallyGradedAlgebra.lof_degreeCast, ExternallyGradedAlgebra.lof_mul_lof]

/-- **Axiom (C)(c)** for the extension: `γ(α · β) = γ(α) ∪ γ(β)`. -/
theorem cycleClassMul : T.toWeilData.CycleClassMul := by
  intro X i j α β
  refine (T.twCoord X (2 * (i + j)) (i + j)).injective (Subtype.ext ?_)
  rw [coe_twistCoord_cycleClass, twistCoord_cupTw, WeilData.coe_cup, coe_twistCoord_cycleClass,
    coe_twistCoord_cycleClass]
  exact T.extCycleClassUntw_mul X i j α β

/-! ### Axiom (C)(d) -/

section Point

/-- The underlying space of `Spec k` has at most one point. -/
instance subsingleton_point_left : Subsingleton (SmoothProjectiveScheme.point k).obj.left :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

/-- The underlying space of `Spec k` is nonempty. -/
instance nonempty_point_left : Nonempty (SmoothProjectiveScheme.point k).obj.left :=
  inferInstanceAs (Nonempty (Spec (.of k)))

/-- `Spec k` has at most one connected component. -/
instance subsingleton_components_point :
    Subsingleton (Components (SmoothProjectiveScheme.point k)) :=
  ⟨fun a b ↦ by
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := _root_.ConnectedComponents.surjective_coe b
    rw [Subsingleton.elim x y]⟩

/-- The index type of the connected components of `Spec k` has at most one element. -/
instance subsingleton_idx_point : Subsingleton (Idx (SmoothProjectiveScheme.point k)) :=
  (idxEquiv (SmoothProjectiveScheme.point k)).injective.subsingleton

/-- The unique component of `Spec k`. -/
def pointIdx : Idx (SmoothProjectiveScheme.point k) :=
  (idxEquiv _).symm (_root_.ConnectedComponents.mk
    (Classical.arbitrary (SmoothProjectiveScheme.point k).obj.left))

/-- The unique component of `Spec k` is all of `Spec k`. -/
instance isIso_compAt_point_hom (i : Idx (SmoothProjectiveScheme.point k)) :
    IsIso (compAt (SmoothProjectiveScheme.point k) i).obj.hom := by
  have : Surjective (compOpens (SmoothProjectiveScheme.point k) (idxEquiv _ i)).ι :=
    ⟨fun x ↦ ⟨⟨x, Subsingleton.elim _ _⟩, rfl⟩⟩
  have : IsIso (compOpens (SmoothProjectiveScheme.point k) (idxEquiv _ i)).ι :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, inferInstance⟩
  exact inferInstanceAs (IsIso ((compOpens _ (idxEquiv _ i)).ι ≫ 𝟙 _))

end Point

/-- **Axiom (C)(d)** for the extension: `∫_{Spec k} γ([Spec k]) = 1`, by the same axiom on the
unique component of `Spec k`. -/
theorem cycleClassPoint : T.toWeilData.CycleClassPoint := by
  unfold WeilData.CycleClassPoint
  have h1 : T.toWeilData.trace (SmoothProjectiveScheme.point k) 0 isNonemptyEquidimensional_point
      (T.toWeilData.cycleClass (SmoothProjectiveScheme.point k) 0
        (fundamentalClass (SmoothProjectiveScheme.point k))) =
      T.extTraceUntw (SmoothProjectiveScheme.point k) isNonemptyEquidimensional_point
        (T.extCycleClassUntw (SmoothProjectiveScheme.point k) 0
          (fundamentalClass (SmoothProjectiveScheme.point k))) := by
    rw [toWeilData_trace]
    exact congrArg _ (T.coe_twistCoord_cycleClass _ 0 _)
  rw [h1, extTraceUntw_apply, Fintype.sum_subsingleton _ pointIdx, extCycleClassUntw_apply,
    ExternallyGradedAlgebra.component_lof_of_eq _ (by simp),
    ExternallyGraded.degreeCast_degreeCast]
  have hfund : restrictChow (SmoothProjectiveScheme.point k) pointIdx 0
      (fundamentalClass (SmoothProjectiveScheme.point k)) =
        fundamentalClass ((SmoothProjective.toSchemeCat k).obj
          (compAt (SmoothProjectiveScheme.point k) pointIdx)) :=
    codimensionGysin_fundamentalClass_point (compAtι _ pointIdx)
  rw [hfund]
  exact T.integration_cycleClass_fundamental _ inferInstance
    (T.dimension_compAt isNonemptyEquidimensional_point pointIdx)

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
