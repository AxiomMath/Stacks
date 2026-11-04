module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTraceFormula
public import StacksFrontier.Homology.Perfect.Saturation
public import StacksFrontier.Homology.Perfect.Filtration
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Basic

/-!
# Perfectness of the cohomology of a scheme finite étale over a finite field

Step 2 of the proof of [Stacks, Tag 03UG] computes `RΓ(Y_k̄, C|_{Y_k̄})`, for `Y` finite étale
over `k`, as the direct sum of the stalks of `C` at the `k̄`-points of `Y_k̄`. Hence it is
perfect as soon as these stalks are.

## Main results

* `StacksDraft.Perfect.isPerfect_of_sum_comp_eq_id`: an object of `D(R)` through which the
  identity factors as a finite sum `∑ᵢ rᵢ ≫ iᵢ` of maps through perfect objects is perfect.
* `Stacks.EtaleCohomology.isPerfect_frobeniusRestriction_of_etale`: for `Y` finite étale over
  `k` and a bounded below complex `C` on `Y` with perfect geometric stalks,
  `RΓ(Y_k̄, C|_{Y_k̄})` is perfect.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived
open ZeroObject

universe u r v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- **A finite product of perfect objects of `D(R)` is perfect.** -/
theorem isPerfect_piObj {R : Type u} [Ring R] {ι : Type*} [Finite ι]
    (B : ι → DerivedCategory (ModuleCat.{v} R)) (hB : ∀ i, IsPerfect (B i)) :
    IsPerfect (∏ᶜ B) := by
  let P : ObjectProperty (DerivedCategory (ModuleCat.{v} R)) := fun K => IsPerfect K
  let : P.ContainsZero := ⟨⟨0, isZero_zero _, isPerfect_of_isZero _ (isZero_zero _)⟩⟩
  let : P.IsClosedUnderBinaryProducts := by
    refine ⟨fun X ⟨L⟩ ↦ ?_⟩
    refine P.prop_of_iso (IsLimit.conePointsIsoOfNatIso L.isLimit
      (BinaryBiproduct.isLimit (L.diag.obj ⟨WalkingPair.left⟩)
        (L.diag.obj ⟨WalkingPair.right⟩)) (diagramIsoPair L.diag)).symm ?_
    exact (isPerfect_of_distinguished (Pretriangulated.binaryBiproductTriangle _ _)
      (Pretriangulated.binaryBiproductTriangle_distinguished _ _)).2.1
        (L.prop_diag_obj _) (L.prop_diag_obj _)
  let : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product hB

/-- **An object through which the identity factors as a finite sum of maps through perfect
objects is perfect**: it is a retract of their product. -/
theorem isPerfect_of_sum_comp_eq_id {R : Type u} [Ring R] {ι : Type*} [Fintype ι]
    {X : DerivedCategory (ModuleCat.{max u v} R)} (B : ι → DerivedCategory (ModuleCat.{max u v} R))
    (r : ∀ i, X ⟶ B i) (s : ∀ i, B i ⟶ X) (h : ∑ i, r i ≫ s i = 𝟙 X)
    (hB : ∀ i, IsPerfect (B i)) : IsPerfect X := by
  let e := Fintype.equivFin ι
  let B' : Fin (Fintype.card ι) → DerivedCategory (ModuleCat.{max u v} R) := fun k => B (e.symm k)
  have h' : ∑ k, r (e.symm k) ≫ s (e.symm k) = 𝟙 X :=
    (Equiv.sum_comp e.symm (fun i => r i ≫ s i)).trans h
  refine isPerfect_of_retract.{u, v} (biproduct.lift (f := B') (fun k => r (e.symm k)) ≫
      (biproduct.isoProduct B').hom)
    ((biproduct.isoProduct B').inv ≫ biproduct.desc (fun k => s (e.symm k))) ?_
    (isPerfect_piObj B' fun k => hB _)
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact biproduct.lift_desc.trans h'

end StacksDraft.Perfect

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Finite k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Etale Y.hom] [IsFinite Y.hom]

/-- **Perfectness in dimension zero.**  For `Y` finite étale over `k` and a bounded below complex
`C` on `Y` whose stalks at all geometric points are perfect, `RΓ(Y_k̄, C|_{Y_k̄})` is perfect: it
is the direct sum of the stalks of `C` at the `k̄`-points of `Y_k̄`. -/
theorem isPerfect_frobeniusRestriction_of_etale
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (hstalk : ∀ s : GeometricPoint Y.left, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          C.obj))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)))) := by
  have := Fintype.ofFinite k
  refine (isPerfect_frobeniusRestrictionSectionsComplex_iff Λ Y kbar C).2 ?_
  refine StacksDraft.Perfect.isPerfect_of_iso (sectionsComplexIso Λ Y kbar C) ?_
  refine StacksDraft.Perfect.isPerfect_of_sum_comp_eq_id.{r, u + 1} _
    (fun y => DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (blockRestriction Λ Y kbar y) (ComplexShape.up ℤ)).app C.obj))
    (fun y => DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (blockInclusion Λ Y kbar y) (ComplexShape.up ℤ)).app C.obj)) ?_
    (fun y => isPerfect_restrictionSections_of_stalk Λ Y kbar C.obj y
      (hstalk ⟨kbar, y.1 ≫ fieldBaseChangeProj Y kbar⟩))
  have hc : ∑ y, (NatTrans.mapHomologicalComplex (blockRestriction Λ Y kbar y)
      (ComplexShape.up ℤ)).app C.obj ≫ (NatTrans.mapHomologicalComplex (blockInclusion Λ Y kbar y)
        (ComplexShape.up ℤ)).app C.obj = 𝟙 _ := by
    ext n : 1
    refine ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map_sum _ _).trans ?_
    simpa using congrArg (fun φ => φ.app (C.obj.X n))
      (sum_blockRestriction_comp_blockInclusion Λ Y kbar)
  simp_rw [← Functor.map_comp, ← Functor.map_sum, hc, CategoryTheory.Functor.map_id]

end Stacks.EtaleCohomology

end
