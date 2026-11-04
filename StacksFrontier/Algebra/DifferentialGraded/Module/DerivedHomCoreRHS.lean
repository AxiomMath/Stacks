module

public import StacksFrontier.Algebra.DifferentialGraded.Module.HomEvaluationDerivedIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.LinkOneSigmaEvaluation

/-!
# The right-hand side of step 3's elementwise equation, computed on a cocycle

The right-hand side of the equation of step 3 of [Stacks, Tag 09LK] is
`DGCategory.RightModule.homShiftEquivEvaluationGradedCohomology` applied to

`Φ(f) ≫ σ_n : h_K ⟶ (Φ Y)⟦n⟧`,

where `Φ = CochainComplex.yonedaHomotopyFunctor` is the differential graded Yoneda functor on the
homotopy category, `f : K ⟶ Y⟦n⟧` is the morphism of `K(A)` that a degree-`n` cohomology class of
`Hom^•(K, Y)` is by [Tag 09LC], and `σ_n` is `Φ`'s comparison with the translation. This file
computes it on a cocycle.

## Main results

* `CochainComplex.yonedaHomotopyFunctor_commShift`: the comparison of `Φ` with the translation,
  as the composite of those of its two factors.
* `CochainComplex.yonedaHomotopyFunctor_commShiftIso` and
  `CochainComplex.yonedaHomotopyFunctor_commShiftIso_hom_app`: that comparison, unfolded.
* `CochainComplex.yonedaHomotopyFunctor_map_comp_commShiftIso`: `Φ(f) ≫ σ_n` is the differential
  graded Yoneda image of a *single* morphism of `(dgCategory A).K` — namely `f` carried across
  the comparison of homotopy categories and then composed with that comparison's own
  commutation — followed by the differential graded Yoneda functor's `σ_n`.
* `CochainComplex.coreRHS_mk`: **the right-hand side at a cocycle.**

## Implementation notes

`Φ` is `CochainComplex.homotopyCategoryEquivalence` followed by
`(DGCategory.yonedaDGFunctor (dgCategory A)).onK`, and both factors carry a registered comparison
with the translation: `CochainComplex.homotopyCategoryEquivalence_functor_commShift` and
`CochainComplex.yonedaOnK_commShift`. The instance `CochainComplex.yonedaHomotopyFunctor_commShift`
is their `CategoryTheory.Functor.CommShift.comp`, obtained by `inferInstanceAs` at the composite,
so no comparison is chosen independently of the ones the library already fixes. Since
`CochainComplex.yonedaHomotopyFunctor` is a plain definition, the equation
`CochainComplex.yonedaHomotopyFunctor_commShiftIso` records this by reflexivity.

`CochainComplex.coreRHS_mk` carries the passage across
`CochainComplex.homotopyCategoryEquivalence` as the *hypothesis* `hf` — that the morphism
`f` becomes the homotopy class of the cocycle `fc` — rather than computing it. The comparison of
the homotopy category of complexes with the homotopy category of the differential graded category
of complexes acts on morphisms by a lemma whose conclusion is an `HEq`; as a hypothesis, `hf` is a
plain equation between morphisms of `(dgCategory A).K`.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 the
  equation belongs to; [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the identification
  of a cohomology class with a morphism of the homotopy category.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Preadditive A] (K : CochainComplex A ℤ)

/-- **The comparison of `Φ = h_{(-)}` on the homotopy category with the translation.** `Φ` is
`CochainComplex.homotopyCategoryEquivalence` followed by the differential graded Yoneda functor
on homotopy classes, and both factors carry a registered comparison; this is their composite and
nothing else. -/
noncomputable instance yonedaHomotopyFunctor_commShift :
    (yonedaHomotopyFunctor A).CommShift ℤ :=
  inferInstanceAs (((homotopyCategoryEquivalence A).functor ⋙
    (DGCategory.yonedaDGFunctor (dgCategory A)).onK).CommShift ℤ)

/-- The comparison of `Φ` with the translation is the composite one, by reflexivity. -/
theorem yonedaHomotopyFunctor_commShiftIso (n : ℤ) :
    (yonedaHomotopyFunctor A).commShiftIso n =
      ((homotopyCategoryEquivalence A).functor ⋙
        (DGCategory.yonedaDGFunctor (dgCategory A)).onK).commShiftIso n :=
  rfl

/-- **`Φ`'s comparison at an object**, as the differential graded Yoneda image of the comparison
of the homotopy categories followed by the differential graded Yoneda functor's own
comparison. -/
theorem yonedaHomotopyFunctor_commShiftIso_hom_app (n : ℤ)
    (Y : HomotopyCategory A (ComplexShape.up ℤ)) :
    ((yonedaHomotopyFunctor A).commShiftIso n).hom.app Y =
      (DGCategory.yonedaDGFunctor (dgCategory A)).onK.map
          (((homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app Y) ≫
        ((DGCategory.yonedaDGFunctor (dgCategory A)).onK.commShiftIso n).hom.app
          ((homotopyCategoryEquivalence A).functor.obj Y) := by
  rw [yonedaHomotopyFunctor_commShiftIso, Functor.commShiftIso_comp_hom_app]

/-- **`Φ(f) ≫ σ_n` is a differential graded Yoneda image followed by one comparison.** The two
`Φ`-images merge into the image of a single morphism of `(dgCategory A).K`: `f` carried across the
comparison of the homotopy categories and composed with that comparison's commutation with the
translation, followed by the differential graded Yoneda functor's own comparison. -/
theorem yonedaHomotopyFunctor_map_comp_commShiftIso (n : ℤ)
    (Y : HomotopyCategory A (ComplexShape.up ℤ))
    (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⟶ Y⟦n⟧) :
    (yonedaHomotopyFunctor A).map f ≫
        ((yonedaHomotopyFunctor A).commShiftIso n).hom.app Y =
      (DGCategory.yonedaDGFunctor (dgCategory A)).onK.map
          ((homotopyCategoryEquivalence A).functor.map f ≫
            (((homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app Y)) ≫
        ((DGCategory.yonedaDGFunctor (dgCategory A)).onK.commShiftIso n).hom.app
          ((homotopyCategoryEquivalence A).functor.obj Y) := by
  rw [yonedaHomotopyFunctor_commShiftIso_hom_app, Functor.map_comp,
    show (yonedaHomotopyFunctor A).map f =
      (DGCategory.yonedaDGFunctor (dgCategory A)).onK.map
        ((homotopyCategoryEquivalence A).functor.map f) from rfl,
    Category.assoc]
  rfl

open DGCategory DGCategory.RightModule

/-- **The right-hand side of step 3's equation, at a cocycle.** Let `f : K ⟶ Y⟦n⟧` be a morphism
of the homotopy category of complexes whose image under the comparison of homotopy categories,
composed with that comparison's commutation with the translation, is the homotopy class of the
degree-zero cocycle `fc : K ⟶ Y[n]` of `dgCategory A` — that is the hypothesis `hf`. Let `c` be
the degree-`0` cocycle of the shifted representable module that `fc` is the reindexing of, as
`hc` says. Then `DGCategory.RightModule.homShiftEquivEvaluationGradedCohomology` takes

`Φ(f) ≫ σ_n`

to the degree-`n` cohomology class of `c`, reindexed from degree `0 + n`. -/
theorem coreRHS_mk (n : ℤ) (Y : HomotopyCategory A (ComplexShape.up ℤ))
    (e : (endDGCategory (dgCategory A) K).Obj)
    (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⟶ Y⟦n⟧)
    (fc : (dgCategory A).Cocycle K
      (((dgShiftAxiomBIso A).shiftFunctor n).obj
        ((homotopyCategoryEquivalence A).functor.obj Y : (dgCategory A).Obj)))
    (c : gradedCocycles (shift (yonedaRightModule (dgCategory A)
        ((homotopyCategoryEquivalence A).functor.obj Y : (dgCategory A).Obj)) n) K 0)
    (hf : (homotopyCategoryEquivalence A).functor.map f ≫
        ((homotopyCategoryEquivalence A).functor.commShiftIso n).hom.app Y =
      Quotient.mk _ fc)
    (hc : (dgShiftAxiomBIso A).toShift n K
      ((homotopyCategoryEquivalence A).functor.obj Y : (dgCategory A).Obj) 0 c.1 = fc.1) :
    homShiftEquivEvaluationGradedCohomology ((yonedaHomotopyFunctor A).obj Y) K e n
        ((yonedaHomotopyFunctor A).map f ≫
          ((yonedaHomotopyFunctor A).commShiftIso n).hom.app Y) =
      Submodule.Quotient.mk (gradedCocyclesShiftEquiv'
        ((yonedaHomotopyFunctor A).obj Y) n K (zero_add n) c) :=
  (congrArg (homShiftEquivEvaluationGradedCohomology ((yonedaHomotopyFunctor A).obj Y) K e n)
      ((yonedaHomotopyFunctor_map_comp_commShiftIso A K n Y f).trans
        (congrArg (fun t => (yonedaDGFunctor (dgCategory A)).onK.map t ≫
            ((yonedaDGFunctor (dgCategory A)).onK.commShiftIso n).hom.app
              ((homotopyCategoryEquivalence A).functor.obj Y)) hf))).trans
    (homShiftEquivEvaluationGradedCohomology_yonedaOnK_map_comp_commShiftIso A n K
      ((homotopyCategoryEquivalence A).functor.obj Y) e fc c hc)

end CochainComplex

end
