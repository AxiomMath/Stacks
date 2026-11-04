module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonSection
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange

/-!
# The keystone hypothesis of the chapter, reduced to K-flat complexes at the canonical models

`Dualizing.KFlatAlgebraActionEq` is the single hypothesis the library's [stacks 0BZM] and
[stacks 0BZN] carry beyond those of their sources, and
`Dualizing.PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq` discharges the
`ProjectionCompatibility` input of every carrier site at once from it.
`Dualizing.kFlatAlgebraActionEq_of_tensorComparisonCompatibility` reduces it to
`Dualizing.TensorComparisonCompatibility` at the canonical models of every Tor-independent square
of rings in one universe, read at *every* object of `D(B)`.

This file removes the quantifier over objects.  Both sides of the obligation are natural in the
object it is read at, so by `Dualizing.tensorComparisonCompatibility_of_kFlat` — which is
[stacks 06Y4] after localization — it has only to be checked at the classes of K-flat complexes
of `B`-modules, which is where both sides are chain-level data.

So the chapter's keystone is exactly the hypothesis `h` below: one equation, at one pair of
canonical models, at the class of a K-flat complex.  By
`Dualizing.tensorComparisonCompatibility_iff_section` that equation may be taken in its
transpose-free form — no unit of [stacks 0GMT], no `homEquiv` of [stacks 0A63], no component of
[stacks 0E1W] and no morphism of [stacks 0E1X] occurring in it — and by
`Dualizing.tensorComparisonCompatibility_iff_eq_inv` it is equivalently a determinate value for
the lax monoidal structure map of derived base change along `B → B'`.

**What is not done here.**  The obligation is not proved here: nothing in this file is
unconditional.  What it buys is that the keystone is a single equation about chain-level data
rather than a family of equations about arbitrary objects.  The keystone itself is proved, by
another route, as `Dualizing.kFlatAlgebraActionEq` in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibilityResolved`.

## Main results

* `Dualizing.kFlatAlgebraActionEq_of_tensorComparisonCompatibility_kFlat` — the keystone
  hypothesis from the tensor-comparison obligation at the classes of K-flat complexes only.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

universe u

/-- **The keystone hypothesis of the chapter, from the tensor-comparison obligation at K-flat
complexes only.**  `Dualizing.kFlatAlgebraActionEq_of_tensorComparisonCompatibility` asks for
`Dualizing.TensorComparisonCompatibility` at every object of `D(B)`; both of its sides are natural
in that object and every object of `D(B)` is the class of a K-flat complex up to isomorphism, so
`Dualizing.tensorComparisonCompatibility_of_kFlat` restricts the check to those classes.

This is the chapter's keystone in its smallest shape: one equation, at the canonical models
`Dualizing.canonicalExtensionModel` and `Dualizing.canonicalExtensionModelIncludeRight` of the two
extensions of scalars across a Tor-independent square, at the class of a K-flat complex — where
the left-hand side is evaluated by `Dualizing.tensorComparisonCompatibility_lhs_app_q_obj` and
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_baseChangeR_q_obj`, and the [stacks 068I]
candidate for the right-hand side by `Dualizing.tensorBaseChangeMor_comp_eq_q_obj`. -/
theorem kFlatAlgebraActionEq_of_tensorComparisonCompatibility_kFlat
    (h : ∀ {B C B' : Type u} [CommRing B] [CommRing C] [CommRing B'] [Algebra B C]
      [Algebra B B']
      (hTor : RingTheory.TorIndependence.TorIndependent B C B')
      (bc : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B'))
      (cmp : DerivedCategory.Q ⋙ bc ⟶
        (ModuleCat.extendScalars.{u, u, u} (algebraMap B B')).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (ld : bc.IsLeftDerivedFunctor cmp
        (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
      (bcC : DerivedCategory (ModuleCat.{u} C) ⥤
        DerivedCategory (ModuleCat.{u} (TensorProduct B C B')))
      (cmpC : DerivedCategory.Q ⋙ bcC ⟶
        (ModuleCat.extendScalars.{u, u, u}
          (algebraMap C (TensorProduct B C B'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (ldC : bcC.IsLeftDerivedFunctor cmpC
        (HomologicalComplex.quasiIso (ModuleCat.{u} C) (ComplexShape.up ℤ)))
      (K : CochainComplex (ModuleCat.{u} B) ℤ), CochainComplex.KFlat.{u, u} K →
      @TensorComparisonCompatibility.{u, u, u, 0} B C B' _ _ _ _ _ hTor bc cmp bcC cmpC
        (canonicalExtensionModel.{u, u, u} B C).functor
        (canonicalExtensionModel.{u, u, u} B C).comparison
        (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').functor
        (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').comparison
        (canonicalExtensionModel.{u, u, u} B C).isLeftDerived ldC ld
        (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').isLeftDerived
        (DerivedCategory.Q.obj K)) :
    KFlatAlgebraActionEq.{u} := by
  refine kFlatAlgebraActionEq_of_tensorComparisonCompatibility ?_
  intro B C B' _ _ _ _ _ hTor bc cmp ld bcC cmpC ldC X
  exact @tensorComparisonCompatibility_of_kFlat B C B' _ _ _ _ _ hTor bc cmp bcC cmpC
    (canonicalExtensionModel.{u, u, u} B C).functor
    (canonicalExtensionModel.{u, u, u} B C).comparison
    (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').functor
    (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').comparison
    (canonicalExtensionModel.{u, u, u} B C).isLeftDerived ldC ld
    (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').isLeftDerived
    (fun K hK => h hTor bc cmp ld bcC cmpC ldC K hK) X

end Dualizing

end
