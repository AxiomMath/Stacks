module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftLegs
public import StacksFrontier.Homology.KFlat.BifunctorComplexModelsShift
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShiftTwo
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The shift compatibility of the comparison of Tag 079U, reduced to cochain complexes

`Stacks.Cohomology.DerivedPullbackTensor.ModelsComparisonCommShift₂` is a statement about the
category of **K-flat objects of the homotopy category** of `𝒪_Y`-modules, and the obstacle to
proving it is not any of its three legs — all three are now proved — but that
`modelsComparison` is not a composite of whiskerings there.  It is a
`CategoryTheory.NatIso.ofComponents` whose component at a pair `M` of K-flat objects conjugates
the comparison at the *chosen cochain representatives* `M.1.obj.as`, `M.2.obj.as` by
`kFlatQPairIso`; and choosing a cochain representative of a homotopy class is not functorial,
so `kFlatQPair` is not of the form `_ ⋙ (DerivedCategory.Q.prod DerivedCategory.Q)` and
`kFlatQPairIso` is not the component of an isomorphism of functors.

This file removes that obstacle.  The homotopy quotient
`CochainComplex.KFlatBifunctor.kFlatQuotient` from the K-flat *complexes* to the K-flat objects
is essentially surjective and commutes with the shift
(`StacksFrontier/Homology/KFlat/BifunctorComplexModelsShift.lean`), so by
`CategoryTheory.NatTrans.CommShift₂.of_essSurj` both halves of
`CategoryTheory.NatTrans.CommShift₂` may be tested after restricting *both* variables along
it — and there every K-flat object is the homotopy class of the complex it is restricted at, so
the chosen representative is a functor of the complex and `kFlatQPairIso` becomes
`CochainComplex.KFlatBifunctor.kFlatQuotientCompQIso` in each variable.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.ModelsComparisonCommShiftOnComplexes`: **the
  statement of the two conditions over cochain complexes**, one per variable.
* `Stacks.Cohomology.DerivedPullbackTensor.modelsComparison_hom_app_kFlatQuotient`: **the
  component of `modelsComparison` at a pair of K-flat complexes**, written as the conjugate of
  `leftComparison` and the inverse of `rightComparison` by `kFlatQuotientCompQIso` in each
  variable.  This is the identification that the obstacle above denied; it holds by `rfl`
  because `kFlatQuotientCompQIso` is `DerivedCategory.quotientCompQhIso` whiskered by the
  inclusion of the K-flat complexes, which is exactly what `kFlatQPairIso` is at a pair of
  homotopy classes of complexes.
* `Stacks.Cohomology.DerivedPullbackTensor.modelsComparisonCommShift₂_of_complexes`: **the
  reduction** — `ModelsComparisonCommShiftOnComplexes f` implies
  `ModelsComparisonCommShift₂ f`.

## Implementation notes

**The four instance binders of the statement are dischargeable.**  `HasSheafify` and
`WEqualsLocallyBijective` for the open-cover site of a ringed space `Z : RingedSpace.{u, u}`
hold at every universe containing `u`, by `Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`, whose conclusions are stated at
`AddCommGrpCat.{max u v}`.  Instance search does not solve `max u v =?= u` while the universes
are metavariables, so they are not found; applied by name with `v := u` they typecheck.  They
are kept as binders here only because `ModelsComparisonCommShift₂` has them.

**What is still owed is `ModelsComparisonCommShiftOnComplexes`.**  Each of its two conjuncts is
a one-variable `CategoryTheory.NatTrans.CommShift` of a transformation of functors on K-flat
cochain complexes, and by `modelsComparison_hom_app_kFlatQuotient` that transformation is a
composite of four factors: the conjugating `kFlatQuotientCompQIso` on each side — shift
compatible by `CochainComplex.KFlatBifunctor.kFlatQuotientCompQIso_commShift` — and
`leftComparison` and the inverse of `rightComparison`.  So what remains is the shift
compatibility of those two, in each variable, which is where the three legs
(`derivedPullbackNatTrans_commShift`,
`CochainComplex.KFlatBifunctor.derivedBifunctorComparisonIso_commShift₂` and
`CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_commShift₂`) enter.  The passage from the
inverse of `rightComparison` to `rightComparison` is
`CategoryTheory.NatTrans.CommShift.of_isIso`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)
open CochainComplex.KFlatBifunctor (kFlatComplexes kFlatQuotient kFlatQuotient_commShift)

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The four instance binders are dischargeable

Recorded here because it is not visible from the statement: the two site hypotheses hold for
every ringed space, in any universe containing its own, and the reason instance search does not
find them is that their conclusions are stated at `AddCommGrpCat.{max u v}` and `max u v =?= u`
is not solved while the universes are metavariables.  Applied by name with `v := u` they
typecheck. -/

example (Z : RingedSpace.{u, u}) :
    HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u} :=
  Stacks.AssociatedSheaf.hasModuleSheafify Z

example (Z : RingedSpace.{u, u}) :
    (Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective Z

/-! ### The K-flat complexes of `𝒪_Y`-modules -/

/-- The K-flat cochain complexes of `𝒪_Y`-modules, as an object property. -/
abbrev kFlatComplexesY :=
  kFlatComplexes (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)

/-- The homotopy quotient from the K-flat complexes of `𝒪_Y`-modules to the K-flat objects of
the homotopy category, which is the category `modelsComparison` lives on. -/
abbrev kFlatQuotientY :=
  kFlatQuotient (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)

/-! ### The component of `modelsComparison` at a pair of K-flat complexes -/

/-- **`modelsComparison` at a pair of homotopy classes of K-flat complexes is the conjugate of
the two comparisons of Tag 079U by `kFlatQuotientCompQIso`.**  At such a pair the chosen cochain
representative is the complex itself, so `kFlatQPairIso` is
`DerivedCategory.quotientCompQhIso` at the two complexes in each variable, which is
`CochainComplex.KFlatBifunctor.kFlatQuotientCompQIso` — a component of an isomorphism of
*functors*, which `kFlatQPairIso` is not. -/
theorem modelsComparison_hom_app_kFlatQuotient
    (K₁ K₂ : (kFlatComplexesY (Y := Y)).FullSubcategory) :
    (modelsComparison f).hom.app ((kFlatQuotientY (Y := Y)).obj K₁,
        (kFlatQuotientY (Y := Y)).obj K₂) =
      (pullbackOfTensor f).map
          ((CochainComplex.KFlatBifunctor.kFlatQuotientCompQIso
              (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).hom.app K₁ ×ₘ
            (CochainComplex.KFlatBifunctor.kFlatQuotientCompQIso
              (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).hom.app K₂) ≫
        (modelComparison f K₁.obj K₂.obj K₁.property K₂.property).hom ≫
        (tensorOfPullbacks f).map
          ((CochainComplex.KFlatBifunctor.kFlatQuotientCompQIso
              (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).inv.app K₁ ×ₘ
            (CochainComplex.KFlatBifunctor.kFlatQuotientCompQIso
              (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).inv.app K₂) :=
  rfl

/-! ### The reduction -/

/-- **The two conditions over cochain complexes that `ModelsComparisonCommShift₂` reduces
to.**  Each is a one-variable `CategoryTheory.NatTrans.CommShift` for the restriction of
`modelsComparison`, curried, along the homotopy quotient from the K-flat complexes: the first
in the second variable at a fixed K-flat complex in the first, the second in the first variable
at a fixed K-flat complex in the second. -/
def ModelsComparisonCommShiftOnComplexes : Prop :=
  letI := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
  letI := curryModelsPullbackOfTensor_commShift₂Int f
  letI := curryModelsTensorOfPullbacks_commShift₂Int f
  (∀ K₁ : (kFlatComplexesY (Y := Y)).FullSubcategory,
      NatTrans.CommShift (Functor.whiskerLeft (kFlatQuotientY (Y := Y))
        ((Functor.curry.map (modelsComparison f).hom).app
          ((kFlatQuotientY (Y := Y)).obj K₁))) ℤ) ∧
    ∀ K₂ : (kFlatComplexesY (Y := Y)).FullSubcategory,
      NatTrans.CommShift (Functor.whiskerLeft (kFlatQuotientY (Y := Y))
        ((Functor.curry.map (modelsComparison f).hom).flipApp
          ((kFlatQuotientY (Y := Y)).obj K₂))) ℤ

/-- **The shift compatibility of the comparison of [Stacks, Tag 079U] on K-flat
representatives follows from the same statement over cochain complexes.**  The homotopy
quotient from the K-flat complexes to the K-flat objects is essentially surjective and commutes
with the shift, so `CategoryTheory.NatTrans.CommShift₂.of_essSurj` tests both halves of
`CategoryTheory.NatTrans.CommShift₂` after restricting both variables along it. -/
theorem modelsComparisonCommShift₂_of_complexes
    (h : ModelsComparisonCommShiftOnComplexes f) : ModelsComparisonCommShift₂ f := by
  let := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
  let := curryModelsPullbackOfTensor_commShift₂Int f
  let := curryModelsTensorOfPullbacks_commShift₂Int f
  exact NatTrans.CommShift₂.of_essSurj _ _ (kFlatQuotientY (Y := Y)) (kFlatQuotientY (Y := Y))
    h.1 h.2

end Stacks.Cohomology.DerivedPullbackTensor

end
