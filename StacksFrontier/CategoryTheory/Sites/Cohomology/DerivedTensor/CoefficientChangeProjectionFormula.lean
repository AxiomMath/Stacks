module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.CoefficientChangeExtendScalars
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.RestrictScalarsHomology

/-!
# The projection formula at a change of coefficient rings

Let `α : O ⟶ O'` be a map of sheaves of commutative rings on a site `(C, J)`, let `M` be an
object of `D(O)` and let `N` be a sheaf of `O'`-modules. Reading `N` over `O` and tensoring
there gives the same answer as extending `M` to `O'`, tensoring over `O'` and reading the
result over `O`:

`M ⊗^L_O N|_O ≅ ((M ⊗^L_O O') ⊗^L_{O'} N)|_O`.

This is the projection formula for the morphism of ringed topoi a coefficient change presents,
in the one case the dévissage of Stacks 0942 part (2) needs: an arbitrary object in the first
variable and a sheaf of modules in degree zero in the second.

## Main definitions

* `Stacks.Cohomology.CoefficientChange.flatModel`: a chosen K-flat complex with flat terms
  representing an object of `D(O)`, with `flatModelIso` identifying it.
* `Stacks.Cohomology.CoefficientChange.projectionComplexIso`: the identity at the level of
  cochain complexes, `Tot(P ⊗_O N|_O) ≅ Tot((O' ⊗_O P) ⊗_{O'} N)|_O`.
* `Stacks.Cohomology.CoefficientChange.projectionModelIso`: the derived identity at a K-flat
  complex with flat terms in the first variable.
* `Stacks.Cohomology.CoefficientChange.projectionFormulaIso`: **the projection formula**, at an
  arbitrary object of `D(O)`.

## Implementation notes

The complex-level identity is the identity of total tensor complexes
`Stacks.Cohomology.MixedDerivedTensor.MixedTensorSetup.totalComplexIso` at the datum
`setupOfCoefficientChange`, which states it with the restricted factor on the left; the Koszul
symmetry `Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` moves it to the right on both
sides, which is the order in which the derived tensor product is read against a module. No
braiding of the derived tensor product is needed, and none is available for this packaging of
it.

Passing to the derived category uses only the one-sided K-flat comparison `comparisonLeft`, so
no hypothesis is placed on `N`: the first factor is a K-flat complex with flat terms over `O`
by Stacks 06YS, and its extension of scalars is one over `O'` by
`Stacks.Cohomology.CoefficientChange.kFlat_extendScalarsComplex`. That the extension computes
the derived change of coefficients is
`Stacks.Cohomology.CoefficientChange.derivedCoefficientChangeFlatIso`, i.e. Stacks 06YY, and
that degreewise restriction of scalars computes the functor it induces on derived categories is
`CategoryTheory.Functor.mapDerivedCategoryFactors`, restriction of scalars being exact.

The isomorphism is constructed at a chosen model and is not asserted to be natural in `M`. Its
consumer, Stacks 0942 part (2), transports a vanishing of cohomology sheaves object by object.

The derived tensor products are taken in the packaging indexed by a sheaf of rings,
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, since a coefficient change is a map of
sheaves of rings and the two sides of the formula live over different ones. A derived tensor
product in the packaging indexed by a ringed site is carried across by
`Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct`, which changes
neither the bifunctor nor the comparisons.

## References

* [The Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [The Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [The Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.MixedDerivedTensor

universe u

namespace Stacks.Cohomology.CoefficientChange

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O O' : Sheaf J CommRingCat.{u}}

/-! ### A K-flat model with flat terms -/

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Every object of `D(O)` is represented by a K-flat complex with flat terms**, by
Stacks 06YS applied to any complex representing it. -/
theorem exists_flatKFlatModel (R : Sheaf J CommRingCat.{u})
    (M : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R)) :
    ∃ P : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) P ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  obtain ⟨K, f, hK, hflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution R
      (DerivedCategory.Q.objPreimage M)
  refine ⟨K, hK, hflat, ⟨?_⟩⟩
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqis
  exact asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso M

variable (R : Sheaf J CommRingCat.{u})
  (M : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R))

/-- The chosen K-flat complex with flat terms representing an object of `D(O)`. -/
def flatModel : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ :=
  (exists_flatKFlatModel R M).choose

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The chosen model is K-flat. -/
theorem kFlat_flatModel :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (flatModel R M) :=
  (exists_flatKFlatModel R M).choose_spec.1

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The terms of the chosen model are flat. -/
theorem isFlat_flatModel (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) ((flatModel R M).X i) :=
  (exists_flatKFlatModel R M).choose_spec.2.1 i

/-- The chosen model does represent the given object of `D(O)`. -/
def flatModelIso : DerivedCategory.Q.obj (flatModel R M) ≅ M :=
  (exists_flatKFlatModel R M).choose_spec.2.2.some

/-! ### The identity at the level of cochain complexes -/

/-- Restriction of scalars along a change of coefficient rings, with the universe of the
modules pinned: it is not determined by the morphism of sheaves of rings, and left open it
makes the derived instances over `(C, O)` fail to apply. -/
abbrev restrict (α : O ⟶ O') :
    Stacks.DerivedTensor.RingedSite.Modules O' ⥤ Stacks.DerivedTensor.RingedSite.Modules O :=
  _root_.SheafOfModules.restrictScalars.{u} (Stacks.FlatChangeOfRings.ringSheafMap α)

/-- **The projection formula for total tensor complexes**:
`Tot(P ⊗_O N|_O) ≅ Tot((O' ⊗_O P) ⊗_{O'} N)|_O`, for unbounded cochain complexes `P` of
`O`-modules and `N` of `O'`-modules.

It is the identity of total tensor complexes at `setupOfCoefficientChange`, which has the
restricted factor on the left, read on the right by the Koszul symmetry on both sides. -/
def projectionComplexIso (α : O ⟶ O')
    (Nc : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules O') ℤ)
    (P : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules O) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex O).obj P).obj
        ((setupOfCoefficientChange α).resComplex.obj Nc) ≅
      (setupOfCoefficientChange α).resComplex.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex O').obj
          ((extendScalarsComplex α).obj P)).obj Nc) :=
  Stacks.SheafOfModules.Tensor.tensorComplexFlipIso O P
      ((setupOfCoefficientChange α).resComplex.obj Nc) ≪≫
    (setupOfCoefficientChange α).totalComplexIso Nc P ≪≫
      (setupOfCoefficientChange α).resComplex.mapIso
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso O' Nc
          ((extendScalarsComplex α).obj P))

/-! ### The projection formula -/

variable (α : O ⟶ O')
  (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct O)
  (T' : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct O')

/-- **The projection formula at a K-flat complex with flat terms.** Both sides are computed by
the one-sided K-flat comparison from the complex-level identity. -/
def projectionModelIso
    (P : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules O) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O) P)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) (P.X i))
    (N : Stacks.DerivedTensor.RingedSite.Modules O') :
    (T.tensor.obj (DerivedCategory.Q.obj P)).obj
        ((DerivedCategory.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules O) 0).obj
          ((restrict α).obj N)) ≅
      (restrict α).mapDerivedCategory.obj
        ((T'.tensor.obj (DerivedCategory.Q.obj ((extendScalarsComplex α).obj P))).obj
          ((DerivedCategory.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules O') 0).obj
            N)) :=
  letI Nc := (HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules O')
    (ComplexShape.up ℤ) 0).obj N
  (T.tensor.obj (DerivedCategory.Q.obj P)).mapIso
      (DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (restrict α)
          (ComplexShape.up ℤ) 0).app N).symm) ≪≫
    T.comparisonLeft P ((setupOfCoefficientChange α).resComplex.obj Nc) hP ≪≫
      DerivedCategory.Q.mapIso (projectionComplexIso α Nc P) ≪≫
        ((restrict α).mapDerivedCategoryFactors.app
          (((Stacks.SheafOfModules.Tensor.tensorComplex O').obj
            ((extendScalarsComplex α).obj P)).obj Nc)).symm ≪≫
          (restrict α).mapDerivedCategory.mapIso
            (T'.comparisonLeft ((extendScalarsComplex α).obj P) Nc
              (kFlat_extendScalarsComplex α P hP hflat)).symm

/-- **The projection formula at a change of coefficient rings**:

`M ⊗^L_O N|_O ≅ ((M ⊗^L_O O') ⊗^L_{O'} N)|_O`

for an object `M` of `D(O)` and a sheaf `N` of `O'`-modules.

`M` is replaced by its chosen K-flat model with flat terms, on which both sides are computed by
total tensor complexes and the identity is `projectionComplexIso`; the extension of scalars of
that model computes `M ⊗^L_O O'` by Stacks 06YY. -/
def projectionFormulaIso (M : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules O))
    (N : Stacks.DerivedTensor.RingedSite.Modules O') :
    (T.tensor.obj M).obj
        ((DerivedCategory.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules O) 0).obj
          ((restrict α).obj N)) ≅
      (restrict α).mapDerivedCategory.obj
        ((T'.tensor.obj ((Stacks.Cohomology.derivedCoefficientChange α).obj M)).obj
          ((DerivedCategory.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules O') 0).obj
            N)) :=
  (T.tensor.mapIso (flatModelIso O M).symm).app _ ≪≫
    projectionModelIso α T T' (flatModel O M) (kFlat_flatModel O M) (isFlat_flatModel O M) N ≪≫
      (restrict α).mapDerivedCategory.mapIso
        ((T'.tensor.mapIso
          ((derivedCoefficientChangeFlatIso α (flatModel O M) (kFlat_flatModel O M)
              (isFlat_flatModel O M)).symm ≪≫
            (Stacks.Cohomology.derivedCoefficientChange α).mapIso (flatModelIso O M))).app _)

end Stacks.Cohomology.CoefficientChange

end
