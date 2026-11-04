module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPieceTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtFromStrictlyPerfectResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProduct
import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# The self-Ext algebra of an object of `D(O_X)`, from a K-injective representative

Let `(X, O_X)` be a ringed space, let `I` be a K-injective complex of `O_X`-modules and let `A`
be an object of `D(O_X)` presented by an isomorphism `Q(I) ≅ A`. A K-injective target computes
the derived internal Hom, so

`RSheafHom(A, A) ≅ RSheafHom(Q I, Q I) ≅ Q(SheafHom^•(I, I))`,

and on `n`-th cohomology sheaves this reads the Ext sheaf `Ext^n_{O_X}(A, A)` as the `n`-th
cohomology sheaf of the internal Hom complex `SheafHom^•(I, I)`. The latter carries the
composition product of `Stacks.SheafOfModules.homologyGradedAlgebra`, a sheaf of graded
`O_X`-algebras, so the Ext sheaves of `A` do too.

Every object of `D(O_X)` has a K-injective representative, so every object of `D(O_X)` has a
self-Ext algebra, with no finiteness or boundedness hypothesis.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafExtIsoEndComplexHomology`: the Ext sheaf
  `Ext^n_{O_X}(A, A)` is the `n`-th cohomology sheaf of `SheafHom^•(I, I)`.
* `Stacks.SheafOfModules.extSelfGradedAlgebra`: **the self-Ext algebra of `A`**, a sheaf of
  graded `O_X`-algebras whose degree-`n` piece is `Ext^n_{O_X}(A, A)` by definition.
* `Stacks.SheafOfModules.kInjectiveModel`, `Stacks.SheafOfModules.kInjectiveModelIso`: a chosen
  K-injective presentation of an arbitrary object of `D(O_X)`.
* `Stacks.SheafOfModules.selfExtAlgebra`: **the self-Ext algebra of an arbitrary object of
  `D(O_X)`**, the previous construction at that choice.

## Main results

* `Stacks.SheafOfModules.extSelfGradedAlgebra_piece` and
  `Stacks.SheafOfModules.selfExtAlgebra_piece`: the pieces are the Ext sheaves.
* `Stacks.SheafOfModules.extSelfGradedAlgebra_mul_app`,
  `Stacks.SheafOfModules.extSelfGradedAlgebra_one_eval`: the multiplication and the unit on
  local sections, computed by the composition product of `SheafHom^•(I, I)` through the
  comparison.
* `Stacks.SheafOfModules.exists_kInjective_presentation`: every object of `D(O_X)` has a
  K-injective presentation.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 0BQP](https://stacks.math.columbia.edu/tag/0BQP)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Category Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive monoidalSpace' symmetricSpace'
  monoidalPreadditiveSpace' monoidalClosedSpace' preservesColimitTensorRightSpace'
  preservesFiniteColimitsTensorRight' preservesFiniteColimitsTensorLeft'

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective]

/-- **The self-Ext sheaves of an object presented by a K-injective complex are the cohomology
sheaves of its endomorphism Hom complex.** For `I` K-injective and `ε : Q(I) ≅ A`, the Ext sheaf
`Ext^n_{O_X}(A, A)` is the `n`-th cohomology sheaf of `SheafHom^•(I, I)`.

It is the composite of three isomorphisms: transport along `ε` in both variables, the comparison
identifying `RSheafHom(Q I, Q I)` with the class of `SheafHom^•(I, I)` on a K-injective target,
and the factorisation of the cohomology functor on the derived category through the cohomology
functor on complexes. -/
def derivedSheafExtIsoEndComplexHomology (A : DerivedCategory (StructureSheafModules Rc))
    (ε : DerivedCategory.Q.obj I ≅ A) (n : ℤ) :
    derivedSheafExt Rc A A n ≅ (endComplex Rc I).homology n :=
  derivedSheafExtMapIso Rc n ε ε.symm ≪≫
    (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).mapIso
      (derivedSheafHomComparison Rc I I) ≪≫
    (DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) n).app (endComplex Rc I)

/-- **The self-Ext algebra of an object of `D(O_X)` with a K-injective representative.** The
degree-`n` piece is the Ext sheaf `Ext^n_{O_X}(A, A)`, the multiplication is the composition
product of the internal Hom complex `SheafHom^•(I, I)` read through
`Stacks.SheafOfModules.derivedSheafExtIsoEndComplexHomology`, and the unit is the class of the
identity. -/
def extSelfGradedAlgebra (A : DerivedCategory (StructureSheafModules Rc))
    (ε : DerivedCategory.Q.obj I ≅ A) :
    _root_.SheafOfModules.GradedAlgebra (structureSheaf Rc) :=
  _root_.SheafOfModules.GradedAlgebra.ofPieceIso (homologyGradedAlgebra Rc I)
    (p := fun n => derivedSheafExt Rc A A n)
    (derivedSheafExtIsoEndComplexHomology Rc I A ε)

/-- The pieces of the self-Ext algebra are the Ext sheaves. -/
theorem extSelfGradedAlgebra_piece (A : DerivedCategory (StructureSheafModules Rc))
    (ε : DerivedCategory.Q.obj I ≅ A) (n : ℤ) :
    (extSelfGradedAlgebra Rc I A ε).piece n = derivedSheafExt Rc A A n :=
  rfl

/-- The multiplication of the self-Ext algebra is the composition product of `SheafHom^•(I, I)`,
read through the comparison. -/
theorem extSelfGradedAlgebra_mul_app (A : DerivedCategory (StructureSheafModules Rc))
    (ε : DerivedCategory.Q.obj I ≅ A) (i j : ℤ) (U : (Opens ↥X)ᵒᵖ)
    (x : (derivedSheafExt Rc A A i).val.obj U) (y : (derivedSheafExt Rc A A j).val.obj U) :
    ((extSelfGradedAlgebra Rc I A ε).mul i j).app U x y =
      (derivedSheafExtIsoEndComplexHomology Rc I A ε (i + j)).inv.val.app U
        ((homologyMul Rc I I I i j).app U
          ((derivedSheafExtIsoEndComplexHomology Rc I A ε i).hom.val.app U x)
          ((derivedSheafExtIsoEndComplexHomology Rc I A ε j).hom.val.app U y)) :=
  rfl

/-- The unit of the self-Ext algebra is the class of the identity, read through the
comparison. -/
theorem extSelfGradedAlgebra_one_eval (A : DerivedCategory (StructureSheafModules Rc))
    (ε : DerivedCategory.Q.obj I ≅ A) (U : (Opens ↥X)ᵒᵖ) :
    (extSelfGradedAlgebra Rc I A ε).one.eval U =
      (derivedSheafExtIsoEndComplexHomology Rc I A ε 0).inv.val.app U
        ((homologyOne Rc I).eval U) :=
  rfl

/-! ### K-injective presentations of objects of `D(O_X)` -/

/-- Sheaves of `O_X`-modules on a ringed space form a Grothendieck abelian category. -/
local instance isGrothendieckAbelian' :
    IsGrothendieckAbelian.{u} (StructureSheafModules Rc) :=
  _root_.SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheaf Rc)

/-- **Every object of `D(O_X)` is presented by a K-injective complex.** -/
theorem exists_kInjective_presentation (A : DerivedCategory (StructureSheafModules Rc)) :
    ∃ I : CochainComplex (StructureSheafModules Rc) ℤ,
      I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ A) := by
  obtain ⟨I, q, hI, hq⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    (DerivedCategory.Q.objPreimage A)
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  exact ⟨I, hI, ⟨(asIso (DerivedCategory.Q.map q)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso A⟩⟩

/-- A chosen K-injective complex presenting an object of `D(O_X)`. -/
def kInjectiveModel (A : DerivedCategory (StructureSheafModules Rc)) :
    CochainComplex (StructureSheafModules Rc) ℤ :=
  (exists_kInjective_presentation Rc A).choose

/-- The chosen complex `kInjectiveModel Rc A` is K-injective. -/
theorem isKInjective_kInjectiveModel (A : DerivedCategory (StructureSheafModules Rc)) :
    (kInjectiveModel Rc A).IsKInjective :=
  (exists_kInjective_presentation Rc A).choose_spec.1

/-- The isomorphism between the class of `kInjectiveModel Rc A` and `A`. -/
def kInjectiveModelIso (A : DerivedCategory (StructureSheafModules Rc)) :
    DerivedCategory.Q.obj (kInjectiveModel Rc A) ≅ A :=
  (exists_kInjective_presentation Rc A).choose_spec.2.some

/-- **The self-Ext algebra of an arbitrary object of `D(O_X)`**, a sheaf of graded
`O_X`-algebras whose degree-`n` piece is `Ext^n_{O_X}(A, A)` by definition, with the
composition product of a chosen K-injective model as its multiplication. -/
def selfExtAlgebra (A : DerivedCategory (StructureSheafModules Rc)) :
    _root_.SheafOfModules.GradedAlgebra (structureSheaf Rc) :=
  haveI := isKInjective_kInjectiveModel Rc A
  extSelfGradedAlgebra Rc (kInjectiveModel Rc A) A (kInjectiveModelIso Rc A)

/-- The pieces of the self-Ext algebra of an object of `D(O_X)` are its Ext sheaves. -/
theorem selfExtAlgebra_piece (A : DerivedCategory (StructureSheafModules Rc)) (n : ℤ) :
    (selfExtAlgebra Rc A).piece n = derivedSheafExt Rc A A n :=
  rfl

end Stacks.SheafOfModules

end
