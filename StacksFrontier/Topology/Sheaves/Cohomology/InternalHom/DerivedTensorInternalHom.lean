module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of derived internal homs on a ringed space

Let `(X, O_X)` be a ringed space and let `K`, `K'`, `M`, `M'` be objects of `D(O_X)`. There is a
canonical morphism

`RSheafHom(K, K') ⊗^L_{O_X} RSheafHom(M, M') ⟶ RSheafHom(K ⊗^L_{O_X} M, K' ⊗^L_{O_X} M')`

in `D(O_X)`. This is Stacks 0FXP. Across the tensor–internal-hom adjunction of Stacks 08DI it
is the same datum as a morphism

`RSheafHom(K, K') ⊗^L RSheafHom(M, M') ⊗^L K ⊗^L M ⟶ K' ⊗^L M'`,

and that morphism is obtained by interchanging the two middle factors and then evaluating each
internal hom against its own source.

## Main definitions

* `Stacks.SheafOfModules.derivedMonoidalStructure` and
  `Stacks.SheafOfModules.derivedSymmetricStructure`: the symmetric monoidal structure on
  `D(O_X)` whose tensor product is the derived tensor product of Stacks 06YU on the nose.
* `Stacks.SheafOfModules.derivedSheafHomCounit`: the evaluation morphism
  `RSheafHom(L, M) ⊗^L_{O_X} L ⟶ M`, the counit of the adjunction of Stacks 08DI.
* `Stacks.SheafOfModules.derivedSheafHomTensorMap` (Stacks 0FXP): the canonical morphism.

## Main results

* `Stacks.SheafOfModules.curriedTensor_derivedMonoidalStructure`: the tensor product of
  `derivedMonoidalStructure` is `Stacks.SheafOfModules.derivedTensor`, as an equality of
  bifunctors.

## Implementation notes

The adjunction of Stacks 08DI is available here only as the bijection of morphism groups
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv`, not as a `CategoryTheory.Adjunction` or a
`CategoryTheory.MonoidalClosed` instance; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Exactness`. That is enough for both
uses made of it below: the evaluation morphism is the bijection applied to the identity, and
the morphism of Stacks 0FXP is the inverse bijection applied to the interchange.

The interchange of the middle two factors needs an associator and a braiding for the derived
tensor product, and `Stacks.SheafOfModules.DerivedTensorProduct` records neither.
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` supplies them, but for the
derived tensor product chosen in `Stacks.DerivedTensor.RingedSite`, which is a different
inhabitant of the same structure from the one the derived internal hom of this directory is
stated against. `derivedTensorAsSiteDatum` is that inhabitant read in the other spelling —
the same bifunctor and the same comparisons, no new choice — which lets
`Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso`, stated for an arbitrary
derived tensor product, compare the two and
`CategoryTheory.MonoidalCategory.reseat` transport the structure onto
`Stacks.SheafOfModules.derivedTensor`. After the transport `A ⊗ B` *is*
`((derivedTensor Rc).obj A).obj B`, so no `eqToHom` occurs below.

The braiding so obtained is the Koszul one of Stacks 0FNI, which is the sign convention the
source prescribes: `Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric` localizes
`CochainComplex.symmetricCategory`, whose braiding is `CochainComplex.koszulBraiding` by
`CochainComplex.symmetricCategory_braiding`, and both the localization and
`CategoryTheory.MonoidalCategory.reseatSymmetric` transport a braiding rather than replace it.

The evaluation morphism used below is `derivedSheafHomCounit`, the counit of the adjunction.
The source instead reaches evaluation as the composition morphism of Stacks 0A8V precomposed
with the identification `K ≅ RSheafHom(O_X, K)`. Both are the canonical evaluation, but
`Stacks.SheafOfModules.derivedSheafHomComposition` is constructed from the composition of
internal Hom complexes rather than from the adjunction, so that the two agree is a statement
about two constructions and is not proved here.

Stacks 0FXP is a remark asserting only that the morphism exists; it states no naturality, no
compatibility and no characterisation, and none is proved here.

## References

* [Stacks Project, Tag 0FXP](https://stacks.math.columbia.edu/tag/0FXP)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FNI](https://stacks.math.columbia.edu/tag/0FNI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The derived tensor product `- ⊗^L_{O_X} -` of a ringed space, read as a derived tensor
product of the ringed site of its opens: the same bifunctor, the same K-flat comparisons and
the same canonical map to the total tensor complex, in the spelling that the comparison with
the localized tensor bifunctor is stated for. -/
def derivedTensorAsSiteDatum : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct Rc :=
  let T := canonicalDerivedTensorProduct (ringedSite Rc)
  { tensor := T.tensor
    comparison := T.comparison
    comparison_naturality := T.comparison_naturality
    comparisonRight := T.comparisonRight
    comparisonRight_naturality := T.comparisonRight_naturality
    comparisonRight_eq_comparison := T.comparisonRight_eq_comparison
    comparisonLeft := T.comparisonLeft
    comparisonLeft_naturality := T.comparisonLeft_naturality
    comparisonLeft_eq_comparison := T.comparisonLeft_eq_comparison
    toTensor := T.toTensor
    toTensor_naturality := T.toTensor_naturality
    toTensor_eq_comparisonRight := T.toTensor_eq_comparisonRight
    toTensor_eq_comparisonLeft := T.toTensor_eq_comparisonLeft
    commShift₂ := T.commShift₂
    exact_left := T.exact_left
    exact_right := T.exact_right }

/-- The tensor product of the monoidal derived category of Stacks 0FPT is the derived tensor
product of `D(O_X)`, as an isomorphism of bifunctors. -/
def derivedTensorMonoidalIso :
    @curriedTensor (DerivedCategory (StructureSheafModules Rc)) _
        (DerivedMonoidal.derivedMonoidal Rc) ≅
      derivedTensor Rc :=
  DerivedMonoidal.derivedTensorBifunctorIso Rc ≪≫
    DerivedMonoidal.derivedBifunctorTensorIso Rc (derivedTensorAsSiteDatum Rc)

/-- **`D(O_X)` is monoidal with the derived tensor product as its tensor product**, on the
nose, and the structure sheaf in degree zero as its unit. The coherence is that of
Stacks 0FPT, transported along `derivedTensorMonoidalIso`. -/
@[instance_reducible]
def derivedMonoidalStructure : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
  @reseat _ _ (DerivedMonoidal.derivedMonoidal Rc) _ _ (derivedTensorMonoidalIso Rc)
    (DerivedMonoidal.canonicalUnitIso Rc)

/-- **That monoidal structure is symmetric**, with the commutativity constraint the Koszul
symmetry of Stacks 0FNI transported from complexes. -/
@[instance_reducible]
def derivedSymmetricStructure :
    @SymmetricCategory (DerivedCategory (StructureSheafModules Rc)) _
      (derivedMonoidalStructure Rc) :=
  @reseatSymmetric _ _ (DerivedMonoidal.derivedMonoidal Rc) _ _
    (DerivedMonoidal.derivedSymmetric Rc) (derivedTensorMonoidalIso Rc)
    (DerivedMonoidal.canonicalUnitIso Rc)

/-- The tensor product of `derivedMonoidalStructure` is the derived tensor product of
Stacks 06YU, as an equality of bifunctors. -/
theorem curriedTensor_derivedMonoidalStructure :
    @curriedTensor (DerivedCategory (StructureSheafModules Rc)) _
        (derivedMonoidalStructure Rc) =
      derivedTensor Rc :=
  rfl

/-- **Evaluation of a derived internal hom**, `RSheafHom(L, M) ⊗^L_{O_X} L ⟶ M`: the counit of
the tensor–internal-hom adjunction of Stacks 08DI, namely the bijection of Stacks 08DI applied
to the identity of `RSheafHom(L, M)`. -/
def derivedSheafHomCounit (L M : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj M)).obj L ⟶ M :=
  derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op L)).obj M) L M
    (𝟙 (((derivedSheafHom Rc).obj (op L)).obj M))

/-- **Stacks 0FXP.** For objects `K`, `K'`, `M`, `M'` of `D(O_X)` on a ringed space there is a
canonical morphism

`RSheafHom(K, K') ⊗^L_{O_X} RSheafHom(M, M') ⟶ RSheafHom(K ⊗^L_{O_X} M, K' ⊗^L_{O_X} M')`,

the morphism adjoint under Stacks 08DI to the interchange of the two middle factors of
`RSheafHom(K, K') ⊗^L RSheafHom(M, M') ⊗^L K ⊗^L M` followed by evaluation of each internal
hom. -/
@[stacks 0FXP]
def derivedSheafHomTensorMap (K K' M M' : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj K')).obj
        (((derivedSheafHom Rc).obj (op M)).obj M') ⟶
      ((derivedSheafHom Rc).obj (op (((derivedTensor Rc).obj K).obj M))).obj
        (((derivedTensor Rc).obj K').obj M') :=
  letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
    derivedMonoidalStructure Rc
  letI : SymmetricCategory (DerivedCategory (StructureSheafModules Rc)) :=
    derivedSymmetricStructure Rc
  let HK := ((derivedSheafHom Rc).obj (op K)).obj K'
  let HM := ((derivedSheafHom Rc).obj (op M)).obj M'
  let interchange : (HK ⊗ HM) ⊗ K ⊗ M ⟶ (HK ⊗ K) ⊗ HM ⊗ M :=
    (α_ HK HM (K ⊗ M)).hom ≫ HK ◁ (α_ HM K M).inv ≫ HK ◁ ((β_ HM K).hom ▷ M) ≫
      HK ◁ (α_ K HM M).hom ≫ (α_ HK K (HM ⊗ M)).inv
  (derivedSheafHomTensorEquiv Rc (HK ⊗ HM) (K ⊗ M) (K' ⊗ M')).symm
    (interchange ≫ (derivedSheafHomCounit Rc K K' ⊗ₘ derivedSheafHomCounit Rc M M'))

end Stacks.SheafOfModules

end
