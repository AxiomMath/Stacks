module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexShift

/-! # The two total tensor-product complexes on a ringed site agree

Let `(C, O)` be a ringed site and let `A` and `B` be complexes of sheaves of `O`-modules.
There are two constructions of their total tensor-product complex, and the sections of
Chapter 21 that use them disagree about which:

* `AlgebraicGeometry.RingedSite.tensorTotal` (Section 34, the source of the evaluation map of
  Stacks 0A92 and of the composition map of Stacks 0A91) takes the total complex of the
  double complex of *presheaf* tensor products and sheafifies it degreewise;
* `Stacks.SheafOfModules.Tensor.tensorComplex` (Section 17, the tensor product entering the
  derived tensor product of Stacks 06YU) tensors degreewise *as sheaves* -- that is, sheafifies
  each term -- and takes the total complex afterwards.

Degreewise the first is `sheafify (⨁_{p + q = n} A_p ⊗ B_q)` and the second is
`⨁_{p + q = n} sheafify (A_p ⊗ B_q)`. Sheafification of presheaves of modules is a left
adjoint, so it preserves those coproducts, and the two complexes are canonically isomorphic.
This file records that isomorphism and its naturality in both arguments.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`: the comparison isomorphism
  `tensorTotal X A B ≅ ((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj A).obj B`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex_naturality`: the comparison is
  natural in both arguments.
* `AlgebraicGeometry.RingedSite.mapBicomplex_presheafTensorBicomplex`,
  `AlgebraicGeometry.RingedSite.tensorTotalMap_eq_sheafifyTotalMap` and
  `AlgebraicGeometry.RingedSite.mapBifunctorMap_eq_totalMapSheafify`: the two constructions
  are "sheafify then totalise" and "totalise then sheafify" of one presheaf-level bicomplex,
  on objects and on morphisms.

## Implementation notes

All the work is done by `HomologicalComplex₂.TotalMap.totalIso`, which says that an additive
functor preserving the relevant coproducts commutes with the total complex of a bicomplex,
with no finiteness hypothesis on the bicomplex. What this file has to supply is that the two
constructions really are "total then sheafify" and "sheafify then total" *of one and the same
presheaf-level bicomplex*, and that is a definitional identity: the sheaf-level double complex
`((SheafOfModules.Tensor.sheafTensor X.O).mapBifunctorHomologicalComplex _ _).obj A |>.obj B`
is literally `HomologicalComplex₂.TotalMap.mapBicomplex` of the presheaf-level one, because
`Stacks.SheafOfModules.Tensor.sheafTensor` is by definition the presheaf tensor product of the
underlying presheaves followed by sheafification. So the comparison is
`HomologicalComplex₂.TotalMap.totalIso` transported by nothing at all, and the naturality
statement is `HomologicalComplex₂.TotalMap.totalIso_naturality`.

The map comparison with Section 34's monoidal encoding is checked on the linear maps of
presheaf sections, rather than by normalizing entire bicomplex records. The constructions in
this file use the native `PresheafOfModules.tensorBifunctor`. Naturality is obtained from the
generic totalization theorem by transporting the two map equalities in an abstract category.

The monoidal structure on presheaves of modules and the two `PreservesZeroMorphisms`
instances for the presheaf tensor bifunctor are
`AlgebraicGeometry.RingedSite.presheafOfModulesMonoidalCategory` and the two
`AlgebraicGeometry.RingedSite.curriedTensor*PreservesZeroMorphisms`, switched on here with
`attribute [local instance]`: they stay file-local because
`CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)` is a second route to the
`Ring` structure `RingCat` already carries, and re-declaring them here would give the monoidal
structure a second spelling that no later lemma could rewrite across. Sheafification is
additive, and it preserves coproducts because it is a left adjoint.

The universes are the diagonal `RingedSite.{u, u, u}`, which is where
`AlgebraicGeometry.RingedSite.tensorTotal` is stated.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

private lemma naturality_of_map_eq
    {CategoryType : Type*} [Category CategoryType]
    {leftSource leftTarget rightSource rightTarget : CategoryType}
    {leftMap leftMap' : leftSource ⟶ leftTarget}
    {rightMap rightMap' : rightSource ⟶ rightTarget}
    (comparison : rightSource ⟶ leftSource) (comparison' : rightTarget ⟶ leftTarget)
    (left_eq : leftMap = leftMap') (right_eq : rightMap = rightMap')
    (naturality : comparison ≫ leftMap' = rightMap' ≫ comparison') :
    comparison ≫ leftMap = rightMap ≫ comparison' :=
  (congrArg (fun morphism => comparison ≫ morphism) left_eq).trans
    (naturality.trans (congrArg (fun morphism => morphism ≫ comparison') right_eq).symm)

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-- The forgetful functor from sheaves of modules to presheaves of modules preserves zero
morphisms. -/
local instance :
    (SheafOfModules.forget.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Sheafification of presheaves of modules preserves coproducts, being a left adjoint. -/
local instance tensorComparisonSheafifyPreservesCoproducts {T : Type} :
    PreservesColimitsOfShape (Discrete T)
      (PresheafOfModules.sheafification.{u, u, u, u}
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) :=
  (PresheafOfModules.sheafificationAdjunction
    (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).leftAdjoint_preservesColimits
    |>.preservesColimitsOfShape

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The presheaf-level double complex of tensor products of the underlying presheaves of two
complexes of sheaves of modules. Both total tensor-product complexes are built from it:
`AlgebraicGeometry.RingedSite.tensorTotal` totalises it and then sheafifies degreewise, while
`Stacks.SheafOfModules.Tensor.tensorComplex` sheafifies it degreewise and then totalises. -/
abbrev presheafTensorBicomplex
    (A B : CochainComplex
      (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    HomologicalComplex₂
      (PresheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((PresheafOfModules.tensorBifunctor.{u, u, u, u, u} X.O.obj).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
      (((SheafOfModules.forget.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A)).obj
      (((SheafOfModules.forget.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj B)

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M : SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex
      (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]

omit [∀ (K L : CochainComplex
    (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
    (ComplexShape.up ℤ)] in
/-- The sheaf-level double complex of Section 17 is the presheaf-level double complex with
sheafification applied to every term, because `Stacks.SheafOfModules.Tensor.sheafTensor` is by
  definition
the presheaf tensor product of the underlying presheaves followed by sheafification. -/
theorem mapBicomplex_presheafTensorBicomplex
    (A B : CochainComplex
      (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj A).obj B =
      HomologicalComplex₂.TotalMap.mapBicomplex
        (PresheafOfModules.sheafification.{u, u, u, u}
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
        (presheafTensorBicomplex X A B) := rfl

/-- **The two total tensor-product complexes agree.** Sheafifying the total complex of the
double complex of presheaf tensor products gives the same complex as taking the total complex
of the sheafified double complex: `tensorTotal X A B ≅ Tot(A ⊗_O B)`. Degreewise this is the
statement that sheafification, being a left adjoint, commutes with the coproduct
`⨁_{p + q = n} A_p ⊗ B_q`. -/
def tensorTotalIsoTensorComplex
    (A B : CochainComplex
      (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotal X A B ≅ ((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj A).obj B :=
  (HomologicalComplex₂.TotalMap.totalIso
    (PresheafOfModules.sheafification.{u, u, u, u}
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
    (presheafTensorBicomplex X A B)).symm

/-- Sheafification applied degreewise to a bicomplex of presheaves of modules. -/
abbrev sheafifyBicomplex :
    HomologicalComplex₂
        (PresheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      HomologicalComplex₂ (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((PresheafOfModules.sheafification.{u, u, u, u}
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)

variable {A A' B B' : CochainComplex
  (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The morphism of presheaf-level double complexes induced by morphisms in both factors. -/
abbrev presheafTensorBicomplexMap (f : A ⟶ A') (g : B ⟶ B') :
    presheafTensorBicomplex X A B ⟶ presheafTensorBicomplex X A' B' :=
  (((PresheafOfModules.tensorBifunctor.{u, u, u, u, u} X.O.obj).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      (((SheafOfModules.forget.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)).app
      (((SheafOfModules.forget.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj B) ≫
    (((PresheafOfModules.tensorBifunctor.{u, u, u, u, u} X.O.obj).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
        (((SheafOfModules.forget.{u, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A')).map
          (((SheafOfModules.forget.{u, u, u, u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M : SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex
      (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)] in
/-- Section 34's functoriality of the total tensor product is sheafification applied to the
totalisation of the presheaf-level double-complex morphism. -/
theorem tensorTotalMap_eq_sheafifyTotalMap (f : A ⟶ A') (g : B ⟶ B') :
    tensorTotalMap X f g =
      ((PresheafOfModules.sheafification.{u, u, u, u}
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (HomologicalComplex₂.total.map (presheafTensorBicomplexMap X f g)
            (ComplexShape.up ℤ)) := by
  unfold tensorTotalMap HomologicalComplex.mapBifunctorMap
  apply congrArg (fun morphism =>
    ((PresheafOfModules.sheafification.{u, u, u, u}
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
      (HomologicalComplex₂.total.map morphism (ComplexShape.up ℤ)))
  exact HomologicalComplex.hom_ext _ _ fun _ => HomologicalComplex.hom_ext _ _ fun _ =>
    PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (TensorProduct.ext rfl)

/-- Section 17's functoriality of the total tensor product is the totalisation of the
sheafified presheaf-level double-complex morphism. Unlike
`tensorTotalMap_eq_sheafifyTotalMap` this is not a definitional identity: the sheaf-level
morphism is a composite of two sheafified morphisms where the presheaf-level one is the
sheafification of a composite. The two are identified by `Functor.map_comp` for
sheafification, applied degreewise. -/
theorem mapBifunctorMap_eq_totalMapSheafify (f : A ⟶ A') (g : B ⟶ B') :
    HomologicalComplex.mapBifunctorMap f g
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
        (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map
        ((sheafifyBicomplex X).map (presheafTensorBicomplexMap X f g))
        (ComplexShape.up ℤ) := by
  unfold HomologicalComplex.mapBifunctorMap
  apply congrArg (fun morphism => HomologicalComplex₂.total.map morphism (ComplexShape.up ℤ))
  refine HomologicalComplex.hom_ext _ _ fun _ => HomologicalComplex.hom_ext _ _ fun _ => ?_
  exact ((PresheafOfModules.sheafification.{u, u, u, u}
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map_comp _ _).symm

/-- The comparison of the two total tensor-product complexes is natural in both arguments. -/
theorem tensorTotalIsoTensorComplex_naturality (f : A ⟶ A') (g : B ⟶ B') :
    (tensorTotalIsoTensorComplex X A B).inv ≫ tensorTotalMap X f g =
      HomologicalComplex.mapBifunctorMap f g
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ) ≫ (tensorTotalIsoTensorComplex X A' B').inv :=
  naturality_of_map_eq (tensorTotalIsoTensorComplex X A B).inv
    (tensorTotalIsoTensorComplex X A' B').inv
    (tensorTotalMap_eq_sheafifyTotalMap X f g)
    (mapBifunctorMap_eq_totalMapSheafify X f g)
    (HomologicalComplex₂.TotalMap.totalIso_naturality (c₁₂ := ComplexShape.up ℤ)
      (PresheafOfModules.sheafification.{u, u, u, u}
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      (presheafTensorBicomplex X A B) (presheafTensorBicomplexMap X f g))

end AlgebraicGeometry.RingedSite

end
