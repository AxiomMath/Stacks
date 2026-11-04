module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompQh
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.ProjectionFormula
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# The projection formula map for étale sheaves of `Λ`-modules and base change

Let `Λ` be a commutative ring and let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes, with common composite `P`. The projection formula maps
`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)` and `Rf'_*E' ⊗^L_Λ K' ⟶ Rf'_*(E' ⊗^L_Λ f'⁻¹K')` are
compatible with the base change maps `g⁻¹Rf_* ⟶ Rf'_*g'⁻¹`: this is the hexagon of
[Stacks, Tag 0E48], for étale sheaves of `Λ`-modules. Its only input beyond the adjunction
calculus is the compatibility of the four comparisons `h⁻¹(- ⊗^L_Λ -) ≅ h⁻¹ - ⊗^L_Λ h⁻¹ -` around
the square with the comparison of the two composite inverse images, which holds because the
composition isomorphisms of inverse images are monoidal.

The base change map is the mate `Stacks.CategoryTheory.BaseChange.map`, for the two derived
adjunctions `Stacks.EtaleCohomology.etaleModuleDerivedAdjunction`, of the comparison of the two
composite derived inverse images around the square (`etaleModuleDerivedBaseChangeMate`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInverseImageCompIso'`: the composition isomorphism
  `(fg)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` of inverse images of étale sheaves of `Λ`-modules, with the composite
  named, as the isomorphism of left adjoints attached to the composition of direct images.
* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeMate`: the base change map
  `g⁻¹Rf_*M ⟶ Rf'_*g'⁻¹M` on `D(-_étale, Λ)`, as a mate.

## Main results

* `Stacks.EtaleCohomology.isMonoidal_etaleModuleInverseImageCompIso'_hom`: the composition
  isomorphisms are monoidal.
* `Stacks.EtaleCohomology.etaleModuleProjectionFormulaMap_baseChange`: **the hexagon**.
* `Stacks.EtaleCohomology.isIso_map_etaleModuleProjectionFormulaMap_of_isIso`: `g⁻¹` of the
  projection formula map of `f` at `(E, K)` is invertible as soon as the base change maps at `E`
  and at `E ⊗^L_Λ f⁻¹K` are, and the projection formula map of `f'` at `(g'⁻¹E, g⁻¹K)` is.

## References

* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 0943](https://stacks.math.columbia.edu/tag/0943)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Prod

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleMonoidalCategory isMonoidal_W_smallEtale_module
  HasDerivedCategory.standard etaleModuleInverseImageMonoidal etaleModuleDirectImageLaxMonoidal

variable (Λ : Type r) [CommRing Λ]

section Composition

variable {X Y Z : Scheme.{u}}

/-- The composition isomorphism `(fg)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` for inverse image of étale sheaves of
`Λ`-modules, with the composite `fg` carried as a named morphism: the isomorphism of left
adjoints attached to the composition isomorphism of direct images. -/
noncomputable def etaleModuleInverseImageCompIso' (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    etaleModuleInverseImage.{u, r} Λ fg ≅
      etaleModuleInverseImage.{u, r} Λ g ⋙ etaleModuleInverseImage.{u, r} Λ f :=
  (Adjunction.leftAdjointCompIso (etaleModuleInverseImageAdj.{u, r} Λ g)
    (etaleModuleInverseImageAdj.{u, r} Λ f) (etaleModuleInverseImageAdj.{u, r} Λ fg)
    (smallEtalePushforwardComp' f g fg hfg (ModuleCat.{max (u + 1) r} Λ))).symm

/-- **The composition isomorphism `(fg)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` of inverse images of étale sheaves of
`Λ`-modules is a monoidal natural isomorphism**: it is the conjugate of the composition
isomorphism of direct images, which is monoidal. -/
instance isMonoidal_etaleModuleInverseImageCompIso'_hom (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    NatTrans.IsMonoidal (etaleModuleInverseImageCompIso'.{u, r} Λ f g fg hfg).hom := by
  have : NatTrans.IsMonoidal
      (Adjunction.leftAdjointCompIso (etaleModuleInverseImageAdj.{u, r} Λ g)
        (etaleModuleInverseImageAdj.{u, r} Λ f) (etaleModuleInverseImageAdj.{u, r} Λ fg)
        (smallEtalePushforwardComp' f g fg hfg (ModuleCat.{max (u + 1) r} Λ))).hom :=
    Stacks.SheafPushforwardMonoidal.isMonoidal_leftAdjointCompIso_hom
      Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
      (ModuleCat.{max (u + 1) r} Λ) (smallEtaleBaseChangeComp' f g fg hfg).symm
      (etaleModuleInverseImageAdj.{u, r} Λ g) (etaleModuleInverseImageAdj.{u, r} Λ f)
      (etaleModuleInverseImageAdj.{u, r} Λ fg)
  exact inferInstanceAs (NatTrans.IsMonoidal
    (Adjunction.leftAdjointCompIso (etaleModuleInverseImageAdj.{u, r} Λ g)
      (etaleModuleInverseImageAdj.{u, r} Λ f) (etaleModuleInverseImageAdj.{u, r} Λ fg)
      (smallEtalePushforwardComp' f g fg hfg (ModuleCat.{max (u + 1) r} Λ))).inv)

end Composition

section Square

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g)

/-- **The four tensor isomorphisms around a commutative square of schemes are compatible with the
comparison of the two composite inverse images**, for étale sheaves of `Λ`-modules: going down
then across and going across then down give the same comparison
`f'⁻¹ g⁻¹ (M ⊗ N) ⟶ g'⁻¹ f⁻¹ M ⊗ g'⁻¹ f⁻¹ N`, because that comparison is a monoidal natural
isomorphism. -/
theorem etaleModuleInverseImageTensorIso_square (M N : EtaleModules.{u, r} Λ Y) :
    Eq
      ((etaleModuleInverseImage.{u, r} Λ f').map
          (etaleModuleInverseImageTensorIso.{u, r} Λ g M N).hom ≫
        (etaleModuleInverseImageTensorIso.{u, r} Λ f' ((etaleModuleInverseImage.{u, r} Λ g).obj M)
          ((etaleModuleInverseImage.{u, r} Λ g).obj N)).hom ≫
        ((etaleModuleTensor Λ X').map
          (((etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm ≪≫
            (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm.symm).hom.app M)).app
            ((etaleModuleInverseImage.{u, r} Λ f').obj
              ((etaleModuleInverseImage.{u, r} Λ g).obj N)) ≫
        ((etaleModuleTensor Λ X').obj ((etaleModuleInverseImage.{u, r} Λ g').obj
          ((etaleModuleInverseImage.{u, r} Λ f).obj M))).map
          (((etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm ≪≫
            (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm.symm).hom.app N))
      (((etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm ≪≫
          (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm.symm).hom.app
          (((etaleModuleTensor Λ Y).obj M).obj N) ≫
        (etaleModuleInverseImage.{u, r} Λ g').map
          (etaleModuleInverseImageTensorIso.{u, r} Λ f M N).hom ≫
        (etaleModuleInverseImageTensorIso.{u, r} Λ g' ((etaleModuleInverseImage.{u, r} Λ f).obj M)
          ((etaleModuleInverseImage.{u, r} Λ f).obj N)).hom) := by
  have : NatTrans.IsMonoidal ((etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm ≪≫
      (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm.symm).hom := by
    rw [Iso.symm_symm_eq, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have h := NatTrans.IsMonoidal.app_tensor_comp_δ
    ((etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm ≪≫
      (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm.symm).hom M N
  simp only [Functor.OplaxMonoidal.comp_δ, Category.assoc] at h
  simp only [etaleModuleInverseImageTensorIso_hom, curriedTensor_map_app,
    curriedTensor_obj_map, curriedTensor_obj_obj]
  rw [h, tensorHom_def]
  rfl

/-- **The base change map** `g⁻¹Rf_*M ⟶ Rf'_*g'⁻¹M` on `D(-_étale, Λ)`: the mate, for the two
derived adjunctions `f⁻¹ ⊣ Rf_*` and `f'⁻¹ ⊣ Rf'_*`, of the comparison of the two composite
derived inverse images around the square. -/
noncomputable abbrev etaleModuleDerivedBaseChangeMate
    (M : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategory.obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj M) ⟶
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').obj
        ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategory.obj M) :=
  Stacks.CategoryTheory.BaseChange.map (etaleModuleDerivedAdjunction.{u, r} Λ f)
    (etaleModuleDerivedAdjunction.{u, r} Λ f')
    (Functor.mapDerivedCategoryCompIsoOfIso
      (etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm).symm
    (Functor.mapDerivedCategoryCompIsoOfIso
      (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm).symm M

/-- **The four comparisons of inverse images with the derived tensor product over `Λ` around a
commutative square are compatible** with the comparison of the two composite inverse images.

The statement is the conclusion of
`CochainComplex.KFlatBifunctor.tensorComparisonCompatible_derivedTransportProdIso` as it stands,
with the comparisons written as the transports `derivedTransportProdIso` (which
`etaleModuleDerivedInverseImageTensorIso` abbreviates) and the composite comparisons as
`Functor.mapDerivedCategoryCompIsoOfIso`: restating it through those abbreviations makes the
kernel's definitional check of the statement time out. -/
theorem tensorComparisonCompatible_etaleModuleDerivedInverseImageTensorIso
    (M N : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    type_of% (CochainComplex.KFlatBifunctor.tensorComparisonCompatible_derivedTransportProdIso
    (F₁ := etaleModuleTensor.{u, r} Λ Y) (F₂ := etaleModuleTensor.{u, r} Λ Y')
    (F₃ := etaleModuleTensor.{u, r} Λ X) (F₄ := etaleModuleTensor.{u, r} Λ X')
    (T := etaleModuleInverseImage.{u, r} Λ g) (R := etaleModuleInverseImage.{u, r} Λ f')
    (L := etaleModuleInverseImage.{u, r} Λ f) (B := etaleModuleInverseImage.{u, r} Λ g')
    (P := etaleModuleInverseImage.{u, r} Λ P)
    (cL := (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm)
    (εL := fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f a b)
    (εB := fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ g' a b)
    (cT := (etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm)
    (εT := fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ g a b)
    (hεT₁ := fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ g φ N)
    (hεT₂ := fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ g M ψ)
    (εR := fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f' a b)
    (hεR₁ := fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f' φ N)
    (hεR₂ := fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f' M ψ)
    (hεL₁ := fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f φ N)
    (hεL₂ := fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f M ψ)
    (hεB₁ := fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ g' φ N)
    (hεB₂ := fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ g' M ψ)
    (hT₁ := fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g K hK)
    (hT₂ := fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g L hL)
    (hR₁ := fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f' K hK)
    (hR₂ := fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f' L hL)
    (hL₁ := fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f K hK)
    (hL₂ := fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f L hL)
    (hB₁ := fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g' K hK)
    (hB₂ := fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g' L hL)
    (hP₁ := fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ P K hK)
    (hP₂ := fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ P L hL)
    (hsq := fun a b ↦ etaleModuleInverseImageTensorIso_square.{u, r} Λ f g g' f' P hP₁ hP₂ a b)
    M N) :=
  CochainComplex.KFlatBifunctor.tensorComparisonCompatible_derivedTransportProdIso
    (F₁ := etaleModuleTensor.{u, r} Λ Y) (F₂ := etaleModuleTensor.{u, r} Λ Y')
    (F₃ := etaleModuleTensor.{u, r} Λ X) (F₄ := etaleModuleTensor.{u, r} Λ X')
    (T := etaleModuleInverseImage.{u, r} Λ g) (R := etaleModuleInverseImage.{u, r} Λ f')
    (L := etaleModuleInverseImage.{u, r} Λ f) (B := etaleModuleInverseImage.{u, r} Λ g')
    (P := etaleModuleInverseImage.{u, r} Λ P)
    (cL := (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm)
    (εL := fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f a b)
    (εB := fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ g' a b)
    (cT := (etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm)
    (εT := fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ g a b)
    (hεT₁ := fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ g φ N)
    (hεT₂ := fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ g M ψ)
    (εR := fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f' a b)
    (hεR₁ := fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f' φ N)
    (hεR₂ := fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f' M ψ)
    (hεL₁ := fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f φ N)
    (hεL₂ := fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f M ψ)
    (hεB₁ := fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ g' φ N)
    (hεB₂ := fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ g' M ψ)
    (hT₁ := fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g K hK)
    (hT₂ := fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g L hL)
    (hR₁ := fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f' K hK)
    (hR₂ := fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f' L hL)
    (hL₁ := fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f K hK)
    (hL₂ := fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f L hL)
    (hB₁ := fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g' K hK)
    (hB₂ := fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g' L hL)
    (hP₁ := fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ P K hK)
    (hP₂ := fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ P L hL)
    (hsq := fun a b ↦ etaleModuleInverseImageTensorIso_square.{u, r} Λ f g g' f' P hP₁ hP₂ a b)
    M N

/-- **The projection formula maps of étale sheaves of `Λ`-modules are compatible with base
change** ([Stacks, Tag 0E48]): for `E ∈ D(X_étale, Λ)` and `K ∈ D(Y_étale, Λ)`, the square relating
`g⁻¹` of the projection formula map of `f` at `(E, K)` with the projection formula map of `f'` at
`(g'⁻¹E, g⁻¹K)` through the base change maps at `E` and at `E ⊗^L_Λ f⁻¹K` commutes.

As for `tensorComparisonCompatible_etaleModuleDerivedInverseImageTensorIso`, the statement is the
conclusion of `Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square` as it stands:
the projection formula maps appear as `adjunctionTensorMap` of the transports, which is what
`etaleModuleProjectionFormulaMap` is. -/
theorem etaleModuleProjectionFormulaMap_baseChange
    (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    type_of% (Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square
      (etaleModuleDerivedAdjunction.{u, r} Λ f) (etaleModuleDerivedAdjunction.{u, r} Λ f')
      (Functor.mapDerivedCategoryCompIsoOfIso
        (etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm).symm
      (Functor.mapDerivedCategoryCompIsoOfIso
        (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm).symm
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ Y)))
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ Y')))
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ X)))
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ X')))
      (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ Y)
      (etaleModuleTensor.{u, r} Λ X) (etaleModuleInverseImage.{u, r} Λ f)
      (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f a b)
      (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f φ N)
      (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f M ψ)
      (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f K hK)
      (fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f L hL)).hom
      (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ Y')
      (etaleModuleTensor.{u, r} Λ X') (etaleModuleInverseImage.{u, r} Λ f')
      (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f' a b)
      (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f' φ N)
      (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f' M ψ)
      (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f' K hK)
      (fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f' L hL)).hom
      (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ Y)
      (etaleModuleTensor.{u, r} Λ Y') (etaleModuleInverseImage.{u, r} Λ g)
      (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ g a b)
      (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ g φ N)
      (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ g M ψ)
      (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g K hK)
      (fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g L hL)).hom
      (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ X)
      (etaleModuleTensor.{u, r} Λ X') (etaleModuleInverseImage.{u, r} Λ g')
      (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ g' a b)
      (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ g' φ N)
      (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ g' M ψ)
      (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g' K hK)
      (fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g' L hL)).hom
      E K (tensorComparisonCompatible_etaleModuleDerivedInverseImageTensorIso.{u, r}
        Λ f g g' f' P hP₁ hP₂ _ K)) :=
  Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square
      (etaleModuleDerivedAdjunction.{u, r} Λ f) (etaleModuleDerivedAdjunction.{u, r} Λ f')
      (Functor.mapDerivedCategoryCompIsoOfIso
        (etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm).symm
      (Functor.mapDerivedCategoryCompIsoOfIso
        (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm).symm
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ Y)))
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ Y')))
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ X)))
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ X')))
      (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ Y)
      (etaleModuleTensor.{u, r} Λ X) (etaleModuleInverseImage.{u, r} Λ f)
      (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f a b)
      (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f φ N)
      (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f M ψ)
      (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f K hK)
      (fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f L hL)).hom
      (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ Y')
      (etaleModuleTensor.{u, r} Λ X') (etaleModuleInverseImage.{u, r} Λ f')
      (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f' a b)
      (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f' φ N)
      (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f' M ψ)
      (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f' K hK)
      (fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f' L hL)).hom
      (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ Y)
      (etaleModuleTensor.{u, r} Λ Y') (etaleModuleInverseImage.{u, r} Λ g)
      (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ g a b)
      (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ g φ N)
      (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ g M ψ)
      (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g K hK)
      (fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g L hL)).hom
      (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ X)
      (etaleModuleTensor.{u, r} Λ X') (etaleModuleInverseImage.{u, r} Λ g')
      (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ g' a b)
      (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ g' φ N)
      (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ g' M ψ)
      (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g' K hK)
      (fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ g' L hL)).hom
      E K (tensorComparisonCompatible_etaleModuleDerivedInverseImageTensorIso.{u, r}
        Λ f g g' f' P hP₁ hP₂ _ K)

/-- The projection formula map of `f'` is the `adjunctionTensorMap` of the transport, as the
hexagon `etaleModuleProjectionFormulaMap_baseChange` writes it. -/
theorem isIso_adjunctionTensorMap_of_isIso_etaleModuleProjectionFormulaMap
    (A : DerivedCategory (EtaleModules.{u, r} Λ X'))
    (B : DerivedCategory (EtaleModules.{u, r} Λ Y'))
    (h : IsIso (etaleModuleProjectionFormulaMap.{u, r} Λ f' A B)) :
    IsIso (adjunctionTensorMap (etaleModuleDerivedAdjunction.{u, r} Λ f')
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ Y')))
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ X')))
      (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ Y')
        (etaleModuleTensor.{u, r} Λ X') (etaleModuleInverseImage.{u, r} Λ f')
        (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f' a b)
        (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f' φ N)
        (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f' M ψ)
        (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f' K hK)
        (fun L hL ↦
          kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f' L hL)).hom A B) := h

/-- `g⁻¹` of the projection formula map of `f`, read back from the `adjunctionTensorMap` of the
transport, as the hexagon `etaleModuleProjectionFormulaMap_baseChange` writes it. -/
theorem isIso_map_etaleModuleProjectionFormulaMap_of_isIso_map_adjunctionTensorMap
    (E : DerivedCategory (EtaleModules.{u, r} Λ X)) (K : DerivedCategory (EtaleModules.{u, r} Λ Y))
    (h : IsIso ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategory.map
      (adjunctionTensorMap (etaleModuleDerivedAdjunction.{u, r} Λ f)
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ Y)))
      (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ X)))
      (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ Y)
        (etaleModuleTensor.{u, r} Λ X) (etaleModuleInverseImage.{u, r} Λ f)
        (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f a b)
        (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f φ N)
        (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f M ψ)
        (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f K hK)
        (fun L hL ↦
          kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f L hL)).hom E K))) :
    IsIso ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategory.map
      (etaleModuleProjectionFormulaMap.{u, r} Λ f E K)) := h

/-- **`g⁻¹` of the projection formula map of étale sheaves of `Λ`-modules is invertible as soon
as the base change maps at `E` and at `E ⊗^L_Λ f⁻¹K` are, and the projection formula map of `f'`
at `(g'⁻¹E, g⁻¹K)` is.** -/
theorem isIso_map_etaleModuleProjectionFormulaMap_of_isIso
    (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y))
    (h₁ : IsIso (etaleModuleDerivedBaseChangeMate.{u, r} Λ f g g' f' P hP₁ hP₂ E))
    (h₂ : IsIso (etaleModuleDerivedBaseChangeMate.{u, r} Λ f g g' f' P hP₁ hP₂
      ((Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
        (etaleModuleTensor.{u, r} Λ X))).obj
          (E, (etaleModuleInverseImage.{u, r} Λ f).mapDerivedCategory.obj K))))
    (h₃ : IsIso (etaleModuleProjectionFormulaMap.{u, r} Λ f'
      ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategory.obj E)
      ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategory.obj K))) :
    IsIso ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategory.map
      (etaleModuleProjectionFormulaMap.{u, r} Λ f E K)) := by
  -- the hexagon, read as an equation `X ≫ Y ≫ Z = W ≫ V ≫ U` of morphisms with all of them but
  -- `W` invertible; the algebra is done on variables
  have key : ∀ {a b c d e e' : DerivedCategory (EtaleModules.{u, r} Λ Y')}
      (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) (w : a ⟶ e) (v : e ⟶ e') (t : e' ⟶ d),
      x ≫ y ≫ z = w ≫ v ≫ t → IsIso x → IsIso y → IsIso z → IsIso v → IsIso t → IsIso w := by
    intro a b c d e e' x y z w v t h _ _ _ _ _
    have : w = (x ≫ y ≫ z) ≫ inv t ≫ inv v := by
      rw [h]
      simp
    rw [this]
    infer_instance
  have h₃' := isIso_adjunctionTensorMap_of_isIso_etaleModuleProjectionFormulaMap.{u, r} Λ f'
    ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategory.obj E)
    ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategory.obj K) h₃
  refine isIso_map_etaleModuleProjectionFormulaMap_of_isIso_map_adjunctionTensorMap.{u, r}
    Λ f g E K ?_
  have : IsIso (etaleModuleDerivedBaseChangeMate.{u, r} Λ f g g' f' P hP₁ hP₂ E ×ₘ
      𝟙 ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategory.obj K)) :=
    (isIso_prod_iff _ _).2 ⟨h₁, inferInstance⟩
  have : IsIso (𝟙 ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategory.obj E) ×ₘ
      (Stacks.AffineProjectionFormula.squareCompositeIso
        (Functor.mapDerivedCategoryCompIsoOfIso
          (etaleModuleInverseImageCompIso'.{u, r} Λ f' g P hP₂).symm).symm
        (Functor.mapDerivedCategoryCompIsoOfIso
          (etaleModuleInverseImageCompIso'.{u, r} Λ g' f P hP₁).symm).symm).inv.app K) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  exact key _ _ _ _ _ _
    (etaleModuleProjectionFormulaMap_baseChange.{u, r} Λ f g g' f' P hP₁ hP₂ E K)
    inferInstance inferInstance h₃' h₂ inferInstance

end Square

end Stacks.EtaleCohomology

end
