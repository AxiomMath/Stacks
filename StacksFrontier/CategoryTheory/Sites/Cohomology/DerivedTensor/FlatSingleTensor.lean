module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex

/-!
# The derived tensor product with a flat module placed in degree zero

Let `R` be a sheaf of commutative rings on a small site and let `M` be a *flat* sheaf of
`R`-modules. Then `M` placed in degree zero is a K-flat complex, so the derived tensor product
`M ⊗^L_R -` of [Stacks, Tag 06YU] is computed by the ordinary total tensor complex, and that
complex is the ordinary tensor product `M ⊗_R -` applied degreewise. Consequently

`M[0] ⊗^L_R - ≅ (M ⊗_R -)^L`,

the derived functor of the exact functor `M ⊗_R -`. This is the identification that turns a
question about `M[0] ⊗^L_R K` into a question about sheaves, which is how Stacks 0D9E is proved:
there `M = g_{n!}ℤ`.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonLeftNatIso`: the left K-flat
  comparison of a derived tensor product read as an isomorphism of functors of the second
  variable.
* `HomologicalComplex.mapBifunctorSingleLeftNatIso`: `Tot(F(N[0], -)) ≅ F(N, -)` applied
  degreewise, as an isomorphism of functors on cochain complexes.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso`: **`M[0] ⊗^L_R -` is
  the derived functor of `M ⊗_R -`** for a flat `M`.

## Main results

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.exactFunctor_sheafTensorObj`: for a flat
  `M`, tensoring on the *left* with `M` is exact. Flatness is stated in this development as
  exactness of tensoring on the right, and the two are exchanged by the braiding
  `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso_hom_app_Q`: the value
  of the identification on the image of a complex.

## Implementation notes

The naturality of `HomologicalComplex.mapBifunctorSingleLeftIso` in the second variable is not
part of the existing objectwise statement and is proved here. In the `inv` direction the
component is `F(μ⁻¹)` followed by the inclusion of the summand of bidegree `(0, i)`
(`HomologicalComplex.singleLeftXIso_inv`), the action of `Tot` on a morphism of the second
variable hits that summand by `HomologicalComplex.ι_mapBifunctorMap`, and what remains is the
naturality of the natural transformation `F(μ⁻¹)`.

The passage from complexes to the derived category is the standard one: the composite
isomorphism is an isomorphism of the two functors precomposed with `DerivedCategory.Q`, and
`CategoryTheory.Localization.fullyFaithfulWhiskeringLeft` turns that into an isomorphism of the
two functors on the derived category, exactly as `CategoryTheory.derivedCompIso` does.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace HomologicalComplex

section SingleLeft

variable {C₁ : Type*} {C₂ : Type*} {D : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasZeroObject C₁]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ M : C₁, (F.obj M).PreservesZeroMorphisms]
  (N : C₁) [(F.obj N).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
    HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]

/-- **Naturality of `HomologicalComplex.singleLeftIsoMapBifunctor` in the second variable.** -/
theorem singleLeftIsoMapBifunctor_hom_naturality {K K' : CochainComplex C₂ ℤ} (g : K ⟶ K') :
    ((F.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).map g ≫
        (singleLeftIsoMapBifunctor F N K').hom =
      (singleLeftIsoMapBifunctor F N K).hom ≫
        mapBifunctorMap (𝟙 ((CochainComplex.singleFunctor C₁ 0).obj N)) g F
          (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  have h : ∀ (L : CochainComplex C₂ ℤ), (singleLeftIsoMapBifunctor F N L).hom.f i =
      (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv).app (L.X i) ≫
        singleLeftι F N L i := fun _ => rfl
  have hι : singleLeftι F N K i ≫
        (mapBifunctorMap (𝟙 ((CochainComplex.singleFunctor C₁ 0).obj N)) g F
          (ComplexShape.up ℤ)).f i =
      (F.obj (((CochainComplex.singleFunctor C₁ 0).obj N).X 0)).map (g.f i) ≫
        singleLeftι F N K' i := by
    refine Eq.trans (ι_mapBifunctorMap (𝟙 ((CochainComplex.singleFunctor C₁ 0).obj N)) g F
      (ComplexShape.up ℤ) 0 i i (by simp)) ?_
    rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp]
    rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, h, h, Category.assoc, hι,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (fun k => k ≫ singleLeftι F N K' i)
    ((F.map (singleObjXSelf (ComplexShape.up ℤ) 0 N).inv).naturality (g.f i))

omit [HasZeroObject C₁] in
/-- The action of the bifunctor of cochain complexes on a morphism of the second variable alone
is the total map of a pair with the identity in the first variable. -/
theorem map₂HomologicalComplex_obj_map (X : CochainComplex C₁ ℤ)
    {K K' : CochainComplex C₂ ℤ} (g : K ⟶ K') :
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj X).map g =
      mapBifunctorMap (𝟙 X) g F (ComplexShape.up ℤ) := rfl

/-- **`Tot(F(N[0], -))` is `F(N, -)` applied degreewise**, as an isomorphism of functors on
cochain complexes. -/
def mapBifunctorSingleLeftNatIso :
    (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor C₁ 0).obj N) ≅
      (F.obj N).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (NatIso.ofComponents (fun K => singleLeftIsoMapBifunctor F N K) (fun {_ _} g => by
    rw [map₂HomologicalComplex_obj_map]
    exact singleLeftIsoMapBifunctor_hom_naturality F N g)).symm

end SingleLeft

end HomologicalComplex

namespace Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

open Stacks.SheafOfModules.Tensor

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (T : DerivedTensorProduct R)

attribute [local instance] Stacks.SheafOfModules.Tensor.sheafTensorAdditiveLocal
  Stacks.SheafOfModules.Tensor.sheafTensorObjAdditiveLocal

/-- **The left K-flat comparison as an isomorphism of functors.** For a K-flat complex `K`, the
functor `Q(K) ⊗^L_R -` precomposed with `DerivedCategory.Q` is the ordinary total tensor complex
`Tot(K ⊗_R -)` followed by `Q`; this is `DerivedTensorProduct.comparisonLeft` read as a natural
isomorphism, its naturality field at the identity of `K`. -/
def comparisonLeftNatIso (K : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat R K) :
    DerivedCategory.Q ⋙ T.tensor.obj (DerivedCategory.Q.obj K) ≅
      (tensorComplex R).obj K ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun L => T.comparisonLeft K L hK) (fun {_ _} g => by
    have h := T.comparisonLeft_naturality (𝟙 K) g hK hK
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
    exact h)

section Flat

variable (M : Modules R)
  (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M)

include hM

/-- **Tensoring on the left with a flat module is exact.** Flatness is stated in this
development as exactness of tensoring on the *right*, and the braiding of the tensor product of
sheaves of modules exchanges the two. -/
theorem exactFunctor_sheafTensorObj :
    exactFunctor (Modules R) (Modules R) ((sheafTensor R).obj M) := by
  have h := (Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor R M).1 hM
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff _).1 h
  exact ⟨preservesFiniteLimits_of_natIso ((sheafTensorBraiding R).app M).symm,
    preservesFiniteColimits_of_natIso ((sheafTensorBraiding R).app M).symm⟩

/-- Tensoring on the left with a flat module preserves finite limits. -/
theorem preservesFiniteLimits_sheafTensorObj :
    PreservesFiniteLimits ((sheafTensor R).obj M) :=
  (exactFunctor_sheafTensorObj R M hM).1

/-- Tensoring on the left with a flat module preserves finite colimits. -/
theorem preservesFiniteColimits_sheafTensorObj :
    PreservesFiniteColimits ((sheafTensor R).obj M) :=
  (exactFunctor_sheafTensorObj R M hM).2

/-- The complex `M[0]` of a flat module is K-flat, in the spelling the comparisons of a
`DerivedTensorProduct` consume. -/
theorem kFlat_single :
    Stacks.SheafOfModules.KFlat R
      ((CochainComplex.singleFunctor (Modules R) 0).obj M) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R M hM 0

/-- The lifting datum exhibiting `M[0] ⊗^L_R -` and the derived functor of `M ⊗_R -` as two
lifts of one functor on complexes. -/
def flatSingleLifting :
    DerivedCategory.Q ⋙
        T.tensor.obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Modules R) 0).obj M)) ≅
      DerivedCategory.Q ⋙
        letI := preservesFiniteLimits_sheafTensorObj R M hM
        letI := preservesFiniteColimits_sheafTensorObj R M hM
        ((sheafTensor R).obj M).mapDerivedCategory :=
  letI := preservesFiniteLimits_sheafTensorObj R M hM
  letI := preservesFiniteColimits_sheafTensorObj R M hM
  comparisonLeftNatIso R T _ (kFlat_single R M hM) ≪≫
    Functor.isoWhiskerRight
      (HomologicalComplex.mapBifunctorSingleLeftNatIso (sheafTensor R) M) DerivedCategory.Q ≪≫
    ((sheafTensor R).obj M).mapDerivedCategoryFactors.symm

/-- **The derived tensor product with a flat module in degree zero is the derived functor of the
ordinary tensor product.** For a flat sheaf of `R`-modules `M`,

`M[0] ⊗^L_R - ≅ (M ⊗_R -)^L`

as functors on the unbounded derived category of `R`-modules. -/
def flatSingleTensorIso :
    T.tensor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Modules R) 0).obj M)) ≅
      letI := preservesFiniteLimits_sheafTensorObj R M hM
      letI := preservesFiniteColimits_sheafTensorObj R M hM
      ((sheafTensor R).obj M).mapDerivedCategory :=
  letI := preservesFiniteLimits_sheafTensorObj R M hM
  letI := preservesFiniteColimits_sheafTensorObj R M hM
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ))
    (DerivedCategory (Modules R))).preimageIso (flatSingleLifting R T M hM)

/-- **The value of `flatSingleTensorIso` on the image of a complex** is the lifting datum it was
built from: the identification is the preimage of that datum under whiskering with the
localization functor, so whiskering it back gives the datum. -/
theorem flatSingleTensorIso_hom_app_Q (L : CochainComplex (Modules R) ℤ) :
    (flatSingleTensorIso R T M hM).hom.app (DerivedCategory.Q.obj L) =
      (flatSingleLifting R T M hM).hom.app L := by
  let := preservesFiniteLimits_sheafTensorObj R M hM
  let := preservesFiniteColimits_sheafTensorObj R M hM
  have equality := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ))
    (DerivedCategory (Modules R))).map_preimage
      (X := T.tensor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Modules R) 0).obj M)))
      (Y := ((sheafTensor R).obj M).mapDerivedCategory)
      (flatSingleLifting R T M hM).hom
  exact congrArg (fun transformation => transformation.app L) equality

end Flat


end Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

end
