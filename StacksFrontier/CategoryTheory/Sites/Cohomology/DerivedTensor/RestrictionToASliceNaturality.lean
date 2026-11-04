module

public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
public import StacksFrontier.CategoryTheory.Functor.NatIsoFromModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionNaturality

/-!
# Towards the naturality of `(K ⊗^L_O L)|_U ≅ K|_U ⊗^L_{O|_U} L|_U`

Let `(C, O)` be a ringed site and let `U` be an object of `C`. The comparison
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIso` identifies the restriction of a
derived tensor product to the site over `U` with the derived tensor product formed there. Its
module records that it supplies **no naturality**, and the naturality is what the derived
restriction compatibility of the canonical map of Stacks 08JD needs — see "What this file does
not contain" in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionRestriction` and in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals`.

This file assembles the inputs of that naturality: the two sides of the comparison as functors,
the comparison at a pair of K-flat complexes, and the squares its naturality splits into.

The route is the one of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomInterchange`: the
comparison at a pair of K-flat complexes is natural for morphisms *of complexes*, and naturality
for an arbitrary morphism of `D(O)` follows by the calculus of fractions, both slots being
factored through a single third pair of K-flat complexes. Since every object of `D(O)` is the
class of a K-flat complex, `CategoryTheory.NatIso.ofModels` then extends the comparison on those
pairs to a natural isomorphism of functors `D(O) × D(O) ⥤ D(O|_U)`.

## Main definitions

* `Stacks.DerivedTensor.SliceRestriction.tensorRestrictSourceFunctor` and
  `Stacks.DerivedTensor.SliceRestriction.tensorRestrictTargetFunctor`: the two sides of the
  comparison as functors `D(O) × D(O) ⥤ D(O|_U)`, namely `(K, L) ↦ (K ⊗^L_O L)|_U` and
  `(K, L) ↦ K|_U ⊗^L_{O|_U} L|_U`.
* `Stacks.DerivedTensor.SliceRestriction.tensorRestrictModels` and
  `Stacks.DerivedTensor.SliceRestriction.tensorRestrictModelObject`: the pairs of K-flat
  complexes, and the pair of objects of `D(O)` such a pair presents.
* `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictModelIso`: the comparison at a
  pair of K-flat complexes, seated between the values of the two functors — that is,
  `derivedTensorRestrictIsoOfKFlat` with the two identifications of a restricted class with the
  class of a restriction folded in, which is what makes its source and target literally the
  values of the two functors.

## Main results

* `AlgebraicGeometry.RingedSite.tensorComplexOverIso_hom_naturality`: the restriction
  comparison of the total tensor complex is natural in both variables at once, for morphisms of
  complexes.
* `AlgebraicGeometry.RingedSite.tensorComplexOverIso_hom_naturality_mapBifunctorMap`: the same
  square with the induced map of total complexes spelled in Mathlib's
  `HomologicalComplex.mapBifunctorMap` vocabulary, which is the vocabulary the naturality field
  of the derived tensor product datum of Stacks 06YU is stated in.
* `CategoryTheory.Functor.mapDerivedCategoryFactors_inv_naturality`: the naturality of Mathlib's
  identification of the derived functor of an exact functor with the functor it is induced by,
  read through the inverse of that identification.
* `CategoryTheory.Functor.bifunctorPairMap_comp`: the map of a bifunctor on a pair of morphisms
  is functorial, which is what splits a naturality square for a pair of morphisms into its two
  variables.
* `Stacks.DerivedTensor.SliceRestriction.tensorComplex_obj_obj_eq`: the total tensor complex of
  Stacks 06YM **is** `HomologicalComplex.mapBifunctor` of
  `Stacks.SheafOfModules.Tensor.sheafTensor`, by `rfl`.
* `Stacks.DerivedTensor.SliceRestriction.tensorOver_mapDerivedCategoryFactors_inv_naturality`:
  the square of the two trailing identifications of `derivedTensorRestrictModelIso`.

## What this file does not contain

**The naturality itself is not here**, and so neither is the natural isomorphism that
`CategoryTheory.NatIso.ofModels` would produce from the data below. The square

`tensorRestrictSourceFunctor.map (Qa, Qb) ≫ (derivedTensorRestrictModelIso n).hom =
  (derivedTensorRestrictModelIso m).hom ≫ tensorRestrictTargetFunctor.map (Qa, Qb)`

splits into five, along the four factors of `derivedTensorRestrictIsoOfKFlat` and the two
trailing identifications. Four are available here: the two comparison fields of the derived
tensor product data of Stacks 06YU enter as `comparison_naturality` itself, Mathlib's
`CategoryTheory.Functor.mapDerivedCategoryFactors_hom_naturality` covers the third, the
chain-level square of this file covers the fourth, and the fifth is
`tensorOver_mapDerivedCategoryFactors_inv_naturality` below. **All five, the square itself, the
calculus-of-fractions step and the natural isomorphism are now in the companion module**
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction`:
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictModelIso_hom_naturality`,
`derivedTensorRestrictModelIso_natural` and
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso`.

The difficulty lies between the first square and the third. In outline:

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparison` has target
  `Q(Tot(K ⊗_O L))` with the total complex spelled
  `Stacks.SheafOfModules.Tensor.tensorComplex`, while its naturality field
  `comparison_naturality` ends in `Q.map (HomologicalComplex.mapBifunctorMap f g ...)`, whose
  own implicit source and target are spelled `HomologicalComplex.mapBifunctor`. The composite
  `(comparison K L hK hL).hom ≫ Q.map (mapBifunctorMap f g ...)` recorded in that field
  therefore carries **both** spellings in its implicit arguments, and
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` is elaborated with the heartbeat limit
  raised tenfold for exactly that reason.
* No rewrite finds that composite: `rw`, `conv ... => rw`, `nth_rewrite` and a fully applied
  `Functor.map_comp` each fail with *did not find an occurrence of the
  pattern*. What works instead is not a rewrite at all. The identification of the two spellings
  is **cheap whenever both sides are concrete** — `tensorComplex_obj_obj_eq` below is `rfl` and
  costs nothing — and ruinous only when it has to be found through a metavariable under
  `DerivedCategory.Q.obj`. So the induced map of total complexes is given a name whose
  *ascribed type* is in the `tensorComplex` spelling,
  `Stacks.DerivedTensor.SliceRestriction.tensorComplexPairMap`; the identification is paid once,
  inside that definition, and every statement afterwards is in one spelling.
* Rewriting the goal with `tensorComplex_obj_obj_eq` to unify the spellings does not work: it
  changes the type of a subterm that `T.comparison A B hA hB` is an argument of, and `simp`
  then abandons the rewrite with an application type mismatch. The equation is still worth
  having — it is the cheap witness that the two spellings are `rfl`-equal in this instance
  context — but it cannot be used as a rewrite rule in the goal.
* `rw` with `CategoryTheory.Functor.bifunctorPairMap_comp` fails to match unless **every**
  object argument is supplied by name, because `mapDerivedCategoryFactors.app` spells its source
  through the composite functor `Q ⋙ F.mapDerivedCategory`; supplying them is what makes the
  fifth square below go through.

What makes any of these statements elaborate at all is **declaring the additivity of
`Stacks.SheafOfModules.Tensor.sheafTensor` and the `HomologicalComplex.HasMapBifunctor` family
explicitly in the variable block**, for both sites, as the sections below do and as
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASlice` does not: left
to instance search, each occurrence of the clash costs the whole budget on its own.

Note also that `mapBifunctorMap_eq_map₂_comp`, used by
`tensorComplexOverIso_hom_naturality_mapBifunctorMap` above, carries
`CategoryTheory.Functor.PreservesZeroMorphisms` hypotheses on the tensor bifunctor which, for
the structure sheaf of a ringed site, hold only through the file-local instances
`AlgebraicGeometry.RingedSite.curriedTensorPreservesZeroMorphisms` and
`AlgebraicGeometry.RingedSite.curriedTensorObjPreservesZeroMorphisms`: a statement made for a
bare `R : Sheaf J CommRingCat` rather than for `X.O` loses them, and instance search then
diverges instead of failing. The same holds for the respelled comparison square: over a bare
`R` it exhausts the budget, over `X.O` it is immediate.

Nothing below is tagged. The comparison this file prepares is the derived tensor product
analogue of Stacks 08JB, which is the statement for the derived internal Hom, and no assertion
of Stacks 08JJ follows from what is here.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction restrictionComplex
  kFlat_restrictionComplex)

universe d u

attribute [local instance] RingedSite.ringSheafSectionsCommRing
  RingedSite.presheafOfModulesMonoidalCategory
  RingedSite.curriedTensorPreservesZeroMorphisms
  RingedSite.curriedTensorObjPreservesZeroMorphisms
  RingedSite.ringSheafOverSectionsCommRing
  Stacks.hasSheafCompose_forget₂_commRingCat

namespace CategoryTheory.Functor

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{d} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{d} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The identification of the derived functor of an exact functor with the functor it is
induced by is natural**, read through the inverse of that identification: the class of the
restriction of a morphism of complexes followed by the inverse identification is the inverse
identification followed by the derived functor applied to the class of the morphism. -/
lemma mapDerivedCategoryFactors_inv_naturality {K L : CochainComplex C₁ ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫
        (F.mapDerivedCategoryFactors.app L).inv =
      (F.mapDerivedCategoryFactors.app K).inv ≫
        F.mapDerivedCategory.map (DerivedCategory.Q.map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (F.mapDerivedCategoryFactors_hom_naturality f).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.tensorComplex
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]

variable {A A' B B' :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The restriction comparison of the total tensor complex is natural in both variables at
once.** For morphisms of complexes `a : A ⟶ A'` and `b : B ⟶ B'` of `O`-modules, the restriction
of the induced map `Tot(A ⊗_O B) ⟶ Tot(A' ⊗_O B')` followed by the comparison at `(A', B')` is
the comparison at `(A, B)` followed by the map induced over `U` by the two restrictions.

This is the two one-variable squares of
`StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionNaturality` composed, the
map of a bifunctor on a pair of morphisms being the composite of its two one-variable maps. -/
lemma tensorComplexOverIso_hom_naturality (a : A ⟶ A') (b : B ⟶ B') :
    restrictComplexMap X U
          (((tensorComplex X.O).map a).app B ≫ ((tensorComplex X.O).obj A').map b) ≫
        (tensorComplexOverIso X U A' B').hom =
      (tensorComplexOverIso X U A B).hom ≫
        (((tensorComplex (X.O.over U)).map (restrictComplexMap X U a)).app
            (restrictComplex X B U) ≫
          ((tensorComplex (X.O.over U)).obj (restrictComplex X A' U)).map
            (restrictComplexMap X U b)) :=
  (congrArg (fun z => z ≫ (tensorComplexOverIso X U A' B').hom)
      (((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map_comp (((tensorComplex X.O).map a).app B)
          (((tensorComplex X.O).obj A').map b))).trans
    (((Category.assoc _ _ _).trans
        (congrArg (fun z => restrictComplexMap X U (((tensorComplex X.O).map a).app B) ≫ z)
          (tensorComplexOverIso_hom_naturality_right X U A' b))).trans
      (((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫
            ((tensorComplex (X.O.over U)).obj (restrictComplex X A' U)).map
              (restrictComplexMap X U b))
            (tensorComplexOverIso_hom_naturality_left X U a B))).trans
        (Category.assoc _ _ _)))

/-- **The restriction comparison of the total tensor complex is natural in both variables at
once**, with the induced map of total complexes spelled in Mathlib's
`HomologicalComplex.mapBifunctorMap` vocabulary.

This is the spelling the naturality field
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparison_naturality` of the derived
tensor product datum of Stacks 06YU is stated in, and it is therefore the form in which the
square above enters the transport of the comparison to the derived category. -/
lemma tensorComplexOverIso_hom_naturality_mapBifunctorMap (a : A ⟶ A') (b : B ⟶ B') :
    restrictComplexMap X U
          (HomologicalComplex.mapBifunctorMap a b (sheafTensor.{u, u, u, u, u} X.O)
            (ComplexShape.up ℤ)) ≫
        (tensorComplexOverIso X U A' B').hom =
      (tensorComplexOverIso X U A B).hom ≫
        @HomologicalComplex.mapBifunctorMap
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)))
          _ _ _ ℤ ℤ ℤ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          Preadditive.preadditiveHasZeroMorphisms Preadditive.preadditiveHasZeroMorphisms
          (SheafOfModules.instPreadditive (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)))
          _ _ _ _ (restrictComplexMap X U a) (restrictComplexMap X U b)
          (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (Functor.preservesZeroMorphisms_of_additive _)
          (fun _ => Functor.preservesZeroMorphisms_of_additive _)
          (ComplexShape.up ℤ) inferInstance inferInstance inferInstance inferInstance :=
  (congrArg (fun z => restrictComplexMap X U z ≫ (tensorComplexOverIso X U A' B').hom)
      (HomologicalComplex.mapBifunctorMap_eq_map₂_comp (sheafTensor.{u, u, u, u, u} X.O)
        (ComplexShape.up ℤ) a b)).symm.trans
    ((tensorComplexOverIso_hom_naturality X U a b).trans
      (congrArg (fun z => (tensorComplexOverIso X U A B).hom ≫ z)
        (@HomologicalComplex.mapBifunctorMap_eq_map₂_comp
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)))
          ℤ ℤ ℤ _ _ _
          Preadditive.preadditiveHasZeroMorphisms Preadditive.preadditiveHasZeroMorphisms
          (SheafOfModules.instPreadditive (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)))
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) _ _ _ _
          (sheafTensor.{u, u, u, u, u} (X.O.over U))
          (Functor.preservesZeroMorphisms_of_additive _)
          (fun _ => Functor.preservesZeroMorphisms_of_additive _)
          (ComplexShape.up ℤ) inferInstance inferInstance
          (Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor (X.O.over U))
          (restrictComplexMap X U a) (restrictComplexMap X U b))))

end AlgebraicGeometry.RingedSite

namespace CategoryTheory.Functor

/-- **The map of a bifunctor on a pair of morphisms is functorial.** Writing the map of
`H : C₁ ⥤ C₂ ⥤ C₃` on a pair `(u, v)` as the first-variable map followed by the second-variable
map, the composite of the maps on `(u, v)` and on `(u', v')` is the map on `(u ≫ u', v ≫ v')`.

This is the identity the `map_comp` fields of
`Stacks.DerivedTensor.SliceRestriction.tensorRestrictSourceFunctor` and
`Stacks.DerivedTensor.SliceRestriction.tensorRestrictTargetFunctor` are instances of, isolated
so that a naturality square for a pair of morphisms can be split into its two variables. -/
lemma bifunctorPairMap_comp {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂]
    {C₃ : Type*} [Category C₃] (H : C₁ ⥤ C₂ ⥤ C₃)
    {X₁ X₂ X₃ : C₁} {Y₁ Y₂ Y₃ : C₂} (u : X₁ ⟶ X₂) (u' : X₂ ⟶ X₃)
    (v : Y₁ ⟶ Y₂) (v' : Y₂ ⟶ Y₃) :
    ((H.map u).app Y₁ ≫ (H.obj X₂).map v) ≫ ((H.map u').app Y₂ ≫ (H.obj X₃).map v') =
      (H.map (u ≫ u')).app Y₁ ≫ (H.obj X₃).map (v ≫ v') := by
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
    NatTrans.naturality_assoc]

end CategoryTheory.Functor

namespace Stacks.DerivedTensor.SliceRestriction

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules X.O)]
  [HasDerivedCategory.{d} (Modules (X.O.over U))]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]
  (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
  (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over U))

/-- **The source of the comparison as a functor of both variables**: the restriction to the site
over `U` of the derived tensor product, `(K, L) ↦ (K ⊗^L_O L)|_U`.

The functor is spelled out by hand rather than assembled from `CategoryTheory.Functor.uncurry`
and the derived restriction functor, for the reason recorded in the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomInterchange`: the
assembled spelling presents each value as a composite, which makes identifying it with the class
of a complex prohibitively expensive. -/
def tensorRestrictSourceFunctor :
    DerivedCategory (Modules X.O) × DerivedCategory (Modules X.O) ⥤
      DerivedCategory (Modules (X.O.over U)) where
  obj d := (restriction X U).mapDerivedCategory.obj ((T.tensor.obj d.1).obj d.2)
  map {d e} f := (restriction X U).mapDerivedCategory.map
    ((T.tensor.map f.1).app d.2 ≫ (T.tensor.obj e.1).map f.2)
  map_id := by
    rintro ⟨d₁, d₂⟩
    simp only [CategoryTheory.prod_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.comp_id, CategoryTheory.Functor.map_id]
  map_comp := by
    rintro ⟨d₁, d₂⟩ ⟨e₁, e₂⟩ ⟨z₁, z₂⟩ ⟨f₁, f₂⟩ ⟨g₁, g₂⟩
    dsimp only [CategoryTheory.prod_comp]
    rw [← CategoryTheory.Functor.map_comp]
    congr 1
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
      NatTrans.naturality_assoc]

/-- **The target of the comparison as a functor of both variables**: the derived tensor product
over `U` of the two restrictions, `(K, L) ↦ K|_U ⊗^L_{O|_U} L|_U`. -/
def tensorRestrictTargetFunctor :
    DerivedCategory (Modules X.O) × DerivedCategory (Modules X.O) ⥤
      DerivedCategory (Modules (X.O.over U)) where
  obj d := (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj d.1)).obj
    ((restriction X U).mapDerivedCategory.obj d.2)
  map {d e} f :=
    (TU.tensor.map ((restriction X U).mapDerivedCategory.map f.1)).app
        ((restriction X U).mapDerivedCategory.obj d.2) ≫
      (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj e.1)).map
        ((restriction X U).mapDerivedCategory.map f.2)
  map_id := by
    rintro ⟨d₁, d₂⟩
    simp only [CategoryTheory.prod_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.comp_id]
  map_comp := by
    rintro ⟨d₁, d₂⟩ ⟨e₁, e₂⟩ ⟨z₁, z₂⟩ ⟨f₁, f₂⟩ ⟨g₁, g₂⟩
    dsimp only [CategoryTheory.prod_comp]
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
      NatTrans.naturality_assoc]

/-- The pairs of K-flat complexes of `O`-modules: the models on which the comparison is
constructed. Every object of `D(O)` is the class of a K-flat complex (Stacks 06YS), so every
pair of objects is presented by one of these. -/
abbrev tensorRestrictModels :=
  {A : CochainComplex (Modules X.O) ℤ // Stacks.SheafOfModules.KFlat.KFlat X.O A} ×
    {B : CochainComplex (Modules X.O) ℤ // Stacks.SheafOfModules.KFlat.KFlat X.O B}

/-- The pair of objects of `D(O)` that a pair of K-flat complexes presents. -/
abbrev tensorRestrictModelObject (m : tensorRestrictModels X) :
    DerivedCategory (Modules X.O) × DerivedCategory (Modules X.O) :=
  (DerivedCategory.Q.obj m.1.1, DerivedCategory.Q.obj m.2.1)

/-- **The comparison at a pair of K-flat complexes, seated between the values of the two
functors.** It is `derivedTensorRestrictIsoOfKFlat` followed by the two identifications of the
class of a restriction with the restriction of a class: those make the target literally
`tensorRestrictTargetFunctor` at the pair of classes, which is what a comparison extended by
`CategoryTheory.NatIso.ofModels` has to be. -/
def derivedTensorRestrictModelIso (m : tensorRestrictModels X) :
    (tensorRestrictSourceFunctor X U T).obj (tensorRestrictModelObject X m) ≅
      (tensorRestrictTargetFunctor X U TU).obj (tensorRestrictModelObject X m) :=
  derivedTensorRestrictIsoOfKFlat X U T TU m.1.1 m.2.1 m.1.2 m.2.2 ≪≫
    (TU.tensor.mapIso ((restriction X U).mapDerivedCategoryFactors.app m.1.1).symm).app
        (DerivedCategory.Q.obj ((restrictionComplex X U).obj m.2.1)) ≪≫
      (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj m.1.1))).mapIso
        ((restriction X U).mapDerivedCategoryFactors.app m.2.1).symm

/-! ### Naturality of the comparison for a pair of morphisms of complexes -/

omit [HasDerivedCategory.{d} (Modules X.O)] in
/-- **The total tensor complex of Stacks 06YM is the total complex of the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, by definition.** The equation is hoisted into its own
declaration because the two spellings sit on either side of a project `def` that no tactic will
unfold across, and because checking them equal is free here — with the additivity and
`HomologicalComplex.HasMapBifunctor` instances of the variable block in scope it is `rfl` — while
the same check inside a larger statement is what exhausts the heartbeat budget. -/
lemma tensorComplex_obj_obj_eq (A B : CochainComplex (Modules X.O) ℤ) :
    ((tensorComplex X.O).obj A).obj B =
      HomologicalComplex.mapBifunctor A B (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  rfl

omit [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)] in
/-- **The two trailing identifications of `derivedTensorRestrictModelIso` are natural.** They
turn the class of a restricted complex into the restriction of a class in each tensor factor, so
the square is the two-variable map of `TU.tensor` applied to
`CategoryTheory.Functor.mapDerivedCategoryFactors_inv_naturality` in each variable.

This is the last of the five factors the naturality square of `derivedTensorRestrictModelIso`
splits into, and the only one that mentions neither spelling of a total tensor complex. -/
lemma tensorOver_mapDerivedCategoryFactors_inv_naturality
    (A A' B B' : CochainComplex (Modules X.O) ℤ) (a : A ⟶ A') (b : B ⟶ B') :
    ((TU.tensor.map (DerivedCategory.Q.map ((restrictionComplex X U).map a))).app
          (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) ≫
        (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj A'))).map
          (DerivedCategory.Q.map ((restrictionComplex X U).map b))) ≫
      ((TU.tensor.map ((restriction X U).mapDerivedCategoryFactors.app A').inv).app
            (DerivedCategory.Q.obj ((restrictionComplex X U).obj B')) ≫
          (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj
            (DerivedCategory.Q.obj A'))).map
            ((restriction X U).mapDerivedCategoryFactors.app B').inv) =
    ((TU.tensor.map ((restriction X U).mapDerivedCategoryFactors.app A).inv).app
          (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) ≫
        (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj
          (DerivedCategory.Q.obj A))).map
          ((restriction X U).mapDerivedCategoryFactors.app B).inv) ≫
      ((TU.tensor.map ((restriction X U).mapDerivedCategory.map
              (DerivedCategory.Q.map a))).app
            ((restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj B)) ≫
          (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj
            (DerivedCategory.Q.obj A'))).map
            ((restriction X U).mapDerivedCategory.map (DerivedCategory.Q.map b))) := by
  have e₁ := CategoryTheory.Functor.bifunctorPairMap_comp TU.tensor
    (X₃ := (restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj A'))
    (Y₃ := (restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj B'))
    (DerivedCategory.Q.map ((restrictionComplex X U).map a))
    ((restriction X U).mapDerivedCategoryFactors.app A').inv
    (DerivedCategory.Q.map ((restrictionComplex X U).map b))
    ((restriction X U).mapDerivedCategoryFactors.app B').inv
  have e₂ := CategoryTheory.Functor.bifunctorPairMap_comp TU.tensor
    (X₁ := DerivedCategory.Q.obj ((restrictionComplex X U).obj A))
    (Y₁ := DerivedCategory.Q.obj ((restrictionComplex X U).obj B))
    (X₂ := (restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj A))
    (X₃ := (restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj A'))
    (Y₂ := (restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj B))
    (Y₃ := (restriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj B'))
    ((restriction X U).mapDerivedCategoryFactors.app A).inv
    ((restriction X U).mapDerivedCategory.map (DerivedCategory.Q.map a))
    ((restriction X U).mapDerivedCategoryFactors.app B).inv
    ((restriction X U).mapDerivedCategory.map (DerivedCategory.Q.map b))
  rw [e₁, e₂, (restriction X U).mapDerivedCategoryFactors_inv_naturality a,
    (restriction X U).mapDerivedCategoryFactors_inv_naturality b]

end Stacks.DerivedTensor.SliceRestriction

end
