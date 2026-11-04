module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.CategoryTheory.Functor.NatIsoFromModels
public import StacksFrontier.CategoryTheory.IsoNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
import StacksCore.Tactic.StacksAttribute

/-! # Functoriality of the derived currying isomorphism

Let `(C, O)` be a ringed site. **Stacks 08J9** asserts that the canonical isomorphism

`RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_O L, M)`

of `AlgebraicGeometry.RingedSite.derivedCurryIso` is functorial in the three objects `K`, `L`,
`M` of `D(O)`, and that it is the complex-level currying isomorphism of Stacks 0A90 whenever
`K`, `L`, `M` are the classes of complexes with the middle one K-flat and the target one
K-injective. This file proves both.

Both sides of the isomorphism are assembled into trifunctors
`AlgebraicGeometry.RingedSite.iteratedHomFunctor` and
`AlgebraicGeometry.RingedSite.tensorHomFunctor` on `D(O)ᵒᵖ × D(O)ᵒᵖ × D(O)`. On a triple of
complexes with K-flat middle and K-injective target the two trifunctors are computed by
internal Hom complexes — by Stacks 0A97 twice, using the K-injectivity of `SheafHom(B, I)` for
a K-flat `B` and a K-injective `I` (Stacks 0A96), and by the one-sided K-flat comparison of
the derived tensor product (Stacks 06YU) — and the currying isomorphism of Stacks 0A90 becomes
an isomorphism between their values which is natural for morphisms *of complexes*. Naturality
for an arbitrary morphism of `D(O)` between two such triples follows by the calculus of
fractions: each component factors through a third complex, which is repaired into an admissible
triple by a K-flat resolution (Stacks 06YS) in the middle slot and a K-injective resolution in
the target slot. Since every object of `D(O)` is the class of some complex, of some K-flat
complex and of some K-injective complex, the comparison extends to a natural isomorphism of
trifunctors, and the extension agrees with `derivedCurryIso` at every triple.

## Main definitions

* `AlgebraicGeometry.RingedSite.iteratedHomFunctor` and
  `AlgebraicGeometry.RingedSite.tensorHomFunctor`: the two sides of Stacks 08J9 as trifunctors
  on `D(O)ᵒᵖ × D(O)ᵒᵖ × D(O)`.
* `AlgebraicGeometry.RingedSite.iteratedHomRepresentativeIso` and
  `AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso`: the identifications of the two
  sides at a triple of complexes with K-flat middle and K-injective target with classes of
  internal Hom complexes.
* `AlgebraicGeometry.RingedSite.representativeCurryingIso`: the currying isomorphism of
  Stacks 0A90 read between those two identifications.
* `AlgebraicGeometry.RingedSite.homTensorModels`: the family of model triples, and
  `AlgebraicGeometry.RingedSite.chosenModel` the model chosen for a triple of objects.
* `AlgebraicGeometry.RingedSite.derivedCurryNatIso`: the derived currying isomorphism as a
  natural isomorphism between those two trifunctors.

## Main results

* `AlgebraicGeometry.RingedSite.model_currying_natural`: naturality of the comparison on models
  for an arbitrary morphism of `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedCurryNatIso_hom_app`: the natural isomorphism is
  `derivedCurryIso` at every triple of objects.
* `AlgebraicGeometry.RingedSite.derivedCurryIso_natural`: the three-variable naturality square
  for `derivedCurryIso`, for arbitrary morphisms of `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedCurryIso_eq_representativeCurryingIso` and
  `AlgebraicGeometry.RingedSite.derivedCurryIso_comparison`: on the classes of a triple of
  complexes with K-flat middle and K-injective target, `derivedCurryIso` is the complex-level
  currying isomorphism of Stacks 0A90.

## Implementation notes

The two trifunctors are spelled out by hand — explicit `obj`, `map`, `map_id` and `map_comp` —
rather than assembled from `CategoryTheory.Functor.uncurry`, the opposite-product equivalence
and the product associator. The assembled spelling names the same functors but presents each
component as a composite of four functors, which makes identifying its values with the internal
Hom complexes that compute them prohibitively expensive.

The identifications of the two sides at a model triple are stated with the trifunctors
themselves as their sources, rather than with the internal Hom and derived tensor product
spelled out. The two are definitionally equal, but only the former makes the composites that
appear in the naturality squares literally the ones the trifunctors produce.

The family of models is a product of subtypes rather than a structure with proof fields, so
that a model triple is a tuple and the projections used to state the model-level comparison
are definitional.

The models used to extend the comparison are the ones that `derivedCurryIso` is itself built
from — `AlgebraicGeometry.RingedSite.kInjectiveModel` in the first and third slots and
`AlgebraicGeometry.RingedSite.kFlatModel` in the second. That is what makes
`derivedCurryNatIso_hom_app` a reassociation of the two definitions rather than a comparison of
two unrelated choices of representatives.

The universes are the diagonal `RingedSite.{u, u, u}` of the whole derived internal Hom
cluster; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying`.

## References

* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Splitting a morphism induced by a bifunctor on homological complexes into its two
one-variable halves: the composite of the two is the morphism of total complexes induced in
both variables at once. -/
private lemma map₂HomologicalComplexReg_map_map
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ A, (F.obj A).PreservesZeroMorphisms]
    {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
    (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
    [∀ (K : HomologicalComplex C₁ c₁) (L : HomologicalComplex C₂ c₂),
      HomologicalComplex.HasMapBifunctorReg K L F c]
    {K K' : HomologicalComplex C₁ c₁} {L L' : HomologicalComplex C₂ c₂}
    (k : K ⟶ K') (l : L ⟶ L') :
    ((F.map₂HomologicalComplexReg c₁ c₂ c).map k).app L ≫
        ((F.map₂HomologicalComplexReg c₁ c₂ c).obj K').map l =
      HomologicalComplex.mapBifunctorMapReg k l F c := by
  show HomologicalComplex.mapBifunctorMap k (𝟙 L) F c ≫
    HomologicalComplex.mapBifunctorMap (𝟙 K') l F c = HomologicalComplex.mapBifunctorMap k l F c
  dsimp only [HomologicalComplex.mapBifunctorMap]
  rw [((F.mapBifunctorHomologicalComplex c₁ c₂).obj K').map_id,
    (F.mapBifunctorHomologicalComplex c₁ c₂).map_id]
  simp only [NatTrans.id_app, Category.id_comp, Category.comp_id,
    HomologicalComplex₂.total.map_comp]

/-! Transposing a naturality square across the inverses of its two vertical isomorphisms is
`CategoryTheory.iso_inv_naturality`, imported. -/

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- Triples of objects of `D(O)`, contravariant in the first two slots and covariant in the
third: the common source of the two sides of Stacks 08J9. -/
abbrev derivedTriples :=
  (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The left-hand side of Stacks 08J9 as a trifunctor: the iterated derived internal Hom
`(K, L, M) ↦ RSheafHom(K, RSheafHom(L, M))`. -/
def iteratedHomFunctor :
    derivedTriples X ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  obj d := ((derivedSheafHomBifunctor X).obj d.1).obj
    (((derivedSheafHomBifunctor X).obj d.2.1).obj d.2.2)
  map {d e} f :=
    ((derivedSheafHomBifunctor X).map f.1).app
        (((derivedSheafHomBifunctor X).obj d.2.1).obj d.2.2) ≫
      ((derivedSheafHomBifunctor X).obj e.1).map
        (((derivedSheafHomBifunctor X).map f.2.1).app d.2.2 ≫
          ((derivedSheafHomBifunctor X).obj e.2.1).map f.2.2)
  map_id := by
    rintro ⟨d₁, d₂, d₃⟩
    simp only [CategoryTheory.prod_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.comp_id]
  map_comp := by
    rintro ⟨d₁, d₂, d₃⟩ ⟨e₁, e₂, e₃⟩ ⟨z₁, z₂, z₃⟩ ⟨f₁, f₂, f₃⟩ ⟨g₁, g₂, g₃⟩
    dsimp only [CategoryTheory.prod_comp]
    have hinner :
        ((derivedSheafHomBifunctor X).map (f₂ ≫ g₂)).app d₃ ≫
            ((derivedSheafHomBifunctor X).obj z₂).map (f₃ ≫ g₃) =
          (((derivedSheafHomBifunctor X).map f₂).app d₃ ≫
              ((derivedSheafHomBifunctor X).obj e₂).map f₃) ≫
            (((derivedSheafHomBifunctor X).map g₂).app e₃ ≫
              ((derivedSheafHomBifunctor X).obj z₂).map g₃) := by
      simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
        NatTrans.naturality_assoc]
    have houter :
        ((derivedSheafHomBifunctor X).obj z₁).map
              (((derivedSheafHomBifunctor X).map g₂).app d₃) ≫
            ((derivedSheafHomBifunctor X).obj z₁).map
              (((derivedSheafHomBifunctor X).obj z₂).map f₃) =
          ((derivedSheafHomBifunctor X).obj z₁).map
              (((derivedSheafHomBifunctor X).obj e₂).map f₃) ≫
            ((derivedSheafHomBifunctor X).obj z₁).map
              (((derivedSheafHomBifunctor X).map g₂).app e₃) := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        NatTrans.naturality]
    rw [hinner]
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
      NatTrans.naturality_assoc]
    rw [reassoc_of% houter]

/-- The right-hand side of Stacks 08J9 as a trifunctor: the derived internal Hom out of the
derived tensor product, `(K, L, M) ↦ RSheafHom(K ⊗^L_O L, M)`. -/
def tensorHomFunctor :
    derivedTriples X ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  obj d := ((derivedSheafHomBifunctor X).obj
    (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj d.1.unop).obj
      d.2.1.unop))).obj d.2.2
  map {d e} f :=
    ((derivedSheafHomBifunctor X).map
        ((((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f.1.unop).app e.2.1.unop ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj d.1.unop).map
            f.2.1.unop).op)).app d.2.2 ≫
      ((derivedSheafHomBifunctor X).obj
        (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj e.1.unop).obj
          e.2.1.unop))).map f.2.2
  map_id := by
    rintro ⟨d₁, d₂, d₃⟩
    simp only [CategoryTheory.prod_id, unop_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.comp_id, op_id]
  map_comp := by
    rintro ⟨d₁, d₂, d₃⟩ ⟨e₁, e₂, e₃⟩ ⟨z₁, z₂, z₃⟩ ⟨f₁, f₂, f₃⟩ ⟨g₁, g₂, g₃⟩
    dsimp only [CategoryTheory.prod_comp]
    have hτ :
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map (f₁ ≫ g₁).unop).app
              z₂.unop ≫
            ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj d₁.unop).map
              (f₂ ≫ g₂).unop =
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g₁.unop).app z₂.unop ≫
              ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj e₁.unop).map
                g₂.unop) ≫
            (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f₁.unop).app e₂.unop ≫
              ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj d₁.unop).map
                f₂.unop) := by
      simp only [unop_comp, CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
        NatTrans.naturality_assoc]
    have hτ' :
        (derivedSheafHomBifunctor X).map
            ((((Stacks.SheafOfModules.derivedTensorProductFunctor X).map (f₁ ≫ g₁).unop).app
                z₂.unop ≫
              ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj d₁.unop).map
                (f₂ ≫ g₂).unop).op) =
          (derivedSheafHomBifunctor X).map
              ((((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f₁.unop).app
                  e₂.unop ≫
                ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj d₁.unop).map
                  f₂.unop).op) ≫
            (derivedSheafHomBifunctor X).map
              ((((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g₁.unop).app
                  z₂.unop ≫
                ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj e₁.unop).map
                  g₂.unop).op) := by
      rw [← CategoryTheory.Functor.map_comp, ← op_comp, hτ]
    rw [hτ', NatTrans.comp_app]
    simp only [Category.assoc]
    rw [NatTrans.naturality_assoc, CategoryTheory.Functor.map_comp]

/-- The triple of objects of `D(O)` represented by a triple of complexes. -/
abbrev modelTriple
    (K L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    derivedTriples X :=
  (op (DerivedCategory.Q.obj K), op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I)

/-- **An iterated derived internal Hom at a K-flat middle complex and a K-injective target.**
It is the class of the iterated internal Hom complex `SheafHom(K, SheafHom(L, I))`: the inner
internal Hom complex is K-injective by Stacks 0A96, so each of the two derived internal Homs is
computed by its K-injective target, by Stacks 0A97. -/
def iteratedHomRepresentativeIso
    (K L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (iteratedHomFunctor X).obj (modelTriple X K L I) ≅
      DerivedCategory.Q.obj (sheafHomComplex X K (sheafHomComplex X L I).obj).obj :=
  haveI := isKInjective_sheafHomComplex_of_isKFlat X L I hL
  ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).mapIso
      (derivedSheafHomComparison X L I) ≪≫
    derivedSheafHomComparison X K (sheafHomComplex X L I).obj

/-- **A derived internal Hom out of a derived tensor product with a K-flat right factor and
into a K-injective target.** It is the class of the internal Hom complex
`SheafHom(Tot(K ⊗_O L), I)`: the derived tensor product is computed by the total tensor complex
because the right factor is K-flat (Stacks 06YU), and the derived internal Hom out of it is
computed by its K-injective target (Stacks 0A97). -/
def tensorHomRepresentativeIso
    (K L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (tensorHomFunctor X).obj (modelTriple X K L I) ≅
      DerivedCategory.Q.obj
        (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L)
          I).obj :=
  ((derivedSheafHomBifunctor X).mapIso
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight K L
          hL).symm.op).app (DerivedCategory.Q.obj I) ≪≫
    derivedSheafHomComparison X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) I

/-- **The derived currying isomorphism at a K-flat middle complex and a K-injective target.**
It is the currying isomorphism of complexes of Stacks 0A90, conjugated by the two
identifications of the derived objects with classes of internal Hom complexes. -/
def representativeCurryingIso
    (K L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (iteratedHomFunctor X).obj (modelTriple X K L I) ≅
      (tensorHomFunctor X).obj (modelTriple X K L I) :=
  iteratedHomRepresentativeIso X K L I hL ≪≫
    DerivedCategory.Q.mapIso (sheafHomTensorCurryIso X K L I) ≪≫
      (tensorHomRepresentativeIso X K L I hL).symm

/-- The derived currying isomorphism at a model triple is the complex-level currying
isomorphism, read through the two identifications with classes of internal Hom complexes. -/
theorem representativeCurryingIso_comparison
    (K L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (representativeCurryingIso X K L I hL).hom ≫
        (tensorHomRepresentativeIso X K L I hL).hom =
      (iteratedHomRepresentativeIso X K L I hL).hom ≫
        DerivedCategory.Q.map (sheafHomTensorCurryIso X K L I).hom := by
  dsimp only [representativeCurryingIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {K K' L L' I I' :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The morphism of model triples induced by three morphisms of complexes, contravariant in
the first two and covariant in the third. -/
private abbrev modelMap (k : K' ⟶ K) (l : L' ⟶ L) (m : I ⟶ I') :
    modelTriple X K L I ⟶ modelTriple X K' L' I' :=
  ((DerivedCategory.Q.map k).op, (DerivedCategory.Q.map l).op, DerivedCategory.Q.map m)

/-- The morphism of total tensor complexes induced by a morphism in each factor. -/
private abbrev tensorMap (k : K' ⟶ K) (l : L' ⟶ L) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K').obj L' ⟶
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L :=
  HomologicalComplex.mapBifunctorMap k l (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)

/-- The iterated-internal-Hom model is natural in the three complexes, for the induced maps
`homMap` of internal Hom complexes. -/
private lemma iteratedHomRepresentativeIso_natural
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) (hL' : Stacks.SheafOfModules.IsKFlat X.O L')
    [I.IsKInjective] [I'.IsKInjective] (k : K' ⟶ K) (l : L' ⟶ L) (m : I ⟶ I') :
    (iteratedHomFunctor X).map (modelMap X k l m) ≫
        (iteratedHomRepresentativeIso X K' L' I' hL').hom =
      (iteratedHomRepresentativeIso X K L I hL).hom ≫
        DerivedCategory.Q.map (homMap X k (homMap X l m)) := by
  have := isKInjective_sheafHomComplex_of_isKFlat X L I hL
  have := isKInjective_sheafHomComplex_of_isKFlat X L' I' hL'
  have hi := derivedSheafHomComparison_naturality X l m
  have ho := derivedSheafHomComparison_naturality X k (homMap X l m)
  dsimp only [iteratedHomFunctor, iteratedHomRepresentativeIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc]
  rw [hi]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← NatTrans.naturality_assoc, ho]

/-- The tensor-internal-Hom model is natural in the three complexes, for the induced maps
`homMap` of internal Hom complexes and the induced maps of total tensor complexes. -/
private lemma tensorHomRepresentativeIso_natural
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) (hL' : Stacks.SheafOfModules.IsKFlat X.O L')
    [I.IsKInjective] [I'.IsKInjective] (k : K' ⟶ K) (l : L' ⟶ L) (m : I ⟶ I') :
    (tensorHomFunctor X).map (modelMap X k l m) ≫
        (tensorHomRepresentativeIso X K' L' I' hL').hom =
      (tensorHomRepresentativeIso X K L I hL).hom ≫
        DerivedCategory.Q.map (homMap X (tensorMap X k l) m) := by
  have ht0 : (((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).tensor.map
            (DerivedCategory.Q.map k)).app (DerivedCategory.Q.obj L') ≫
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).tensor.obj
            (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map l)) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight K L hL).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight K' L' hL').hom ≫
        DerivedCategory.Q.map (tensorMap X k l) := by
    rw [Category.assoc]
    exact (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight_naturality
      k l hL' hL
  have ht := iso_inv_naturality
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight K' L' hL')
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight K L hL) _ _ ht0
  have hh := derivedSheafHomComparison_naturality X (tensorMap X k l) m
  dsimp only [tensorHomFunctor, tensorHomRepresentativeIso,
    Stacks.SheafOfModules.derivedTensorProductFunctor, Quiver.Hom.unop_op, Iso.trans_hom,
    Iso.symm_hom, Iso.op, Iso.app_hom, CategoryTheory.Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [NatTrans.naturality_assoc, ← hh]
  simp only [← NatTrans.comp_app_assoc, ← CategoryTheory.Functor.map_comp, ← op_comp]
  rw [← ht]

/-- The derived currying isomorphism at a model triple is natural in the three complexes. -/
private lemma representativeCurryingIso_natural
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) (hL' : Stacks.SheafOfModules.IsKFlat X.O L')
    [I.IsKInjective] [I'.IsKInjective] (k : K' ⟶ K) (l : L' ⟶ L) (m : I ⟶ I') :
    (iteratedHomFunctor X).map (modelMap X k l m) ≫
        (representativeCurryingIso X K' L' I' hL').hom =
      (representativeCurryingIso X K L I hL).hom ≫
        (tensorHomFunctor X).map (modelMap X k l m) := by
  have e₁ : (iteratedHomFunctor X).map (modelMap X k l m) ≫
        (representativeCurryingIso X K' L' I' hL').hom ≫
        (tensorHomRepresentativeIso X K' L' I' hL').hom =
      (iteratedHomRepresentativeIso X K L I hL).hom ≫
        DerivedCategory.Q.map (homMap X k (homMap X l m)) ≫
        DerivedCategory.Q.map (sheafHomTensorCurryIso X K' L' I').hom := by
    rw [representativeCurryingIso_comparison X K' L' I' hL',
      ← Category.assoc ((iteratedHomFunctor X).map (modelMap X k l m)),
      iteratedHomRepresentativeIso_natural X hL hL' k l m, Category.assoc]
  have e₂ : (representativeCurryingIso X K L I hL).hom ≫
        (tensorHomFunctor X).map (modelMap X k l m) ≫
        (tensorHomRepresentativeIso X K' L' I' hL').hom =
      (iteratedHomRepresentativeIso X K L I hL).hom ≫
        DerivedCategory.Q.map (sheafHomTensorCurryIso X K L I).hom ≫
        DerivedCategory.Q.map (homMap X (tensorMap X k l) m) := by
    rw [tensorHomRepresentativeIso_natural X hL hL' k l m,
      ← Category.assoc (representativeCurryingIso X K L I hL).hom,
      representativeCurryingIso_comparison X K L I hL, Category.assoc]
  apply (cancel_mono (tensorHomRepresentativeIso X K' L' I' hL').hom).1
  rw [Category.assoc, Category.assoc, e₁, e₂]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  simpa only [Stacks.SheafOfModules.Tensor.tensorComplex, map₂HomologicalComplexReg_map_map] using
    sheafHomTensorCurryIso_natural X k l m

/-- The models on which the derived currying isomorphism is constructed: an arbitrary complex,
a K-flat complex and a K-injective complex. Every triple of objects of `D(O)` is represented by
one, and that is what makes the comparison on models extend to all of `D(O)`. -/
abbrev homTensorModels :=
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ×
    {L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ //
      Stacks.SheafOfModules.IsKFlat X.O L} ×
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ //
      I.IsKInjective}

/-- The triple of objects of `D(O)` represented by a model. -/
abbrev modelObject (a : homTensorModels X) : derivedTriples X :=
  modelTriple X a.1 a.2.1.1 a.2.2.1

/-- The derived currying isomorphism at a model. -/
def modelCurrying (a : homTensorModels X) :
    (iteratedHomFunctor X).obj (modelObject X a) ≅
      (tensorHomFunctor X).obj (modelObject X a) :=
  haveI := a.2.2.2
  representativeCurryingIso X a.1 a.2.1.1 a.2.2.1 a.2.1.2

/-- **Naturality of the derived currying isomorphism between models, for an arbitrary morphism
of `D(O)`.** Each of the three components of the morphism is factored as a fraction through a
third complex, contravariantly in the first two slots and covariantly in the third; the apex is
made into a model by a K-flat resolution in the middle slot and the K-injective resolution in
the target slot. Both legs of the resulting pair of fractions are then classes of morphisms of
complexes, where naturality is already known, and the denominator is invertible. -/
lemma model_currying_natural (a b : homTensorModels X)
    (f : modelObject X a ⟶ modelObject X b) :
    (iteratedHomFunctor X).map f ≫ (modelCurrying X b).hom =
      (modelCurrying X a).hom ≫ (tensorHomFunctor X).map f := by
  have := a.2.2.2
  have := b.2.2.2
  obtain ⟨K₀, sk, hsk, gk, hk⟩ := DerivedCategory.right_fac f.1.unop
  obtain ⟨L₀, sl, hsl, gl, hl⟩ := DerivedCategory.right_fac f.2.1.unop
  obtain ⟨I₀, gi, si, hsi, hi⟩ := DerivedCategory.left_fac f.2.2
  obtain ⟨LF, qL, hLF, hqL⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X L₀
  set s := modelMap X sk (qL ≫ sl) (si ≫ (kInjectiveAugmentation X).app I₀) with hsdef
  set t := modelMap X gk (qL ≫ gl) (gi ≫ (kInjectiveAugmentation X).app I₀) with htdef
  have hsIso : IsIso s := by
    rw [hsdef]
    simp only [modelMap, CategoryTheory.Functor.map_comp]
    exact (isIso_prod_iff _ _).2 ⟨inferInstance,
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩⟩
  have hfs : f ≫ s = t := by
    rw [hsdef, htdef]
    ext
    · apply Quiver.Hom.unop_inj
      show DerivedCategory.Q.map sk ≫ f.1.unop = DerivedCategory.Q.map gk
      simp only [hk, IsIso.hom_inv_id_assoc]
    · apply Quiver.Hom.unop_inj
      show DerivedCategory.Q.map (qL ≫ sl) ≫ f.2.1.unop = DerivedCategory.Q.map (qL ≫ gl)
      simp only [hl, CategoryTheory.Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
    · show f.2.2 ≫ DerivedCategory.Q.map (si ≫ (kInjectiveAugmentation X).app I₀) =
        DerivedCategory.Q.map (gi ≫ (kInjectiveAugmentation X).app I₀)
      simp only [hi, CategoryTheory.Functor.map_comp, Category.assoc, IsIso.inv_hom_id_assoc]
  have nat : ∀ (c : homTensorModels X) (k : K₀ ⟶ c.1) (l : LF ⟶ c.2.1.1)
      (m : c.2.2.1 ⟶ (kInjectiveResolution X).obj I₀),
      (iteratedHomFunctor X).map (modelMap X k l m) ≫
        (modelCurrying X (K₀, ⟨LF, hLF⟩, ⟨(kInjectiveResolution X).obj I₀, inferInstance⟩)).hom =
      (modelCurrying X c).hom ≫ (tensorHomFunctor X).map (modelMap X k l m) := fun c k l m => by
    have := c.2.2.2
    exact representativeCurryingIso_natural X c.2.1.2 hLF k l m
  have hs := nat b sk (qL ≫ sl) (si ≫ (kInjectiveAugmentation X).app I₀)
  have ht := nat a gk (qL ≫ gl) (gi ≫ (kInjectiveAugmentation X).app I₀)
  apply (cancel_mono ((tensorHomFunctor X).map s)).1
  rw [Category.assoc, ← hs, ← Category.assoc, ← CategoryTheory.Functor.map_comp, hfs, ht,
    Category.assoc, ← CategoryTheory.Functor.map_comp, hfs]

/-- The model chosen for a triple of objects of `D(O)`: the same representatives that
`derivedCurryIso` is built from. -/
def chosenModel (d : derivedTriples X) : homTensorModels X :=
  (kInjectiveModel X d.1.unop,
    ⟨kFlatModel X d.2.1.unop, isKFlat_kFlatModel X d.2.1.unop⟩,
    ⟨kInjectiveModel X d.2.2, inferInstance⟩)

/-- The chosen model does represent the given triple of objects of `D(O)`. -/
def chosenModelIso (d : derivedTriples X) : modelObject X (chosenModel X d) ≅ d :=
  ((kInjectiveModelIso X d.1.unop).symm.op).prod
    (((kFlatModelIso X d.2.1.unop).symm.op).prod (kInjectiveModelIso X d.2.2))

/-- **Stacks 08J9: the derived currying isomorphism is a natural isomorphism.** The canonical
isomorphism

`RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_O L, M)`

of `AlgebraicGeometry.RingedSite.derivedCurryIso`, bundled as an isomorphism between the
trifunctor `(K, L, M) ↦ RSheafHom(K, RSheafHom(L, M))` and the trifunctor
`(K, L, M) ↦ RSheafHom(K ⊗^L_O L, M)` on `D(O)ᵒᵖ × D(O)ᵒᵖ × D(O)`. It is obtained by extending
the comparison on models. -/
@[stacks 08J9 "functoriality in all three objects", sga "6 I 7.4" "first isomorphism"]
def derivedCurryNatIso : iteratedHomFunctor X ≅ tensorHomFunctor X :=
  NatIso.ofModels (iteratedHomFunctor X) (tensorHomFunctor X) (modelObject X)
    (modelCurrying X) (model_currying_natural X) (chosenModel X) (chosenModelIso X)

/-- At a model triple the natural isomorphism is the comparison it was built from. -/
theorem derivedCurryNatIso_hom_app_model
    (K L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (derivedCurryNatIso X).hom.app (modelTriple X K L I) =
      (representativeCurryingIso X K L I hL).hom := by
  dsimp only [derivedCurryNatIso]
  exact NatIso.ofModels_hom_app_models _ _ _ _ _ _ _
    ((K, ⟨L, hL⟩, ⟨I, inferInstance⟩) : homTensorModels X)

/-- **The bundled natural isomorphism is the derived currying isomorphism at every triple of
objects.** Both are the comparison at the chosen models, conjugated by the isomorphisms
identifying the classes of those models with the given objects, so the identity is a
reassociation. -/
theorem derivedCurryNatIso_hom_app
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedCurryNatIso X).hom.app (op K, op L, M) = (derivedCurryIso X K L M).hom := by
  have : (sheafHomComplex X (kFlatModel X L) (kInjectiveModel X M)).obj.IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X (kFlatModel X L) (kInjectiveModel X M)
      (isKFlat_kFlatModel X L)
  have happ : (derivedCurryNatIso X).hom.app (op K, op L, M) =
      (iteratedHomFunctor X).map (chosenModelIso X (op K, op L, M)).inv ≫
        (representativeCurryingIso X (kInjectiveModel X K) (kFlatModel X L)
            (kInjectiveModel X M) (isKFlat_kFlatModel X L)).hom ≫
          (tensorHomFunctor X).map (chosenModelIso X (op K, op L, M)).hom := rfl
  rw [happ]
  dsimp only [representativeCurryingIso, iteratedHomRepresentativeIso,
    tensorHomRepresentativeIso, derivedCurryIso, derivedSheafHomObjectsModelIso,
    derivedSheafHomObjectsKFlatModelIso, derivedTensorObjectsKFlatModelIso, chosenModelIso,
    chosenModel, iteratedHomFunctor, tensorHomFunctor, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.symm, Iso.op, Iso.prod, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv, Quiver.Hom.unop_op]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp_assoc, ← NatTrans.comp_app_assoc, ← op_comp,
    NatTrans.naturality]

/-- **Functoriality of the derived currying isomorphism in all three objects.** For morphisms
`k : K' ⟶ K`, `l : L' ⟶ L` and `m : M ⟶ M'` of `D(O)` the square formed by `derivedCurryIso`
at `(K, L, M)` and at `(K', L', M')` commutes: the derived currying isomorphism is natural
contravariantly in the source and in the middle object and covariantly in the target. -/
@[stacks 08J9 "functoriality in all three objects", sga "6 I 7.4" "functoriality, 1st iso"]
theorem derivedCurryIso_natural
    {K K' L L' M M' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K' ⟶ K) (l : L' ⟶ L) (m : M ⟶ M') :
    ((derivedSheafHomBifunctor X).map k.op).app
          (((derivedSheafHomBifunctor X).obj (op L)).obj M) ≫
        ((derivedSheafHomBifunctor X).obj (op K')).map
          (((derivedSheafHomBifunctor X).map l.op).app M ≫
            ((derivedSheafHomBifunctor X).obj (op L')).map m) ≫
        (derivedCurryIso X K' L' M').hom =
      (derivedCurryIso X K L M).hom ≫
        ((derivedSheafHomBifunctor X).map
            ((((Stacks.SheafOfModules.derivedTensorProductFunctor X).map k).app L' ≫
              ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map l).op)).app M ≫
          ((derivedSheafHomBifunctor X).obj
            (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K').obj L'))).map
              m := by
  have h := (derivedCurryNatIso X).hom.naturality
    (show ((op K, op L, M) : derivedTriples X) ⟶ (op K', op L', M') from (k.op, l.op, m))
  rw [derivedCurryNatIso_hom_app, derivedCurryNatIso_hom_app] at h
  dsimp only [iteratedHomFunctor, tensorHomFunctor, Quiver.Hom.unop_op] at h
  simpa only [Category.assoc] using h

/-- **The derived currying isomorphism on a triple of complexes.** For complexes `A`, `B`, `I`
with `B` K-flat and `I` K-injective, `derivedCurryIso` at the classes of `A`, `B`, `I` is the
comparison built from those complexes: the currying isomorphism of Stacks 0A90, conjugated by
the identifications of the two derived objects with classes of internal Hom complexes. -/
theorem derivedCurryIso_eq_representativeCurryingIso
    (A B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective] :
    (derivedCurryIso X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj I)).hom = (representativeCurryingIso X A B I hB).hom := by
  rw [← derivedCurryNatIso_hom_app]
  exact derivedCurryNatIso_hom_app_model X A B I hB

/-- **The comparison of Stacks 08J9 with the currying isomorphism of complexes of Stacks
0A90.** For complexes `A`, `B`, `I` with `B` K-flat and `I` K-injective, `derivedCurryIso` on
the classes of `A`, `B`, `I` is, after the two identifications

`RSheafHom(QA, RSheafHom(QB, QI)) ≅ Q SheafHom(A, SheafHom(B, I))` and
`RSheafHom(QA ⊗^L_O QB, QI) ≅ Q SheafHom(Tot(A ⊗_O B), I)`,

the class of the complex-level currying isomorphism `SheafHom(A, SheafHom(B, I)) ≅
SheafHom(Tot(A ⊗_O B), I)`. -/
@[stacks 08J9 "comparison with currying of complexes"]
theorem derivedCurryIso_comparison
    (A B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective] :
    (derivedCurryIso X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
            (DerivedCategory.Q.obj I)).hom ≫
        (tensorHomRepresentativeIso X A B I hB).hom =
      (iteratedHomRepresentativeIso X A B I hB).hom ≫
        DerivedCategory.Q.map (sheafHomTensorCurryIso X A B I).hom := by
  rw [derivedCurryIso_eq_representativeCurryingIso X A B I hB]
  exact representativeCurryingIso_comparison X A B I hB

end AlgebraicGeometry.RingedSite

end
