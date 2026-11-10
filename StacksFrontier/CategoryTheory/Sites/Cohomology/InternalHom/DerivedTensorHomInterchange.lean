module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.CategoryTheory.Functor.NatIsoFromModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
import StacksCore.Tactic.StacksAttribute

/-! # Moving a derived tensor factor inside a derived internal Hom

Let `(C, O)` be a ringed site. **Stacks 0BYU** asserts that for objects `K`, `L`, `M` of `D(O)`
there is a canonical morphism

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

in `D(O)`, functorial in `K`, `L` and `M`. This file constructs it and proves that
functoriality.

Both sides are assembled into trifunctors `AlgebraicGeometry.RingedSite.tensorIntoHomFunctor`
and `AlgebraicGeometry.RingedSite.homOfTensorFunctor` on `D(O) × D(O) × D(O)ᵒᵖ`, covariant in
the tensor factor `K` and in the target `L` of the internal Hom and contravariant in its
source `M`. On a triple of complexes `(A, I, C)` with `A` K-flat and `I` K-injective the two
trifunctors are computed by complexes: the derived internal Hom into `I` is the internal Hom
complex `SheafHom(C, I)` because `I` is K-injective (Stacks 0A97), and both derived tensor
products with the K-flat left factor `A` are the ordinary total tensor complex (Stacks 06YU).
The target still needs one further step, since `Tot(A ⊗_O I)` need not be K-injective: the
derived internal Hom out of `C` into its class is the internal Hom complex into the chosen
functorial K-injective resolution of `Tot(A ⊗_O I)`. The interchange morphism of complexes of
Stacks 0BYT, followed by the resolution augmentation, therefore gives a morphism between the
values of the two trifunctors which is natural for morphisms *of complexes*.

Naturality for an arbitrary morphism of `D(O)` between two such triples follows by the
calculus of fractions. The three components are factored simultaneously through a single third
triple: the tensor slot by a right fraction whose apex is then replaced by a K-flat resolution
of it (Stacks 06YS), the internal-Hom source slot by a left fraction with an arbitrary apex,
and the internal-Hom target slot not at all, every morphism of `D(O)` into the class of a
K-injective complex being the class of a morphism of complexes. The resulting morphism of
triples is the given one composed with an invertible one, and naturality for both of those is
already known. Since every object of `D(O)` is the class of a K-flat complex and of a
K-injective complex, the comparison on models extends to a natural transformation of
trifunctors.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorIntoHomFunctor` and
  `AlgebraicGeometry.RingedSite.homOfTensorFunctor`: the two sides of Stacks 0BYU as
  trifunctors on `D(O) × D(O) × D(O)ᵒᵖ`.
* `AlgebraicGeometry.RingedSite.tensorTotalKFlatComparison`: the derived tensor product with a
  K-flat left factor, identified with the class of the total tensor complex of Stacks 0A92.
* `AlgebraicGeometry.RingedSite.interchangeSourceIso` and
  `AlgebraicGeometry.RingedSite.interchangeTargetIso`: the identifications of the two sides at
  a triple of complexes with K-flat tensor factor and K-injective internal-Hom target with
  classes of complexes.
* `AlgebraicGeometry.RingedSite.interchangeComplexMap`: the interchange morphism of complexes
  of Stacks 0BYT followed by the K-injective resolution augmentation.
* `AlgebraicGeometry.RingedSite.representativeInterchange`: that morphism read between the two
  identifications.
* `AlgebraicGeometry.RingedSite.interchangeModels`: the family of model triples, and
  `AlgebraicGeometry.RingedSite.interchangeChosenModel` the model chosen for a triple of
  objects.
* `AlgebraicGeometry.RingedSite.derivedTensorHomInterchangeNatTrans`: the interchange morphism
  as a natural transformation between the two trifunctors.
* `AlgebraicGeometry.RingedSite.derivedTensorHomInterchange`: **Stacks 0BYU**, the canonical
  morphism `K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorTotalKFlatComparison_natural`: naturality of the
  identification of a derived tensor product with a K-flat left factor in both factors.
* `AlgebraicGeometry.RingedSite.model_interchange_natural`: naturality of the comparison on
  models for an arbitrary morphism of `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedTensorHomInterchange_natural`: **Stacks 0BYU**,
  functoriality in all three objects, for arbitrary morphisms of `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedTensorHomInterchange_eq_representativeInterchange` and
  `AlgebraicGeometry.RingedSite.derivedTensorHomInterchange_comparison`: on the classes of a
  triple of complexes with K-flat tensor factor and K-injective internal-Hom target, the
  canonical morphism is the interchange morphism of complexes of Stacks 0BYT followed by the
  resolution augmentation.

## Implementation notes

The two trifunctors are spelled out by hand — explicit `obj`, `map`, `map_id` and `map_comp` —
rather than assembled from `CategoryTheory.Functor.uncurry`, the opposite-product equivalence
and the product associator. The assembled spelling names the same functors but presents each
component as a composite of four functors, which makes identifying its values with the
complexes that compute them prohibitively expensive.

The identifications of the two sides at a model triple are stated with the trifunctors
themselves as their sources, rather than with the internal Hom and derived tensor product
spelled out. The two are definitionally equal, but only the former makes the composites that
appear in the naturality squares literally the ones the trifunctors produce.

K-flatness of the tensor factor is not optional here, unlike in Stacks 0A98, because the
target has the derived tensor product in a *covariant* slot: the canonical comparison
`Stacks.SheafOfModules.DerivedTensorProduct.toTensor` points from the derived tensor product
to the ordinary one, which is the wrong way for a target, so that comparison has to be
invertible. The one-sided comparison
`Stacks.SheafOfModules.DerivedTensorProduct.comparisonLeft` of Stacks 06YU supplies this as
soon as the left factor is K-flat, and the right factor — the internal Hom target, or the
internal Hom complex out of it — is K-injective rather than K-flat. The source of the internal
Hom is unconstrained.

Since Stacks 0BYU is a morphism and not an isomorphism, the extension from models is
`CategoryTheory.NatTrans.ofModels` rather than `CategoryTheory.NatIso.ofModels`.

The interchange morphism of Stacks 0BYT is stated for
`AlgebraicGeometry.RingedSite.tensorTotal`, the total complex of the presheaf-level tensor
double complex sheafified degreewise, while the K-flat comparison of the derived tensor product
is stated for `Stacks.SheafOfModules.Tensor.tensorComplex`, the total complex of the sheafified
double complex. The two are identified by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, and that identification is folded
into `AlgebraicGeometry.RingedSite.tensorTotalKFlatComparison` once and for all, so that the
rest of the file works in the `tensorTotal` spelling only. Its naturality is what converts the
induced maps of one spelling into those of the other; stating it needs
`Stacks.SheafOfModules.Tensor.tensorComplex` unfolded, because the value of that bifunctor and
the `HomologicalComplex.mapBifunctor` it is defined to be are equal only by unfolding a
semireducible definition, and the two appear as the endpoints of one composite.

The `HasMapBifunctor` hypothesis of the section is spelled with
`HomologicalComplex.HasMapBifunctorReg`, the copy of Mathlib's `abbrev` with a regular kernel
reducibility hint, as in `Stacks.SheafOfModules.Tensor.tensorComplex` and
`Stacks.SheafOfModules.IsKFlat`. The value of a definition carries the hypothesis with its nested
proofs abstracted into auxiliary lemmas; the kernel compares it with the hypothesis in the type of
the definition, and in the hypotheses of `tensorComplex` and `IsKFlat`, argument by argument
instead of evaluating `Stacks.SheafOfModules.Tensor.sheafTensor`.

The universes are the diagonal `RingedSite.{u, u, u}` of the whole derived internal Hom
cluster; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying`.

## References

* [Stacks Project, Tag 0BYU](https://stacks.math.columbia.edu/tag/0BYU)
* [Stacks Project, Tag 0BYT](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0A93](https://stacks.math.columbia.edu/tag/0A93)
* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- Triples of objects of `D(O)`, covariant in the tensor factor and in the target of the
internal Hom and contravariant in its source: the common source of the two sides of Stacks
0BYU. -/
abbrev interchangeTriples :=
  DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ

/-- The left-hand side of Stacks 0BYU as a trifunctor: the derived tensor product with a
derived internal Hom, `(K, L, M) ↦ K ⊗^L_O RSheafHom(M, L)`. -/
def tensorIntoHomFunctor :
    interchangeTriples X ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  obj d := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj d.1).obj
    (((derivedSheafHomBifunctor X).obj d.2.2).obj d.2.1)
  map {d e} f :=
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f.1).app
        (((derivedSheafHomBifunctor X).obj d.2.2).obj d.2.1) ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj e.1).map
        (((derivedSheafHomBifunctor X).map f.2.2).app d.2.1 ≫
          ((derivedSheafHomBifunctor X).obj e.2.2).map f.2.1)
  map_id := by
    rintro ⟨d₁, d₂, d₃⟩
    simp only [CategoryTheory.prod_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.comp_id]
  map_comp := by
    rintro ⟨d₁, d₂, d₃⟩ ⟨e₁, e₂, e₃⟩ ⟨z₁, z₂, z₃⟩ ⟨f₁, f₂, f₃⟩ ⟨g₁, g₂, g₃⟩
    dsimp only [CategoryTheory.prod_comp]
    have hinner :
        ((derivedSheafHomBifunctor X).map (f₃ ≫ g₃)).app d₂ ≫
            ((derivedSheafHomBifunctor X).obj z₃).map (f₂ ≫ g₂) =
          (((derivedSheafHomBifunctor X).map f₃).app d₂ ≫
              ((derivedSheafHomBifunctor X).obj e₃).map f₂) ≫
            (((derivedSheafHomBifunctor X).map g₃).app e₂ ≫
              ((derivedSheafHomBifunctor X).obj z₃).map g₂) := by
      simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
        NatTrans.naturality_assoc]
    have houter :
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj z₁).map
              (((derivedSheafHomBifunctor X).map g₃).app d₂) ≫
            ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj z₁).map
              (((derivedSheafHomBifunctor X).obj z₃).map f₂) =
          ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj z₁).map
              (((derivedSheafHomBifunctor X).obj e₃).map f₂) ≫
            ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj z₁).map
              (((derivedSheafHomBifunctor X).map g₃).app e₂) := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        NatTrans.naturality]
    rw [hinner]
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
      NatTrans.naturality_assoc]
    rw [reassoc_of% houter]

/-- The right-hand side of Stacks 0BYU as a trifunctor: the derived internal Hom into a
derived tensor product, `(K, L, M) ↦ RSheafHom(M, K ⊗^L_O L)`. -/
def homOfTensorFunctor :
    interchangeTriples X ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  obj d := ((derivedSheafHomBifunctor X).obj d.2.2).obj
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj d.1).obj d.2.1)
  map {d e} f :=
    ((derivedSheafHomBifunctor X).map f.2.2).app
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj d.1).obj d.2.1) ≫
      ((derivedSheafHomBifunctor X).obj e.2.2).map
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f.1).app d.2.1 ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj e.1).map f.2.1)
  map_id := by
    rintro ⟨d₁, d₂, d₃⟩
    simp only [CategoryTheory.prod_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.comp_id]
  map_comp := by
    rintro ⟨d₁, d₂, d₃⟩ ⟨e₁, e₂, e₃⟩ ⟨z₁, z₂, z₃⟩ ⟨f₁, f₂, f₃⟩ ⟨g₁, g₂, g₃⟩
    dsimp only [CategoryTheory.prod_comp]
    have hinner :
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map (f₁ ≫ g₁)).app d₂ ≫
            ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj z₁).map (f₂ ≫ g₂) =
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f₁).app d₂ ≫
              ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj e₁).map f₂) ≫
            (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g₁).app e₂ ≫
              ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj z₁).map g₂) := by
      simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
        NatTrans.naturality_assoc]
    have houter :
        ((derivedSheafHomBifunctor X).obj z₃).map
              (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g₁).app d₂) ≫
            ((derivedSheafHomBifunctor X).obj z₃).map
              (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj z₁).map f₂) =
          ((derivedSheafHomBifunctor X).obj z₃).map
              (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj e₁).map f₂) ≫
            ((derivedSheafHomBifunctor X).obj z₃).map
              (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g₁).app e₂) := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        NatTrans.naturality]
    rw [hinner]
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
      NatTrans.naturality_assoc]
    rw [reassoc_of% houter]

/-- The triple of objects of `D(O)` represented by a triple of complexes: the tensor factor,
the target of the internal Hom, and its source. -/
abbrev interchangeModelTriple
    (A I C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    interchangeTriples X :=
  (DerivedCategory.Q.obj A, DerivedCategory.Q.obj I, op (DerivedCategory.Q.obj C))

/-- **A derived tensor product with a K-flat left factor is the total tensor complex of
Stacks 0A92.** It is the one-sided K-flat comparison of Stacks 06YU followed by the
identification of the two total tensor complexes of a ringed site. -/
def tensorTotalKFlatComparison
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B) ≅
      DerivedCategory.Q.obj (tensorTotal X A B) :=
  (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A B hA ≪≫
    (DerivedCategory.Q.mapIso (tensorTotalIsoTensorComplex X A B)).symm

/-- The comparison of a derived tensor product with a K-flat left factor and the total tensor
complex is natural in both factors, no flatness being required of the right one. -/
theorem tensorTotalKFlatComparison_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    (a : A ⟶ A') (b : B ⟶ B') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj B) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A')).map (DerivedCategory.Q.map b) ≫
        (tensorTotalKFlatComparison X A' B' hA').hom =
      (tensorTotalKFlatComparison X A B hA).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X a b) := by
  have hc := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft_naturality
    a b hA hA'
  have hb := congrArg DerivedCategory.Q.map (tensorTotalIsoTensorComplex_naturality X a b)
  dsimp only [Stacks.SheafOfModules.Tensor.tensorComplex,
    CategoryTheory.Functor.map₂HomologicalComplexReg] at hc hb
  simp only [CategoryTheory.Functor.map_comp] at hb
  dsimp only [tensorTotalKFlatComparison, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_inv]
  dsimp only [Stacks.SheafOfModules.Tensor.tensorComplex,
    CategoryTheory.Functor.map₂HomologicalComplexReg]
  simp only [Category.assoc]
  rw [reassoc_of% hc, hb]

/-- **A derived tensor product with a derived internal Hom at a K-flat tensor factor and a
K-injective internal-Hom target.** It is the class of the total tensor complex
`Tot(A ⊗_O SheafHom(C, I))`: the derived internal Hom is computed by its K-injective target by
Stacks 0A97, and the derived tensor product by the total tensor complex because its left
factor is K-flat (Stacks 06YU). -/
def interchangeSourceIso
    (A I C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] :
    (tensorIntoHomFunctor X).obj (interchangeModelTriple X A I C) ≅
      DerivedCategory.Q.obj (tensorTotal X A (sheafHomComplex X C I).obj) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (DerivedCategory.Q.obj A)).mapIso (derivedSheafHomComparison X C I) ≪≫
    tensorTotalKFlatComparison X A (sheafHomComplex X C I).obj hA

/-- **A derived internal Hom into a derived tensor product with a K-flat tensor factor.** It is
the class of the internal Hom complex `SheafHom(C, J)` into the chosen functorial K-injective
resolution `J` of `Tot(A ⊗_O I)`: the derived tensor product is the total tensor complex
because its left factor is K-flat (Stacks 06YU), and the derived internal Hom into the class of
an arbitrary complex is the internal Hom complex into its chosen K-injective resolution. -/
def interchangeTargetIso
    (A I C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) :
    (homOfTensorFunctor X).obj (interchangeModelTriple X A I C) ≅
      DerivedCategory.Q.obj
        (sheafHomComplex X C ((kInjectiveResolution X).obj (tensorTotal X A I))).obj :=
  ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj C))).mapIso
      (tensorTotalKFlatComparison X A I hA) ≪≫
    derivedSheafHomResolutionComparison X C (tensorTotal X A I)

/-- The interchange morphism of complexes of Stacks 0BYT followed by the augmentation of
`Tot(A ⊗_O I)` into its chosen K-injective resolution:
`Tot(A ⊗_O SheafHom(C, I)) ⟶ SheafHom(C, J)`. -/
def interchangeComplexMap
    (A I C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotal X A (sheafHomComplex X C I).obj ⟶
      (sheafHomComplex X C ((kInjectiveResolution X).obj (tensorTotal X A I))).obj :=
  tensorHomInterchange X A I C ≫
    homMap X (𝟙 C) ((kInjectiveAugmentation X).app (tensorTotal X A I))

/-- **The interchange morphism of Stacks 0BYU at a K-flat tensor factor and a K-injective
internal-Hom target.** It is the interchange morphism of complexes of Stacks 0BYT, followed by
the K-injective resolution augmentation, read between the two identifications of the derived
objects with classes of complexes. -/
def representativeInterchange
    (A I C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] :
    (tensorIntoHomFunctor X).obj (interchangeModelTriple X A I C) ⟶
      (homOfTensorFunctor X).obj (interchangeModelTriple X A I C) :=
  (interchangeSourceIso X A I C hA).hom ≫
    DerivedCategory.Q.map (interchangeComplexMap X A I C) ≫
      (interchangeTargetIso X A I C hA).inv

/-- The interchange morphism at a model triple is the morphism of complexes of Stacks 0BYT
followed by the resolution augmentation, read through the two identifications with classes of
complexes. -/
theorem representativeInterchange_comparison
    (A I C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] :
    representativeInterchange X A I C hA ≫ (interchangeTargetIso X A I C hA).hom =
      (interchangeSourceIso X A I C hA).hom ≫
        DerivedCategory.Q.map (interchangeComplexMap X A I C) := by
  dsimp only [representativeInterchange]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {A A' I I' C C' :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The morphism of model triples induced by three morphisms of complexes, covariant in the
tensor factor and in the target of the internal Hom and contravariant in its source. -/
private abbrev interchangeModelMap (a : A ⟶ A') (i : I ⟶ I') (c : C' ⟶ C) :
    interchangeModelTriple X A I C ⟶ interchangeModelTriple X A' I' C' :=
  (DerivedCategory.Q.map a, DerivedCategory.Q.map i, (DerivedCategory.Q.map c).op)

/-- The identification of the source of Stacks 0BYU at a model triple is natural in the three
complexes. -/
private lemma interchangeSourceIso_natural
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    [I.IsKInjective] [I'.IsKInjective] (a : A ⟶ A') (i : I ⟶ I') (c : C' ⟶ C) :
    (tensorIntoHomFunctor X).map (interchangeModelMap X a i c) ≫
        (interchangeSourceIso X A' I' C' hA').hom =
      (interchangeSourceIso X A I C hA).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X a (homMap X c i)) := by
  have hh := derivedSheafHomComparison_naturality X c i
  have htt := tensorTotalKFlatComparison_natural X hA hA' a (homMap X c i)
  dsimp only [tensorIntoHomFunctor, interchangeSourceIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc]
  rw [hh]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← NatTrans.naturality_assoc, htt]

/-- The identification of the target of Stacks 0BYU at a model triple is natural in the three
complexes. -/
private lemma interchangeTargetIso_natural
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    (a : A ⟶ A') (i : I ⟶ I') (c : C' ⟶ C) :
    (homOfTensorFunctor X).map (interchangeModelMap X a i c) ≫
        (interchangeTargetIso X A' I' C' hA').hom =
      (interchangeTargetIso X A I C hA).hom ≫
        DerivedCategory.Q.map
          (homMap X c ((kInjectiveResolution X).map (tensorTotalMap X a i))) := by
  have htt := tensorTotalKFlatComparison_natural X hA hA' a i
  have hr := derivedSheafHomResolutionComparison_naturality X c (tensorTotalMap X a i)
  dsimp only [homOfTensorFunctor, interchangeTargetIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc]
  rw [htt]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← NatTrans.naturality_assoc, hr]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u,
    u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The morphism of complexes underlying Stacks 0BYU is natural in the three complexes: the
interchange morphism of Stacks 0BYT followed by the resolution augmentation commutes with the
induced maps. -/
private lemma interchangeComplexMap_natural (a : A ⟶ A') (i : I ⟶ I') (c : C' ⟶ C) :
    tensorTotalMap X a (homMap X c i) ≫ interchangeComplexMap X A' I' C' =
      interchangeComplexMap X A I C ≫
        homMap X c ((kInjectiveResolution X).map (tensorTotalMap X a i)) := by
  have haug : (kInjectiveAugmentation X).app (tensorTotal X A I) ≫
      (kInjectiveResolution X).map (tensorTotalMap X a i) =
        tensorTotalMap X a i ≫ (kInjectiveAugmentation X).app (tensorTotal X A' I') :=
    ((kInjectiveAugmentation X).naturality (tensorTotalMap X a i)).symm
  dsimp only [interchangeComplexMap]
  rw [← Category.assoc, ← tensorHomInterchange_natural X a i c, Category.assoc, Category.assoc,
    homMap_comp, homMap_comp, Category.comp_id, Category.id_comp, haug]

/-- The interchange morphism at a model triple is natural in the three complexes. -/
private lemma representativeInterchange_natural
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    [I.IsKInjective] [I'.IsKInjective] (a : A ⟶ A') (i : I ⟶ I') (c : C' ⟶ C) :
    (tensorIntoHomFunctor X).map (interchangeModelMap X a i c) ≫
        representativeInterchange X A' I' C' hA' =
      representativeInterchange X A I C hA ≫
        (homOfTensorFunctor X).map (interchangeModelMap X a i c) := by
  rw [← cancel_mono (interchangeTargetIso X A' I' C' hA').hom, Category.assoc, Category.assoc,
    interchangeTargetIso_natural X hA hA' a i c,
    representativeInterchange_comparison X A' I' C' hA',
    ← Category.assoc ((tensorIntoHomFunctor X).map _), interchangeSourceIso_natural X hA hA' a i c,
    ← Category.assoc (representativeInterchange X A I C hA),
    representativeInterchange_comparison X A I C hA, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    interchangeComplexMap_natural X a i c]

/-- The models on which the interchange morphism of Stacks 0BYU is constructed: a K-flat
complex, a K-injective complex and an arbitrary complex. Every triple of objects of `D(O)` is
represented by one, and that is what makes the comparison on models extend to all of
`D(O)`. -/
abbrev interchangeModels :=
  {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ //
      Stacks.SheafOfModules.IsKFlat X.O A} ×
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ //
      I.IsKInjective} ×
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ

/-- The triple of objects of `D(O)` represented by a model. -/
abbrev interchangeModelObject (m : interchangeModels X) : interchangeTriples X :=
  interchangeModelTriple X m.1.1 m.2.1.1 m.2.2

/-- The interchange morphism of Stacks 0BYU at a model. -/
def modelInterchange (m : interchangeModels X) :
    (tensorIntoHomFunctor X).obj (interchangeModelObject X m) ⟶
      (homOfTensorFunctor X).obj (interchangeModelObject X m) :=
  haveI := m.2.1.2
  representativeInterchange X m.1.1 m.2.1.1 m.2.2 m.1.2

/-- **Naturality of the interchange morphism between models, for an arbitrary morphism of
`D(O)`.** The three components are factored through a single third triple of complexes: the
tensor slot by a right fraction, whose apex is replaced by a K-flat resolution of it (Stacks
06YS); the internal-Hom target slot not at all, every morphism of `D(O)` into the class of a
K-injective complex being the class of a morphism of complexes; and the internal-Hom source
slot by a left fraction, whose apex needs no repair. The given morphism is thus the composite
of the inverse of an invertible morphism of model triples with another one, and naturality for
morphisms of model triples that come from morphisms of complexes is already known. -/
lemma model_interchange_natural (m n : interchangeModels X)
    (f : interchangeModelObject X m ⟶ interchangeModelObject X n) :
    (tensorIntoHomFunctor X).map f ≫ modelInterchange X n =
      modelInterchange X m ≫ (homOfTensorFunctor X).map f := by
  have := m.2.1.2
  have := n.2.1.2
  obtain ⟨A₀, sa, hsa, ga, ha⟩ := DerivedCategory.right_fac f.1
  obtain ⟨AF, qa, hAF, hqa⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X A₀
  have hqa' : IsIso (DerivedCategory.Q.map qa) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqa
  obtain ⟨ti, hti⟩ := exists_Q_map_eq_of_isKInjective X f.2.1
  obtain ⟨C₀, gc, sc, hsc, hcf⟩ := DerivedCategory.left_fac f.2.2.unop
  set p : interchangeModels X := (⟨AF, hAF⟩, ⟨m.2.1.1, m.2.1.2⟩, C₀) with hpdef
  set s := interchangeModelMap X (qa ≫ sa) (𝟙 m.2.1.1) sc with hsdef
  set t := interchangeModelMap X (qa ≫ ga) ti gc with htdef
  have hsIso : IsIso s := by
    rw [hsdef]
    simp only [interchangeModelMap, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_id]
    exact (isIso_prod_iff _ _).2 ⟨inferInstance,
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩⟩
  have hsf : s ≫ f = t := by
    rw [hsdef, htdef]
    ext
    · change DerivedCategory.Q.map (qa ≫ sa) ≫ f.1 = DerivedCategory.Q.map (qa ≫ ga)
      simp only [ha, CategoryTheory.Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
    · change DerivedCategory.Q.map (𝟙 m.2.1.1) ≫ f.2.1 = DerivedCategory.Q.map ti
      simp only [hti, CategoryTheory.Functor.map_id, Category.id_comp]
    · change f.2.2.unop ≫ DerivedCategory.Q.map sc = DerivedCategory.Q.map gc
      simp only [hcf, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hs : (tensorIntoHomFunctor X).map s ≫ modelInterchange X m =
      modelInterchange X p ≫ (homOfTensorFunctor X).map s :=
    representativeInterchange_natural X hAF m.1.2 (qa ≫ sa) (𝟙 m.2.1.1) sc
  have ht : (tensorIntoHomFunctor X).map t ≫ modelInterchange X n =
      modelInterchange X p ≫ (homOfTensorFunctor X).map t :=
    representativeInterchange_natural X hAF n.1.2 (qa ≫ ga) ti gc
  apply (cancel_epi ((tensorIntoHomFunctor X).map s)).1
  rw [← CategoryTheory.Functor.map_comp_assoc, hsf, ht, ← Category.assoc, hs, Category.assoc,
    ← CategoryTheory.Functor.map_comp, hsf]

/-- The model chosen for a triple of objects of `D(O)`: the chosen K-flat representative of the
tensor factor, the chosen K-injective representative of the target of the internal Hom, and the
chosen K-injective representative of its source, which is not required to be anything. -/
def interchangeChosenModel (d : interchangeTriples X) : interchangeModels X :=
  (⟨kFlatModel X d.1, isKFlat_kFlatModel X d.1⟩,
    ⟨kInjectiveModel X d.2.1, inferInstance⟩,
    kInjectiveModel X d.2.2.unop)

/-- The chosen model does represent the given triple of objects of `D(O)`. -/
def interchangeChosenModelIso (d : interchangeTriples X) :
    interchangeModelObject X (interchangeChosenModel X d) ≅ d :=
  (kFlatModelIso X d.1).prod ((kInjectiveModelIso X d.2.1).prod
    ((kInjectiveModelIso X d.2.2.unop).symm.op))

/-- **Stacks 0BYU: the interchange morphism as a natural transformation.** The canonical
morphism

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

bundled as a transformation from the trifunctor `(K, L, M) ↦ K ⊗^L_O RSheafHom(M, L)` to the
trifunctor `(K, L, M) ↦ RSheafHom(M, K ⊗^L_O L)` on `D(O) × D(O) × D(O)ᵒᵖ`. It is obtained by
extending the comparison on models. -/
def derivedTensorHomInterchangeNatTrans :
    tensorIntoHomFunctor X ⟶ homOfTensorFunctor X :=
  NatTrans.ofModels (tensorIntoHomFunctor X) (homOfTensorFunctor X)
    (interchangeModelObject X) (modelInterchange X) (model_interchange_natural X)
    (interchangeChosenModel X) (interchangeChosenModelIso X)

/-- **Stacks 0BYU.** For objects `K`, `L`, `M` of `D(O)` there is a canonical morphism

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

in `D(O)`: on a K-flat representative `A` of `K`, a K-injective representative `I` of `L` and
an arbitrary representative `C` of `M` it is the interchange morphism of complexes of Stacks
0BYT, followed by the augmentation of `Tot(A ⊗_O I)` into a K-injective resolution. -/
@[stacks 0BYU "the canonical morphism"]
def derivedTensorHomInterchange
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj L) ⟶
      ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) :=
  (derivedTensorHomInterchangeNatTrans X).app (K, L, op M)

/-- At a model triple the natural transformation is the comparison it was built from. -/
theorem derivedTensorHomInterchange_eq_representativeInterchange
    (A I C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] :
    derivedTensorHomInterchange X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I)
        (DerivedCategory.Q.obj C) = representativeInterchange X A I C hA := by
  dsimp only [derivedTensorHomInterchange, derivedTensorHomInterchangeNatTrans]
  exact NatTrans.ofModels_app_models _ _ _ _ _ _ _
    ((⟨A, hA⟩, ⟨I, inferInstance⟩, C) : interchangeModels X)

/-- **The comparison of Stacks 0BYU with the interchange morphism of complexes of Stacks
0BYT.** For complexes `A`, `I`, `C` with `A` K-flat and `I` K-injective, the canonical morphism
on their classes is, after the two identifications

`QA ⊗^L_O RSheafHom(QC, QI) ≅ Q Tot(A ⊗_O SheafHom(C, I))` and
`RSheafHom(QC, QA ⊗^L_O QI) ≅ Q SheafHom(C, J)` with `J` the chosen K-injective resolution of
`Tot(A ⊗_O I)`,

the class of the interchange morphism of complexes `Tot(A ⊗_O SheafHom(C, I)) ⟶
SheafHom(C, Tot(A ⊗_O I))` followed by the resolution augmentation. -/
@[stacks 0BYU "comparison with the interchange morphism of complexes"]
theorem derivedTensorHomInterchange_comparison
    (A I C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] :
    derivedTensorHomInterchange X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I)
          (DerivedCategory.Q.obj C) ≫
        (interchangeTargetIso X A I C hA).hom =
      (interchangeSourceIso X A I C hA).hom ≫
        DerivedCategory.Q.map (tensorHomInterchange X A I C ≫
          homMap X (𝟙 C) ((kInjectiveAugmentation X).app (tensorTotal X A I))) := by
  rw [derivedTensorHomInterchange_eq_representativeInterchange X A I C hA]
  exact representativeInterchange_comparison X A I C hA

/-- **Functoriality of the interchange morphism of Stacks 0BYU in all three objects.** For
morphisms `k : K ⟶ K'`, `l : L ⟶ L'` and `m : M' ⟶ M` of `D(O)` the square formed by the
canonical morphism at `(K, L, M)` and at `(K', L', M')` commutes: the interchange morphism is
natural covariantly in the tensor factor and in the target of the internal Hom and
contravariantly in its source. -/
@[stacks 0BYU "functoriality in all three objects"]
theorem derivedTensorHomInterchange_natural
    {K K' L L' M M' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K ⟶ K') (l : L ⟶ L') (m : M' ⟶ M) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map k).app
          (((derivedSheafHomBifunctor X).obj (op M)).obj L) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K').map
          (((derivedSheafHomBifunctor X).map m.op).app L ≫
            ((derivedSheafHomBifunctor X).obj (op M')).map l) ≫
        derivedTensorHomInterchange X K' L' M' =
      derivedTensorHomInterchange X K L M ≫
        ((derivedSheafHomBifunctor X).map m.op).app
            (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) ≫
          ((derivedSheafHomBifunctor X).obj (op M')).map
            (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map k).app L ≫
              ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K').map l) := by
  have h := (derivedTensorHomInterchangeNatTrans X).naturality
    (show ((K, L, op M) : interchangeTriples X) ⟶ (K', L', op M') from (k, l, m.op))
  dsimp only [tensorIntoHomFunctor, homOfTensorFunctor] at h
  simpa only [derivedTensorHomInterchange, Category.assoc] using h

end AlgebraicGeometry.RingedSite

end
