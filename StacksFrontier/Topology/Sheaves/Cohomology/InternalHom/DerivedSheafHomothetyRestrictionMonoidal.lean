module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIsIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedRestrictionMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomothetyRestriction

/-!
# The homothety restricted to an open, through the monoidal structure of derived restriction

Let `(C, O)` be a ringed site, `U` a subterminal object of `C` (every open of a topological space
is one) and `K` an object of `D(O)`. A morphism

`a : O[0] ⟶ R𝓗om_O(K, K)`

with `a ▷ K ≫ e_{K,K} = λ_ K` — a *homothety* of `K`, in the sense of
`Stacks.SheafOfModules.derivedSheafHomothety` — restricts to an isomorphism over `U` as soon as
`R𝓗om_{O|_U}(K|_U, K|_U)` is isomorphic to `O|_U[0]` as an *object*, with no further input.

Read at the tensor comparison
`Stacks.Cohomology.SliceDerivedSheafHom.sliceTensorRestrictionObjIso`, which is built with no
monoidal structure on restriction in sight, the same argument would ask for a comparison `u` of
the units together with the left-unitor identity relating the two. Here the comparison of tensor
products is instead the **tensorator of the monoidal structure on derived restriction**,
`Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal`, re-seated onto the derived
tensor product of [Stacks, Tag 06YU] on each side; its unit comparison is the structure's own `ε`
and the left-unitor identity is the structure's own left unitality axiom, so neither is a
parameter here.

## What makes the re-seating work

`AlgebraicGeometry.RingedSite.derivedTensorMonoidal`, the monoidal structure whose tensor product
is the derived tensor product of [Stacks, Tag 06YU] on the nose, is
`CategoryTheory.MonoidalCategory.reseat` applied to the structure of [Stacks, Tag 0FPT], while
`Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal` is stated for Tag 0FPT itself
on each side. `CategoryTheory.MonoidalCategory.reseatMonoidal` makes the identity functor from a
re-seated structure to the given one monoidal, and
`CategoryTheory.MonoidalCategory.reseatMonoidalInv` below makes the identity functor in the
*other* direction monoidal; derived restriction for the re-seated structures is then a composite
of three monoidal functors whose underlying functor is derived restriction itself. That composite
is `Stacks.Cohomology.SliceDerivedSheafHom.restrictDMonoidal`.

With it, every input of
`CategoryTheory.MonoidalCategory.isIso_map_of_whiskerRight_comp_eq_leftUnitor_of_iso_tensorUnit`
is read off a single monoidal functor:

* the comparison of tensor products is `CategoryTheory.Functor.Monoidal.μIso` and its naturality
  in the first variable is `CategoryTheory.Functor.OplaxMonoidal.δ_natural_left`;
* the comparison of units is `CategoryTheory.Functor.Monoidal.εIso` and the left-unitor identity
  is `CategoryTheory.Functor.LaxMonoidal.left_unitality`;
* the morphism `R𝓗om_O(K, K)|_U ⟶ R𝓗om_{O|_U}(K|_U, K|_U)` is the transpose, under the
  tensor–internal-hom bijection of [Stacks, Tag 08J8] on the slice site, of the tensorator
  followed by the restricted evaluation morphism — `restrictDHomMap` below — and it is an
  isomorphism by `CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective`, which takes
  the comparison of tensor products as a parameter and so reads at the tensorator exactly as it
  reads at `sliceTensorRestrictionObjIso`.

## Main definitions

* `CategoryTheory.MonoidalCategory.reseatMonoidalInv`: the identity functor from a monoidal
  structure to its re-seating is monoidal.
* `Stacks.Cohomology.SliceDerivedSheafHom.restrictDMonoidal`: **derived restriction to the slice
  site over `U` is monoidal for the derived tensor product of [Stacks, Tag 06YU] on each side.**
* `Stacks.Cohomology.SliceDerivedSheafHom.restrictDHomDatum` and `restrictDHomMap`: the transpose
  datum of the tensorator and the comparison of derived internal homs it transposes to.

## Main results

* `Stacks.Cohomology.SliceDerivedSheafHom.isIso_restrictDHomMap`: that comparison is an
  isomorphism.
* `Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_of_whiskerRight_comp_derivedSheafHomCounit`
  — **a homothety of `K` restricts to an isomorphism over `U`**, from an isomorphism
  `R𝓗om_{O|_U}(K|_U, K|_U) ≅ O|_U[0]` of objects alone.
* `Stacks.SheafOfModules.isIso_map_derivedSheafHomothety_of_iso_derivedSheafHom`: that statement
  over a ringed space, at `Stacks.SheafOfModules.derivedSheafHomothety`.
* `Stacks.SheafOfModules.isIso_derivedSheafHomothety_of_iso_derivedSheafHom_of_coversTop` —
  **the homothety of `K` is an isomorphism**, from such an isomorphism over each member of a
  family of opens covering the space.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
open Opposite AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction)

universe v u

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

/-- **The identity functor, from `C` with the given monoidal structure to `C` with the re-seated
one, is a monoidal functor.** This is the direction
`CategoryTheory.MonoidalCategory.reseatMonoidal` does not supply: re-seating is
`CategoryTheory.Monoidal.induced` at the identity functor, which makes the identity monoidal out
of the re-seated structure and into the given one. The identity functor is an equivalence and the
inverse of a monoidal equivalence is monoidal, so the other direction follows. -/
@[instance_reducible]
def reseatMonoidalInv (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @Functor.Monoidal C _ _ C _ (reseat e ε) (𝟭 C) :=
  @CategoryTheory.Equivalence.inverseMonoidal C _ (reseat e ε) C _ _
    (Equivalence.refl) (reseatMonoidal e ε)

end CategoryTheory.MonoidalCategory

namespace Stacks.Cohomology.SliceDerivedSheafHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.over U).O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.over U).O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.over U).O)
      (ComplexShape.up ℤ)]

/-! ### Derived restriction is monoidal for the derived tensor product -/

section Monoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-- **Derived restriction to the slice site `C/U` is a monoidal functor for the derived tensor
product of [Stacks, Tag 06YU] on each side**, that is, for
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal` over `C` and over `C/U`.

Both of those are `CategoryTheory.MonoidalCategory.reseat` applied to the structure of
[Stacks, Tag 0FPT], and `Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal` is that
structure's own statement for derived restriction; this is it conjugated by the identity functor
on each side, monoidal by `CategoryTheory.MonoidalCategory.reseatMonoidal` and
`CategoryTheory.MonoidalCategory.reseatMonoidalInv`. The underlying functor of the composite is
derived restriction itself. -/
@[instance_reducible]
def restrictDMonoidal :
    @Functor.Monoidal
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) _
        (RingedSite.derivedTensorMonoidal X)
        (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))) _
        (RingedSite.derivedTensorMonoidal (X.over U))
        (restrictD X U) :=
  @Functor.Monoidal.instComp
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) _
      (RingedSite.derivedTensorMonoidal X)
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O)
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))) _
      (RingedSite.derivedTensorMonoidal (X.over U))
    (𝟭 _) (restrictD X U ⋙ 𝟭 _)
    (@reseatMonoidal _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.O
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)))
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.O))
    (@Functor.Monoidal.instComp
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O)
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))) _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (X.O.over U))
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))) _
        (RingedSite.derivedTensorMonoidal (X.over U))
      (restrictD X U) (𝟭 _)
      (Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal X U)
      (@reseatMonoidalInv _ _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (X.over U).O) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso (X.over U).O
          (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
            (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over U))))
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso (X.over U).O)))

end Monoidal

/-! ### The comparison of derived internal homs attached to the tensorator -/

variable (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The transpose datum of the tensorator: the tensorator of
`Stacks.Cohomology.SliceDerivedSheafHom.restrictDMonoidal` followed by the restriction to `C/U`
of the evaluation morphism `R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M` of [Stacks, Tag 08J8]. It is the
tensorator's analogue of
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionDatum`. -/
def restrictDHomDatum :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).obj
          ((restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M))).obj
        ((restrictD X U).obj L) ⟶
      (restrictD X U).obj M :=
  letI := RingedSite.derivedTensorMonoidal X
  letI := RingedSite.derivedTensorMonoidal (X.over U)
  letI := restrictDMonoidal X U
  Functor.LaxMonoidal.μ (restrictD X U)
      (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) L ≫
    (restrictD X U).map (RingedSite.derivedSheafHomCounit X L M)

/-- **The comparison `R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)` attached to the tensorator of
`Stacks.Cohomology.SliceDerivedSheafHom.restrictDMonoidal`**: the unique morphism whose transpose
under the tensor–internal-hom bijection of [Stacks, Tag 08J8] on the slice site is
`Stacks.Cohomology.SliceDerivedSheafHom.restrictDHomDatum`.

The bijection is read as `Stacks.Cohomology.SliceDerivedSheafHom.bijective_derivedSheafHomCounit`
over `C/U`, the bijection with its formula already substituted, rather than as
`Stacks.Cohomology.SliceDerivedSheafHom.sliceCurryEquiv`: the latter is spelled with the
instances of the slice site named at `X.O.over U`, the datum at `(X.over U).O`, and an equation
between the datum and an application of `sliceCurryEquiv` exhausts the elaborator's recursion
budget. Read through the substituted bijection the defining equation is
`Stacks.Cohomology.SliceDerivedSheafHom.map_restrictDHomMap_comp_derivedSheafHomCounit`, with no
bijection left in it. -/
def restrictDHomMap :
    (restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) ⟶
      ((RingedSite.derivedSheafHomBifunctor (X.over U)).obj
          (op ((restrictD X U).obj L))).obj ((restrictD X U).obj M) :=
  (Equiv.ofBijective _ (bijective_derivedSheafHomCounit (X.over U)
      ((restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M))
      ((restrictD X U).obj L) ((restrictD X U).obj M))).symm (restrictDHomDatum X U L M)

/-- **The defining equation of `Stacks.Cohomology.SliceDerivedSheafHom.restrictDHomMap`**: the
comparison tensored with the identity of `L|_U`, followed by the evaluation morphism formed over
`C/U`, is the transpose datum. -/
theorem map_restrictDHomMap_comp_derivedSheafHomCounit :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).map
          (restrictDHomMap X U L M)).app ((restrictD X U).obj L) ≫
        RingedSite.derivedSheafHomCounit (X.over U) ((restrictD X U).obj L)
          ((restrictD X U).obj M) =
      restrictDHomDatum X U L M :=
  Equiv.ofBijective_apply_symm_apply _ (bijective_derivedSheafHomCounit (X.over U) _ _ _) _

/-- **The defining equation determines
`Stacks.Cohomology.SliceDerivedSheafHom.restrictDHomMap`.** The tensor–internal-hom bijection of
[Stacks, Tag 08J8] on the slice site is a bijection, so a morphism
`R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)` is that comparison exactly when its transpose is the
transpose datum. The companion of
`Stacks.Cohomology.SliceDerivedSheafHom.eq_derivedSheafHomRestrictionTranspose_iff`. -/
theorem eq_restrictDHomMap_iff
    (g : (restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) ⟶
      ((RingedSite.derivedSheafHomBifunctor (X.over U)).obj
        (op ((restrictD X U).obj L))).obj ((restrictD X U).obj M)) :
    g = restrictDHomMap X U L M ↔
      ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).map g).app
          ((restrictD X U).obj L) ≫
        RingedSite.derivedSheafHomCounit (X.over U) ((restrictD X U).obj L)
          ((restrictD X U).obj M) =
      restrictDHomDatum X U L M :=
  ⟨fun h => h ▸ map_restrictDHomMap_comp_derivedSheafHomCounit X U L M,
    fun h => (bijective_derivedSheafHomCounit (X.over U) _ _ _).1
      (h.trans (map_restrictDHomMap_comp_derivedSheafHomCounit X U L M).symm)⟩

variable [HasBinaryProducts X.C] [IsIso (Over.forgetAdjStar U).unit]

/-- **`Stacks.Cohomology.SliceDerivedSheafHom.restrictDHomMap` is an isomorphism.** This is
`CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective` — Yoneda, the adjunction
`j_! ⊣ j^*` on derived categories and the projection formula [Stacks, Tag 0GL1] — read at the
tensorator of `Stacks.Cohomology.SliceDerivedSheafHom.restrictDMonoidal` in place of
`Stacks.Cohomology.SliceDerivedSheafHom.sliceTensorRestrictionObjIso`; that statement takes the
comparison of tensor products as a parameter, so the two readings cost the same. -/
theorem isIso_restrictDHomMap : IsIso (restrictDHomMap X U L M) := by
  let := RingedSite.derivedTensorMonoidal X
  let := RingedSite.derivedTensorMonoidal (X.over U)
  let := restrictDMonoidal X U
  have := Stacks.DerivedTensor.ExtensionByZero.isIso_derivedAdjunction_unit X U
  exact CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective
    (Stacks.SheafOfModules.derivedTensorProductFunctor X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U))
    (Stacks.DerivedTensor.ExtensionByZero.derivedAdjunction X U)
    (fun A B => (Functor.Monoidal.μIso (restrictD X U) A B).symm)
    (fun f B => (Functor.OplaxMonoidal.δ_natural_left (restrictD X U) f B).symm)
    (projectionIso X U)
    (RingedSite.derivedSheafHomCounit X L M)
    (fun Z => bijective_derivedSheafHomCounit X Z L M)
    (RingedSite.derivedSheafHomCounit (X.over U) ((restrictD X U).obj L)
      ((restrictD X U).obj M))
    (fun Z => bijective_derivedSheafHomCounit (X.over U) Z _ _)
    (restrictDHomMap X U L M) (map_restrictDHomMap_comp_derivedSheafHomCounit X U L M)

/-! ### A homothety restricted to the slice site -/

/-- **A homothety of `K` restricts to an isomorphism over `U`**, from an object computation over
`U` alone.

Let `K` be an object of `D(O)` and `a : O[0] ⟶ R𝓗om_O(K, K)` a morphism with
`a ▷ K ≫ e_{K,K} = λ_ K`, where `e` is the evaluation morphism of [Stacks, Tag 08J8]. If
`R𝓗om_{O|_U}(K|_U, K|_U)` is isomorphic to `O|_U[0]` as an object, with no compatibility asked
of the isomorphism, then `a|_U` is an isomorphism.

Both the comparison of tensor products and the comparison of units are read off
`Stacks.Cohomology.SliceDerivedSheafHom.restrictDMonoidal`, so the left-unitor identity relating
them is that structure's own left unitality axiom
(`CategoryTheory.Functor.LaxMonoidal.left_unitality`) and is not a parameter. -/
theorem isIso_map_of_whiskerRight_comp_derivedSheafHomCounit
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : letI := RingedSite.derivedTensorMonoidal X
      𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
        ((RingedSite.derivedSheafHomBifunctor X).obj (op K)).obj K)
    (ha : letI := RingedSite.derivedTensorMonoidal X
      a ▷ K ≫ RingedSite.derivedSheafHomCounit X K K = (λ_ K).hom)
    (ψ : letI := RingedSite.derivedTensorMonoidal (X.over U)
      ((RingedSite.derivedSheafHomBifunctor (X.over U)).obj
            (op ((restrictD X U).obj K))).obj ((restrictD X U).obj K) ≅
        𝟙_ (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)))) :
    IsIso ((restrictD X U).map a) := by
  let := RingedSite.derivedTensorMonoidal X
  let := RingedSite.derivedTensorMonoidal (X.over U)
  let := restrictDMonoidal X U
  have := isIso_restrictDHomMap X U K K
  exact isIso_map_of_whiskerRight_comp_eq_leftUnitor_of_iso_tensorUnit
    (R := restrictD X U)
    (c := fun A B => (Functor.Monoidal.μIso (restrictD X U) A B).symm)
    (u := (Functor.Monoidal.εIso (restrictD X U)).symm)
    (hc := fun f B => (Functor.OplaxMonoidal.δ_natural_left (restrictD X U) f B).symm)
    (K := K) (hu := (Functor.LaxMonoidal.left_unitality (restrictD X U) K).symm)
    (A := ((RingedSite.derivedSheafHomBifunctor X).obj (op K)).obj K)
    (e := RingedSite.derivedSheafHomCounit X K K) (a := a) (ha := ha)
    (e' := RingedSite.derivedSheafHomCounit (X.over U) ((restrictD X U).obj K)
      ((restrictD X U).obj K))
    (he' := fun Z => bijective_derivedSheafHomCounit (X.over U) Z _ _)
    (t := restrictDHomMap X U K K)
    (ht := map_restrictDHomMap_comp_derivedSheafHomCounit X U K K) (ψ := ψ)

end Stacks.Cohomology.SliceDerivedSheafHom

/-! ### The ringed space -/

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} Rc)
      (ComplexShape.up ℤ)]

/-- **The restriction of the homothety of `K` to the slice site over an open is an
isomorphism**, from an object computation over that open alone.

Let `K` be an object of `D(𝒪_X)` and `U` an open of `X`, and suppose given an isomorphism

`ψ : R𝓗om_{𝒪_X|_U}(K|_U, K|_U) ≅ 𝒪_X|_U[0]`

of objects, with no compatibility asked of it. Then the restriction of
`Stacks.SheafOfModules.derivedSheafHomothety Rc K` to the slice site over `U` is an isomorphism.

This is
`Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_of_whiskerRight_comp_derivedSheafHomCounit`,
where the comparison of tensor products is the tensorator of
`Stacks.Cohomology.SliceDerivedSheafHom.restrictDMonoidal` and both of those are structure.

The defining equation of the homothety is
`Stacks.SheafOfModules.whiskerRight_derivedSheafHomothety_comp`, read at the ringed site of the
opens of `X` by `Stacks.SheafOfModules.derivedSheafHomCounit_eq_ringedSite`. -/
theorem isIso_map_derivedSheafHomothety_of_iso_derivedSheafHom (U : Opens X)
    [HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
    [((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify ((ringedSite Rc).over U).J AddCommGrpCat.{u}]
    [((ringedSite Rc).over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Tensor.sheafTensor.{u, u, u, u, u} ((ringedSite Rc).over U).O).Additive]
    [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} ((ringedSite Rc).over U).O).obj M).Additive]
    [∀ (K₁ K₂ : CochainComplex
        (SheafOfModules.{u} (Tensor.ringSheaf ((ringedSite Rc).over U).O)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Tensor.sheafTensor.{u, u, u, u, u} ((ringedSite Rc).over U).O) (ComplexShape.up ℤ)]
    [IsIso (Over.forgetAdjStar U).unit]
    (K : DerivedCategory (StructureSheafModules Rc))
    (ψ : letI := RingedSite.derivedTensorMonoidal ((ringedSite Rc).over U)
      ((RingedSite.derivedSheafHomBifunctor ((ringedSite Rc).over U)).obj
            (op ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD
              (ringedSite Rc) U).obj K))).obj
          ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite Rc) U).obj K) ≅
        𝟙_ (DerivedCategory (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite Rc).over U).O)))) :
    IsIso ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite Rc) U).map
      (derivedSheafHomothety Rc K)) := by
  let := RingedSite.derivedTensorMonoidal (ringedSite Rc)
  -- `ha` whiskers the homothety, which is written over `structureSheaf Rc`; the monoidal
  -- structure on that spelling of `D(𝒪_X)` is the ringed space's, and instance search does
  -- not reach it from the ringed site's.
  let := derivedMonoidalStructure Rc
  have ha : derivedSheafHomothety Rc K ▷ K ≫
      RingedSite.derivedSheafHomCounit (ringedSite Rc) K K = (λ_ K).hom := by
    rw [← derivedSheafHomCounit_eq_ringedSite Rc K K]
    exact whiskerRight_derivedSheafHomothety_comp Rc K
  exact Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_of_whiskerRight_comp_derivedSheafHomCounit
    (ringedSite Rc) U K (derivedSheafHomothety Rc K) ha ψ

/-- **The homothety of `K` is an isomorphism**, from an object computation over each member of a
family of opens covering `X`.

This is `Stacks.SheafOfModules.isIso_map_derivedSheafHomothety_of_iso_derivedSheafHom` over each
member, composed with `Stacks.SheafOfModules.isIso_derivedSheafHomothety_of_coversTop`, which
reads invertibility of a morphism of `D(𝒪_X)` off its restrictions to a covering family. -/
theorem isIso_derivedSheafHomothety_of_iso_derivedSheafHom_of_coversTop
    {ι : Type*} {Y : ι → Opens X}
    (hY : (Opens.grothendieckTopology X).CoversTop Y)
    [∀ i, HasSheafify ((Opens.grothendieckTopology X).over (Y i)) AddCommGrpCat.{u}]
    [∀ i, ((Opens.grothendieckTopology X).over (Y i)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ i, HasSheafify ((ringedSite Rc).over (Y i)).J AddCommGrpCat.{u}]
    [∀ i, ((ringedSite Rc).over (Y i)).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ i, (Tensor.sheafTensor.{u, u, u, u, u} ((ringedSite Rc).over (Y i)).O).Additive]
    [∀ i, ∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} ((ringedSite Rc).over (Y i)).O).obj M).Additive]
    [∀ i, ∀ (K₁ K₂ : CochainComplex
        (SheafOfModules.{u} (Tensor.ringSheaf ((ringedSite Rc).over (Y i)).O)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Tensor.sheafTensor.{u, u, u, u, u} ((ringedSite Rc).over (Y i)).O) (ComplexShape.up ℤ)]
    [∀ i, IsIso (Over.forgetAdjStar (Y i)).unit]
    (K : DerivedCategory (StructureSheafModules Rc))
    (ψ : ∀ i, letI := RingedSite.derivedTensorMonoidal ((ringedSite Rc).over (Y i))
      ((RingedSite.derivedSheafHomBifunctor ((ringedSite Rc).over (Y i))).obj
            (op ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD
              (ringedSite Rc) (Y i)).obj K))).obj
          ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite Rc) (Y i)).obj K) ≅
        𝟙_ (DerivedCategory (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite Rc).over (Y i)).O)))) :
    IsIso (derivedSheafHomothety Rc K) :=
  isIso_derivedSheafHomothety_of_coversTop Rc hY K
    (fun i => isIso_map_derivedSheafHomothety_of_iso_derivedSheafHom Rc (Y i) K (ψ i))

end Stacks.SheafOfModules

end
