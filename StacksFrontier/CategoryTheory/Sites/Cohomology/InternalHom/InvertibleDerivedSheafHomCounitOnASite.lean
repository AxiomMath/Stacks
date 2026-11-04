module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence
public import StacksFrontier.CategoryTheory.Monoidal.CounitAtAnInvertibleObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLocality.InvertibilityOnACovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIso
import StacksCore.Tactic.StacksAttribute

/-!
# The evaluation morphism out of an invertible object, on a ringed site

Let `(C, O)` be a ringed site and let `L`, `M` be objects of `D(O)`. If `L` is invertible for
the derived tensor product ([Stacks, Tag 0FFN]) then the evaluation morphism of
[Stacks, Tag 08J8]

`R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M`

is an isomorphism. The localization and globalization steps of [Stacks, Tag 0ATP] are then
stated with invertibility of the restrictions `L|_U` as hypothesis.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorMonoidal`,
  `AlgebraicGeometry.RingedSite.derivedTensorSymmetric`: `D(O)` symmetric monoidal with
  `Stacks.SheafOfModules.derivedTensorProductFunctor` for its tensor product, on the nose.

## Main results

* `AlgebraicGeometry.RingedSite.curriedTensor_derivedTensorMonoidal`: that identification, as
  an equality of bifunctors.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomCounit_of_isInvertible`: **the evaluation
  morphism out of an invertible object is an isomorphism**, on a ringed site.
* `SliceDerivedSheafHom.isIso_map_derivedSheafHomCounit_of_isInvertible_restriction`: if the mate
  of the slice tensor comparison is an isomorphism and `L|_U` is an invertible object of
  `D(O|_U)`, then the restriction to `C/U` of the evaluation morphism formed over `C` is an
  isomorphism.
* `SliceDerivedSheafHom.isInvertible_of_isIso_transpose_of_isInvertible_restriction`: if over
  each member of a covering family the mate is an isomorphism and the object restricts to an
  invertible one, the object is invertible.

## Implementation notes

`AlgebraicGeometry.RingedSite.derivedSheafHomCounit` is written at the derived tensor product
`Stacks.SheafOfModules.derivedTensorProductFunctor`, so invertibility is read at a monoidal
structure whose tensor product is that bifunctor and not merely isomorphic to it:
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal`, the structure of [Stacks, Tag 0FPT]
re-seated by `Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal`, for which `a ▷ L`
is `((derivedTensorProductFunctor X).map a).app L` by `rfl`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

namespace AlgebraicGeometry.RingedSite

section Site

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- **`D(O)` is monoidal with the derived tensor product of [Stacks, Tag 06YU] for its tensor
product**, on the nose: the structure of [Stacks, Tag 0FPT] re-seated onto
`Stacks.SheafOfModules.derivedTensorProductFunctor` by
`Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal`. -/
@[instance_reducible]
def derivedTensorMonoidal :
    MonoidalCategory
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal X.O
    (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X))

/-- **`AlgebraicGeometry.RingedSite.derivedTensorMonoidal` is symmetric**, with the
commutativity constraint the Koszul symmetry of complexes re-seated along the same two
isomorphisms. -/
@[instance_reducible]
def derivedTensorSymmetric :
    @SymmetricCategory
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) _
      (derivedTensorMonoidal X) :=
  @reseatSymmetric _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric X.O)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.O _)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.O)

/-- The tensor product of `AlgebraicGeometry.RingedSite.derivedTensorMonoidal` is the derived
tensor bifunctor of [Stacks, Tag 06YU], as an equality of bifunctors. -/
theorem curriedTensor_derivedTensorMonoidal :
    @curriedTensor
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) _
        (derivedTensorMonoidal X) =
      Stacks.SheafOfModules.derivedTensorProductFunctor X :=
  Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_reseatedDerivedMonoidal X.O _

/-- **The evaluation morphism out of an invertible object is an isomorphism, on a ringed
site.** If `L` is an invertible object of `D(O)` ([Stacks, Tag 0FFN]) then

`R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M`

is an isomorphism for every object `M` of `D(O)`. -/
theorem isIso_derivedSheafHomCounit_of_isInvertible
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : letI := derivedTensorMonoidal X; MonoidalCategory.IsInvertible L) :
    IsIso (derivedSheafHomCounit X L M) := by
  let := derivedTensorMonoidal X
  refine MonoidalCategory.isIso_of_isInvertible_of_tensorHomBijective
    (derivedSheafHomCounit X L M) (fun Z => ?_) hL
  have hfun : (fun a : Z ⟶ ((derivedSheafHomBifunctor X).obj (op L)).obj M =>
        a ▷ L ≫ derivedSheafHomCounit X L M) =
      ⇑(derivedCurryHomEquiv X Z L M) :=
    funext fun a => (derivedCurryHomEquiv_apply X Z L M a).symm
  rw [hfun]
  exact (derivedCurryHomEquiv X Z L M).bijective

end Site

end AlgebraicGeometry.RingedSite

namespace Stacks.Cohomology.SliceDerivedSheafHom

/-! ### The localization step at one object of the site -/

section Slice

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
  (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- If the mate `Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose` is
an isomorphism and `L|_U` is an invertible object of `D(O|_U)`, then the restriction to `C/U` of
the evaluation morphism `R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M` formed over `C` is an isomorphism. -/
theorem isIso_map_derivedSheafHomCounit_of_isInvertible_restriction
    (htr : IsIso (derivedSheafHomRestrictionTranspose X U L M))
    (hL : letI := RingedSite.derivedTensorMonoidal (X.over U)
      MonoidalCategory.IsInvertible ((restrictD X U).obj L)) :
    IsIso ((restrictD X U).map (RingedSite.derivedSheafHomCounit X L M)) := by
  have : IsIso (RingedSite.derivedSheafHomCounit (X.over U)
      ((restrictD X U).obj L) ((restrictD X U).obj M)) :=
    RingedSite.isIso_derivedSheafHomCounit_of_isInvertible (X.over U)
      ((restrictD X U).obj L) ((restrictD X U).obj M) hL
  apply isIso_map_derivedSheafHomCounit X U L M
  have hcurry : sliceCurryEquiv X U L M =
      RingedSite.derivedCurryHomEquiv (X.over U)
        ((restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M))
        ((restrictD X U).obj L) ((restrictD X U).obj M) := rfl
  have hdatum := ((congrArg (sliceCurryEquiv X U L M)
    (derivedSheafHomRestrictionTranspose_eq_symm_apply X U L M)).trans
    ((sliceCurryEquiv X U L M).apply_symm_apply (derivedSheafHomRestrictionDatum X U L M))).symm
  rw [hcurry, RingedSite.derivedCurryHomEquiv_apply] at hdatum
  rw [hdatum]
  infer_instance

end Slice

/-! ### Glueing an invertible object -/

section Glueing

variable (X : RingedSite.{u, u, u}) [HasBinaryProducts X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- **An object of `D(O)` is invertible as soon as, over the members of a covering family, the
mate is an isomorphism and the object restricts to an invertible one**: if `Y` covers the site
and, for each `i`, the mate of the slice tensor comparison at `(L, 𝟙)` over `Y i` is an
isomorphism and `L|_{Y i}` is an invertible object of `D(O|_{Y i})`, then `L` is invertible. -/
theorem isInvertible_of_isIso_transpose_of_isInvertible_restriction
    {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y)
    [∀ i, HasSheafify (X.J.over (Y i)) AddCommGrpCat.{u}]
    [∀ i, (X.J.over (Y i)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ i, (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (Y i)).Additive]
    [∀ i, (sheafTensor.{u, u, u, u, u} (X.over (Y i)).O).Additive]
    [∀ i, ∀ M, ((sheafTensor.{u, u, u, u, u} (X.over (Y i)).O).obj M).Additive]
    [∀ i, ∀ (K L : CochainComplex (Modules (X.over (Y i)).O) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.over (Y i)).O)
        (ComplexShape.up ℤ)]
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (htr : ∀ i, letI := RingedSite.derivedTensorMonoidal X
      IsIso (derivedSheafHomRestrictionTranspose X (Y i) L
        (𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))))
    (hL : ∀ i, letI := RingedSite.derivedTensorMonoidal (X.over (Y i))
      MonoidalCategory.IsInvertible ((restrictD X (Y i)).obj L)) :
    letI := RingedSite.derivedTensorMonoidal X
    MonoidalCategory.IsInvertible L := by
  let := RingedSite.derivedTensorMonoidal X
  let := RingedSite.derivedTensorSymmetric X
  have he : IsIso (RingedSite.derivedSheafHomCounit X L
      (𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))) :=
    isIso_of_isIso_mapDerivedCategory_overFunctor hY _ fun i =>
      isIso_map_derivedSheafHomCounit_of_isInvertible_restriction X (Y i) L _ (htr i) (hL i)
  exact MonoidalCategory.isInvertible_of_tensorIsoUnit
    (β_ L (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj
        (𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))) ≪≫
      @asIso _ _ _ _ _ he)

end Glueing

end Stacks.Cohomology.SliceDerivedSheafHom

end
