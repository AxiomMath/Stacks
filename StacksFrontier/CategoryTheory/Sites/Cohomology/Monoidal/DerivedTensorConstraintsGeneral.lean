module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.KFlatComplexesInTheDerivedCategoryGeneral

/-!
# The constraints of the derived tensor product, at general universes

Let `(C, O)` be a ringed site whose objects live in a universe `c` and whose morphisms and sections
live in the universe `u` of the sheaf of rings. The associator, unitors and braiding of `D(Mod(O))`
are computed on K-flat complexes by those of complexes.

## Implementation notes

This is the part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorConstraints` that does not
need
`C` to be a `SmallCategory.{u}`, for a site `C : Type c` with `[Category.{u} C]`; the statements
and proofs are the same, in the namespace `Stacks.SheafOfModules.DerivedMonoidalGeneral`. This
applies to the small étale ringed site of an algebraic space.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

universe d c u

namespace Stacks.SheafOfModules.DerivedMonoidalGeneral

variable {C : Type c} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  CochainComplex.symmetricCategory

/- The pinned-universe monoidal structures of `CanonicalDerivedTensorComparison`, back in
scope.  `SheafOfModules.monoidalCategorySheafTensor` has sections in `max u v w` for a `w`
that the `u` of `Mod R` does not determine, and the constraints below cannot be reduced
through a structure whose universe is still a metavariable. -/
attribute [local instance] monoidalCategoryMod symmetricCategoryMod monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod monoidalComplexes

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal
  CochainComplex.KFlatMonoidal.homotopyBraided
  kFlatQ_isLocalization derivedMonoidal derivedSymmetric

attribute [local instance] homQMonoidal homQBraided kFlatQMonoidal kFlatQBraided
  kFlatQuotientMonoidal kFlatQuotientLaxBraided kFlatComplexQMonoidal kFlatComplexQLaxBraided

/-! ### The comparison on K-flat complexes -/

/-- **For K-flat complexes the tensor product of `D(Mod(O))` is the image of the total tensor
product of complexes.**  This is the tensorator of `kFlatComplexQ`. -/
abbrev kFlatComparison
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)]
    {K L : Complexes R} (hK : KFlat R K) (hL : KFlat R L) :
    DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj (K ⊗ L) :=
  Functor.Monoidal.μIso (kFlatComplexQ R) ⟨K, hK⟩ ⟨L, hL⟩

/-- **The commutativity constraint of `D(Mod(O))` is the Koszul symmetry of complexes**: the
comparison on K-flat complexes carries the braiding of `D(Mod(O))` to that of
`Comp(Mod(O))`. -/
theorem kFlatComparison_braiding
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)]
    {K L : Complexes R} (hK : KFlat R K) (hL : KFlat R L) :
    (β_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        (kFlatComparison R hL hK).hom =
      (kFlatComparison R hK hL).hom ≫ DerivedCategory.Q.map (β_ K L).hom :=
  (Functor.LaxBraided.braided (F := kFlatComplexQ R) ⟨K, hK⟩ ⟨L, hL⟩).symm

/-- **The associativity constraint of `D(Mod(O))` is the associator of the total tensor product
of complexes**: the comparison on K-flat complexes carries the associator of `D(Mod(O))` to
that of `Comp(Mod(O))`. -/
theorem kFlatComparison_associator
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)]
    {K L M : Complexes R} (hK : KFlat R K) (hL : KFlat R L)
    (hM : KFlat R M) :
    (kFlatComparison R hK hL).hom ▷ DerivedCategory.Q.obj M ≫
        (kFlatComparison R (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hK hL) hM).hom ≫
        DerivedCategory.Q.map (α_ K L M).hom =
      (α_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M)).hom ≫
        DerivedCategory.Q.obj K ◁ (kFlatComparison R hL hM).hom ≫
        (kFlatComparison R hK (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hL hM)).hom :=
  Functor.LaxMonoidal.associativity (kFlatComplexQ R) ⟨K, hK⟩ ⟨L, hL⟩ ⟨M, hM⟩

/-- **The comparison is natural in both complexes.** -/
theorem kFlatComparison_naturality
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)]
    {K K' L L' : Complexes R} (f : K ⟶ K') (g : L ⟶ L')
    (hK : KFlat R K) (hK' : KFlat R K') (hL : KFlat R L) (hL' : KFlat R L') :
    (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫ (kFlatComparison R hK' hL').hom =
      (kFlatComparison R hK hL).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g) :=
  Functor.LaxMonoidal.μ_natural (F := kFlatComplexQ R)
    (X := ⟨K, hK⟩) (Y := ⟨K', hK'⟩) (X' := ⟨L, hL⟩) (Y' := ⟨L', hL'⟩)
    (ObjectProperty.homMk f) (ObjectProperty.homMk g)

end Stacks.SheafOfModules.DerivedMonoidalGeneral

end
