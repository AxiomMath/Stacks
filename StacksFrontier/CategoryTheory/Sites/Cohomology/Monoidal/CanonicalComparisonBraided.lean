module

public import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ReseatComparisonBraided
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedTensorBraiding

/-!
# The derived tensor product of Tag 06YU is commutative through its K-flat comparison

`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric` is the commutativity
constraint of [Stacks, Tag 0FPT] on the symmetric monoidal structure of `D(Mod(O))` whose
tensor product *is* the derived tensor product of [Stacks, Tag 06YU], and
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison` is that tensor product's K-flat
comparison with the total tensor product of complexes.  This file proves the compatibility of
the two: for K-flat complexes `K` and `L` the square

```
Q(K) ⊗^L Q(L) ------> Q(Tot(K ⊗_O L))
      |                      |
      | ψ                    | Q(Koszul)
      v                      v
Q(L) ⊗^L Q(K) ------> Q(Tot(L ⊗_O K))
```

commutes, the horizontal arrows being `canonicalComparison` and `ψ` the commutativity
constraint.  So the Koszul sign convention of `CochainComplex.koszulBraiding` is the sign
convention of the commutativity constraint of Tag 0FPT, as a checkable equation rather than by
construction.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.canonicalReseatIso_comp_canonicalComparison`: the
  re-seating isomorphism followed by the comparison of Tag 06YU is the comparison
  `CochainComplex.KFlatMonoidal.derivedTensorIso` of the localized structure.  This is what
  carries a statement about the latter to one about the former.
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_koszulBraiding`: **the square
  above**, with the symmetry of complexes written as `CochainComplex.koszulBraiding`.  The same
  square with that symmetry written as `β_` is
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedTensorReseatConstraints.lean`.

## Implementation notes

Nothing about signs is recomputed.  The same square for the *localized* tensor product of
`D(Mod(O))` is `CochainComplex.KFlatMonoidal.derivedTensorIso_braiding`; what is new here is
that the re-seated structure — whose tensor product is Tag 06YU's bifunctor on the nose —
satisfies it as well, with Tag 06YU's own comparison in place of the localized one.  The
passage is `CategoryTheory.MonoidalCategory.reseatSymmetric_braiding`, which computes the
re-seated braiding as the conjugate of the given one, together with the identification of the
two comparisons.

That identification is where the work is.  Tag 06YU's comparison is a field of a structure
sealed with `irreducible_def`, so it is opaque; the handle on it used here is
`Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_hom_app_app`, which expresses
the comparison of bifunctors at a pair of K-flat complexes through the one-sided K-flat
comparison of `CochainComplex.KFlatBifunctor.derivedBifunctor`.  Chasing that through the
re-seating isomorphism uses
`CochainComplex.KFlatBifunctor.comparisonRight_eq_comparison` and
`CochainComplex.KFlatMonoidal.derivedLocalizedTensorIso_comp_comparison_eq`.

Every step is taken in term mode through the generic lemmas of
`StacksFrontier/CategoryTheory/Category/CompositionChains.lean`, and the monoidal and symmetric
structures are supplied by `@`-application: `D(Mod(O))` carries both the localized structure
and the re-seated one, and neither is an instance.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal
  CochainComplex.KFlatMonoidal.homotopyBraided
  kFlatQ_isLocalization kFlatQLeft_isLocalization derivedMonoidal derivedSymmetric

/-! ### The comparison of Tag 06YU through the re-seating isomorphism -/

/-- **The re-seating isomorphism followed by the K-flat comparison of Tag 06YU is the
comparison of the localized structure.**  Tag 06YU's comparison is opaque, being a field of an
`irreducible_def`; this is the identification that makes a statement about
`CochainComplex.KFlatMonoidal.derivedTensorIso` a statement about it. -/
theorem canonicalReseatIso_comp_canonicalComparison {K L : Complexes R}
    (hK : KFlat R K) (hL : KFlat R L) :
    (@reseatIso (DerivedModules R) _ (derivedMonoidal R) _ (monoidalTensorCanonicalIso R)
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        (canonicalComparison R K L hK hL).hom =
      (CochainComplex.KFlatMonoidal.derivedTensorIso (Mod R) (exists_kFlat_resolution R)
        hK hL).hom :=
  CategoryTheory.comp_comp_eq_of_eq_comp_inv
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparison K L hK hL)
    (((derivedTensorBifunctorIso R).hom.app (DerivedCategory.Q.obj K)).app
      (DerivedCategory.Q.obj L))
    (((canonicalTensorIso R).hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L))
    (derivedBifunctorTensorIso_hom_app_app R
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R) K L hK hL)
    (CategoryTheory.comp_congr_eq
      (derivedTensorBifunctorIso_hom_app_app R (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L))
      (congrArg Iso.hom (comparisonRight_eq_comparison (curriedTensor (Mod R)) K L
        (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat (Mod R) hK) hL))
      (CochainComplex.KFlatMonoidal.derivedLocalizedTensorIso_comp_comparison_eq (Mod R)
        (exists_kFlat_resolution R) hK
        (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat (Mod R) hK) hL))

/-! ### The commutativity constraint of Tag 0FPT through the comparison of Tag 06YU -/

/-- **[Stacks, Tag 0FPT], the commutativity constraint is the Koszul symmetry**, with that
symmetry named.  For K-flat complexes `K` and `L`, the commutativity constraint of the symmetric
monoidal structure on `D(Mod(O))` whose tensor product is the derived tensor product of Tag 06YU
is carried by that tensor product's K-flat comparison to the symmetry of `Comp(Mod(O))`, which is
`CochainComplex.koszulBraiding`: the sectionwise symmetry times the sign `(-1)^{pq}` on the
summand of bidegree `(p, q)`. -/
theorem canonicalComparison_koszulBraiding {K L : Complexes R}
    (hK : KFlat R K) (hL : KFlat R L) :
    letI := canonicalDerivedMonoidal R
    letI := canonicalDerivedSymmetric R
    (β_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        (canonicalComparison R L K hL hK).hom =
      (canonicalComparison R K L hK hL).hom ≫
        DerivedCategory.Q.map (CochainComplex.koszulBraiding K L).hom :=
  CategoryTheory.comp_congr_eq_left
    (@reseatSymmetric_braiding (DerivedModules R) _ (derivedMonoidal R) _ _
      (derivedSymmetric R) (monoidalTensorCanonicalIso R) (canonicalUnitIso R)
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    (CategoryTheory.braiding_transport _ _
      (canonicalReseatIso_comp_canonicalComparison R hK hL)
      (canonicalReseatIso_comp_canonicalComparison R hL hK)
      (CochainComplex.KFlatMonoidal.derivedTensorIso_braiding (Mod R)
        (exists_kFlat_resolution R) hK hL))

end Stacks.SheafOfModules.DerivedMonoidal

end
