module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.UnitComplexCocycles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedRestrictionMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualCoevaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualRetract

/-!
# The direct-summand step of Stacks 0FPV over a slice of the site

Let `(C, O)` be a ringed site, let `N` be a left dual of `M` in `D(O)`, and let `ℳ` and `𝒩` be
K-flat complexes representing them. Let `j : 𝒦 ⟶ ℳ` be a map of complexes and `σ : 𝒮 ⟶ ℳ ⊗ 𝒩`
a map whose class in `D(O)` is `Q(j) ▷ Q(𝒩)` up to an isomorphism `Q(𝒮) ≅ Q(𝒦) ⊗^L Q(𝒩)`. If,
over an object `U` of the site, the coevaluation of the pairing is the class of the map of
complexes out of `O[0]|_U` determined by a cocycle section of `𝒮|_U`, then `M|_U` is a retract of
`𝒦|_U` in `D(O|_U)`.

This is the step the source performs three times: "denoting `K` the object of `D(O)` represented
by `𝒦^•` we find a commutative diagram … since the composition of the upper row is the identity
on `M` we conclude that `M` is a direct summand of `K` in `D(O)`."

## Main results

* `Stacks.Cohomology.LeftDualOnASite.nonempty_retract_restrict`: the statement above.

## Implementation notes

The monoidal yoga is not redone: it is `CategoryTheory.nonempty_retract_map_of_factorization` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualRetract`, which is stated for
an arbitrary monoidal functor and mentions neither a space nor a site. What this file supplies is
the four pieces of data that lemma asks for, on a site:

* the monoidal functor is derived restriction to the slice, monoidal by
  `Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal`;
* the unit and tensor comparisons are `(symmetricMonoidalDerived O).unitIso` and `.comparison`;
* the three isomorphisms comparing the functor's action on a class with the class of its action
  on a complex are `CategoryTheory.Functor.mapDerivedCategoryFactors`;
* the morphism out of the unit over the slice is the class of
  `AlgebraicGeometry.RingedSite.unitComplexHomOfCocycle`, the map of complexes determined by a
  cocycle section.

**Three spellings of the structure sheaf of the slice.**
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U`,
`(Stacks.ringSheaf X.J X.O).over U` and `Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)` are
definitionally equal and not reducibly so, as the module doc of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor` records: an
instance proved at one is not found at another. That is why
`restriction X U`, which is
`SheafOfModules.overFunctor (Stacks.ringSheaf X.J X.O) U`, needs no comparison with the
`SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U` that
`AlgebraicGeometry.RingedSite.restrictComplex`
and the cocycle dictionary are written at — they are the same functor — while the instances
still have to be supplied at the spelling each statement uses. In the event nothing had to be
supplied by hand: `restriction X U` and the
`SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U` of the
cocycle dictionary unified without a comparison, and the elaborator accepted the cocycle
`t : (𝒮^0)(U)` of the dictionary where the restricted complex's degree-zero sections were
wanted.

The declaration sits in `Stacks.Cohomology.LeftDualOnASite` rather than in
`AlgebraicGeometry.RingedSite`: inside the latter, `DerivedModules`, `Complexes`, `KFlat`,
`derivedMonoidal` and `symmetricMonoidalDerived` all resolve to `RingedSite`'s own homonyms
instead of to `Stacks.SheafOfModules.DerivedMonoidal`'s, and fully qualifying them makes the
statement unreadable and over-long. The ringed-space counterpart
`Stacks.Cohomology.LeftDualPerfect.nonempty_retract_restrict` keeps its name; the two are in
different namespaces and neither shadows the other.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.DerivedTensor.ExtensionByZero (restriction)

universe u

namespace Stacks.Cohomology.LeftDualOnASite

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The direct-summand step of Stacks 0FPV over a slice.** The data is the one
`CategoryTheory.nonempty_retract_map_of_factorization` consumes, read on a ringed site: K-flat
representatives of the two sides of the pairing, a map `j : 𝒦 ⟶ ℳ`, a map `σ : 𝒮 ⟶ ℳ ⊗ 𝒩`
whose class is `Q(j) ▷ Q(𝒩)` up to `Θ`, and a cocycle section of `𝒮|_U` whose map of complexes
out of `O[0]|_U` represents the restricted coevaluation. -/
theorem nonempty_retract_restrict (U : X.C) (M N : DerivedModules X.O)
    (pair : letI := derivedMonoidal X.O; ExactPairing M N)
    (Mc Nc K Sc : Complexes X.O)
    (eM : DerivedCategory.Q.obj Mc ≅ M) (eN : DerivedCategory.Q.obj Nc ≅ N)
    (hM : KFlat X.O Mc) (hN : KFlat X.O Nc) (j : K ⟶ Mc) :
    letI := derivedMonoidal X.O
    letI := derivedMonoidal (X.O.over U)
    letI := Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal X U
    letI := pair
    ∀ (σ : Sc ⟶ (Mc ⊗ Nc : Complexes X.O))
      (Θ : DerivedCategory.Q.obj Sc ≅ DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj Nc)
      (_ : Θ.hom ≫ (DerivedCategory.Q.map j ▷ DerivedCategory.Q.obj Nc) =
        DerivedCategory.Q.map σ ≫ ((symmetricMonoidalDerived X.O).comparison Mc Nc hM hN).inv)
      (t : (Sc.X 0).val.obj (op U)) (ht : (Sc.d 0 1).val.app (op U) t = 0),
      (restriction X U).mapDerivedCategory.map
            (X.coevaluationUnitHom Mc Nc hM hN (η_ M N ≫ (eM.inv ⊗ₘ eN.inv))) ≫
          (restriction X U).mapDerivedCategoryFactors.hom.app (Mc ⊗ Nc) =
        (restriction X U).mapDerivedCategoryFactors.hom.app (X.structureSheafComplex) ≫
          DerivedCategory.Q.map (X.unitComplexHomOfCocycle t ht ≫
            ((restriction X U).mapHomologicalComplex
              (ComplexShape.up ℤ)).map σ) →
      Nonempty (Retract
        ((restriction X U).mapDerivedCategory.obj M)
        ((restriction X U).mapDerivedCategory.obj
          (DerivedCategory.Q.obj K))) := by
  let _ := derivedMonoidal X.O
  let _ := derivedMonoidal (X.O.over U)
  let _ := Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal X U
  let _ := pair
  intro σ Θ hΘ t ht hβ
  exact nonempty_retract_map_of_factorization
    (restriction X U).mapDerivedCategory M N
    (symmetricMonoidalDerived X.O).unitIso eM eN
    ((symmetricMonoidalDerived X.O).comparison Mc Nc hM hN) (DerivedCategory.Q.map j)
    (DerivedCategory.Q.map σ) Θ hΘ
    ((restriction X U).mapDerivedCategoryFactors.app (X.structureSheafComplex))
    ((restriction X U).mapDerivedCategoryFactors.app Sc)
    ((restriction X U).mapDerivedCategoryFactors.app (Mc ⊗ Nc))
    (DerivedCategory.Q.map (((restriction X U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map σ))
    ((restriction X U).mapDerivedCategoryFactors_hom_naturality σ)
    (DerivedCategory.Q.map (X.unitComplexHomOfCocycle t ht))
    (hβ.trans (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _)))

end Stacks.Cohomology.LeftDualOnASite

end
