module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatInBothVariables
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatResolutionInstances
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.Homology.KFlat.BifunctorCommShiftTwoInstances
public import StacksFrontier.Homology.KFlat.BifunctorToTotalComplex
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product on a ringed site, with the sections universe free

Let `(C, O)` be a ringed site whose objects lie in `Type c`, whose morphisms lie in `Type v`
and whose structure sheaf and modules have sections in `Type w`, the three universes being
independent. This file constructs the derived tensor product of sheaves of `O`-modules, that
is an element of `Stacks.SheafOfModules.DerivedTensorProduct`: a bifunctor on `D(Mod(O))`
computed on K-flat representatives by the ordinary total tensor product, with the canonical
map to that total tensor product, its naturality, the two-variable shift coherence and
exactness in each variable.

## Main definitions

* `Stacks.SheafOfModules.FreeSections.derivedTensorProduct`: the derived tensor product.
* `Stacks.SheafOfModules.FreeSections.sliceDerivedTensorProduct`: the same on each slice
  `(C/U, O|_U)`, which is the family `LocallyHasFiniteTorDimension` measures Tor amplitude
  against.

## Main results

* `Stacks.SheafOfModules.FreeSections.existsKFlatRes`: every complex of `O`-modules receives
  a quasi-isomorphism from a K-flat one, at these universes.

## Why the sections universe is free here

The construction is the abstract one of `CochainComplex.KFlatBifunctor`, instantiated at the
tensor product of sheaves of modules. That development — the descent `derivedBifunctor` of
`Tot(- ⊗ -)` along the two K-flat localizations, the comparison with the total complex, the
canonical map `toTensor` with its naturality, the two-variable shift coherence
`derivedBifunctor_commShift₂Int` and exactness in each variable — is stated for an arbitrary
bifunctor of abelian categories and relates no universes at all. Its one unproved input is
that every complex receives a quasi-isomorphism from a K-flat one, and for sheaves of modules
that is `Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize`, Stacks 06YS with
the object, morphism and sections universes independent and with no size condition relating
them. Left K-flatness of the resolution, which the second localization needs, comes from
K-flatness by the symmetry of `⊗_O`,
`Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat`, which is also stated at three free
universes. Both resolutions are the instances
`Stacks.DerivedTensor.RingedSite.kFlatLocalizer_hasLeftResolutions` and
`kFlatLocalizerLeft_hasLeftResolutions`, from which instance search finds the two K-flat
localizations.

The typeclass hypotheses are therefore exactly those of
`Stacks.SheafOfModules.DerivedTensorProduct` itself, plus nothing: sheafification and local
bijectivity for `AddCommGrpCat.{w}`, the two additivity instances of `⊗_O`, the totalisation
instance, and a derived category.

## Relation to `Existence.lean`

`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/Existence.lean` proves the same
thing for a `AlgebraicGeometry.RingedSite.{c, u, u}`, through the site-level re-derivation of
the same abstract development that occupies the rest of this directory, and
`ExistenceOnARingedSite.lean` proves it for a small site with all four universes equal. Both
are left exactly as they stand, with their developments and their consumers. What is added
here is the statement with the sections universe free of the morphism universe, which neither
reaches: the small étale site of a scheme ringed by the constant coefficient sheaf of
Stacks 03TR is an `AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) w r}`, and so is each
of its slices, since a slice of a `RingedSite.{c, v, w}` is a `RingedSite.{max c v, v, w}`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex.KFlatBifunctor

universe c v w d

namespace Stacks.SheafOfModules.FreeSections

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : AlgebraicGeometry.RingedSite.{c, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)]

/-- **Every complex of `O`-modules receives a quasi-isomorphism from a K-flat complex**, in the
shape the abstract K-flat localization of `CochainComplex.KFlatBifunctor` consumes. This is
Stacks 06YS at a sections universe free of the two site universes,
`Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize`, read at the bundled
ringed site. -/
theorem existsKFlatRes :
    ∀ G : CochainComplex (RingedSite.Modules.{c, v, w} X) ℤ,
      ∃ (P : CochainComplex (RingedSite.Modules.{c, v, w} X) ℤ) (p : P ⟶ G),
        KFlat (Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O) P ∧ QuasiIso p :=
  fun G => Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize.{v, c, w} X.O G

variable [HasDerivedCategory.{d} (RingedSite.Modules.{c, v, w} X)]

/-- **The canonical map to the ordinary total tensor product is invertible when the right
factor is K-flat**: it is then the one-sided comparison isomorphism. -/
theorem isIsoToTensorRight
    (K L : CochainComplex (RingedSite.Modules.{c, v, w} X) ℤ) (hL : IsKFlat X.O L) :
    IsIso (toTensor (Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O)
      (existsKFlatRes X) K L) := by
  rw [toTensor_eq_comparisonRight _ (existsKFlatRes X) K hL]
  infer_instance

/-- **The canonical map to the ordinary total tensor product is invertible when the left factor
is K-flat.** A K-flat complex is left K-flat by the symmetry of `⊗_O`, and tensoring a
quasi-isomorphism with a left K-flat complex is a quasi-isomorphism. -/
theorem isIsoToTensorLeft
    (K L : CochainComplex (RingedSite.Modules.{c, v, w} X) ℤ) (hK : IsKFlat X.O K) :
    IsIso (toTensor (Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O)
      (existsKFlatRes X) K L) :=
  isIso_toTensor_of_kFlatLeft _ (existsKFlatRes X)
    (Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat X.O hK) L

/-- **Stacks 06YU with the sections universe free of the morphism universe.** The derived
tensor product of sheaves of modules on a ringed site whose objects, morphisms and sections lie
in three independent universes: the descent of `Tot(- ⊗_O -)` along the two K-flat
localizations, with its K-flat comparisons, its canonical map to the ordinary total tensor
product, the two-variable shift coherence and exactness in each variable.

All three comparison isomorphisms are the same morphism, the canonical map
`CochainComplex.KFlatBifunctor.toTensor`, promoted by whichever K-flatness hypothesis the field
carries; so the four equations relating them hold by definition and the three naturality
statements are the single naturality of that map. -/
def derivedTensorProduct : DerivedTensorProduct.{c, v, w, d} X where
  tensor := derivedBifunctor (Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O)
  comparison K L _ hL := @asIso _ _ _ _ _ (isIsoToTensorRight X K L hL)
  comparison_naturality f g _ _ _ _ := toTensor_naturality _ (existsKFlatRes X) f g
  comparisonRight K L hL := @asIso _ _ _ _ _ (isIsoToTensorRight X K L hL)
  comparisonRight_naturality f g _ _ := toTensor_naturality _ (existsKFlatRes X) f g
  comparisonRight_eq_comparison _ _ _ _ := rfl
  comparisonLeft K L hK := @asIso _ _ _ _ _ (isIsoToTensorLeft X K L hK)
  comparisonLeft_naturality f g _ _ := toTensor_naturality _ (existsKFlatRes X) f g
  comparisonLeft_eq_comparison _ _ _ _ := rfl
  toTensor := toTensor _ (existsKFlatRes X)
  toTensor_naturality f g := toTensor_naturality _ (existsKFlatRes X) f g
  toTensor_eq_comparisonRight _ _ _ := rfl
  toTensor_eq_comparisonLeft _ _ _ := rfl
  commShift₂ := inferInstance
  exact_left _ := inferInstance
  exact_right _ := inferInstance

section Slices

attribute [local instance] AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective

variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c v, v, w, w, w} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c v, v, w, w, w}
      (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c v, v, w} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]
  [∀ U : X.C, HasDerivedCategory.{d} (RingedSite.Modules.{max c v, v, w} (X.over U))]

/-- **The derived tensor product on each slice of the ringed site.** A slice of a
`AlgebraicGeometry.RingedSite.{c, v, w}` is a `AlgebraicGeometry.RingedSite.{max c v, v, w}`,
again with its sections universe free of its morphism universe, so
`Stacks.SheafOfModules.FreeSections.derivedTensorProduct` applies to it unchanged.

This is the family of derived tensor products that
`Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension` measures Tor
amplitude against: one datum for each object of the site, because a slice has its own module
category and a datum on the site cannot measure Tor amplitude on a slice. -/
def sliceDerivedTensorProduct (U : X.C) :
    DerivedTensorProduct.{max c v, v, w, d} (X.over U) :=
  derivedTensorProduct (X.over U)

end Slices

end Stacks.SheafOfModules.FreeSections

end
