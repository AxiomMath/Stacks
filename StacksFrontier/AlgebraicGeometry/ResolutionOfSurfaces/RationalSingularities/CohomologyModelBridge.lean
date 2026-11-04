module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.Reduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LocalBirationalExtensions
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer
public import StacksCore.Tactic.StacksAttribute

/-!
# The two models of `H¹(X, 𝒪_X)` vanish together

The first cohomology of the structure sheaf of a scheme is spelled two ways in this development.
`AlgebraicGeometry.DefinesRationalSingularity`, and with it
`AlgebraicGeometry.IsZeroFirstStructureSheafCohomology`, uses Mathlib's `CategoryTheory.Sheaf.H`
of the abelian sheaf underlying `𝒪_X`; the boundedness and base-change results use the first
right derived functor of module-valued global sections, as in
`AlgebraicGeometry.firstCohomologyAsBaseModule`. This file identifies the vanishing of the one
with the vanishing of the other, in both directions.

## Main results

* `AlgebraicGeometry.isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived`: the
  comparison, in the shape its consumers use: `H¹(X, 𝒪_X) = 0` as a `Sheaf.H` subsingleton holds
  exactly when the first right derived functor of module-valued global sections is a zero object.
* `AlgebraicGeometry.subsingleton_firstCohomologyAsBaseModule_iff`: the same comparison with the
  right-hand side read as `AlgebraicGeometry.firstCohomologyAsBaseModule`, the `A`-module in which
  the boundedness results of [Stacks, Tag 0B4N] are stated.
* `AlgebraicGeometry.subsingleton_sheafH_unit_iff_isZero_rightDerived_evaluation`: the
  general-degree statement from which both are read off.
* `AlgebraicGeometry.isZeroFirstStructureSheafCohomology_iff_isZero_firstCohomologyStructureSheaf`:
  the same comparison against the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus`, which is
  the indexing in which [Stacks, Tag 02KH] and the higher direct images of the
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange` namespace are stated. Its right-hand side is
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstCohomologyStructureSheaf X`.
* `AlgebraicGeometry.definesRationalSingularity_iff_subsingleton_firstCohomologyAsBaseModule`:
  `AlgebraicGeometry.DefinesRationalSingularity` itself, restated in the module-valued model.

## Implementation notes

The proofs compose existing comparisons. Reading from the module-valued side,

* `Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup` forgets
  the module structure, which is harmless because forgetting it does not change the carrier;
* `Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH` is the
  composite of [Stacks, Tag 03FD] with the identification of `Ext` out of the free abelian sheaf
  on `yoneda.obj ⊤` with derived sections, and with the fact that `⊤` is a terminal open.

What remains is that the two statements speak of two abelian sheaves. `Sheaf.H` is applied to
`𝒪_X` composed with the two forgetful functors by
`AlgebraicGeometry.IsZeroFirstStructureSheafCohomology`, and to the image of
`SheafOfModules.unit` under `SheafOfModules.toSheaf` by the comparison. These are the same
sheaf: `SheafOfModules.unit` of a sheaf of rings `R` has as its sheaf condition the sheaf
condition of `R` composed with `forget₂ RingCat AddCommGrpCat`, so the underlying abelian sheaf
of the unit module is that composite, and composition of functors is associative definitionally.
So the two statements are definitionally equal and no transport is written.

Likewise `AlgebraicGeometry.firstCohomologyAsBaseModule` is the derived evaluation with its
scalars restricted along `A ⟶ Γ(X, 𝒪_X)`, and restriction of scalars leaves the carrier alone,
so being a subsingleton is the same condition before and after it.

The passage to the `ℤ`-indexed derived functor is `Stacks.DerivedIndexing.rightDerivedIso`, at
`HasDerivedCategory.standard`, which is the local instance the `ℤ`-indexed consumers are stated
at as well.

**No `@[stacks ...]` attribute is attached.** This is a comparison of two spellings internal to
this development, not a statement of the Stacks project; the tag for the comparison of
cohomology theories is [Stacks, Tag 03FD], which is carried by the results composed here.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The two models of the cohomology of the structure sheaf vanish together**, in every degree.
On the left is Mathlib's `CategoryTheory.Sheaf.H` of the abelian sheaf underlying `𝒪_X`, on the
right the degree-`n` right derived functor of module-valued global sections applied to the unit
module. -/
theorem subsingleton_sheafH_unit_iff_isZero_rightDerived_evaluation (X : Scheme.{u})
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] (n : ℕ) :
    Subsingleton (Sheaf.H.{u, u, u, u}
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)) n) ↔
      IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : Opens X))).rightDerived n).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
  ((Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      X.ringCatSheaf (⊤ : Opens X) n (SheafOfModules.unit X.ringCatSheaf)).trans
    (Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH
      X n (SheafOfModules.unit X.ringCatSheaf))).symm

/-- **`H¹(X, 𝒪_X) = 0` in the `Sheaf.H` spelling is `H¹(X, 𝒪_X) = 0` in the module-valued
spelling.** The left-hand side is the vanishing asserted by
`AlgebraicGeometry.DefinesRationalSingularity`; the right-hand side is the first right derived
functor of module-valued global sections, which is what the boundedness and base-change results
of this development compute with. -/
theorem isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived (X : Scheme.{u}) :
    IsZeroFirstStructureSheafCohomology X ↔
      IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : Opens X))).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  let : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  exact subsingleton_sheafH_unit_iff_isZero_rightDerived_evaluation X 1

/-- **The first cohomology module over the base vanishes exactly when `H¹(X, 𝒪_X)` does.**  This
is `AlgebraicGeometry.isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived` with the
module-valued side read as `AlgebraicGeometry.firstCohomologyAsBaseModule`, the `A`-module whose
lengths [Stacks, Tag 0B4N] bounds; restricting the scalars along `A ⟶ Γ(X, 𝒪_X)` does not change
the carrier, so it does not change whether the carrier is a subsingleton. -/
theorem subsingleton_firstCohomologyAsBaseModule_iff {A : Type u} [CommRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) :
    Subsingleton (firstCohomologyAsBaseModule X f) ↔ IsZeroFirstStructureSheafCohomology X :=
  (ModuleCat.isZero_iff_subsingleton (M :=
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : Opens X))).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf))).symm.trans
    (isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived X).symm

/-! ### The `ℤ`-indexed derived functor -/

section Plus

attribute [local instance] HasDerivedCategory.standard

/-- **The comparison against the `ℤ`-indexed derived functor.** [Stacks, Tag 02KH] and the
higher direct images of the `Stacks.AlgebraicGeometry.TopDegreeBaseChange` namespace are stated
for `CategoryTheory.Functor.rightDerivedPlus`, so this is the form in which they meet
`AlgebraicGeometry.DefinesRationalSingularity`. -/
theorem isZeroFirstStructureSheafCohomology_iff_isZero_firstCohomologyStructureSheaf
    (X : Scheme.{u}) :
    IsZeroFirstStructureSheafCohomology X ↔
      IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstCohomologyStructureSheaf X) :=
  (isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived X).trans
    ((Stacks.DerivedIndexing.rightDerivedIso
        (Stacks.Cohomology.AffineBase.moduleGlobalSections X) 1).app
        (SheafOfModules.unit X.ringCatSheaf)).isZero_iff

end Plus

/-! ### Rational singularities in the module-valued model -/

/-- **A domain defines a rational singularity exactly when the first cohomology module over the
base vanishes for every normal modification.** This is
`AlgebraicGeometry.definesRationalSingularity_iff` with the vanishing read in the model the
boundedness results of [Stacks, Tag 0B4N] compute in, so it is the form in which a vanishing
proved about `AlgebraicGeometry.firstCohomologyAsBaseModule` discharges — and a rational
singularity supplies — the hypothesis of
`AlgebraicGeometry.DefinesRationalSingularity`. -/
theorem definesRationalSingularity_iff_subsingleton_firstCohomologyAsBaseModule (A : Type u)
    [CommRing A] [IsDomain A] :
    DefinesRationalSingularity A ↔
      ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
        Subsingleton (firstCohomologyAsBaseModule X f) :=
  ⟨fun h X _ f hf => (subsingleton_firstCohomologyAsBaseModule_iff X f).2 (h X f hf),
   fun h X _ f hf => (subsingleton_firstCohomologyAsBaseModule_iff X f).1 (h X f hf)⟩

end AlgebraicGeometry

end

end
