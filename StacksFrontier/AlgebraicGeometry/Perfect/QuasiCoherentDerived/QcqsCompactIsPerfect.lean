module

public import StacksFrontier.AlgebraicGeometry.Perfect.ClassicalGeneratorOfPerfectComplexes
public import StacksFrontier.AlgebraicGeometry.Perfect.QcqsPerfectGenerator
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import StacksFrontier.CategoryTheory.Triangulated.CompactGenerationAdjunction
public import StacksFrontier.Homology.Perfect.ModelIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# A compact object of `D_QCoh(𝒪_X)` is perfect, for `X` quasi-compact and quasi-separated

Let `X` be a quasi-compact quasi-separated scheme. An object `K` of `D_QCoh(𝒪_X)` which is
compact, with direct sums tested over index types in the universe of `X`, is perfect as an object
of `D(𝒪_X)`: this is `Stacks.Duality.QcqsPerfect.isPerfect_of_isCompactObject_of_qcqs` of
`StacksFrontier/AlgebraicGeometry/Perfect/QcqsPerfectGenerator.lean`. Together with
`Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect` it is [Stacks, Tag 09M1] in both
directions, at the locally small derived category
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which this file records as one statement.
It also supplies the two restriction facts the argument below runs on.

## The proof

The source's: perfectness is local, so it suffices that `K` restrict to a perfect object on each
affine open `V`. Write `j : Spec Γ(X, V) ⟶ X` for the open immersion onto `V`. Its direct image
`Rj_* : D_QCoh(𝒪_{Spec Γ(X, V)}) ⥤ D_QCoh(𝒪_X)` commutes with direct sums ([Stacks, Tag 08DZ]),
so its left adjoint `j^*` preserves compactness, and `j^*K` is compact on an affine scheme, hence
perfect by the affine case `AlgebraicGeometry.isCompactObject_iff_isPerfect_spec_of_model`. The
isomorphism `V ≅ Spec Γ(X, V)` carries this back to `K|_V`.

## Main results

* `Stacks.Duality.QcqsPerfect.isCompactObject_restrictedDerivedRestrict_of_isCompactObject`:
  restriction along an affine open immersion preserves compactness.
* `Stacks.Duality.QcqsPerfect.derivedRestrictCompIso`: restriction along a composite of open
  immersions.
* `Stacks.Duality.QcqsPerfect.isCompactObject_iff_isPerfect`: **[Stacks, Tag 09M1]**, both
  directions, on a quasi-compact quasi-separated scheme.

## References

* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Duality.OpenImmersion

universe u

namespace Stacks.Duality.QcqsPerfect

/-- **The restriction of a compact object along an affine open immersion is compact.** For
`j : Spec A ⟶ X` an open immersion into a quasi-separated scheme, `j^*` is left adjoint to `Rj_*`,
which commutes with direct sums by [Stacks, Tag 08DZ]. -/
theorem isCompactObject_restrictedDerivedRestrict_of_isCompactObject {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {A : CommRingCat.{u}} (j : Spec A ⟶ X)
    [IsOpenImmersion j] (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hK : IsCompactObject.{u} K) : IsCompactObject.{u} ((restrictedDerivedRestrict j).obj K) := by
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward j
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward j
  have : (Stacks.Duality.quasiCoherentDerivedPushforward j
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)).Additive :=
    (restrictedDerivedRestrictAdjunction j).right_adjoint_additive
  exact isCompactObject_map_of_adjunction (restrictedDerivedRestrictAdjunction j) hK

/-- Restricting along `a : W ⟶ V` after restricting along `b : V ⟶ X` is restricting along
`a ≫ b`, on unbounded derived categories. -/
def derivedRestrictCompIso {W V X : Scheme.{u}} (a : W ⟶ V) (b : V ⟶ X) [IsOpenImmersion a]
    [IsOpenImmersion b] :
    derivedRestrict b ⋙ derivedRestrict a ≅ derivedRestrict (a ≫ b) :=
  (Stacks.DerivedQCoh.mapDerivedCategoryComp (Scheme.Modules.restrictFunctor b)
      (Scheme.Modules.restrictFunctor a)).symm ≪≫
    Stacks.DerivedQCoh.mapDerivedCategoryCongr _ _ (Scheme.Modules.restrictFunctorComp a b).symm

/-- **[Stacks, Tag 09M1].** On a quasi-compact quasi-separated scheme `X`, an object of
`D_QCoh(𝒪_X)` is compact if and only if it is perfect, at the locally small derived category. -/
@[stacks 09M1 "both directions, on a quasi-compact quasi-separated scheme, at the locally small \
AlgebraicGeometry.Scheme.Modules.hasDerivedCategory"]
theorem isCompactObject_iff_isPerfect (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) :
    IsCompactObject.{u} K ↔
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj :=
  ⟨isPerfect_of_isCompactObject_of_qcqs X K, isCompactObject_of_isPerfect X K⟩

end Stacks.Duality.QcqsPerfect

end
