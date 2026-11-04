module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceClassicalGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.AffineCompactObject
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QcohDirectSumsAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparisonModel
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullbackSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSumsLocallySmall

/-!
# The structure sheaf is a compact object of `D_QCoh(𝒪_X)` on a qcqs scheme

Let `X` be a quasi-compact quasi-separated scheme. Then `𝒪_X` placed in degree zero is a compact
object of `D_QCoh(𝒪_X)`: a morphism from it into a direct sum indexed by a type of the scheme
universe factors through a finite subsum in exactly one way. Equivalently, degree-zero
hypercohomology `H⁰(X, -)` commutes with direct sums on `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.Duality.derivedPullbackUnitIsoScheme`: `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` for a morphism of
  schemes, at the locally small model of the derived categories.
* `quasiCoherentDerivedPullbackDerivedStructureSheafIsoOfIsQuasicoherent`, in the namespace
  `Stacks.Duality.DerivedPushforward`: the same isomorphism inside `D_QCoh`.
* `Stacks.Duality.DerivedPushforward.isCompactObject_derivedStructureSheaf_spec`: `𝒪_{Spec R}[0]`
  is a compact object of `D_QCoh(𝒪_{Spec R})`.
* `Stacks.Duality.DerivedPushforward.isCompactObject_derivedStructureSheaf`: `𝒪_X[0]` is a
  compact object of `D_QCoh(𝒪_X)` for `X` quasi-compact and quasi-separated.

## Implementation notes

The derived categories are taken at the locally small model,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`: it is the model at which `D_QCoh(𝒪_X)` has
the `Type u`-indexed direct sums that compactness is tested against, the morphisms of the standard
model lying in `Type (u + 1)`.

## References

* [The Stacks Project, Proposition 36.17.1 (09M1)](https://stacks.math.columbia.edu/tag/09M1)
* [The Stacks Project, Lemma 36.4.5 (08DZ)](https://stacks.math.columbia.edu/tag/08DZ)
* [The Stacks Project, Lemma 36.3.8 (08DW)](https://stacks.math.columbia.edu/tag/08DW)
* [The Stacks Project, Lemma 36.3.2 (079W)](https://stacks.math.columbia.edu/tag/079W)
* [The Stacks Project, Lemma 20.49.5 (08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

/-! ### The derived pullback of the structure sheaf -/

/-- **`Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` for a morphism of schemes**, at the locally small model of the
derived categories. -/
def derivedPullbackUnitIsoScheme {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIsoAtModel f.toLRSHom.toShHom

namespace DerivedPushforward

/-- **`Lf^*` carries the structure sheaf of `D_QCoh(𝒪_Y)` to that of `D_QCoh(𝒪_X)`**: the
isomorphism `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` in `D_QCoh(𝒪_X)`, for `Lf^*` preserving quasi-coherence of
cohomology. -/
def quasiCoherentDerivedPullbackDerivedStructureSheafIsoOfIsQuasicoherent {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (hpull : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPullback f).obj K.obj)).IsQuasicoherent) :
    (quasiCoherentDerivedPullback f hpull).obj (derivedStructureSheaf Y) ≅
      derivedStructureSheaf X :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((quasiCoherentDerivedPullbackCompιIso f hpull).app (derivedStructureSheaf Y) ≪≫
      derivedPullbackUnitIsoScheme f)

/-! ### The affine case -/

/-- **`𝒪_{Spec R}[0]` as the derived sheafification of `R[0]`**: the isomorphism between the
image of the regular module `R` in degree zero under derived sheafification and the structure
sheaf of `Spec R` in degree zero. -/
def derivedTildeSingleSelfIsoStructureSheaf (R : CommRingCat.{u}) :
    (derivedTilde R).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R)) ≅ derivedStructureSheaf (Spec R) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((AlgebraicGeometry.derivedTildeCompι R).app _ ≪≫
      ((tilde.functor R).mapDerivedCategorySingleFunctor 0).app _)

/-- **`𝒪_{Spec R}[0]` is a compact object of `D_QCoh(𝒪_{Spec R})`.** -/
theorem isCompactObject_derivedStructureSheaf_spec (R : CommRingCat.{u}) :
    IsCompactObject.{u} (derivedStructureSheaf (Spec R)) :=
  isCompactObject_of_iso (derivedTildeSingleSelfIsoStructureSheaf R).symm
    (AlgebraicGeometry.isCompactObject_derivedTildeUnit R)

/-! ### The quasi-compact quasi-separated case -/

/-- **`𝒪_X[0]` is a compact object of `D_QCoh(𝒪_X)` for `X` quasi-compact and quasi-separated**:
a morphism from the structure sheaf in degree zero into a direct sum indexed by a type of the
scheme universe factors through a finite subsum in exactly one way. Equivalently, degree-zero
hypercohomology `H⁰(X, -)` commutes with direct sums on `D_QCoh(𝒪_X)`. -/
theorem isCompactObject_derivedStructureSheaf (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsCompactObject.{u} (derivedStructureSheaf X) := by
  let R : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)
  let g : X ⟶ Spec R := AlgebraicGeometry.specULiftZIsTerminal.from X
  have hpull := isQuasicoherent_homology_derivedPullback' g
  have hpush := isQuasicoherent_homology_derivedPushforward_locallySmall g
  have adj := Stacks.Duality.quasiCoherentDerivedAdjunction g hpull hpush
  have hadd' : (Stacks.Duality.quasiCoherentDerivedPullback g hpull).Additive :=
    adj.left_adjoint_additive
  have hG : ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (Stacks.Duality.quasiCoherentDerivedPushforward g hpush) :=
    LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward g hpush
  exact isCompactObject_of_iso
    (quasiCoherentDerivedPullbackDerivedStructureSheafIsoOfIsQuasicoherent g hpull).symm
    (CategoryTheory.isCompactObject_obj_of_adjunction adj hG
      (isCompactObject_derivedStructureSheaf_spec R))

end DerivedPushforward

end Stacks.Duality

end
