module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSectionsOfTheRingedSite
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DualOfAPerfectComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedDualTensorIsoSheafHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms out of a perfect complex from the dual tensor product, on a scheme

Let `X` be a scheme, let `K` be a perfect object of `D(𝒪_X)` and let `RΓ` be a total right
derived functor of global sections. If the degree-zero cohomology of `RΓ(X, K^∨ ⊗^𝐋_{𝒪_X} M)`
vanishes then there is no nonzero morphism `K ⟶ M` in `D(𝒪_X)`.

This is the direction of the identification
`H⁰(X, K^∨ ⊗^𝐋_{𝒪_X} M) = Hom_{D(𝒪_X)}(K, M)` of step (5) of the proof of
[Stacks, Tag 08JJ] that [Stacks, Tag 09M4] consumes, read at the scheme-level spellings of the
derived tensor product and of derived global sections.

## Main results

* `Stacks.DerivedQCoh.subsingleton_hom_of_isZero_homology_derivedTensorDual`.

## Implementation notes

Two readings have to be crossed, and each crossing is a comparison proved in the library.

The identification itself is
`AlgebraicGeometry.RingedSite.subsingleton_hom_of_isZero_homology_derivedTensorDual` on the
ringed site of opens of `X`, which gets it from part (1) of [Stacks, Tag 0ATN]; perfectness
crosses from the ringed-space predicate of [Stacks, Tag 08CM] that [Stacks, Tag 09M4] is stated
at to the ringed-site predicate of [Stacks, Tag 08G5] by
`Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite`.

Derived global sections cross by
`AlgebraicGeometry.isZero_homology_derivedModuleGlobalSections_iff`: the `RΓ` here lands in
`DerivedCategory (ModuleCat Γ(X, ⊤))` whereas the ringed-site statement is phrased at
`Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections`, which lands in
`DerivedCategory AddCommGrpCat`, and a hypercohomology group of one vanishes exactly when the
corresponding group of the other does.

The derived tensor product needs no comparison: `Stacks.Cohomology.TorAmplitude.derTensor` of
the ringed space underlying `X` is the structure-sheaf-indexed canonical derived tensor product
of [Stacks, Tag 06YU] of the sheaf `X.sheaf`, which is the structure sheaf of the ringed site of
opens of `X`, so the two objects are the same.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology (sectionsFunctor)
open Stacks.Cohomology.TorAmplitude (derTensor)

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.DerivedQCoh

variable (X : Scheme.{u})
  (RΓ : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
  (α : (sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]

include α in
/-- Vanishing of `H⁰(X, K^∨ ⊗^𝐋 M)` forces `Hom_{D(𝒪_X)}(K, M)` to vanish, for `K` perfect. -/
theorem subsingleton_hom_of_isZero_homology_derivedTensorDual
    (K M : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) 0).obj
      (RΓ.obj (((derTensor X.toRingedSpace).tensor.obj
        (Stacks.SheafOfModules.derivedDual X.sheaf K)).obj M)))) :
    Subsingleton (K ⟶ M) :=
  RingedSite.subsingleton_hom_of_isZero_homology_derivedTensorDual
    (Stacks.SheafOfModules.ringedSite X.sheaf) K M
    ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite X.toRingedSpace K).1 hK)
    ((isZero_homology_derivedModuleGlobalSections_iff X RΓ α _ 0).mpr h)

end Stacks.DerivedQCoh

end
