module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionPointProjectionFormula
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.ProjectionMapComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionCoefficientsDirectSums

/-!
# The projection formula to a separably closed point under finite cohomological dimension

Let `k` be a separably closed field, `π : X ⟶ Spec k` a quasi-compact and quasi-separated
morphism with `cd(π) < ∞`, and `n ≥ 1`. For `E ∈ D(X_étale, ℤ/nℤ)` and
`K ∈ D(Spec(k)_étale, ℤ/nℤ) = D(ℤ/nℤ)`, unbounded, the canonical map of Cohomology on Sites,
Section 21.50 ([Stacks, Tag 0943]),

`Rπ_*E ⊗^L K ⟶ Rπ_*(E ⊗^L π^{-1}K)`,

is an isomorphism. Through `D(Spec(k)_étale, ℤ/nℤ) = D(ℤ/nℤ)` this is the computation
`RΓ(X, E ⊗^L K̲) = RΓ(X, E) ⊗^L K` of [Stacks, Tag 0F12] for the scheme `X`.

## Main results

* `Stacks.EtaleCohomology.isIso_projectionFormulaMap_zmod_of_etaleCohomologicalDimension_lt_top`:
  on the constant ringed topoi.
* On `D(X_étale, ℤ/nℤ)`:
  `isIso_etalePushforwardProjectionMap_zmod_of_etaleCohomologicalDimension_lt_top`.

## References

* [Stacks Project, Tag 0F12](https://stacks.math.columbia.edu/tag/0F12)
* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.ProjectionFormulaOfToposHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable (n : ℕ) (hn : 0 < n) {X : Scheme.{u}} (k : Type u) [Field k] [IsSepClosed k]
  (π : X ⟶ Spec (.of k)) [QuasiCompact π] [QuasiSeparated π]

include hn in
/-- **The projection formula to a separably closed point for `ℤ/nℤ` coefficients, when `π` has
finite cohomological dimension**, on the constant ringed topoi: for every `E ∈ D(X_étale, ℤ/nℤ)`
and every `K ∈ D(Spec(k)_étale, ℤ/nℤ)`, unbounded, `Rπ_*E ⊗^L K ⟶ Rπ_*(E ⊗^L π^{-1}K)` is an
isomorphism. -/
theorem isIso_projectionFormulaMap_zmod_of_etaleCohomologicalDimension_lt_top
    (hcd : π.etaleCohomologicalDimension < ⊤)
    (E : DerivedCategory (EtaleRingedModules.{u, 0} (ZMod n) X))
    (K : DerivedCategory (EtaleRingedModules.{u, 0} (ZMod n) (Spec (.of k)))) :
    IsIso (projectionFormulaMap (etaleRingedToposHom.{u, 0} (ZMod n) π) E K) :=
  isIso_projectionFormulaMap_of_preservesCoproducts_of_isSepClosed (ZMod n) k π (fun I ↦ by
    have := preservesColimitsOfShape_derivedDirectImage_zmod π hcd n hn
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod n) π)
      (Stacks.Injectives.KInjectiveResolution.homotopyCategoryUnit
        (etaleModuleDirectImage.{u, 0} (ZMod n) π)
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod n) π)
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} (ZMod n) π)) I
    exact preservesColimitsOfShape_etaleRingedDerivedPushforward_of_etaleModule (ZMod n) π _) E K

include hn in
/-- **The projection formula to a separably closed point for `ℤ/nℤ` coefficients, when `π` has
finite cohomological dimension**, on `D(X_étale, ℤ/nℤ)`: for every `E ∈ D(X_étale, ℤ/nℤ)` and
every `K ∈ D(Spec(k)_étale, ℤ/nℤ)`, unbounded, the projection map
`Rπ_*E ⊗^L K ⟶ Rπ_*(E ⊗^L π^{-1}K)` is an isomorphism. -/
theorem isIso_etalePushforwardProjectionMap_zmod_of_etaleCohomologicalDimension_lt_top
    (hcd : π.etaleCohomologicalDimension < ⊤)
    (E : DerivedCategory (EtaleModules.{u, 0} (ZMod n) X))
    (K : DerivedCategory (EtaleModules.{u, 0} (ZMod n) (Spec (.of k)))) :
    IsIso (etalePushforwardProjectionMap.{u, 0} (ZMod n) π E K) :=
  (isIso_etalePushforwardProjectionMap_iff (ZMod n) π E K).2
    (isIso_projectionFormulaMap_zmod_of_etaleCohomologicalDimension_lt_top n hn k π hcd _ _)

end Stacks.EtaleCohomology

end
