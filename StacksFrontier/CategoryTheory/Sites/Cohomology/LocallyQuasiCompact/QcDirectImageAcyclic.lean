module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcCohomologicalDescent

/-!
# The higher direct images of `a_X^{-1}F` along the comparison of `LC_qc/X` with `X`

Let `X` be an object of `LC_qc` and let `a_X : Sh(LC_qc/X) → Sh(X)` be the comparison morphism of
Section 09WY. For every abelian sheaf `F` on `X` and every `q > 0` the higher direct image
`R^q a_{X,*} a_X^{-1} F` vanishes, the vanishing of the source's proof of Stacks 0D91, stated for
Mathlib's `ℕ`-indexed right derived functors. The direct image `a_{X,*}` is additive and left
exact.

## Main results

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `qcTopologicalAbelianDirectImage_additive`: `a_{X,*}` is additive.
* `qcTopologicalAbelianDirectImage_preservesFiniteLimits`: `a_{X,*}` is left exact.
* `isZero_rightDerived_qcTopologicalAbelianDirectImage`: `R^q a_{X,*} a_X^{-1} F = 0` for `q > 0`.

## References

* [Stacks Project, Tag 0D91](https://stacks.math.columbia.edu/tag/0D91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

attribute [local instance] enoughInjectives_sheafOpens_site enoughInjectives_qcSliceSheaf

/-- The direct image `a_{X,*}` on abelian sheaves of `LC_qc/X` is additive. -/
theorem qcTopologicalAbelianDirectImage_additive :
    (qcTopologicalAbelianDirectImage.{u, w, v} S X).Additive :=
  inferInstance

/-- The direct image `a_{X,*}` on abelian sheaves of `LC_qc/X` is left exact. -/
theorem qcTopologicalAbelianDirectImage_preservesFiniteLimits :
    PreservesFiniteLimits (qcTopologicalAbelianDirectImage.{u, w, v} S X) :=
  inferInstance

/-- **The vanishing `R^q a_{X,*} a_X^{-1} F = 0` for `q > 0`** of the source's proof of
Stacks 0D91, stated for Mathlib's `ℕ`-indexed right derived functors. -/
theorem isZero_rightDerived_qcTopologicalAbelianDirectImage
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (hq : 0 < q) :
    IsZero (((qcTopologicalAbelianDirectImage.{u, w, v} S X).rightDerived q).obj
      ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F)) := by
  let := HasDerivedCategory.standard
    (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v})
  let := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})
  exact (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat
    (qcTopologicalAbelianDirectImage.{u, w, v} S X) _).1
    (rightAcyclic_qcTopologicalAbelianDirectImage.{u, w, v} S X F) q hq

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
