module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineSiteQuasiCoherentObjects
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsTriangulatedSubcategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackQuasiCoherentBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentCohomologyUnderFlatRestrictions

/-!
# Further results on `AffineSiteQuasiCoherentObjects`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineSiteQuasiCoherentObjects` that need imports
beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


section BaseChange

open Stacks.ModulesOnACategory.QuasiCoherentCohomology
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

/-- The section rings of the structure sheaf of the small affine site commute: they are rings of
global functions on a scheme, which the structure sheaf delivers as objects of `CommRingCat`. -/
theorem mul_comm_smallAffineChaoticRingedSite_ringSheaf
    (U : ((smallAffineChaoticRingedSite B S hS).Cᵒᵖ))
    (x y : (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineChaoticRingedSite B S hS).O).obj.obj U) :
    x * y = y * x := by
  let _ : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineChaoticRingedSite B S hS).O).obj.obj U) :=
    ((smallAffineChaoticRingedSite B S hS).O.obj.obj U).commRing
  exact mul_comm x y

/-- A base-change datum on the small affine site `S_affine` of an arbitrary scheme: the derived
extension-of-scalars functors along the restriction homomorphisms of the structure sheaf, with
their adjunctions to derived restriction of scalars.

This is the universe-free counterpart of `smallAffineChaoticBaseChangeData`, which is pinned to
`Scheme.{0}` and to the module universe `0`: it exhibits a
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData` for a scheme in any universe
and for any module universe `w`. The only hypothesis of the construction
`Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.baseChangeDataOfComm` is
commutativity of the section rings, which `mul_comm_smallAffineChaoticRingedSite_ringSheaf`
supplies. -/
def smallAffineChaoticBaseChangeDataUniv :
    BaseChangeData.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineChaoticRingedSite B S hS).O).obj :=
  baseChangeDataOfComm
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineChaoticRingedSite B S hS).O).obj
    (mul_comm_smallAffineChaoticRingedSite_ringSheaf B S hS)

/-- `QC(S_affine, 𝒪)` is a triangulated subcategory of `D(S_affine, 𝒪)`, by Stacks 0GYW, for an
arbitrary scheme and module universe. -/
theorem smallAffineChaotic_isQCProperty_isTriangulated_univ :
    ObjectProperty.IsTriangulated
      (isQCProperty.{w} (smallAffineChaoticBaseChangeDataUniv.{w} B S hS)) :=
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isTriangulated _

/-- **Stacks 0GZZ, triangulatedness of (4) and (5).** For an arbitrary scheme `S`,
`D_QCoh(S_affine, 𝒪)` is a triangulated subcategory of `D(S_affine, 𝒪)`: it is the same
subcategory as `QC(S_affine, 𝒪)`, which is triangulated by Stacks 0GYW.

Together with `smallAffineChaoticDerivedQuasiCoherentEquivQC` and
`smallAffineChaoticDerivedQuasiCoherentEquivQC_functor_comp_ι` this makes the comparison of (4)
and (5) an exact equivalence of triangulated categories, both sides being triangulated
subcategories of `D(S_affine, 𝒪)` and the comparison commuting with the two inclusions. -/
@[stacks 0GZZ "(4) and (5) are triangulated"]
theorem smallAffineChaotic_qcohCohomologyProperty_isTriangulated_univ :
    ObjectProperty.IsTriangulated
      (qcohCohomologyProperty.{w} (smallAffineChaoticRingedSite B S hS)) := by
  rw [← smallAffineChaotic_isQC_eq_hasQuasicoherentCohomology.{w} B S hS
    (smallAffineChaoticBaseChangeDataUniv.{w} B S hS)]
  exact smallAffineChaotic_isQCProperty_isTriangulated_univ B S hS

end BaseChange

end AlgebraicGeometry

end
