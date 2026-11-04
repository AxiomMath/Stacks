module

public import StacksFrontier.AlgebraicGeometry.Modules.ExactStalkSurjective
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing

/-!
# A quotient supported on a divisor makes the stalk maps surjective off it

If the last term of a complex of `𝒪_X`-modules exact at its middle term is the direct image of
a module on the closed subscheme of an ideal sheaf, then the stalk map of its first arrow is
surjective at every point outside the support of that ideal sheaf.

## Main results

* `AlgebraicGeometry.Scheme.Modules.surjective_stalkHom_of_notMem_supportSet`: **the stalk map
  is surjective off the support of the divisor.**

## Implementation notes

The stalk of a direct image along a closed immersion vanishes off the image of that immersion
([Stacks, Tag 00AE]), which is
`AlgebraicGeometry.subsingleton_stalk_pushforward_of_notMemRange'`; the image of the immersion
of the closed subscheme of an ideal sheaf is its support, by
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`.  The isomorphism with the direct
image is transported to the stalks by functoriality of `stalkHom`, so no hypothesis on the
second arrow of the complex is needed: exactness at the middle term is enough.

## References

* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **The stalk map of `S.f` is surjective off the support of `D`**, when `S` is exact at its
middle term and its last term is the direct image of a module on the closed subscheme of `D`. -/
theorem surjective_stalkHom_of_notMem_supportSet {S : ShortComplex X.Modules} (hS : S.Exact)
    {D : X.IdealSheafData} {G : D.subscheme.Modules}
    (hquot : S.X₃ ≅ (Scheme.Modules.pushforward D.subschemeι).obj G)
    {x : X} (hx : x ∉ D.supportSet) :
    Function.Surjective (stalkHom S.f x) := by
  have hx' : x ∉ Set.range (ConcreteCategory.hom D.subschemeι.base) := by
    rw [show Set.range (ConcreteCategory.hom D.subschemeι.base) = (D.support : Set X) from
      Scheme.IdealSheafData.range_subschemeι D]
    exact hx
  have hsub := subsingleton_stalk_pushforward_of_notMemRange' D.subschemeι G x hx'
  have hid : (stalkHom hquot.inv x).comp (stalkHom hquot.hom x) = LinearMap.id :=
    (stalkHom_comp hquot.hom hquot.inv x).symm.trans
      ((congrArg (fun f : S.X₃ ⟶ S.X₃ => stalkHom f x) hquot.hom_inv_id).trans
        (stalkHom_id S.X₃ x))
  refine Stacks.SheafOfModules.surjective_stalkHom_of_forall_modStalk_eq_zero hS fun a => ?_
  refine (DFunLike.congr_fun hid a).symm.trans ?_
  change stalkHom hquot.inv x (stalkHom hquot.hom x a) = 0
  rw [show stalkHom hquot.hom x a = 0 from @Subsingleton.elim _ hsub _ _, map_zero]

end AlgebraicGeometry.Scheme.Modules

end
