module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeSectionsBijection

/-!
# The comparison of the two readings of the functions on `W` intertwines multiplication

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.sectionsIsoPushforwardUnitSections` compares the
two readings of the ring of an affine open `W` of `Y''` as a module over the functions on an
affine open `V` of `Y'`: through `h.appLE V W` on the one hand, and as the global sections of
`(h ∣_ V^W)_* 𝒪_W` on the other. Besides the `Γ(V, ⊤)`-action, the comparison is compatible
with multiplication by an element of `Γ(Y'', W)`, as in conclusion (c) of [Stacks, Tag 0EX3].

## Main results

* `…TopDegreeBaseChange.mulLeftRestrictScalars_comp_sectionsIsoPushforwardUnitSections`:
  **the comparison intertwines multiplication by `a` with multiplication by the function `a`
  becomes on `W`.** Neither base carries a hypothesis and neither open need be affine.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {Y'' : Scheme.{u}} (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (h : Y'' ⟶ S.Y') {V : S.Y'.Opens} {W : Y''.Opens} (hWV : W ≤ h ⁻¹ᵁ V)

/-- **The comparison of the two readings of the ring of `W` intertwines multiplication.**
Multiplication by `a : Γ(Y'', W)`, read as an endomorphism of `Γ(Y'', W)` over the functions on
`V`, is carried by `…TopDegreeBaseChange.sectionsIsoPushforwardUnitSections` to multiplication by
the function `a` becomes on `W`. -/
theorem mulLeftRestrictScalars_comp_sectionsIsoPushforwardUnitSections (a : Γ(Y'', W)) :
    mulLeftRestrictScalars ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom) a ≫
        (sectionsIsoPushforwardUnitSections S h hWV).hom =
      (sectionsIsoPushforwardUnitSections S h hWV).hom ≫
        mulLeftRestrictScalars (h.resLE V W hWV).appTop.hom
          ((Scheme.Opens.topIso W).symm.commRingCatIsoToRingEquiv a) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have hx : ∀ y, (((Scheme.Opens.topIso W).symm.commRingCatIsoToRingEquiv y) :
      Γ((W : Scheme), ⊤)) =
      (ModuleCat.Hom.hom (sectionsIsoPushforwardUnitSections S h hWV).hom) y := by
    intro y
    rw [sectionsIsoPushforwardUnitSections,
      ModuleCat.ExtendScalars.restrictScalarsSelfIso_hom_apply]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    mulLeftRestrictScalars, mulLeftRestrictScalars,
    ModuleCat.restrictScalars.map_apply, ModuleCat.restrictScalars.map_apply]
  exact Eq.trans (hx _).symm
    (Eq.trans (map_mul ((Scheme.Opens.topIso W).symm.commRingCatIsoToRingEquiv) a x)
      (congrArg (fun z : Γ((W : Scheme), ⊤) =>
        (LinearMap.mulLeft Γ((W : Scheme), ⊤)
          ((Scheme.Opens.topIso W).symm.commRingCatIsoToRingEquiv a)) z) (hx x)))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
