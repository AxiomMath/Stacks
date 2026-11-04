module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZeroStalkMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekForgetStalk

/-!
# The stalk of an extension by zero of a map of modules

Combining Tag 0798 with Equation 08GU: for an étale morphism `f : X ⟶ Y` of algebraic spaces and
a map `α` of sheaves of `𝒪_X`-modules, the stalk at a geometric point `x̄` of `Y` of the abelian
sheaf underlying `f_!α` is invertible as soon as, for every lift `t` of `x̄` to `X`, the stalk at
`t` of the abelian sheaf underlying `α` is.

## Main results

* `AlgebraicGeometry.Space.isIso_sheafFiber_toSheaf_etaleModuleShriek_map_of_lifts`.

## References

* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
  (x : GeometricPoint B S hS Y.1)

/-- **The stalk of the extension by zero of a map of modules is invertible as soon as the stalks
of that map at all the lifts of the point are.** -/
@[stacks 08GU "the stalk of an extension by zero of a map of modules"]
theorem isIso_sheafFiber_toSheaf_etaleModuleShriek_map_of_lifts
    {M N : Modules.{u, u} B S hS X.1 X.2} (α : M ⟶ N)
    (hα : ∀ t : GeometricPointLift B S hS f.hom x,
      IsIso ((liftSitePoint B S hS f t).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α))) :
    IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
        ((etaleModuleLowerShriek B S hS f hf).map α))) :=
  isIso_sheafFiber_toSheaf_etaleModuleShriek_map B S hS f hf x α
    (EtaleShriekStalk.isIso_sheafFiber_extensionByZero_map B S hS f hf x
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α) hα)

end AlgebraicGeometry.Space

end
