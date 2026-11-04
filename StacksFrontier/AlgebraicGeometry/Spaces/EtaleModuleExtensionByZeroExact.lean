module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekForgetStalk
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of extension by zero of modules along an étale morphism of algebraic spaces

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`.  Extension by zero
of sheaves of modules `f_! : Mod(𝒪_X) ⥤ Mod(𝒪_Y)`, the functor
`AlgebraicGeometry.Space.etaleModuleLowerShriek`, is exact.

## Main results

* `AlgebraicGeometry.Space.preservesFiniteLimits_etaleModuleLowerShriek`: extension by zero of
  sheaves of modules along an étale morphism of algebraic spaces is left exact.
* `AlgebraicGeometry.Space.etaleModuleLowerShriek_exact`: it is exact.

## References

* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- Forgetting the module structure on the small étale site of an algebraic space reflects
finite limits. -/
theorem reflectsFiniteLimits_toSheaf_etaleRingSheaf (Z : AlgebraicSpaces B S hS) :
    ReflectsFiniteLimits (SheafOfModules.toSheaf (etaleRingSheaf B S hS Z)) :=
  inferInstance

/-- Extension by zero of sheaves of modules along an étale morphism of algebraic spaces is left
exact. -/
@[stacks 03DJ "left exactness for modules along an étale morphism of algebraic spaces",
  sga "4 IV 11.3.1" "partial"]
instance preservesFiniteLimits_etaleModuleLowerShriek :
    PreservesFiniteLimits (etaleModuleLowerShriek B S hS f hf) :=
  have habelian : PreservesFiniteLimits
      (SheafOfModules.toSheaf (etaleRingSheaf B S hS X) ⋙
        abelianEtaleExtensionByZero B S hS f hf) :=
    comp_preservesFiniteLimits (SheafOfModules.toSheaf (etaleRingSheaf B S hS X))
      (abelianEtaleExtensionByZero B S hS f hf)
  have hforget : PreservesFiniteLimits (etaleModuleLowerShriek B S hS f hf ⋙
      SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (etaleModuleShriekForgetIso B S hS f hf) habelian
  @preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _
    (etaleModuleLowerShriek B S hS f hf)
    (SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)) hforget
    (reflectsFiniteLimits_toSheaf_etaleRingSheaf B S hS Y)

/-- Extension by zero of sheaves of modules along an étale morphism of algebraic spaces is
exact. -/
@[stacks 03DJ "exactness for modules along an étale morphism of algebraic spaces"]
theorem etaleModuleLowerShriek_exact :
    exactFunctor _ _ (etaleModuleLowerShriek B S hS f hf) := by
  rw [exactFunctor_iff]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Space

end
