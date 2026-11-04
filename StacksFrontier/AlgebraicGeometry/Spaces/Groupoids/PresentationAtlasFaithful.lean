module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentMonoidal

/-!
# Morphisms of quasi-coherent modules are determined on the atlas of a presentation

Let `X = U/R` be a presentation of an algebraic space with atlas `U ⟶ X`.  Inverse image along
the atlas is part of the equivalence of Stacks 03M3 between quasi-coherent `𝒪_X`-modules and
quasi-coherent modules on the presentation groupoid with descent data
(`AlgebraicGeometry.Space.presentationQuasicoherentEquivalence`), so it is faithful on
quasi-coherent modules: two morphisms between quasi-coherent `𝒪_X`-modules whose inverse images
along the atlas agree are equal.  This applies to morphisms out of iterated tensor products of
quasi-coherent modules and out of `𝒪_X ⊗ G`, which are quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorObj` and
`SheafOfModules.isQuasicoherentOnSite_unit`; this is how laws of a multiplication descended along
a presentation are checked on the atlas.

## Main results

* `AlgebraicGeometry.Space.presentationAtlas_map_injective`: **inverse image along the atlas of a
  presentation is injective on morphisms of quasi-coherent modules.**

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)

/-- **Inverse image along the atlas of a presentation is injective on morphisms of quasi-coherent
modules**: two morphisms `G ⟶ H` of quasi-coherent `𝒪_X`-modules whose inverse images along the
atlas agree are equal. -/
theorem presentationAtlas_map_injective {G H : Modules.{u, u} B S hS X.obj X.property}
    [G.IsQuasicoherentOnSite] [H.IsQuasicoherentOnSite] {φ ψ : G ⟶ H}
    (h : (modulePullback B S hS (presentationAtlas P)).map φ =
      (modulePullback B S hS (presentationAtlas P)).map ψ) :
    φ = ψ := by
  have e : (presentationQuasicoherentEquivalence P).functor.map
      (ObjectProperty.homMk φ : (⟨G, inferInstance⟩ : QuasicoherentSheaves.{u, u} B S hS X.obj
        X.property) ⟶ ⟨H, inferInstance⟩) =
      (presentationQuasicoherentEquivalence P).functor.map (ObjectProperty.homMk ψ) := by
    refine QuasicoherentModule.Hom.ext ?_
    refine (presentationQuasicoherentEquivalence_functor_map_hom P _).trans ?_
    refine Eq.trans ?_ (presentationQuasicoherentEquivalence_functor_map_hom P _).symm
    exact h
  exact congrArg (fun k => k.hom) ((presentationQuasicoherentEquivalence P).functor.map_injective e)

end AlgebraicGeometry.Space

end
