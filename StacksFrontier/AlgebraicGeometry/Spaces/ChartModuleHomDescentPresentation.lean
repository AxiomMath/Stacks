module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleHomDescent

/-!
# Descent of morphisms of modules from the atlas of an étale presentation

A morphism of the restrictions of two `𝒪_X`-modules to a *surjective* étale chart `W` of an
algebraic space `X` descends, uniquely, as soon as its two relocalizations to a chart exhibited as
the kernel pair `W ×_X W` agree (`AlgebraicGeometry.Space.existsUnique_hom_of_isPullback`). An
étale presentation of `X` supplies all three hypotheses at once: its atlas is surjective
(`AlgebraicGeometry.Space.Presentation.surjective`) and étale (`…etale`), and its relation *is* the
kernel pair of the atlas (`…isPullback`). This file states the resulting descent of morphisms from
the atlas of an étale presentation, the setting `R = U ×_X U` of Stacks 03M3.

## Main results

* `AlgebraicGeometry.Space.existsUnique_hom_of_presentation`: a morphism of the restrictions of two
  `𝒪_X`-modules to the atlas of an étale presentation, whose slice reading has equal
  relocalizations along the two legs of the presentation's relation, is the restriction of a unique
  morphism of `𝒪_X`-modules.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Descent of morphisms of `𝒪_X`-modules from the atlas of an étale presentation.**  A
morphism `a` of the restrictions of two `𝒪_X`-modules to the atlas of an étale presentation,
whose slice reading has equal relocalizations along the two legs of the presentation's relation,
is the restriction of a unique morphism `M ⟶ N`. -/
theorem existsUnique_hom_of_presentation (P : Presentation B S hS X.1 X.2)
    (M N : Modules.{u, u} B S hS X.1 X.2)
    (a : (chartModuleRestriction B S hS X (presentationChart P)).obj M ⟶
      (chartModuleRestriction B S hS X (presentationChart P)).obj N)
    (hpq : homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) M.val N.val
            (presentationRelationTargetHom P)
            (chartSliceHom B S hS X (presentationChart P) M N a) =
        homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) M.val N.val
            (presentationRelationSourceHom P)
            (chartSliceHom B S hS X (presentationChart P) M N a)) :
    ∃! ψ : M ⟶ N, (chartModuleRestriction B S hS X (presentationChart P)).map ψ = a :=
  existsUnique_hom_of_isPullback B S hS X (presentationChart P)
    (isSurjective_of_presheafSurjective B S hS P.toSpace P.surjective)
    (presentationRelationTargetHom P) (presentationRelationSourceHom P) P.isPullback M N a hpq

end AlgebraicGeometry.Space

end
