module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections
import StacksCore.Tactic.StacksAttribute

/-!
# Global sections under a morphism submersive after every étale base change

Let `f : X ⟶ S` have geometrically connected fibres, and suppose that for every étale morphism
`g : V ⟶ S` the base change `V ×_S X ⟶ V` of `f` is submersive. Then pulling back a sheaf of
sets on the small étale site of `S` to the small étale site of `X` does not change its global
sections: `Γ(S, F) = Γ(X, f⁻¹F)`.

This is Stacks Tag 0EZK under the exact corrected hypothesis of the Stacks erratum: the source
asks only that `f` be submersive, which is not enough (see the
characteristic-`2` counterexample in the docstring of
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso`). The universally submersive
case is `Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage`; the statements
here assume only what the descent step of the proof consumes. The injectivity and surjectivity
lemmas of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections` are private there
and are read here through `import all`.

## Main results

* `Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage_of_etaleBaseChange` — the
  canonical comparison `Γ(S, F) ⟶ Γ(X, f⁻¹F)` is an isomorphism, naturally in `F`.
* `Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIsoOfEtaleBaseChange` — the same
  statement packaged as an isomorphism of global-sections functors.

## References

* [Stacks Project, Tag 0EZK](https://stacks.math.columbia.edu/tag/0EZK)
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MorphismProperty
open AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- **Stacks Project, Tag 0EZK.** Let `f : X ⟶ S` have geometrically connected fibres and be
submersive after every étale base change: for every étale `g : V ⟶ S` the projection
`V ×_S X ⟶ V` is a quotient map. Then the canonical comparison `Γ(S, F) ⟶ Γ(X, f⁻¹F)` is an
isomorphism, naturally in the sheaf `F` on the small étale site of `S`. -/
@[stacks 0EZK "corrected: Stacks erratum: f submersive after every \
etale base change, the exact corrected hypothesis; the source's plain submersivity of f is not \
enough, see the counterexample in the docstring of globalSectionsSmallEtaleInverseImageIso. \
The universally submersive special case is isIso_globalSectionsSmallEtaleInverseImage"]
public theorem isIso_globalSectionsSmallEtaleInverseImage_of_etaleBaseChange
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsub : ∀ ⦃V : Scheme.{u}⦄ (g : V ⟶ S) [Etale g],
      Topology.IsQuotientMap (pullback.fst g f))
    [GeometricallyConnected f] :
    IsIso (globalSectionsSmallEtaleInverseImage.{u, v} f) := by
  have hsub' : IsQuotientMapEtaleBaseChange f := fun V ↦ by
    have : Etale V.hom := V.prop
    exact hsub V.hom
  have hbij (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
      Function.Bijective ((globalSectionsSmallEtaleInverseImage f).app F) :=
    ⟨globalSectionsComparison_injective f f.surjective F,
      globalSectionsComparison_surjective f hsub' F⟩
  let (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
      IsIso ((globalSectionsSmallEtaleInverseImage f).app F) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij F)
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks Project, Tag 0EZK.** Pullback along a morphism with geometrically connected fibres
that is submersive after every étale base change preserves global sections of every sheaf of
sets on the small étale site, naturally in the sheaf; the isomorphism is the canonical
comparison `Γ(S, F) ⟶ Γ(X, f⁻¹F)`. -/
@[stacks 0EZK "corrected: Stacks erratum: f submersive after every \
etale base change, the exact corrected hypothesis; the source's plain submersivity of f is not \
enough, see the counterexample in the docstring of globalSectionsSmallEtaleInverseImageIso. \
The universally submersive special case is globalSectionsSmallEtaleInverseImageIso"]
public noncomputable def globalSectionsSmallEtaleInverseImageIsoOfEtaleBaseChange
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsub : ∀ ⦃V : Scheme.{u}⦄ (g : V ⟶ S) [Etale g],
      Topology.IsQuotientMap (pullback.fst g f))
    [GeometricallyConnected f] :
    Sheaf.Γ (smallEtaleTopology S) (Type (max (u + 1) v)) ≅
      smallEtaleInverseImage f ⋙
        Sheaf.Γ (smallEtaleTopology X) (Type (max (u + 1) v)) :=
  let := isIso_globalSectionsSmallEtaleInverseImage_of_etaleBaseChange.{u, v} f hsub
  asIso (globalSectionsSmallEtaleInverseImage f)

end Stacks.EtaleCohomology
