module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormula
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceAbelianLowerShriekTransition

/-!
# The simplicial transition of Stacks 09WG is the relocalization `r_φ^{-1}`

Let `(C, J)` be a small site and `K` a simplicial object of `SR(C)`. Two functors
`Ab(C/K_m) ⥤ Ab(C/K_n)` are attached to a simplex map `φ : m ⟶ n`.

`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAb` is the summand of the direct-sum
formula of Stacks 09WG: for a situation of case (B) it is restriction of presheaves along the
*cocontinuous* transition functor, followed by sheafification.
`CategoryTheory.SimplicialSemiRepresentable.transitionAbelianLowerShriek` is the extension by zero
`r_{φ!}` along the relocalization functor `r_φ : C/K_n ⥤ C/K_m`, whose right adjoint `r_φ^{-1}` is
restriction along that *continuous* functor, with no sheafification.

For the simplicial semi-representable situation the two underlying site functors are the same
functor `componentOverMap (K φ)`, which is both continuous and cocontinuous, and then the
sheafification is unnecessary: this module records that comparison, which is Stacks 00XR (1) at
this functor.

This relates the simplex-coefficient resolution of Stacks 09WG/0D78 to the localizations `j_p`
of the simplicial degrees, as needed to compare the resolution of Stacks 0D78 with the Čech
resolution of Stacks 01GE.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.situationTransitionInverseImageAbIso`: **the
  summand of Stacks 09WG is the restriction `r_φ^{-1}` along the relocalization functor.**

## Implementation notes

Continuity of the transition functor is the registered instance
`CategoryTheory.SimplicialSemiRepresentable.componentTransitionFunctor_isContinuous`, and the
sheafification of abelian sheaves on a component is found by instance search at the spelling
`(situation J K).componentTopology n`. Cocontinuity is *not*: it is registered for
`componentOverMap (K.map φ.op)` at the `topologyOfCoverings` spelling by
`CategoryTheory.SimplicialSemiRepresentable.isCocontinuous_sliceCoverings`, and instance search
does not unfold `situation` to reach it. It is therefore supplied as a `haveI` whose statement is
written at the `componentTransitionFunctor` spelling, so that the two spellings are identified
during term elaboration rather than by instance search.

## References

* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- The transition functor of a simplex map is cocontinuous for the component topologies, at the
spelling of `componentTransitionFunctor`. This is the cocontinuity field of the simplicial site of
Stacks 0D85, which instance search does not reach at this spelling. -/
theorem componentTransitionFunctor_isCocontinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentTransitionFunctor J K φ).IsCocontinuous
      ((situation J K).componentTopology n) ((situation J K).componentTopology m) :=
  isCocontinuous_sliceCoverings J K φ.op

/-- The summand of the direct-sum formula of Stacks 09WG is restriction along the relocalization
functor, at the spelling of `componentTransitionFunctor`: the simplicial-site situation of a
simplicial semi-representable object is of case (B), where the summand is the sheafified
restriction along the cocontinuous transition functor. -/
theorem transitionInverseImageAb_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    SimplicialSiteSituation.transitionInverseImageAb (situation J K) φ =
      (componentTransitionFunctor J K φ).sheafPullbackCocontinuous Ab.{u}
        ((situation J K).componentTopology n) ((situation J K).componentTopology m) :=
  rfl

/-- **The summand of Stacks 09WG is the restriction `r_φ^{-1}` along the relocalization functor.**
For a simplex map `φ : m ⟶ n`, the summand
`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAb` of the direct-sum formula of
Stacks 09WG — the sheafified restriction along the cocontinuous transition functor — is the
inverse image `r_φ^{-1}` right adjoint to the extension by zero
`CategoryTheory.SimplicialSemiRepresentable.transitionAbelianLowerShriek`, that is plain
restriction along the same functor read as a continuous one.

The transition functor is both continuous (Stacks 0D85) and cocontinuous, so the sheafification in
the first description is unnecessary; this is Stacks 00XR (1) at that functor. -/
def situationTransitionInverseImageAbIso {m n : SimplexCategory} (φ : m ⟶ n) :
    SimplicialSiteSituation.transitionInverseImageAb (situation J K) φ ≅
      (componentTransitionFunctor J K φ).sheafPushforwardContinuous Ab.{u}
        ((situation J K).componentTopology n) ((situation J K).componentTopology m) :=
  haveI := componentTransitionFunctor_isCocontinuous J K φ
  (componentTransitionFunctor J K φ).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    Ab.{u} ((situation J K).componentTopology n) ((situation J K).componentTopology m)

end CategoryTheory.SimplicialSemiRepresentable

end
