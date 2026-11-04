module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange
public import StacksFrontier.RingTheory.Rig.RigSmoothLocalityRefined

/-!
# The base change of a rig-smooth morphism by an adic morphism

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCR** says that if
`f` is rig-smooth (Definition 0GCP) and `g` is adic (Definition 0AQ3), then the second
projection `X ×_Y Z ⟶ Z` is rig-smooth.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSmooth_pullback_snd`: **Stacks 0GCR**.

## Implementation notes

The proof is the one of the source. Rig-smoothness and adicness are local properties of arrows
of `WAdm^{Noeth}` (Stacks 0GCK, `Rig.rigSmooth_isLocalNoetherian`, and the adic half of
`TopologicalRing.rigSmooth_isStableUnderBaseChangeByAdic`), invariant under isomorphism of
source and target (`Rig.rigSmooth_isomorphismInvariant`), and rig-smoothness is stable under
base change by adic maps (Stacks 0GCL). Remark 0GBG
(`AlgebraicGeometry.FormalSpace.conditions_pullback_snd_of_isStableUnderBaseChangeBy`) then
carries condition (1) of Stacks 0ANG from `f` and from `g` to the second projection, and that
condition is rig-smoothness by Stacks 0GCQ.

Adicness of `g` is the source's Definition 0AQ3, representability by algebraic spaces. The
chart condition that Remark 0GBG asks of `g` is drawn from it as in the discussion of Section
0AQ2: a chart map of an adic morphism is the formal spectrum map of a taut continuous
homomorphism, and a taut homomorphism out of a ring with a finitely generated ideal of
definition — as a Noetherian adic ring has — is adic (Stacks 0GBS).

## References

* [Stacks Project, Tag 0GCR](https://stacks.math.columbia.edu/tag/0GCR)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0GCL](https://stacks.math.columbia.edu/tag/0GCL)
* [Stacks Project, Tag 0AQ2](https://stacks.math.columbia.edu/tag/0AQ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GCR.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally Noetherian formal
algebraic spaces over `S`. If `f` is rig-smooth and `g` is adic, then the base change
`X ×_Y Z ⟶ Z` is rig-smooth. -/
@[stacks 0GCR]
theorem isRigSmooth_pullback_snd {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z) (hf : IsRigSmooth B S hS f)
    (hg : IsAdicMorphism B S hS g) :
    IsRigSmooth B S hS (pullback.snd f g) :=
  (isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (pullback.snd f g)).mpr
    (conditions_pullback_snd_of_isStableUnderBaseChangeBy B S hS _ _
      (TopologicalRing.rigSmooth_isStableUnderBaseChangeByAdic Rig.rigSmooth_isLocalNoetherian)
      Rig.rigSmooth_isomorphismInvariant f g hX hY hZ
      ((isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf)
      (isAdicOnEveryAffineEtaleDiagramNoetherian_of_isAdicMorphism B S hS g hg)).1

end AlgebraicGeometry.FormalSpace

end
