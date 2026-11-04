module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedPullbackProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffineCharts

/-!
# Stacks 0GBD: base change of the conditions of Stacks 0ANG

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a local property of morphisms
of `WAdm^count` which is stable under base change, and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally countably indexed formal algebraic spaces over `S`. **Stacks 0GBD** says
that if `f` satisfies the equivalent conditions of Stacks 0ANG, then so does the second
projection `pr₂ : X ×_Y Z ⟶ Z`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasProperty_pullback_snd_of_isLocallyCountablyIndexed`:
  **Stacks 0GBD**.
* `AlgebraicGeometry.FormalSpace.hasProperty_pullback_snd_of_isLocallyCountablyIndexed_of_etale`:
  the same statement for any proof `hEt` of the étale case of Stacks 0AJH; the registered
  statement instantiates it at `representableEtaleOverAffineIsFormal`.

## Implementation notes

The chart argument of the source, which gives conditions (2) and (3) for `pr₂` together with
Stacks 0GBB clause (1) for `X ×_Y Z`, is
`isLocallyCountablyIndexed_pullback_and_hasPropertyAfterCovers_of_etale`. Condition (1) is then
the implication (3) ⟹ (1) of Stacks 0ANG,
`hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal`.

Situation 0CBA, which defines a local property, opens with "Let `P` be a property of morphisms
of `WAdm^count`, invariant under isomorphism of source and target in this category".
`TopologicalRing.PropertyIsLocal`, and so `TopologicalRing.IsStableUnderBaseChange`, records
the three axioms that follow that sentence and not the invariance, so the invariance is stated
as the two hypotheses `hsrc` and `htgt`: they are the source's hypothesis that `P` be local.

## References

* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GBC](https://stacks.math.columbia.edu/tag/0GBC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GBD, for a given proof of the étale case of Stacks 0AJH.** Let `P` be a local
property of morphisms of `WAdm^count` (Situation 0CBA, which asks `P` to be invariant under
isomorphism of source and target) stable under base change (Stacks 0GBC), and let `f : X ⟶ Y`,
`g : Z ⟶ Y` be morphisms of locally countably indexed formal algebraic spaces over `S`. If `f`
satisfies the conditions of Stacks 0ANG, then so does `pr₂ : X ×_Y Z ⟶ Z`: `X ×_Y Z` is locally
countably indexed and `pr₂` satisfies all three conditions of Stacks 0ANG.

Conditions (2) and (3) are
`isLocallyCountablyIndexed_pullback_and_hasPropertyAfterCovers_of_etale`; condition (1) follows
from condition (3) in its form with charts of the class by the implication (3) ⟹ (1) of Stacks
0ANG, whose covering refinement is `hasEtaleRefinementOfSourceCover_of_etale`. The one input is
`hEt`, the étale case of Stacks 0AJH, which `representableEtaleOverAffineIsFormal` proves. -/
theorem hasProperty_pullback_snd_of_isLocallyCountablyIndexed_of_etale
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.IsStableUnderBaseChange.{u} P)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f) :
    IsLocallyCountablyIndexed B S hS (pullback f g) ∧
      HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) := by
  obtain ⟨hpb, h2, h3⟩ := isLocallyCountablyIndexed_pullback_and_hasPropertyAfterCovers_of_etale
    B S hS hEt P hP htgt f g hX hY hZ hf
  refine ⟨hpb, hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal B S hS _ P
    classIsWeaklyAdmissible_isCountablyWeaklyAdmissible
    classHasCountableNhdsZero_isCountablyWeaklyAdmissible
    classIsStableUnderEtaleCompletion_isCountablyWeaklyAdmissible
    classIsStableUnderFinitePi_isCountablyWeaklyAdmissible hsrc htgt hP.isLocal _
    (hasEtaleRefinementOfSourceCover_of_etale B S hS hEt _) h3, h2, ?_⟩
  obtain ⟨I, U, u, hU, hfac⟩ := h3
  exact ⟨I, U, u, hU, fun i ↦ by
    obtain ⟨V, v, t, hV, hv, hsq, -, -, ht⟩ := hfac i
    exact ⟨V, v, t, hV, hv, hsq, ht⟩⟩

/-- **Stacks 0GBD.** Let `S` be a scheme. Let `P` be a local property of morphisms of
`WAdm^count` which is stable under base change. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of
locally countably indexed formal algebraic spaces over `S`. If `f` satisfies the equivalent
conditions of Stacks 0ANG, then so does `pr₂ : X ×_Y Z ⟶ Z`.

`P` being local in the sense of Situation 0CBA is `TopologicalRing.PropertyIsLocal P`, which
`TopologicalRing.IsStableUnderBaseChange P` (Stacks 0GBC) contains, together with the
invariance under isomorphism of source and target with which Situation 0CBA opens, `hsrc` and
`htgt`. The conditions of Stacks 0ANG for `f` are equivalent by
`hasProperty_tfae_of_isLocallyCountablyIndexed`, and `hf` is condition (1). The conclusion is
that `X ×_Y Z` is locally countably indexed (Stacks 0GBB, clause (1)), so that the conditions
of Stacks 0ANG are equivalent for `pr₂`, and that `pr₂` satisfies all three of them. -/
@[stacks 0GBD]
theorem hasProperty_pullback_snd_of_isLocallyCountablyIndexed
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.IsStableUnderBaseChange.{u} P)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f) :
    IsLocallyCountablyIndexed B S hS (pullback f g) ∧
      HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) :=
  hasProperty_pullback_snd_of_isLocallyCountablyIndexed_of_etale B S hS
    (representableEtaleOverAffineIsFormal B S hS) P hP hsrc htgt f g hX hY hZ hf

end AlgebraicGeometry.FormalSpace

end
