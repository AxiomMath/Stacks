module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationSubgroupoid
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersionSupplement

/-!
# The affineness hypotheses of the formal-space tree are the conclusions of Stacks 07VT and 07VS

`AlgebraicGeometry.FormalSpace.Is07VT` is the shape in which the formal-space tree states
**Stacks 07VT** — an algebraic space over `S` receiving a surjective universally closed
morphism from an affine scheme of the site is an affine scheme. It is the special case of
Stacks 07VT in which the source is representable by an affine scheme of the site. The
library's Stacks 07VT is
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`,
proved outright; this file works with its conditional form
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`.

This file proves that specialisation, so that the hypothesis is not an assumption beyond the
three its conditional form carries, and proves the converse: the restriction of the
source to a representable one is no restriction at all, so `Is07VT` and Stacks 07VT
are equivalent.

It does the first of those for `AlgebraicGeometry.FormalSpace.Is07VS` as well. That is the
same shape asking only a *finite* morphism — the conclusion of **Stacks 07VS** — and it, not
`Is07VT`, is what the consumers in the formal-space tree carry, the single place the grant is
eliminated applying it to a closed immersion. It is strictly weaker, by
`AlgebraicGeometry.FormalSpace.is07VS_of_is07VT`, and unlike `Is07VT` it is proved with no
hypothesis, as `AlgebraicGeometry.FormalSpace.is07VS` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.Is07VSUnconditional`, from the library's Stacks 07VS,
`AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`.

## Main results

* `AlgebraicGeometry.FormalSpace.is07VT_of_grants`: `Is07VT` holds granted the three
  hypotheses of `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`,
  passed on unchanged.
* `AlgebraicGeometry.FormalSpace.is07VS_of_grants`: the same for
  `AlgebraicGeometry.FormalSpace.Is07VS`, the weaker proposition the consumers in the
  formal-space tree actually take, granted the three hypotheses of the library's **Stacks 07VS**,
  `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_isFinite`. Those three are weaker:
  they ask the conclusion of Stacks 07VR about finite morphisms where the 07VT triple asks the
  conclusion of Stacks 09YA about integral ones, the other two being the same propositions.
  Together with `AlgebraicGeometry.FormalSpace.is07VS_of_is07VT` this is why the tree's grant
  was weakened — the one place it is eliminated applies it to a closed immersion, which is
  finite outright.
* `AlgebraicGeometry.FormalSpace.isAffineSpace_of_is07VT`: conversely, `Is07VT` implies the
  statement of Stacks 07VT for an arbitrary affine algebraic-space source, with no hypothesis
  of its own.
* `AlgebraicGeometry.FormalSpace.isAffineSpace_of_is07VS`: the same converse for `Is07VS` — it
  implies the statement of Stacks 07VS for an arbitrary affine algebraic-space source, with no
  hypothesis of its own. With `is07VS_of_grants` this makes `Is07VS` *equivalent* to the
  statement of Stacks 07VS, so the grant the consumers carry is the whole tag.

## Implementation notes

Nothing is granted here beyond what the library's Stacks 07VT grants: `h09YA`, `h07SQ` and
`hFinitePresentation` are written in the shape that declaration states them in and are passed
to it verbatim. The two facts about the representable source that the specialisation has to
supply are proved rather than assumed: a presheaf represented by an object of the site is an
algebraic space by Stacks 025Z
(`AlgebraicGeometry.isAlgebraicSpace_yoneda`), and one represented by an object with affine
underlying scheme is an affine algebraic space
(`AlgebraicGeometry.Space.isAffineSpace_yoneda`).

*The specialisation is not a weakening.* `AlgebraicGeometry.Space.IsAffineSpace` is by
definition the existence of an isomorphism with a presheaf represented by an object of the site
with affine underlying scheme, so an arbitrary affine source is a representable one up to
isomorphism; precomposing with that isomorphism preserves surjectivity on points, an
isomorphism being surjective on points by
`AlgebraicGeometry.Space.pointsMap_surjective_of_isIso`, and preserves universal closedness by
`AlgebraicGeometry.Space.universallyClosed_comp`, an isomorphism being universally closed. That
is `AlgebraicGeometry.FormalSpace.isAffineSpace_of_is07VT`, and together with
`AlgebraicGeometry.FormalSpace.is07VT_of_grants` it says that the two propositions are
equivalent. So no route to `Is07VT` is cheaper than a proof of Stacks 07VT in full: inhabiting
the hypothesis the formal-space tree carries means proving the tag, not a special case of it.
Stacks 07VT is now proved outright, as
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`,
by a route that avoids the three grants of its conditional form, none of which this library
inhabits — `h09YA` needs the anti-equivalence of Stacks 081V,
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`, which is a structure with no inhabitant,
together with the colimit presentation of Stacks 086Z; `h07SQ` needs the sections identification
of Stacks 07SI, `AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit`, which is stated and
nowhere established, and the separated-stage weakening
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isAffineSpace`
is not a substitute, its conclusion being separatedness of a stage rather than affineness;
and `hFinitePresentation` runs through Serre's criterion for affineness of an algebraic space,
Stacks 07VP, of which this library has only the scheme-level form
`Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal`.

### The same holds of `Is07VS`, and it is proved

`AlgebraicGeometry.FormalSpace.isAffineSpace_of_is07VS` runs that argument for the weaker
proposition the consumers actually carry: finiteness is stable under precomposition with an
isomorphism by `AlgebraicGeometry.Space.isFinite_comp` and
`AlgebraicGeometry.Space.isFinite_of_isIso`, so the representable-source restriction in
`Is07VS` is vacuous too, and `Is07VS` is *equivalent* to the statement of Stacks 07VS. That
statement is proved with no hypothesis as
`AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`, so `Is07VS` is
inhabited, by `AlgebraicGeometry.FormalSpace.is07VS`; the three hypotheses of
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_isFinite` and of `is07VS_of_grants`
are not needed for it. Of those three, `h07VR` is itself a theorem of this library,
`AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite` (Stacks 07VR).

No `@[stacks 07VT]` registration is added, on any declaration here, and no `@[stacks 07VS]`
registration either; the latter sits on
`AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`, of which `is07VS`
and `is07VS_of_grants` are only the representable-source special case. The 07VT tag sits on
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`,
which states the proposition for an arbitrary affine algebraic-space source; `is07VT_of_grants`
below is a special case of its conditional form for a representable source, and registering
the tag on a special case as well would claim coverage for a statement that does not state the
tag. `isAffineSpace_of_is07VT` does state the tag, but it assumes it: `Is07VT` is the
universally quantified form of its own conclusion, which is why it is a hypothesis of the
consumers in the formal-space tree and not a hypothesis of anything carrying the tag.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
* [Stacks Project, Tag 09YA](https://stacks.math.columbia.edu/tag/09YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `AlgebraicGeometry.FormalSpace.Is07VT`, the form of **Stacks 07VT** used in the
formal-space tree, holds granted the three hypotheses of the library's Stacks 07VT,
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`.

The source of the morphism is represented by an object of the site with affine underlying
scheme, hence is an algebraic space by Stacks 025Z and an affine algebraic space; the library's
Stacks 07VT applies to it directly. -/
theorem is07VT_of_grants
    (h09YA : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' →
      Space.IsIntegralHom B S hS g →
      Space.IsQuasiCompactSpace B S hS Y' →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      Space.IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : Space.DescentSituation B S hS B.contains_terminal I),
      Space.IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ Space.IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → Space.IsFinite B S hS g →
      Space.IsFinitePresentation B S hS g → Space.IsSurjective B S hS g →
      Space.IsAffineSpace B S hS X' → Space.IsAffineSpace B S hS Y') :
    Is07VT B S hS := by
  intro F T c hF hTaff hsurj hclosed
  exact Space.isAffineSpace_of_isSurjective_of_universallyClosed B S hS c
    (isAlgebraicSpace_yoneda B S hS T) hF hsurj hclosed
    (Space.isAffineSpace_yoneda B S hS T hTaff) h09YA h07SQ hFinitePresentation

/-- `AlgebraicGeometry.FormalSpace.Is07VS`, the weaker form of Stacks 07VT that the
formal-space tree actually consumes, holds granted the three hypotheses of the library's
**Stacks 07VS**, `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_isFinite`.

This is the point of weakening the grant. The three hypotheses here — the conclusion of
Stacks 07VR that a *finite* morphism over a quasi-compact quasi-separated algebraic space is a
directed limit of finite morphisms of finite presentation, the conclusion of Stacks 07SQ, and
the finite-presentation special case — are weaker than the three that
`AlgebraicGeometry.FormalSpace.is07VT_of_grants` asks, which differ by taking the conclusion of
Stacks 09YA about *integral* morphisms in place of Stacks 07VR about finite ones; `h07SQ` and
`hFinitePresentation` are literally the same propositions in both. So the formal-space tree's
debt is discharged by strictly less than before, and
`AlgebraicGeometry.FormalSpace.is07VS_of_is07VT` shows the old route still works.

As with `is07VT_of_grants`, nothing is granted here beyond what the library's Stacks 07VS grants:
the three hypotheses are passed to it verbatim, and the two facts about the representable source
are proved — it is an algebraic space by Stacks 025Z and an affine algebraic space because its
underlying scheme is affine. -/
theorem is07VS_of_grants
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' →
      Space.IsFinite B S hS g →
      Space.IsQuasiCompactSpace B S hS Y' →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      Space.IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : Space.DescentSituation B S hS B.contains_terminal I),
      Space.IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ Space.IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → Space.IsFinite B S hS g →
      Space.IsFinitePresentation B S hS g → Space.IsSurjective B S hS g →
      Space.IsAffineSpace B S hS X' → Space.IsAffineSpace B S hS Y') :
    Is07VS B S hS := by
  intro F T c hF hTaff hsurj hfin
  exact Space.isAffineSpace_of_isSurjective_of_isFinite B S hS c
    (isAlgebraicSpace_yoneda B S hS T) hF hsurj hfin
    (Space.isAffineSpace_yoneda B S hS T hTaff) h07VR h07SQ hFinitePresentation

/-- Precomposing a surjective-on-points morphism with the inverse of an isomorphism keeps it
surjective on points. -/
private theorem isSurjective_inv_comp {F X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : X ≅ F) (f : X ⟶ Y) (hsurj : Space.IsSurjective B S hS f) :
    Space.IsSurjective B S hS (e.inv ≫ f) := fun z ↦ by
  obtain ⟨x, hx⟩ := hsurj z
  obtain ⟨t, ht⟩ := Space.pointsMap_surjective_of_isIso B S hS e.inv x
  refine ⟨t, ?_⟩
  have hcomp := congrFun (Space.pointsMap_comp B S hS (F := F) e.inv f) t
  simp only [Function.comp_apply] at hcomp
  rw [hcomp, ht, hx]

/-- **The restriction of Stacks 07VT to a representable source is no restriction**: granted
`AlgebraicGeometry.FormalSpace.Is07VT`, a surjective universally closed morphism of algebraic
spaces over `S` with affine source has affine target, which is the statement of Stacks 07VT,
proved outright as
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`.

An affine algebraic space is isomorphic to the presheaf represented by an object of the site
with affine underlying scheme, so precomposing with that isomorphism turns the given morphism
into one out of such a presheaf; the precomposite is again surjective on points, an isomorphism
being surjective on points by `AlgebraicGeometry.Space.pointsMap_surjective_of_isIso`, and
again universally closed by
`AlgebraicGeometry.Space.universallyClosed_comp`, an isomorphism being universally closed.

With `AlgebraicGeometry.FormalSpace.is07VT_of_grants` this makes `Is07VT` equivalent to the
statement of Stacks 07VT, so the hypothesis the formal-space tree carries is the whole tag and
not a special case of it. Algebraicity of the source is not assumed: it follows from affineness
by `AlgebraicGeometry.Space.IsAffineSpace.isAlgebraicSpace`. -/
theorem isAffineSpace_of_is07VT (h07VT : Is07VT B S hS)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) (hsurj : Space.IsSurjective B S hS f)
    (hclosed : Space.UniversallyClosed B S hS f)
    (haff : Space.IsAffineSpace B S hS X) :
    Space.IsAffineSpace B S hS Y := by
  have hX : IsAlgebraicSpace B S hS X := haff.isAlgebraicSpace
  obtain ⟨T, hTaff, ⟨e⟩⟩ := haff
  refine h07VT (e.inv ≫ f) hY hTaff (fun z ↦ ?_) ?_
  · exact isSurjective_inv_comp B S hS e f hsurj z
  · exact Space.universallyClosed_comp B S hS hX hY e.inv f
      (Space.universallyClosed_of_isIso B S hS e.inv) hclosed

/-- **The restriction of Stacks 07VS to a representable source is no restriction either**:
granted `AlgebraicGeometry.FormalSpace.Is07VS`, a surjective *finite* morphism of algebraic
spaces over `S` with affine source has affine target, which is the statement of Stacks 07VS,
proved outright as `AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`.

The argument is that of `AlgebraicGeometry.FormalSpace.isAffineSpace_of_is07VT`, with
finiteness in place of universal closedness: an affine algebraic space is isomorphic to the
presheaf represented by an object of the site with affine underlying scheme, and precomposing
with that isomorphism preserves surjectivity on points by
`AlgebraicGeometry.Space.pointsMap_surjective_of_isIso` and finiteness by
`AlgebraicGeometry.Space.isFinite_comp`, an isomorphism being finite by
`AlgebraicGeometry.Space.isFinite_of_isIso`. Unlike the universally closed case this needs no
algebraicity of the source, finiteness being stable under composition outright.

With `AlgebraicGeometry.FormalSpace.is07VS` and
`AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective` it says that `Is07VS`
and the statement of Stacks 07VS are *equivalent*, and both hold. -/
theorem isAffineSpace_of_is07VS (h07VS : Is07VS B S hS)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) (hsurj : Space.IsSurjective B S hS f)
    (hfin : Space.IsFinite B S hS f)
    (haff : Space.IsAffineSpace B S hS X) :
    Space.IsAffineSpace B S hS Y := by
  obtain ⟨T, hTaff, ⟨e⟩⟩ := haff
  refine h07VS (e.inv ≫ f) hY hTaff (fun z ↦ ?_) ?_
  · exact isSurjective_inv_comp B S hS e f hsurj z
  · exact Space.isFinite_comp B S hS (Space.isFinite_of_isIso B S hS e.inv) hfin

end AlgebraicGeometry.FormalSpace

end
