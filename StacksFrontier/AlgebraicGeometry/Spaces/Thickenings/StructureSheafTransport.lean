module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleToposSupplement
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# The structure sheaf of a thickening, read on the small étale site of the subspace

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`. Base change of étale scheme
charts exhibits the small étale site of `X` as a dense subsite of the small étale site of `G`,
so restriction along it is an equivalence on sheaves. Stacks 05ZM is that equivalence, and
`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` carries it for sheaves of *sets*.

This file carries the same equivalence for sheaves of **commutative rings**, and uses it to read
the structure sheaf `𝒪_X` of the ambient space as a sheaf of rings on the small étale site of the
subspace. That sheaf is the object Stacks 05ZT asserts an isomorphism of: the lemma realizes a
square-zero extension of `𝒪_G` by a first order thickening `G ⊂ X` together with an isomorphism
`𝒪_X ≅ 𝒜`, and `𝒜` lives on the small étale site of `G`, so `𝒪_X` has to be read there too.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleCommRingSheafEquiv_of_isThickening` — **Stacks 05ZM for
  sheaves of commutative rings.**
* `AlgebraicGeometry.Space.smallEtaleThickeningStructureSheaf` — `𝒪_X` read on the small étale
  site of the subspace `G`.  The structure sheaf of the ambient space read on the *spaces*-étale
  site of the subspace, at `CommRingCat.{u + 1}`, is a different sheaf on a different site:
  `AlgebraicGeometry.Space.thickeningStructureSheaf` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRingedTopos`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleCommRingSheafEquiv_inverse_eq` — the inverse of the
  equivalence is restriction along base change of étale charts.
* `AlgebraicGeometry.Space.thickeningStructureSheafRestrictionIso` — the characterising property
  of the transported sheaf: restricting it back along base change recovers `𝒪_X`.
* `CategoryTheory.StructuredArrow.essentiallySmall` (Mathlib) — the essential smallness that
  makes the ring-valued instantiation available at all, found by instance search from
  `AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`.  The limits instance it supplies is
  bound where it is used; stated for an arbitrary target category with `u`-small limits it is
  `AlgebraicGeometry.Space.hasLimitsOfShape_structuredArrow_thickeningChartBaseChange` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRingedTopos`.

## Implementation notes

*Why the library's Stacks 05ZM cannot be used.*
`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` is stated at `Type (u + 1)`, and
that choice is load-bearing in the following sense:
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` asks for
`[∀ Y, HasLimitsOfShape (StructuredArrow Y G.op) A]`, the shapes of the right Kan extension
computing the inverse, and the small étale site of an algebraic space has objects in
`Type (u + 1)`, so those shapes are not `u`-small on the nose. `Type (u + 1)` has limits of that
size and `CommRingCat.{u}` does not.

What makes the ring-valued version go through anyway is that the shapes are nonetheless
*essentially* `u`-small. The small étale site is `EssentiallySmall.{u}` —
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall` — which is exactly the content of the
size cutoff defining the big fppf site, and a structured-arrow category over an essentially small
category with locally small target is essentially small,
`CategoryTheory.StructuredArrow.essentiallySmall`. So
`CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` supplies the instance from the
`u`-small limits of `CommRingCat.{u}`, and the same argument would serve any category with
`u`-small limits.

*What is transported and what is not.* Only the sheaf of rings is transported here. The sections
lemma below is the whole computational content: the equivalence is restriction along
`AlgebraicGeometry.Space.thickeningChartBaseChange`, so a section of the transported sheaf over
an étale chart `V` of `G` is a section of `𝒪_X` over a chart of `X` whose base change is `V` —
and the comparison with the *module*-level transport, which Stacks 05ZT also needs for the
kernel, is not here.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- **Stacks 05ZM for sheaves of commutative rings.** For a thickening `G ⊂ X` of algebraic
spaces over `S`, the sheaves of commutative rings on the small étale site of `X` and on the small
étale site of `G` are equivalent, by restriction along base change of étale scheme charts.

This is the comparison lemma for the dense subsite inclusion
`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`, instantiated at
`CommRingCat.{u}` rather than at sheaves of sets; see the implementation notes for why that
instantiation needs the essential smallness of the site. -/
@[stacks 05ZM "equivalence of the small étale sheaves of commutative rings"]
noncomputable def smallEtaleCommRingSheafEquiv_of_isThickening (hG : IsThickening B S hS X G) :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} ≌
      Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) CommRingCat.{u} :=
  letI := isContinuous_smallBaseChange B S hS (IsThickening.inclusion B S hS hG)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep
  letI := thickeningChartBaseChange_isDenseSubsite B S hS hG
  letI : ∀ Y : (SmallEtale B S hS (IsThickening.space B S hS hG).1)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow Y (thickeningChartBaseChange B S hS hG).op)
        CommRingCat.{u} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall _ _
  Functor.IsDenseSubsite.sheafEquiv (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)
    (thickeningChartBaseChange B S hS hG) CommRingCat.{u}

/-- **`𝒪_X` read on the small étale site of a thickening `G ⊂ X`.** The structure sheaf of the
ambient space, transported along the equivalence of Stacks 05ZM for sheaves of commutative rings.

This is the sheaf that Stacks 05ZT asserts is isomorphic to a prescribed square-zero extension
of `𝒪_G`. -/
noncomputable def smallEtaleThickeningStructureSheaf (hG : IsThickening B S hS X G) :
    Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) CommRingCat.{u} :=
  (smallEtaleCommRingSheafEquiv_of_isThickening B S hS hG).functor.obj
    (smallEtaleRingedTopos B S hS X).O

/-- **The inverse of the transport is restriction along base change of étale charts.** A sheaf on
the small étale site of the subspace is read on the small étale site of the ambient space by
precomposing with base change, and that is the inverse of the equivalence by the definition of
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`. The transport itself is therefore the
right Kan extension in the other direction, which is why it needs the limits instance above. -/
theorem smallEtaleCommRingSheafEquiv_inverse_eq (hG : IsThickening B S hS X G) :
    letI := isContinuous_smallBaseChange B S hS (IsThickening.inclusion B S hS hG)
      (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep
    (smallEtaleCommRingSheafEquiv_of_isThickening B S hS hG).inverse =
      (thickeningChartBaseChange B S hS hG).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) :=
  rfl

/--
**The characterising property of `AlgebraicGeometry.Space.smallEtaleThickeningStructureSheaf`.**
Reading it back on the small étale site of the ambient space — that is, restricting along base
change of étale charts — recovers `𝒪_X`. This is the unit of the equivalence, which pins the
transported sheaf up to canonical isomorphism. -/
noncomputable def thickeningStructureSheafRestrictionIso (hG : IsThickening B S hS X G) :
    (smallEtaleCommRingSheafEquiv_of_isThickening B S hS hG).inverse.obj
      (smallEtaleThickeningStructureSheaf B S hS hG) ≅ (smallEtaleRingedTopos B S hS X).O :=
  ((smallEtaleCommRingSheafEquiv_of_isThickening B S hS hG).unitIso.app
    (smallEtaleRingedTopos B S hS X).O).symm

end AlgebraicGeometry.Space

end
