module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPoints

/-!
# The points of the Quot functor with values in an algebraic space (Stacks 0D3V)

In Situation 09TR a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` of a big fppf
site is given, of finite presentation, together with a quasi-coherent `𝒪_X`-module `F`.
Stacks 09TR reads `Quot_{F/X/B}` as a presheaf on the big fppf site of `S`, whose value at a
scheme `T` over `S` is the set of pairs `(h, Q)` consisting of a morphism `h : T ⟶ B` and a
quotient of `F_T` which is quasi-coherent, of finite presentation, flat over `T` and with
support proper over `T`; Stacks 09TT says that presheaf is a sheaf.  Stacks 0D3V extends the
description of those pairs from the schemes of the site to an arbitrary algebraic space `T`:

`Mor_{Sh((Sch/S)_fppf)}(T, Quot_{F/X/B}) = {(h, F_T ⟶ Q) : h : T ⟶ B, Q of finite presentation,`
`flat over T with support proper over T}`

with `F_T` the pullback of `F` to the algebraic space `X ×_{B, h} T`.

This file supplies the right-hand side over an arbitrary algebraic space `T` — the four
conditions of Stacks 09TR read on the base change of the situation along a morphism out of an
algebraic space, and the pairs themselves — and proves the identification in the case where `T`
is a scheme of the site.  It is the exact analogue, with the proper-support condition added, of
the sibling Stacks 0D3U of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorPoints.lean`, and the base change it reads
the conditions on is the one built there.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.SpaceIsProperlySupportedOver`: the proper-support
  condition on a module over the base change along a morphism out of an algebraic space.
* `AlgebraicGeometry.Space.QuotSituation.spaceProperlySupportedQuotients`: the four conditions
  of Stacks 09TR read over an algebraic-space base.
* `AlgebraicGeometry.Space.QuotSituation.SpaceProperlySupportedQuotients`: **the right-hand side
  of the displayed identification of Stacks 0D3V**, a morphism `h : T ⟶ B` bundled with such a
  quotient of `F_T`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.isLocallyOfFiniteType_spaceBaseToSpace`: the projection
  `X_T ⟶ T` of the base change along a morphism out of an algebraic space is locally of finite
  type, which is what makes the proper-support condition expressible there.
* `AlgebraicGeometry.Space.QuotSituation.spaceProperlySupportedQuotients_eq`: over a test scheme
  the conditions read over an algebraic-space base are the conditions of Stacks 09TR.
* `AlgebraicGeometry.Space.QuotSituation.morEquivSpaceProperlySupportedQuotient`:
  **Stacks 0D3V for a representable algebraic space.**  The morphisms of sheaves from a scheme
  of the site into `Quot_{F/X/B}` are the pairs `(h, Q)` over it.

## Implementation notes

**Why the identification is a bijection and not an equality.**  The source writes `=` between a
set of morphisms of sheaves and a set of pairs.  Those are two different types here — a type of
natural transformations on one side, a structure with three fields on the other — so a
propositional equality between them is not even well typed, and the honest reading of the
source's `=` is a bijection.  It is given as an `Equiv`, that is as data, and the data is
*constructed*: the forward map is the Yoneda bijection followed by the renaming of the three
fields, and both directions are written down, so nothing is chosen from an existence statement.
This is also the form the sibling Stacks 0D3U takes, which keeps the two tags comparable.

**Why the conditions over an algebraic-space base need nothing new.**  The base change
`X_T = X ×_{B, h} T` along a morphism out of an algebraic space is
`AlgebraicGeometry.Space.QuotientSituation.spaceBaseChange`, built for Stacks 0D3U, and for `h`
out of a test scheme it is literally the base change at that test scheme.  The three conditions
of Stacks 082M read there are already
`AlgebraicGeometry.Space.QuotientSituation.spaceFinitePresentationQuotients`; the fourth, proper
support, is added here, and the only thing it needs is that the projection `X_T ⟶ T` be locally
of finite type, which is a base change of the morphism of the situation and so follows from its
being of finite presentation exactly as for a test scheme.  Because `IsLocallyOfFiniteType` is a
proposition, that proof does not have to be matched on the nose for the conditions over a test
scheme to agree with the conditions of Stacks 09TR, and
`AlgebraicGeometry.Space.QuotSituation.spaceProperlySupportedQuotients_eq` holds by reflexivity.

**Which clause of Stacks 0D3V is proved and which is not.**  The identification is proved for
`T` a scheme of the big fppf site, where it is the Yoneda lemma for the sheaf of Stacks 09TT.
For a general algebraic space it is not, and the obstruction is the same one recorded on
`AlgebraicGeometry.Space.QuotientSituation.morEquivSpaceQuotient` for the sibling Stacks 0D3U:
the source chooses a scheme `U` with a surjective étale morphism `U ⟶ T`, reads a transformation
at it as a pair over `U`, and descends, and the descent of the quotient is the fullness and
effectivity clauses of Stacks 04W8 together with Stacks 0262, 05VY and 060V, of which this
development carries none — only the faithfulness clause of Stacks 04W8 is available, as
`AlgebraicGeometry.Space.QuasiCoherentDescent.faithful_canonicalDescentFunctor_of_isFpqcCovering`.
The proper-support condition would additionally have to be descended, which the source gets from
Stacks 0CZJ read on the chart.  Nothing is claimed for the general case.

**The universe of the identification.**  An algebraic space is a presheaf of `Type u` on the big
fppf site, whereas `Quot_{F/X/B}` takes values in `Type (u + 1)`, its sections being recorded by
subobjects of a module.  As for Stacks 0D3U the left-hand side is therefore read with the sheaf
of the algebraic space lifted, which for a representable space is
`CategoryTheory.uliftYoneda`; the lift is an isomorphism onto its image at every object of the
site, so no morphism is added or lost.

## References

* [Stacks Project, Tag 0D3V](https://stacks.math.columbia.edu/tag/0D3V)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 0D3U](https://stacks.math.columbia.edu/tag/0D3U)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-! ### The proper-support condition over an algebraic-space base -/

/-- The projection `X_T ⟶ T` of the base change of the situation along a morphism `h : T ⟶ B`
out of an algebraic space is locally of finite type, being a base change of the morphism of the
situation, which is of finite presentation.

This is `AlgebraicGeometry.Space.QuotSituation.isLocallyOfFiniteType_projection` with the
structure morphism of a test scheme replaced by an arbitrary morphism of algebraic spaces; the
fibre product is the same construction at a different second argument. -/
theorem isLocallyOfFiniteType_spaceBaseToSpace {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) :
    IsLocallyOfFiniteType B S hS (D.spaceBaseToSpace h).hom :=
  (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (D.isPullback_spaceBaseChange h)
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS D.finitePresentation.1)

/-- An `𝒪_{X_T}`-module has *support proper over `T`*, for `h : T ⟶ B` a morphism out of an
algebraic space, when its support is a closed subset of the points of `X_T` proper over `T` in
the sense of Stacks 0CZD.  This is
`AlgebraicGeometry.Space.QuotSituation.IsProperlySupportedOver` with the structure morphism of a
test scheme replaced by an arbitrary morphism of algebraic spaces. -/
abbrev SpaceIsProperlySupportedOver {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y)
    (G : Modules.{u, u} B S hS (D.spaceBaseChange h).1 (D.spaceBaseChange h).2) : Prop :=
  HasProperSupport B S hS (D.spaceBaseChange h).2 T.2 (D.spaceBaseToSpace h).hom
    (D.isLocallyOfFiniteType_spaceBaseToSpace h) ((SheafOfModules.toSheaf _).obj G)

/-- **Stacks 09TR over an algebraic-space base.**  The quotients of `F_T` which are
quasi-coherent, of finite presentation, flat over `T` and have support proper over `T`, for
`h : T ⟶ B` a morphism out of an algebraic space.  As in Stacks 082M a quotient is recorded by
its kernel, the quotient itself being the cokernel of the inclusion. -/
def spaceProperlySupportedQuotients {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) :
    Set (Subobject (D.spaceBaseModule h)) :=
  {K | K ∈ D.spaceFinitePresentationQuotients h ∧
    D.SpaceIsProperlySupportedOver h (cokernel K.arrow)}

/-- The properly supported quotients over an algebraic-space base form a subset of the finitely
presented ones, the objectwise half of the claim of Stacks 09TR that `Quot_{F/X/B}` is a
subfunctor of `Q^{fp}_{F/X/B}`, read over an algebraic-space base. -/
theorem spaceProperlySupportedQuotients_subset {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) :
    D.spaceProperlySupportedQuotients h ⊆ D.spaceFinitePresentationQuotients h :=
  fun _ hK ↦ hK.1

/-- Over a test scheme the four conditions of Stacks 09TR read over an algebraic-space base are
the four conditions of Stacks 09TR read at that test scheme.  The two base changes are the same
fibre product, the two projections to the base are the same morphism, and the proof that it is
locally of finite type is a proof of a proposition, so the two sets agree with no transport. -/
theorem spaceProperlySupportedQuotients_eq {U : BigFppfOver B S hS}
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) :
    D.spaceProperlySupportedQuotients h = D.properlySupportedQuotients (D.testAt h) :=
  rfl

/-! ### The pairs of the source -/

/-- **The right-hand side of the displayed identification of Stacks 0D3V.**  A pair `(h, Q)`
consisting of a morphism `h : T ⟶ B` out of an algebraic space and a quotient of `F_T` which is
quasi-coherent, of finite presentation, flat over `T` and has support proper over `T`.

This is `AlgebraicGeometry.Space.QuotientSituation.SpaceQuotient`, built for the sibling
Stacks 0D3U, at the condition of Stacks 09TR. -/
abbrev SpaceProperlySupportedQuotients (T : AlgebraicSpaces B S hS) :=
  D.SpaceQuotient (fun _ h ↦ D.spaceProperlySupportedQuotients h) T

/-! ### The identification over a scheme of the site -/

/-- **Over a scheme of the site the sections of the Quot presheaf are the pairs of Stacks 0D3V.**
A section of `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf` at a scheme `U` of the big
fppf site is a morphism `U ⟶ B` together with a member of `Quot_{F/X/B}` for the test scheme it
makes of `U`; a pair of Stacks 0D3V at the algebraic space of `U` is a morphism `U ⟶ B` together
with a quotient of the base change of the situation along it.  The two base changes are the same
fibre product, so the two agree with no transport. -/
def quotFamilyEquivSpaceProperlySupportedQuotient {U : BigFppfOver B S hS} :
    QuotFamilyOver D U ≃
      D.SpaceProperlySupportedQuotients ((schemeSpaceFunctor B S hS).obj U) where
  toFun q := ⟨q.toBase, q.subobject, q.mem⟩
  invFun q := ⟨q.hom, q.ker, q.mem⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Stacks 0D3V for a representable algebraic space.**  The morphisms of sheaves on the big
fppf site of `S` from a scheme `U` of the site into `Quot_{F/X/B}` are the pairs `(h, Q)`
consisting of a morphism `h : U ⟶ B` of algebraic spaces and a quotient of `F_U` which is
quasi-coherent, of finite presentation, flat over `U` and has support proper over `U`, where
`F_U` is the pullback of `F` to `X ×_{B, h} U`.

This is the source's displayed identification in the case where the algebraic space `T` is a
scheme of the site, which is the base of the source's proof: that proof chooses a scheme `U`
with a surjective étale morphism `U ⟶ T`, reads the transformation at it as a pair over `U`, and
descends.  The identification here is the Yoneda lemma for the sheaf of Stacks 09TT, whose value
at `U` is the set of those pairs; the sheaf of the algebraic space of `U` is lifted to the
universe of the Quot presheaf, which adds and loses no morphism.  The general case is not
covered; see the implementation notes for the precise obstruction. -/
@[stacks 0D3V "RESTRICTED: the displayed identification, read as a bijection, only for an \
algebraic space T that is a scheme of the big fppf site; the general case needs the fullness \
and effectivity of quasi-coherent descent, which this development lacks"]
def morEquivSpaceProperlySupportedQuotient (U : BigFppfOver B S hS) :
    (uliftYoneda.{u + 1}.obj U ⟶ D.quotSitePresheaf) ≃
      D.SpaceProperlySupportedQuotients ((schemeSpaceFunctor B S hS).obj U) :=
  uliftYonedaEquiv.trans D.quotFamilyEquivSpaceProperlySupportedQuotient

end QuotSituation

end AlgebraicGeometry.Space

end
