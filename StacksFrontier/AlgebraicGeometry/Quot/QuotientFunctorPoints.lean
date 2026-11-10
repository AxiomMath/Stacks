module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorSheaf

/-!
# The points of the functor of quotients with values in an algebraic space (Stacks 0D3U)

In Situation 082M a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf
site is given together with a quasi-coherent `𝒪_X`-module `F`.  Stacks 082P reads the functor
of quotients of Stacks 082N as a sheaf `Q_{F/X/Y}` on the big fppf site of `S`, whose value at
a scheme `U` over `S` is the set of pairs `(h, Q)` consisting of a morphism `h : U ⟶ Y` and a
quotient of `F_U` which is quasi-coherent and flat over `U`.  Stacks 0D3U extends the
description of those pairs from the schemes of the site to an arbitrary algebraic space `T`:

`Mor_{Sh((Sch/S)_fppf)}(T, Q_{F/X/Y}) = {(h, F_T ⟶ Q) : h : T ⟶ Y, Q quasi-coherent and flat`
`over T}`

with `F_T` the pullback of `F` to the algebraic space `X ×_{Y, h} T`, and likewise for the
finite-presentation subsheaf `Q^{fp}_{F/X/Y}`.

This file supplies the right-hand side of that identification over an arbitrary algebraic space
`T` — the base change of the situation along a morphism out of an algebraic space, the two
conditions of Stacks 082M read there, and the pairs themselves — and proves the identification
in the case where `T` is a scheme of the site.  That case is the base of the source's induction:
the source's proof chooses a scheme `U` with a surjective étale morphism `U ⟶ T` and descends
the pair obtained over `U`, so the pair over a scheme is what it descends *from*.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation.spaceBaseChange`: the base change
  `X_T = X ×_{Y, h} T` of the situation along a morphism `h : T ⟶ Y` out of an algebraic space,
  with its two projections `spaceBaseToSource` and `spaceBaseToSpace`.
* `AlgebraicGeometry.Space.QuotientSituation.spaceBaseModule`: the module `F_T` on that base
  change.
* `AlgebraicGeometry.Space.QuotientSituation.spaceQuotients` and
  `AlgebraicGeometry.Space.QuotientSituation.spaceFinitePresentationQuotients`: the two
  conditions of Stacks 082M — quasi-coherence together with flatness over `T`, and finite
  presentation — read over an algebraic-space base.
* `AlgebraicGeometry.Space.QuotientSituation.SpaceQuotient`: **the right-hand side of the
  displayed identification of Stacks 0D3U**, a morphism `h : T ⟶ Y` bundled with a quotient of
  `F_T` satisfying the condition.
* `AlgebraicGeometry.Space.QuotientSituation.spaceChartMap`: the morphism `X_U ⟶ X_T` of base
  changes induced by a morphism `U ⟶ T` from a scheme of the site, with its comparison
  `spaceChartComparison` of the two inverse images of `F` and the resulting restriction
  `spaceQuotientRestrict` of a quotient of `F_T` to a quotient of `F_U`.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.totalQuotientEquivSpaceQuotient`: over a scheme of
  the site the pairs of Stacks 082P *are* the pairs of Stacks 0D3U.  The base change along the
  structure morphism of a test scheme and the base change along the same morphism read out of an
  algebraic space are the same fibre product, so the two descriptions agree with no transport.
* `AlgebraicGeometry.Space.QuotientSituation.morEquivSpaceQuotient`: **Stacks 0D3U for a
  representable algebraic space.**  The morphisms from a scheme of the site into `Q_{F/X/Y}` are
  the pairs `(h, Q)` over it.

## Implementation notes

**Why the base change needs no new fibre products.**  `AlgebraicGeometry.Space.baseChangeSpace`
of `StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean` is defined as
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` of the morphism of the situation against the
structure morphism of a test scheme, and that fibre product exists for *any* pair of morphisms
of algebraic spaces with a common target.  The restriction of the existing machinery to test
schemes is therefore incidental, and the base change along a morphism out of an arbitrary
algebraic space is the same construction at a different second argument.  This is what makes
`AlgebraicGeometry.Space.QuotientSituation.totalQuotientEquivSpaceQuotient` hold with no
transport: for `h` out of a test scheme the two fibre products are literally the same object,
and the quasi-coherence and flatness conditions are then the same conditions.

**Which clause of Stacks 0D3U is proved and which is not.**  The identification is proved here
for `T` a scheme of the big fppf site, where it is the Yoneda lemma applied to the sheaf of
Stacks 082P.  For a general algebraic space `T` it is not proved, and the obstruction is a
descent input rather than a bookkeeping one.  The source's proof chooses a scheme `U` with a
surjective étale morphism `p : U ⟶ T`, reads a transformation at `p` as a pair over `U`, and then
descends: the morphism `h` descends because `T = U/R` for `R = U ×_T U` (Spaces, Lemma 0262) and
the quotient descends by the fpqc descent of quasi-coherent modules (Descent on Spaces,
Proposition 04W8), after which the descended quotient is flat over `T` because `U ⟶ T` is
surjective and flat (Morphisms of Spaces, Lemma 05VY) and of finite presentation by Descent on
Spaces, Lemma 060V.  Of those inputs this development carries only the *faithfulness* half of
Stacks 04W8, as
`AlgebraicGeometry.Space.QuasiCoherentDescent.faithful_canonicalDescentFunctor_of_isFpqcCovering`,
whose own attribute says as much, while the fullness and effectivity clauses are absent:
`AlgebraicGeometry.Space.QuasiCoherentDescent.IsEffective` is defined and is concluded for no
covering.  So the descent of the quotient, which is the whole forward direction for a general
`T`, has no engine here, and nothing is claimed for it; the tag attributes say which case they
cover.

**The universe of the identification.**  An algebraic space is a presheaf of `Type u` on the big
fppf site, whereas the functor of quotients takes values in `Type (u + 1)`: its value at a test
scheme is a set of subobjects of a module, and a module is itself a `Type u`-sized sheaf.  The
two therefore do not live in one functor category, and the left-hand side of the displayed
identification is read with the sheaf of the algebraic space lifted, which for a representable
space is `CategoryTheory.uliftYoneda`.  This is a reading of the source's `Mor` and not a
weakening of it: the lift is an isomorphism onto its image at every object of the site, so no
morphism is added or lost.

**The restriction of a pair, and what it still needs.**  `spaceQuotientRestrict` restricts a
quotient of `F_T` along a morphism `U ⟶ T` out of a scheme of the site, and is the assignment
the source's converse direction uses to turn a pair into a transformation.  It is built, as the
pullback of a quotient of Stacks 082M is, by conjugating the projection onto the quotient with a
comparison of inverse images, because the inverse image of modules preserves epimorphisms but
is not known to preserve monomorphisms.  Turning the assignment into a transformation needs its
two functor laws, which are the unit and composition coherences of the comparison, and those
are not proved here: unlike the test-scheme comparison of
`AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison`, the morphism of an algebraic
space out of a test scheme is recovered from a section of its sheaf only up to the naturality of
the Yoneda bijection, so the two sides of each law sit over propositionally — not
syntactically — equal structure morphisms.

## References

* [Stacks Project, Tag 0D3U](https://stacks.math.columbia.edu/tag/0D3U)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 082N](https://stacks.math.columbia.edu/tag/082N)
* [Stacks Project, Tag 082P](https://stacks.math.columbia.edu/tag/082P)
* [Stacks Project, Tag 0CZL](https://stacks.math.columbia.edu/tag/0CZL)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site over `S` is slow
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_QuotientFunctorPoints :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_QuotientFunctorPoints
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-! ### Base change along a morphism out of an algebraic space -/

/-- The base change `X_T = X ×_{Y, h} T` of the situation along a morphism `h : T ⟶ Y` out of an
algebraic space.  For `T` a test scheme this is
`AlgebraicGeometry.Space.baseChangeSpace`: both are the fibre product of the morphism of the
situation against `h`. -/
def spaceBaseChange {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS D.f h

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullback D.f.hom h.hom` on presheaves over the big fppf site is slow
/-- The projection `X_T ⟶ X` of the base change along a morphism out of an algebraic space, along
which the module of the situation is pulled back. -/
def spaceBaseToSource {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) :
    D.spaceBaseChange h ⟶ D.X :=
  ObjectProperty.homMk (pullback.fst D.f.hom h.hom)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullback D.f.hom h.hom` on presheaves over the big fppf site is slow
/-- The projection `X_T ⟶ T` of the base change along a morphism out of an algebraic space, over
which the quotients are required to be flat. -/
def spaceBaseToSpace {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) : D.spaceBaseChange h ⟶ T :=
  ObjectProperty.homMk (pullback.snd D.f.hom h.hom)

/-- The base change along a morphism out of an algebraic space is a fibre product. -/
theorem isPullback_spaceBaseChange {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) :
    IsPullback (D.spaceBaseToSource h) (D.spaceBaseToSpace h) D.f h :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS D.f h

/-- The module `F_T` on the base change along a morphism out of an algebraic space: the pullback
of the module of the situation along the projection `X_T ⟶ X`. -/
abbrev spaceBaseModule {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) :
    Modules.{u, u} B S hS (D.spaceBaseChange h).1 (D.spaceBaseChange h).2 :=
  (modulePullback B S hS (D.spaceBaseToSource h)).obj D.F

/-- **Stacks 082M over an algebraic-space base.**  The quotients of `F_T` which are
quasi-coherent and flat over `T`, for `h : T ⟶ Y` a morphism out of an algebraic space.  As in
Stacks 082M a quotient is recorded by its kernel, the quotient itself being the cokernel of the
inclusion. -/
def spaceQuotients {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) :
    Set (Subobject (D.spaceBaseModule h)) :=
  {K | (cokernel K.arrow).IsQuasicoherentOnSite ∧
    IsFlatOver B S hS (D.spaceBaseChange h).2 (D.spaceBaseToSpace h).hom (cokernel K.arrow)}

/-- **Stacks 0CZL over an algebraic-space base.**  The subset of
`AlgebraicGeometry.Space.QuotientSituation.spaceQuotients` of those quotients that are of finite
presentation as modules on `X_T`. -/
def spaceFinitePresentationQuotients {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) :
    Set (Subobject (D.spaceBaseModule h)) :=
  {K | K ∈ D.spaceQuotients h ∧ (cokernel K.arrow).IsFinitePresentationOnSite}

/-- The finitely presented quotients over an algebraic-space base form a subset of all the
quotients that are quasi-coherent and flat over the base. -/
theorem spaceFinitePresentationQuotients_subset_spaceQuotients
    {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) :
    D.spaceFinitePresentationQuotients h ⊆ D.spaceQuotients h :=
  fun _ hK ↦ hK.1

/-! ### The pairs of the source -/

/-- **The right-hand side of the displayed identification of Stacks 0D3U.**  A pair `(h, Q)`
consisting of a morphism `h : T ⟶ Y` out of an algebraic space and a quotient of `F_T`
satisfying the condition `Q` — quasi-coherence together with flatness over `T` for
`Q_{F/X/Y}`, and finite presentation in addition for `Q^{fp}_{F/X/Y}`.

The condition is a parameter, so that the construction serves both sheaves of the source. -/
structure SpaceQuotient
    (Q : ∀ (T' : AlgebraicSpaces B S hS) (h : T' ⟶ D.Y),
      Set (Subobject (D.spaceBaseModule h)))
    (T : AlgebraicSpaces B S hS) where
  /-- The morphism `T ⟶ Y` along which the situation is based changed. -/
  hom : T ⟶ D.Y
  /-- The kernel of the quotient of `F_T`. -/
  ker : Subobject (D.spaceBaseModule hom)
  /-- The quotient satisfies the condition. -/
  mem : ker ∈ Q T hom

/-- The pairs of Stacks 0D3U for `Q_{F/X/Y}`: the condition is quasi-coherence together with
flatness over the base. -/
abbrev SpaceQuotients (T : AlgebraicSpaces B S hS) :=
  D.SpaceQuotient (fun _ h ↦ D.spaceQuotients h) T

/-- The pairs of Stacks 0D3U for `Q^{fp}_{F/X/Y}`: the condition has finite presentation added. -/
abbrev SpaceFinitePresentationQuotients (T : AlgebraicSpaces B S hS) :=
  D.SpaceQuotient (fun _ h ↦ D.spaceFinitePresentationQuotients h) T

/-! ### Restriction of a pair to a test scheme -/

/-- The morphism `X_U ⟶ X_T` of base changes induced by a morphism `α : U ⟶ T` out of a scheme
of the big fppf site: the morphism onto the fibre product given by the projection of `X_U` to
`X` and by its projection to `U` followed by `α`. -/
def spaceChartMap {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y) {U : BigFppfOver B S hS}
    (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) :
    D.space (D.testAt (α ≫ h)) ⟶ D.spaceBaseChange h :=
  (D.isPullback_spaceBaseChange h).lift (D.sourceProjection (D.testAt (α ≫ h)))
    (D.projection (D.testAt (α ≫ h)) ≫ α)
    (by
      rw [Category.assoc]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f (α ≫ h)).w)

/-- The morphism of base changes induced by a morphism out of a test scheme commutes with the
projections to the source of the situation. -/
theorem spaceChartMap_comp_toSource {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y)
    {U : BigFppfOver B S hS} (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) :
    D.spaceChartMap h α ≫ D.spaceBaseToSource h =
      D.sourceProjection (D.testAt (α ≫ h)) :=
  (D.isPullback_spaceBaseChange h).lift_fst _ _ _

/-- The comparison of the module `F_U` on the base change at a test scheme with the inverse image
along `X_U ⟶ X_T` of the module `F_T` on the base change at an algebraic space, at the level of
the inverse-image functors. -/
def spaceChartComparison {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y)
    {U : BigFppfOver B S hS} (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) :
    modulePullback B S hS (D.sourceProjection (D.testAt (α ≫ h))) ≅
      modulePullback B S hS (D.spaceBaseToSource h) ⋙
        modulePullback B S hS (D.spaceChartMap h α) :=
  modulePullbackTriangle B S hS (D.spaceChartMap_comp_toSource h α)

/-- **The restriction of a quotient of `F_T` to a test scheme.**  For a morphism
`α : U ⟶ T` out of a scheme of the big fppf site, the quotient `F_U ⟶ (X_U ⟶ X_T)^*(F_T/K)` of
`F_U`, recorded — as the quotients themselves are — by its kernel.

This is the assignment the converse direction of Stacks 0D3U uses to turn a pair over `T` into a
transformation; it is built by conjugating the projection onto the quotient, because the inverse
image of modules preserves epimorphisms but is not known to preserve monomorphisms. -/
def spaceQuotientRestrict {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y)
    {U : BigFppfOver B S hS} (α : (schemeSpaceFunctor B S hS).obj U ⟶ T)
    (K : Subobject (D.spaceBaseModule h)) :
    Subobject (D.baseChangeModule (D.testAt (α ≫ h))) :=
  Functor.conjSubobject (D.spaceChartComparison h α) K

/-- The quotient by the restriction of a quotient to a test scheme is the inverse image of the
quotient, so the restriction really does record the source's quotient
`F_U ⟶ (X_U ⟶ X_T)^*(F_T/K)`. -/
def spaceQuotientRestrictCokernelIso {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y)
    {U : BigFppfOver B S hS} (α : (schemeSpaceFunctor B S hS).obj U ⟶ T)
    (K : Subobject (D.spaceBaseModule h)) :
    D.quotientModule (D.testAt (α ≫ h)) (D.spaceQuotientRestrict h α K) ≅
      (modulePullback B S hS (D.spaceChartMap h α)).obj (cokernel K.arrow) :=
  Functor.conjSubobjectCokernelIso (D.spaceChartComparison h α) K

/-! ### The identification over a scheme of the site -/

/-- Over a test scheme the base change of the situation along the structure morphism, read out of
an algebraic space, is the base change of the situation at that test scheme: both are the fibre
product of the morphism of the situation against the same morphism. -/
theorem spaceBaseToSource_eq_sourceProjection {U : BigFppfOver B S hS}
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) :
    D.spaceBaseToSource h = D.sourceProjection (D.testAt h) :=
  rfl

/-- Over a test scheme the projection of the base change to the base is the projection of the
base change to the test scheme. -/
theorem spaceBaseToSpace_eq_projection {U : BigFppfOver B S hS}
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) :
    D.spaceBaseToSpace h = D.projection (D.testAt h) :=
  rfl

/-- Over a test scheme the conditions of Stacks 082M read over an algebraic-space base are the
conditions of Stacks 082M read at that test scheme. -/
theorem spaceQuotients_eq_quotients {U : BigFppfOver B S hS}
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) :
    D.spaceQuotients h = D.quotients (D.testAt h) :=
  rfl

/-- Over a test scheme the finite-presentation condition read over an algebraic-space base is the
finite-presentation condition read at that test scheme. -/
theorem spaceFinitePresentationQuotients_eq_finitePresentationQuotients
    {U : BigFppfOver B S hS} (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) :
    D.spaceFinitePresentationQuotients h = D.finitePresentationQuotients (D.testAt h) :=
  rfl

/-- **Over a scheme of the site the pairs of Stacks 082P are the pairs of Stacks 0D3U.**  An
element of the total presheaf of Stacks 082P at a scheme `U` of the big fppf site is a morphism
`U ⟶ Y` together with a quotient of `F_U` over the test scheme it makes of `U`; a pair of
Stacks 0D3U at the algebraic space of `U` is a morphism `U ⟶ Y` together with a quotient of the
base change of the situation along it.  The two base changes are the same fibre product, so the
two agree with no transport. -/
def totalQuotientEquivSpaceQuotient {U : BigFppfOver B S hS} :
    D.TotalQuotient D.quotients U ≃ D.SpaceQuotients ((schemeSpaceFunctor B S hS).obj U) where
  toFun q := ⟨q.hom, q.ker, q.mem⟩
  invFun q := ⟨q.hom, q.ker, q.mem⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Over a scheme of the site the finitely presented pairs of Stacks 082P are the finitely
presented pairs of Stacks 0D3U.** -/
def totalQuotientEquivSpaceFinitePresentationQuotient {U : BigFppfOver B S hS} :
    D.TotalQuotient D.finitePresentationQuotients U ≃
      D.SpaceFinitePresentationQuotients ((schemeSpaceFunctor B S hS).obj U) where
  toFun q := ⟨q.hom, q.ker, q.mem⟩
  invFun q := ⟨q.hom, q.ker, q.mem⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Stacks 0D3U for a representable algebraic space.**  The morphisms of sheaves on the big
fppf site of `S` from a scheme `U` of the site into `Q_{F/X/Y}` are the pairs `(h, Q)`
consisting of a morphism `h : U ⟶ Y` of algebraic spaces and a quotient of `F_U`, quasi-coherent
and flat over `U`, where `F_U` is the pullback of `F` to `X ×_{Y, h} U`.

This is the source's displayed identification in the case where the algebraic space `T` is a
scheme of the site, which is the base of the source's proof: that proof chooses a scheme `U`
with a surjective étale morphism `U ⟶ T`, reads the transformation at it as a pair over `U`, and
descends.  The identification here is the Yoneda lemma for the sheaf of Stacks 082P, whose value
at `U` is the set of those pairs; the sheaf of the algebraic space of `U` is lifted to the
universe of the functor of quotients, which adds and loses no morphism. -/
@[stacks 0D3U "the displayed identification for Q_{F/X/Y}, in the case where the algebraic \
space is a scheme of the big fppf site: the morphisms of sheaves into the functor of quotients \
of Stacks 082P are the pairs of a morphism to Y and a quotient, quasi-coherent and flat over \
the base, of the pullback of F to the base change along it.  Conditional on the one hypothesis \
of Stacks 082N still carried, the pseudofunctoriality of the inverse images of Stacks 03LU.  \
The case of a general algebraic space is not covered: it needs \
the descent of the quotient along a surjective étale chart, which is the fullness and \
effectivity clauses of Stacks 04W8 together with Stacks 0262, 05VY and 060V, none of which \
this development carries"]
def morEquivSpaceQuotient (hc : ModulePushforwardCoherence B S hS)
    (U : BigFppfOver B S hS) :
    (uliftYoneda.{u + 1}.obj U ⟶ D.totalQuotientsFunctor hc) ≃
      D.SpaceQuotients ((schemeSpaceFunctor B S hS).obj U) :=
  uliftYonedaEquiv.trans D.totalQuotientEquivSpaceQuotient

end QuotientSituation

end AlgebraicGeometry.Space

end
