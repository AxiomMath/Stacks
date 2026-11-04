module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedPushforwardBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images across the two presentations of the small étale site

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of its underlying category. Two
small étale sites are attached to `S`: the size-bounded site
`AlgebraicGeometry.SmallEtale B S.obj S.property` of Stacks 021B, and Mathlib's site
`AlgebraicGeometry.Scheme.Etale` of *all* schemes étale over `S`. The abelian theory of higher
direct images is developed on both, and the two developments were previously unrelated at the
level of right derived functors:

* the mainstream direct image is `Stacks.EtaleCohomology.etaleAbelianDirectImage`, that is
  restriction along `Stacks.EtaleCohomology.smallEtaleBaseChange` at the coefficients
  `AddCommGrpCat.{max (u + 1) v}`;
* the bounded-site direct image is `Stacks.HigherDirectImage.pushforward`, that is restriction
  along `AlgebraicGeometry.smallEtaleBaseChange` at the coefficients `AddCommGrpCat.{w}`.

Writing `ρ_S` and `ρ_T` for restriction of abelian sheaves along the embeddings
`AlgebraicGeometry.SmallEtale.toEtaleSite` — the functors underlying
`AlgebraicGeometry.SmallEtale.sheafEquiv` — the undetermined square of *underived* direct images
is `AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`,

```
f_* ⋙ ρ_S  ≅  ρ_T ⋙ f_*  .
```

This file derives it: for every `q`,

```
R^q f_* ⋙ ρ_S  ≅  ρ_T ⋙ R^q f_*  ,
```

the left `R^q f_*` being the mainstream higher direct image and the right one the bounded site's,
together with the form in which the mainstream higher direct image is read off from the bounded
one,

```
R^q f_*  ≅  ρ_T ⋙ R^q f_* ⋙ (sheafEquiv S).functor .
```

That second form is the point of the file. **Stacks 03Q8** — `R^q f_* F` is the sheafification of
`V ↦ H^q(T ×_S V, F)` — is proved unconditionally in the bounded framework, as
`Stacks.HigherDirectImage.higherDirectImageSheafificationIso` and (at a geometric point)
`Stacks.HigherDirectImage.higherDirectImageStalkCohomologyPresheafIso`, while the consumers that
need it are stated with the mainstream `etaleAbelianDirectImage`. The second isomorphism below is
what carries that statement across.

## Main results

* `AlgebraicGeometry.SmallEtale.rightDerivedToEtaleSitePushforwardBaseChangeIso` — the commuting
  square of higher direct images, in every degree.
* `AlgebraicGeometry.SmallEtale.rightDerivedSheafEquivPushforwardBaseChangeIso` — the same with
  the restriction on the side of `S` replaced by the inverse equivalence, so that the mainstream
  higher direct image stands alone on the left.
* `AlgebraicGeometry.SmallEtale.isEquivalence_toEtaleSiteRestrictionAb`,
  `AlgebraicGeometry.SmallEtale.preservesInjectiveObjects_toEtaleSiteRestrictionAb` and the three
  exactness instances beside them — the properties of the mediator that the transport needs.

## The mediator preserves injective objects

A right derived functor is determined by the underived one on injectives, so a square of
underived functors derives only if the two functors that are *not* derived behave well: the one
postcomposed must be exact, and the one precomposed must be exact and carry injectives to
injectives. Restriction along `AlgebraicGeometry.SmallEtale.toEtaleSite` does both for a reason
stronger than either: it *is an equivalence*. The embedding of the bounded site is full, faithful
and cover-dense, so it is a dense subsite and
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` applies —
`AlgebraicGeometry.SmallEtale.sheafEquiv` is that equivalence, and restriction is its inverse.
Hence restriction preserves all limits and colimits (it is both a left and a right adjoint, of
one and the same functor), and it preserves injective objects because its own inverse is a left
adjoint of it which preserves monomorphisms, which is
`CategoryTheory.Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`. This
is the same argument as in
`Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence`, where restriction
along an equivalence of sites is shown not to change global cohomology.

No hypothesis is needed for any of it: the limits of shape `StructuredArrow X (toEtaleSite ..).op`
that the comparison lemma wants exist in `AddCommGrpCat.{max (u + 1) v}` because the bounded
small étale category is essentially small in the universe `u` of the schemes, exactly as in
`AlgebraicGeometry.SmallEtale.sheafEquiv` itself.

## Implementation notes

**The transport.** `CategoryTheory.Functor.rightDerivedSquareIsoOfExact`, in
`StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedPushforwardBaseChange`, is exactly this
passage from a square of additive functors to the square of their right derived functors, under
the hypotheses discussed above; it was built there for the lisse-étale and flat-fppf subsites of
Stacks 0GR3, and nothing in it is specific to those. It is used here unchanged, so the whole
content of this file is the identification of the mediator as an equivalence.

**Why the exactness instances are passed by hand.**
`Stacks.Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction` is a global
instance whose subject, `abelianRestriction`, *is* `Functor.sheafPushforwardContinuous` — at the
coefficients `AddCommGrpCat.{max v₁ w}`, with `v₁` the morphism universe of the sites. Instance
search selects it for the goals below, solves `max v₁ ?w =?= max (u + 1) v` by assigning
`?w := v`, and leaves the residual universe constraint `max u v =?= max (u + 1) v`, which is
reported as a failure of the enclosing declaration rather than as a rejected candidate. The
instances this file proves are therefore handed to
`CategoryTheory.Functor.rightDerivedSquareIsoOfExact` through local `haveI`s, which are consulted
before the global ones. For the same reason the two `PreservesFinite*` instances are assembled
from `CategoryTheory.Limits.PreservesLimitsOfSize.preservesFiniteLimits` and its dual applied to
an explicitly supplied `PreservesLimitsOfSize.{0, 0}`, rather than by instance search.

**The coefficient universe.** The two frameworks are written at different coefficient
conventions: `etaleAbelianDirectImage.{u, v}` is fixed at `AddCommGrpCat.{max (u + 1) v}`, the
universe in which this library computes étale cohomology, whereas
`Stacks.HigherDirectImage.pushforward.{u, w}` is polymorphic in `w`. Everything below is stated
at `AddCommGrpCat.{max (u + 1) v}` with `v` a free universe, which is the whole range of the
mainstream framework and the instance `w := max (u + 1) v` of the bounded one; no universe is
fixed and neither side is narrowed. `AlgebraicGeometry.SmallEtale.sheafEquiv` needs only limits
of size `u` in the coefficients, which `AddCommGrpCat.{max (u + 1) v}` has.

**What is assumed.** The two `HasSheafify` hypotheses per scheme are what makes the four sheaf
categories abelian, and the two `HasInjectiveResolutions` hypotheses on the sheaf categories of
`T` are what makes `Functor.rightDerived` meaningful at all; both are carried as instance
arguments in the same shape as `Stacks.HigherDirectImage.pushforward`'s own consumers in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage`. Nothing is assumed
about `f`, `S` or `T`.

No tag attribute is placed: this is the comparison of two formalizations, not a statement of the
source. Stacks 03Q8 remains carried where it is proved, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage` and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageStalkColimit`.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 0GR3](https://stacks.math.columbia.edu/tag/0GR3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **Restriction of abelian sheaves along the embedding of the bounded small étale site is an
equivalence.** The embedding is a dense subsite, so this is
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`, of which restriction is the inverse; the
limits of shape `StructuredArrow Y (toEtaleSite ..).op` it asks for in the coefficients exist
because the bounded small étale category is essentially small in the universe of the schemes,
exactly as in `AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
@[sga "4 VII 3.1" "special case"]
public instance isEquivalence_toEtaleSiteRestrictionAb :
    ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
      X.obj.smallEtaleTopology).IsEquivalence := by
  have : ∀ Y : (X.obj.Etale)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow Y (toEtaleSite B X.obj X.property).op)
        AddCommGrpCat.{max (u + 1) v} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  infer_instance

/-- **Restriction of abelian sheaves along the embedding of the bounded small étale site carries
injective objects to injective objects.** Restriction is an equivalence, so its own inverse is a
left adjoint of it, and a left adjoint preserving monomorphisms makes its right adjoint preserve
injectives. -/
public instance preservesInjectiveObjects_toEtaleSiteRestrictionAb :
    ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
      X.obj.smallEtaleTopology).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
      X.obj.smallEtaleTopology).asEquivalence.symm.toAdjunction

/-- Restriction of abelian sheaves along the embedding of the bounded small étale site preserves
finite limits, being the right adjoint of the inverse equivalence. -/
public instance preservesFiniteLimits_toEtaleSiteRestrictionAb :
    PreservesFiniteLimits ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
      X.obj.smallEtaleTopology) :=
  haveI h : PreservesLimitsOfSize.{0, 0}
      ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
        X.obj.smallEtaleTopology) :=
    Adjunction.rightAdjoint_preservesLimits
      ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
        X.obj.smallEtaleTopology).asEquivalence.symm.toAdjunction
  @PreservesLimitsOfSize.preservesFiniteLimits _ _ _ _ _ h

/-- Restriction of abelian sheaves along the embedding of the bounded small étale site preserves
finite colimits, being the left adjoint of the inverse equivalence. -/
public instance preservesFiniteColimits_toEtaleSiteRestrictionAb :
    PreservesFiniteColimits ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
      X.obj.smallEtaleTopology) :=
  haveI h : PreservesColimitsOfSize.{0, 0}
      ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
        X.obj.smallEtaleTopology) :=
    Adjunction.leftAdjoint_preservesColimits
      ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
        X.obj.smallEtaleTopology).asEquivalence.toAdjunction
  @PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ _ h

/-- Restriction of abelian sheaves along the embedding of the bounded small étale site is
additive: on underlying presheaves it is precomposition with the embedding, which reindexes the
components of a morphism. -/
public instance additive_toEtaleSiteRestrictionAb :
    ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
      X.obj.smallEtaleTopology).Additive where
  map_add := rfl

section

variable [HasSheafify (topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify X.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- Restriction of abelian sheaves along the embedding of the bounded small étale site preserves
homology, being exact. -/
public instance preservesHomology_toEtaleSiteRestrictionAb :
    ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B X.obj X.property)
      X.obj.smallEtaleTopology).PreservesHomology :=
  Functor.preservesHomologyOfExact _

end

variable {S T : B.Scheme} (f : T ⟶ S)

section

variable
  [HasSheafify (topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (topology B T.obj T.property) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify S.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify T.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasInjectiveResolutions (Sheaf T.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasInjectiveResolutions
    (Sheaf (topology B T.obj T.property) AddCommGrpCat.{max (u + 1) v})]

/-- **The two presentations of the small étale site have the same higher direct images along base
change.** For every `q`, the `q`-th higher direct image for Mathlib's presentation — the right
derived functor of `Stacks.EtaleCohomology.etaleAbelianDirectImage (B.inclusion.map f)` —
followed by restriction along the embedding of the bounded site of `S`, is restriction along the
embedding of the bounded site of `T` followed by the `q`-th higher direct image
`(Stacks.HigherDirectImage.pushforward B f).rightDerived q` for the bounded presentation.

This is the derived form of `AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`.
Right derivation commutes with postcomposition by the exact restriction on the side of `S` and
collapses along the exact, injective-preserving restriction on the side of `T`, which is
`CategoryTheory.Functor.rightDerivedSquareIsoOfExact`; both restrictions have those properties
because each is an equivalence,
`AlgebraicGeometry.SmallEtale.isEquivalence_toEtaleSiteRestrictionAb`. -/
public def rightDerivedToEtaleSitePushforwardBaseChangeIso (q : ℕ) :
    ((Stacks.EtaleCohomology.smallEtaleBaseChange
            (B.inclusion.map f)).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} S.obj.smallEtaleTopology
          T.obj.smallEtaleTopology).rightDerived q ⋙
        (toEtaleSite B S.obj S.property).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} (topology B S.obj S.property)
          S.obj.smallEtaleTopology ≅
      (toEtaleSite B T.obj T.property).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} (topology B T.obj T.property)
          T.obj.smallEtaleTopology ⋙
        (Stacks.HigherDirectImage.pushforward.{u, max (u + 1) v} B f).rightDerived q := by
  haveI : ((toEtaleSite B S.obj S.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B S.obj S.property)
      S.obj.smallEtaleTopology).PreservesHomology :=
    preservesHomology_toEtaleSiteRestrictionAb B S
  haveI : PreservesFiniteLimits ((toEtaleSite B T.obj T.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B T.obj T.property)
      T.obj.smallEtaleTopology) :=
    preservesFiniteLimits_toEtaleSiteRestrictionAb B T
  haveI : PreservesFiniteColimits ((toEtaleSite B T.obj T.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B T.obj T.property)
      T.obj.smallEtaleTopology) :=
    preservesFiniteColimits_toEtaleSiteRestrictionAb B T
  haveI : ((toEtaleSite B T.obj T.property).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (topology B T.obj T.property)
      T.obj.smallEtaleTopology).PreservesInjectiveObjects :=
    preservesInjectiveObjects_toEtaleSiteRestrictionAb B T
  exact Functor.rightDerivedSquareIsoOfExact _ _ _ _
    (toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{max (u + 1) v}) q

/-- **The mainstream higher direct image is the bounded site's, transported along the equivalence
of sheaf categories.** For every `q`, the `q`-th right derived functor of
`Stacks.EtaleCohomology.etaleAbelianDirectImage (B.inclusion.map f)` is restriction along the
embedding of the bounded site of `T`, followed by
`(Stacks.HigherDirectImage.pushforward B f).rightDerived q`, followed by the forward direction of
`AlgebraicGeometry.SmallEtale.sheafEquiv` for `S`.

This is `AlgebraicGeometry.SmallEtale.rightDerivedToEtaleSitePushforwardBaseChangeIso` with the
restriction on the side of `S` undone by the counit of the equivalence it is the inverse of. It
is the form in which a statement about the bounded site's higher direct images — Stacks 03Q8, as
`Stacks.HigherDirectImage.higherDirectImageSheafificationIso` — becomes a statement about the
mainstream one. -/
public def rightDerivedSheafEquivPushforwardBaseChangeIso (q : ℕ) :
    ((Stacks.EtaleCohomology.smallEtaleBaseChange
          (B.inclusion.map f)).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v} S.obj.smallEtaleTopology
        T.obj.smallEtaleTopology).rightDerived q ≅
      (toEtaleSite B T.obj T.property).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} (topology B T.obj T.property)
          T.obj.smallEtaleTopology ⋙
        (Stacks.HigherDirectImage.pushforward.{u, max (u + 1) v} B f).rightDerived q ⋙
          (sheafEquiv B S.obj S.property AddCommGrpCat.{max (u + 1) v}).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _
      (sheafEquiv B S.obj S.property AddCommGrpCat.{max (u + 1) v}).counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedToEtaleSitePushforwardBaseChangeIso B f q) _ ≪≫
    Functor.associator _ _ _

end

end AlgebraicGeometry.SmallEtale

end
