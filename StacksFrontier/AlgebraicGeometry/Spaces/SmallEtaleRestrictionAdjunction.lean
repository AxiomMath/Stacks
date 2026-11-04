module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage

/-!
# Étale restriction is left adjoint to the direct image, at the universe of the structure rings

Let `h : U ⟶ V` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Restriction along small étale postcomposition with `h`,
`AlgebraicGeometry.Space.smallEtaleSetRestriction`, is the inverse image of the morphism of
small étale topoi of `h` — that is Stacks 03LQ, and
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRestrictionInverseImage.lean` proves it at
`Type (u + 1)`, the only universe at which that morphism of topoi exists.

This file supplies the adjunction that identification expresses, at the universe `u` of the
structure rings, against the direct image `AlgebraicGeometry.Space.smallEtaleDirectImage` that
the module development actually uses:

`(-)|_U ⊣ h_*`.

No new mathematics is involved: on the *spaces*-étale sites, postcomposition with `h` is left
adjoint to base change along `h` as a functor of sites
(`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction`), hence on sheaves with
arbitrary coefficients (`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction`), and both
functors of this file are the conjugates of those two by the comparison equivalences of
Stacks 03G1 at `Type u`.  So the content here is the conjugation, plus the two computations that
keep the *spaces*-étale adjunction it is conjugated from being opaque: that adjunction's unit is
restriction along the cartesian projection.  The unit of the conjugated adjunction below is
**not** computed; it is the spaces-étale unit composed with the unit and the counit of the two
comparison equivalences.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` is the adjunction: small étale
  restriction along an étale morphism is left adjoint to the direct image of sheaves of sets at
  the universe of the structure rings.
* `AlgebraicGeometry.Space.smallEtaleDirectImageIsoPushforwardCocontinuous` identifies
  `AlgebraicGeometry.Space.smallEtaleDirectImage` of an étale morphism with the pushforward
  attached to the cocontinuity of Stacks 03LP, wherever the right Kan extensions that the latter
  is built from exist.

## Main results

* `AlgebraicGeometry.Space.toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit`: the
  counit of the adjunction of *sites* is the cartesian projection of the base change.
* `AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction_unit_app`: the unit of the
  spaces-étale adjunction on sheaves is restriction along that counit, by `rfl`.  Together with
  the previous result this says that the unit, on sections over an object `W` of the
  spaces-étale site of `V`, is restriction along the projection `W ×_V U ⟶ W`.
* `AlgebraicGeometry.Space.isLeftAdjoint_smallEtaleSetRestriction`: restriction along small
  étale postcomposition with an étale morphism preserves all colimits.

There is deliberately *no* companion statement that the direct image is a right adjoint: it is
one for an **arbitrary** morphism already, because
`AlgebraicGeometry.Space.isRightAdjoint_sheafPushforwardContinuous_spacesBaseChange` supplies a
left adjoint to its middle factor and the other two factors are halves of equivalences, so
`unfold smallEtaleDirectImage; infer_instance` proves it outright.  What the adjunction below
adds is the *identification* of that left adjoint with restriction, and that is what needs `h`
to be étale.

## Implementation notes

**Why this is not tagged.** The assertion of Stacks 03LQ, and the clause of Stacks 03LP that
the morphism of topoi attached to the postcomposition functor is `h_small`, are already carried
by `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` and
`AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso`.  The source states nothing
separately about the universe of the structure rings — that distinction is an artefact of this
development, where `AlgebraicGeometry.Space.smallEtaleDirectImage` lives at `Type u` because
the direct image of modules applies it to the sheaf of sets underlying a module — so the
declarations here carry no attribute of their own.

**What this is for.** It is *an* input that Stacks 03M8 needs and this development did not
have — not the only one; the exactness of the resulting fork and the module-level reading of
its arrows are both still owed.  In the notation of that
lemma, write `τ : U ⟶ X` for the surjective étale chart, `ρ = t ≫ τ = s ≫ τ : R ⟶ X`, and
`a = τ ≫ f`, `b = ρ ≫ f`.  Splitting those two composites with
`AlgebraicGeometry.Space.modulePushforwardCompIso` turns the sequence
`0 → f_*F → a_*(F|_U) → b_*(F|_R)` into `f_*` applied to
`0 → F → τ_*(F|_U) → ρ_*(F|_R)`, whose first arrow is the unit at `τ` and whose two parallel
arrows are `τ_*` of the units at `t` and at `s` — the two readings of `F|_R` being the two
factorizations of `ρ`.  So the arrows are units of exactly this adjunction, and `f_*` carries a
limiting fork to a limiting fork because it is a right adjoint
(`AlgebraicGeometry.Space.isRightAdjoint_modulePushforward`).

The adjunction here is at the level of sheaves of *sets*, so it does not by itself produce
those arrows in `Mod(𝒪_Y)`: a morphism of modules needs in addition that the structure map of
Stacks 03G8 for an étale morphism *is* this unit, which is the statement

`structureSharpSet h = (smallEtaleSetRestrictionAdjunction h hh).unit.app (structureSetSheaf V)`

and is not proved here.  The equation is well-posed for a reason worth recording: both sides are
morphisms out of `𝒪_V`, because `(smallEtaleSetRestriction h hh).obj (structureSetSheaf V)` is
`structureSetSheaf U` on the nose.

That equation is a *third* route, and it supersedes the account in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardPresentationExact.lean`, which record two other
routes — Stacks' Equation 03LW, and the hypothesis `hsharp` of the
module form of Stacks 03LR, part (1) — and name
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction` as the available set-level
adjunction without conjugating it to the small étale sites.

**Coefficients and universes.** The conjugation below works at any coefficient category for
which the comparison restriction of Stacks 03G1 is an equivalence — at `AddCommGrpCat.{u}` it
is, by `AlgebraicGeometry.Space.hasLimitsOfShape_structuredArrow_comparisonFunctor_op_addCommGrp`
— but `AlgebraicGeometry.Space.smallEtaleDirectImage` is declared only at `Type u`, so stating
the general form would mean introducing a second direct image.  It is therefore stated at
`Type u` only.

**Elaboration: the hazard recorded by the sibling files does not arise here.**  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRestrictionInverseImage.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardEtaleBaseChange.lean` record that leaving
a metavariable in a `CategoryTheory.Functor.comp` position in this area hands the unifier
`?F ⋙ ?G =?= (P ⋙ A) ⋙ B`, whose fallback unfolds
`AlgebraicGeometry.Space.smallEtaleDirectImage` through `CategoryTheory.Functor.objPreimage`
into `Classical.choose` and diverges; both therefore name every intermediate functor with a
`let`.  That is not needed below: the fully implicit
term elaborates in three seconds.  The reason is that no metavariable ever reaches a
composition position — the two composite adjunctions are determined by their *arguments*, and
the target of `CategoryTheory.Adjunction.ofNatIsoLeft` is fixed by
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso`, which carries both composites in its
own declared type.  No `set_option` appears in this file.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicSpaces B S hS}

/-! ### The unit of the spaces-étale adjunction -/

/-- **The counit of the adjunction of sites is the cartesian projection.**  For an étale
`h : U ⟶ V` and an object `W` of the spaces-étale site of `V`, the component at `W` of the
counit of `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction` is, on underlying
algebraic spaces, the projection `W ×_V U ⟶ W` of
`AlgebraicGeometry.Space.spacesBaseChange`.

The adjunction is the restriction of `CategoryTheory.Over.mapPullbackAdj` along the two fully
faithful inclusions of the étale objects into the slices, so
`CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app` computes its counit in the
slice; the two comparison isomorphisms are `CategoryTheory.Iso.refl` because
`CategoryTheory.ObjectProperty.liftCompιIso` is, and the counit of `Over.mapPullbackAdj` is the
first projection of the chosen fibre product, which is the projection of the base-change
datum. -/
theorem toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) (W : SpacesEtale B S hS V) :
    (SpacesEtale.toSpaces B S hS V).map
        ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app W) =
      (spacesBaseChange B S hS h).projection.app W := by
  have key := Adjunction.map_restrictFullyFaithful_counit_app (Over.mapPullbackAdj h)
    (ObjectProperty.fullyFaithfulι (IsEtaleOver B S hS U))
    (ObjectProperty.fullyFaithfulι (IsEtaleOver B S hS V))
    (L := spacesEtalePostcomp B S hS h hh)
    (R := (spacesBaseChange B S hS h).functor)
    (comm1 := (ObjectProperty.liftCompιIso _ _ _).symm)
    (comm2 := (ObjectProperty.liftCompιIso _ _ _).symm) W
  have h2 := congrArg (fun m : (SpacesEtale.inclusion B S hS V).obj
      ((spacesEtalePostcomp B S hS h hh).obj ((spacesBaseChange B S hS h).functor.obj W)) ⟶
      (SpacesEtale.inclusion B S hS V).obj W ↦ m.left) key
  simp only [ObjectProperty.liftCompιIso, Iso.symm_inv, Iso.refl_hom, NatTrans.id_app,
    Over.mapPullbackAdj_counit_app] at h2
  exact h2

/-- **The unit of the spaces-étale adjunction on sheaves is restriction along the counit of the
adjunction of sites.**  For a sheaf `P` on the spaces-étale site of `V` and an object `W` of
that site, the unit of `AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction` sends a
section of `P` over `W` to its restriction along
`(spacesEtalePostcompBaseChangeAdjunction h hh).counit.app W`, which by
`AlgebraicGeometry.Space.toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit` is the
projection `W ×_V U ⟶ W`.

It holds by `rfl`: Mathlib's `CategoryTheory.Adjunction.sheafPushforwardContinuous` defines the
unit by whiskering the opposite adjunction into the functor category, and both restriction
functors are precomposition with the opposite functor of sites. -/
theorem spacesEtalePostcompSheafAdjunction_unit_app (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (P : Sheaf (SpacesEtale.topology B S hS V) (Type u)) (W : SpacesEtale B S hS V)
    (x : P.obj.obj (op W)) :
    ((spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app P).hom.app (op W) x =
      P.obj.map ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app W).op x := rfl

/-! ### The adjunction on the small étale sites -/

/-- **Étale restriction is left adjoint to the direct image, at the universe of the structure
rings.**  For an étale morphism `h : U ⟶ V` of algebraic spaces, restriction of sheaves of sets
along small étale postcomposition with `h` is left adjoint to
`AlgebraicGeometry.Space.smallEtaleDirectImage` of `h`:

`Hom(G|_U, F) = Hom(G, h_*F)`.

This is the adjunction of Stacks 03LP and 03G2, part (1) between the two functors of
spaces-étale sites, carried to sheaves by
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction` and then conjugated by the
comparison equivalences of Stacks 03G1 at `Type u`.  The conjugation is by two instances of
`CategoryTheory.Adjunction.comp` against `CategoryTheory.Equivalence.toAdjunction`;
`AlgebraicGeometry.Space.smallEtaleDirectImage` is literally the conjugated right adjoint, and
the left adjoint is identified with small étale restriction by
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso`. -/
noncomputable def smallEtaleSetRestrictionAdjunction (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    smallEtaleSetRestriction B S hS h hh ⊣ smallEtaleDirectImage B S hS h :=
  Adjunction.ofNatIsoLeft
    (((smallEtaleComparisonRestriction B S hS V).asEquivalence.symm.toAdjunction.comp
        (spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh)).comp
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.toAdjunction)
    (smallEtaleSetRestrictionConjIso B S hS h hh).symm

/-- Restriction of sheaves of sets along small étale postcomposition with an étale morphism, at
the universe of the structure rings, is a left adjoint.

Instance search does not find this on its own: the left adjoint of a continuous functor's
restriction is `CategoryTheory.Functor.sheafPullback`, whose existence needs the left Kan
extension along small étale postcomposition, and that is not available at this universe.  It is
the adjunction above — which produces the left adjoint from the *spaces*-étale side instead —
that gives it.

It is a `theorem` and not an `instance`, so preservation of colimits does not follow by
instance search: a consumer that wants
`CategoryTheory.Limits.PreservesColimitsOfSize (smallEtaleSetRestriction h hh)` must put this in
scope with `have` first.  That is the shape
`AlgebraicGeometry.Space.hasSheafify_smallEtaleRingedSite_addCommGrpCat`
(`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentGrothendieck.lean:232`) and its sibling
already take, and it is the conservative choice here: an instance affects elaboration in every
module that imports this one, which is a decision to take when this module enters the library
umbrella rather than before.  Promoting it costs one word and nothing else — it was checked that
`instance` typechecks and that `inferInstance` then finds the colimit preservation. -/
theorem isLeftAdjoint_smallEtaleSetRestriction (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    (smallEtaleSetRestriction B S hS h hh).IsLeftAdjoint :=
  (smallEtaleSetRestrictionAdjunction B S hS h hh).isLeftAdjoint

/-- **The direct image of an étale morphism is the pushforward attached to the cocontinuity of
Stacks 03LP.**  Wherever the pointwise right Kan extensions along small étale postcomposition
exist, `AlgebraicGeometry.Space.smallEtaleDirectImage` agrees with
`CategoryTheory.Functor.sheafPushforwardCocontinuous`.

Both are right adjoint to small étale restriction — the first by
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` and the second by
`AlgebraicGeometry.Space.smallEtalePostcompAdjunction` — so they agree by uniqueness of right
adjoints.  This discharges, at the universe of the structure rings, the comparison that the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtalePostcompCocontinuous.lean` leave open; the Kan
extension hypothesis is still carried, exactly as it is there. -/
noncomputable def smallEtaleDirectImageIsoPushforwardCocontinuous (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom)
    [∀ F : (SmallEtale B S hS U.1)ᵒᵖ ⥤ Type u,
      (smallEtalePostcomp B S hS h hh).op.HasPointwiseRightKanExtension F] :
    smallEtaleDirectImage B S hS h ≅
      (smallEtalePostcomp B S hS h hh).sheafPushforwardCocontinuous (Type u)
        (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1) :=
  (smallEtaleSetRestrictionAdjunction B S hS h hh).rightAdjointUniq
    (smallEtalePostcompAdjunction B S hS h hh (Type u))

end AlgebraicGeometry.Space

end
