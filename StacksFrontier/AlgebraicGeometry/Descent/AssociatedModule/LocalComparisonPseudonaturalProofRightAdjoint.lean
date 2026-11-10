module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.LocalComparisonPseudonaturalProofStarAdjunction

/-!
# The comparison of the two right adjoints of restriction along an arrow of a site

`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso` is the canonical comparison of the two
right adjoints of restriction to an object of the big fppf site, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/PseudonaturalityClosure.lean` record that
*nothing computes it*: it is `CategoryTheory.Adjunction.rightAdjointUniq` of two adjunctions, with
no handle on it beyond its universal property.
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso_eq_rightAdjointUniq_overMap` reduced it
to the same comparison at an arbitrary site, between
`Stacks.SheafOfModules.overMapStarAdjunction` and `SheafOfModules.overMapPushforwardAdj`.  This
file carries out that comparison, and so computes it.

The answer is the one Stacks 04IR predicts.  The right adjoint of `overMapStarAdjunction` is an
*iterated* pushforward — the reindexing of Stacks 06WI followed by the pushforward along the
product with `Over.mk f` — and `SheafOfModules.pushforwardComp` contracts it to the single
pushforward along `Over.star (Over.mk f) ⋙ Over.iteratedSliceForward`.  That functor of sites is
base change along `f`, by `CategoryTheory.starIteratedSliceForwardIsoPullback` of Stacks 04IR, and
`Stacks.SheafOfModules.comparisonComp_starIteratedSliceForwardIsoPullback` says the two functors
carry the same comparison of structure sheaves; so `SheafOfModules.pushforwardCongr₂` carries that
isomorphism of sites to `SheafOfModules.overPullback`.  The comparison of right adjoints is that
composite.

## Main definitions

* `Stacks.SheafOfModules.overMapStarPushforwardIsoOverPullback`: **the reindexed pushforward along
  the product with `Over.mk f` is base change along `f`**, as functors on sheaves of modules —
  built from `SheafOfModules.pushforwardComp` and from the isomorphism of sites of Stacks 04IR.

## Main results

* `Stacks.Mates.unit_comp_conjugateIsoEquiv_inv_app`: **the inverse of a conjugate carries the
  unit of the second adjunction to the unit of the first**, twisted by the conjugating
  isomorphism.  This is `CategoryTheory.unit_conjugateEquiv` read through
  `CategoryTheory.conjugateIsoEquiv`, and for a conjugating isomorphism that is the identity it is
  `Stacks.Mates.unit_comp_rightAdjointUniq_inv_app`.
* `Stacks.SheafOfModules.unit_comp_starIteratedSliceForwardIsoPullback_inv_app`: **the isomorphism
  of Stacks 04IR carries the unit of base change to the unit of the localization**, which is the
  one identity of the site that the computation below rests on.
* `Stacks.SheafOfModules.rightAdjointUniq_overMapStarAdjunction`: **the comparison of the two
  right adjoints of restriction along an arrow of a site is the contraction of the iterated
  pushforward followed by the transport along the isomorphism of sites of Stacks 04IR.**  This is
  the computation that was missing.
* `AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso_eq`: **the comparison of the two right
  adjoints of restriction to an object of the big fppf site, computed.**

## Implementation notes

Nothing here carries a `stacks` attribute: the comparison this file is about is a step
Stacks 03DV leaves implicit and carries no tag of its own.

**Why the comparison is proved by its universal property rather than assembled.**  The two
`rightAdjointUniq` computations of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.LocalComparisonPseudonaturalProofMates`
would each apply to one half of this statement, but they do not compose here: their junction is a
`SheafOfModules.pushforwardPushforwardAdj` whose functor of sites is spelled
`Over.iteratedSliceBackward ⋙ Over.forget (Over.mk f)`, while
`SheafOfModules.overMapPushforwardAdj` spells it `Over.map f`, and
`CategoryTheory.Adjunction.rightAdjointUniq` requires its two adjunctions to have one and the same
left adjoint *as a term*.  Going instead through `Stacks.Mates.rightAdjointUniq_eq_of_counit` asks
only for an identity between morphisms of the site, which is where the two spellings are
`CategoryTheory.Over.iteratedSliceBackward_forget` apart and that is `rfl`.

Three further constraints are forced rather than stylistic.

* The inverse of `Stacks.SheafOfModules.overMapReindexEquivalence` is identified with a pushforward
  by spelling the structure morphism as `Stacks.SheafOfModules.reindexBackSharp` —
  `overMapReindexBackSharp` below — and *not* by spelling the functor of sites as
  `CategoryTheory.Over.iteratedSliceForward`.  The second route asks the unifier to unfold
  `CategoryTheory.Limits.getLimitCone`, which this library does not see exposed; the first is pure
  delta-iota and is `rfl`.
* That structure morphism is the identity, `overMapReindexBackSharp_eq_id`, but only up to
  `CategoryTheory.Functor.map_id`: its components are the structure sheaf applied to an identity
  of the site, which is not the identity on the nose.  So
  `Stacks.SheafOfModules.comparisonComp_starIteratedSliceForwardIsoPullback`, which is stated with
  the identity, is bridged to the form `SheafOfModules.pushforwardComp` produces rather than
  matched against it.
* `Stacks.SheafOfModules.reindexBackSharp`, `SheafOfModules.pushforward`,
  `SheafOfModules.pushforwardComp` and `SheafOfModules.pushforwardCongr₂` are applied with their
  continuity hypotheses supplied explicitly.  In each of them such a hypothesis precedes, in the
  telescope, the argument that determines what it is a hypothesis *about*, so at the point where it
  is synthesized the functor or the topology is still a metavariable and synthesis fails;
  `CategoryTheory.Functor.IsContinuous` is a proposition, so any witness will do.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 04IR](https://stacks.math.columbia.edu/tag/04IR)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₀ v₁ w v u

namespace Stacks.Mates

variable {C₀ : Type v₀} {C₁ : Type v₁} [Category C₀] [Category C₁]

/-- **The inverse of a conjugate carries the unit of the second adjunction to the unit of the
first**, twisted by the conjugating isomorphism.  For `adj₁ : L₁ ⊣ R₁`, `adj₂ : L₂ ⊣ R₂` and
`α : L₂ ≅ L₁`, the unit of `adj₂` followed by the inverse of
`CategoryTheory.conjugateIsoEquiv adj₁ adj₂ α` is the unit of `adj₁` followed by `R₁` applied to
`α.inv`.

This is `CategoryTheory.unit_conjugateEquiv` read through `CategoryTheory.conjugateIsoEquiv`, whose
inverse is the conjugate of `α.inv` with the two adjunctions exchanged.  For `α` the identity it is
`Stacks.Mates.unit_comp_rightAdjointUniq_inv_app`; the point of the general form is that a
conjugate of a *transport* along an equality of functors is admissible, which is the shape of
`CategoryTheory.starIteratedSliceForwardIsoPullback`. -/
public theorem unit_comp_conjugateIsoEquiv_inv_app {L₁ L₂ : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ≅ L₁) (X : C₀) :
    adj₂.unit.app X ≫ (conjugateIsoEquiv adj₁ adj₂ α).inv.app (L₂.obj X) =
      adj₁.unit.app X ≫ R₁.map (α.inv.app X) :=
  unit_conjugateEquiv adj₂ adj₁ α.inv X

end Stacks.Mates

namespace Stacks.SheafOfModules

-- As in Stacks 04IR: the slice `C/U` has binary products as soon as `C` has pullbacks, and that
-- is what makes `CategoryTheory.Over.star` available on it.
attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : GrothendieckTopology C}
  {U V : C} (f : V ⟶ U)

/-- **The isomorphism of Stacks 04IR carries the unit of base change to the unit of the
localization.**  The unit of `CategoryTheory.Over.mapPullbackAdj` at `W`, followed by the inverse
of `CategoryTheory.starIteratedSliceForwardIsoPullback` at `Over.map f` of `W`, is the unit of the
adjunction that localizes `C/U` at `Over.mk f`.

This is the one identity of the site that the computation of the comparison of right adjoints rests
on.  The isomorphism of Stacks 04IR is by construction the conjugate of the transport along
`CategoryTheory.Over.iteratedSliceBackward_forget`, so this is
`Stacks.Mates.unit_comp_conjugateIsoEquiv_inv_app`; the transport contributes nothing because that
equality of functors holds by `rfl`, so its components are identities. -/
public theorem unit_comp_starIteratedSliceForwardIsoPullback_inv_app (W : Over V) :
    (Over.mapPullbackAdj f).unit.app W ≫
        (starIteratedSliceForwardIsoPullback f).inv.app ((Over.map f).obj W) =
      ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp
        (Over.forgetAdjStar (Over.mk f))).unit.app W := by
  refine Eq.trans (Stacks.Mates.unit_comp_conjugateIsoEquiv_inv_app _ _ _ W) ?_
  exact Eq.trans (congrArg (fun k => _ ≫ k) (CategoryTheory.Functor.map_id _ _))
    (Category.comp_id _)

variable (R : Sheaf J RingCat.{w})

/-- **The structure morphism of the inverse of the reindexing of Stacks 06WI along an arrow of a
site.**  This is `Stacks.SheafOfModules.reindexBackSharp` at
`CategoryTheory.Over.iteratedSliceEquiv`, with its two continuity hypotheses supplied explicitly;
see the implementation notes.  Spelling the inverse of
`Stacks.SheafOfModules.overMapReindexEquivalence` as the pushforward along *this* morphism is what
makes that identification `rfl`. -/
public noncomputable abbrev overMapReindexBackSharp :=
  @Stacks.SheafOfModules.reindexBackSharp _ _ _ _ ((J.over U).over (Over.mk f))
    (J.over V) ((Over.mk f).iteratedSliceEquiv.symm)
    (isContinuous_iteratedSliceEquivSymm_functor f)
    (isContinuous_iteratedSliceEquivSymm_inverse f)
    ((R.over U).over (Over.mk f))

omit [HasPullbacks C] in
/-- **The reindexing of Stacks 06WI matches the structure sheaves on the nose.**  Its structure
morphism is the identity: the counit of the iterated slice equivalence is an identity of the site,
so the morphism's components are the structure sheaf applied to an identity.

That last step is `CategoryTheory.Functor.map_id` and not `rfl`, which is why the comparison of
structure sheaves recorded with the identity has to be bridged to the form
`SheafOfModules.pushforwardComp` produces rather than matched against it. -/
public theorem overMapReindexBackSharp_eq_id :
    overMapReindexBackSharp f R = 𝟙 ((R.over U).over (Over.mk f)) := by
  ext A : 3
  exact R.obj.map_id _

/-- **The comparison of structure sheaves of the contracted pushforward**, in the spelling
`SheafOfModules.pushforwardComp` produces.  This is
`Stacks.SheafOfModules.comparisonComp_starIteratedSliceForwardIsoPullback` with the identity
replaced by the structure morphism of the reindexing, which is the same morphism by
`overMapReindexBackSharp_eq_id`; it is the hypothesis of `SheafOfModules.pushforwardCongr₂` for the
isomorphism of sites of Stacks 04IR, at the morphism of structure sheaves that the contraction of
the iterated pushforward actually carries. -/
public theorem comparisonComp_backSharp_starIteratedSliceForwardIsoPullback :
    Sheaf.toPushforwardOverPullback R f ≫
        (@Functor.sheafPushforwardContinuousNatTrans (Over U) _ (Over V) _ _ _
          (starIteratedSliceForwardIsoPullback f).hom RingCat.{w} _ (J.over U) (J.over V)
          (isContinuous_starIteratedSliceForward f)
          (isContinuous_overPullback f)).app (R.over V) =
      @SheafOfModules.comparisonComp (Over U) _ (Over (Over.mk f)) _ (Over V) _
        (J.over U) ((J.over U).over (Over.mk f)) (J.over V)
        (Over.star (Over.mk f)) ((Over.mk f).iteratedSliceForward)
        _ (isContinuous_iteratedSliceForward' f) (isContinuous_starIteratedSliceForward f)
        _ _ (R.over V)
        (SheafOfModules.pushforwardOver (R := R.over U) (Over.mk f))
        (overMapReindexBackSharp f R) :=
  by
  rw [overMapReindexBackSharp_eq_id]
  exact comparisonComp_starIteratedSliceForwardIsoPullback f R

/-- **The reindexed pushforward along the product with `Over.mk f` is base change along `f`.**
The right adjoint of `Stacks.SheafOfModules.overMapStarAdjunction` is an iterated pushforward;
`SheafOfModules.pushforwardComp` contracts it to the single pushforward along
`Over.star (Over.mk f) ⋙ Over.iteratedSliceForward`, which is base change along `f` by
`CategoryTheory.starIteratedSliceForwardIsoPullback` of Stacks 04IR, and
`SheafOfModules.pushforwardCongr₂` carries that isomorphism of sites to sheaves of modules with
`comparisonComp_backSharp_starIteratedSliceForwardIsoPullback` as its compatibility of structure
sheaves.

This is the explicit isomorphism that the comparison of the two right adjoints turns out to be,
`Stacks.SheafOfModules.rightAdjointUniq_overMapStarAdjunction`. -/
public noncomputable abbrev overMapStarPushforwardIsoOverPullback :=
  @SheafOfModules.pushforwardComp.{w} _ _ _ _ _ _ _ _ _ _ _ _
      (SheafOfModules.pushforwardOver (R := R.over U) (Over.mk f))
      _ _ _ (isContinuous_iteratedSliceEquivSymm_inverse f) (overMapReindexBackSharp f R) ≪≫
    (@SheafOfModules.pushforwardCongr₂.{w} _ _ _ _ _ _ _ _ _ _
      (isContinuous_starIteratedSliceForward f) (isContinuous_overPullback f)
      (Sheaf.toPushforwardOverPullback R f) _ (starIteratedSliceForwardIsoPullback f)
      (comparisonComp_backSharp_starIteratedSliceForwardIsoPullback f R)).symm

/-- **The comparison of the two right adjoints of restriction along an arrow of a site is the
contraction of the iterated pushforward followed by the transport along the isomorphism of sites of
Stacks 04IR.**  Restriction along `f` is a left adjoint in two ways, by
`Stacks.SheafOfModules.overMapStarAdjunction` and by `SheafOfModules.overMapPushforwardAdj`, and
`CategoryTheory.Adjunction.rightAdjointUniq` compares the two right adjoints; this says that
comparison is `Stacks.SheafOfModules.overMapStarPushforwardIsoOverPullback`.

Both sides are determined by the counits, `Stacks.Mates.rightAdjointUniq_eq_of_counit`, and every
structural comparison that enters — `SheafOfModules.pushforwardComp`,
`SheafOfModules.pushforwardCongr`, and the counit of a pushforward adjunction — is given on
sections by restriction along a morphism of the site.  So the identity to check is one identity
between morphisms of the site, and that is
`unit_comp_starIteratedSliceForwardIsoPullback_inv_app` together with
`CategoryTheory.Adjunction.comp_unit_app`.

Instantiated at the big fppf site this computes
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso`, which nothing computed. -/
public theorem rightAdjointUniq_overMapStarAdjunction :
    Adjunction.rightAdjointUniq (overMapStarAdjunction f R)
        (SheafOfModules.overMapPushforwardAdj R f) =
      overMapStarPushforwardIsoOverPullback f R := by
  refine (Stacks.Mates.rightAdjointUniq_eq_of_counit _ _ _ fun M => ?_).symm
  ext W x
  change (M.val.presheaf.map ((starIteratedSliceForwardIsoPullback f).inv.app
        ((Over.map f).obj W.unop)).op ≫
      M.val.presheaf.map ((Over.mapPullbackAdj f).unit.app W.unop).op) x =
    (M.val.presheaf.map ((Over.mk f).iteratedSliceEquiv.symm.inverse.map
        ((Over.forgetAdjStar (Over.mk f)).unit.app
          ((Over.mk f).iteratedSliceEquiv.symm.functor.obj W.unop))).op ≫
      M.val.presheaf.map
        ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.unit.app W.unop).op) x
  rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp, ← op_comp,
    unit_comp_starIteratedSliceForwardIsoPullback_inv_app f W.unop, Adjunction.comp_unit_app]
  rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

open Stacks.SheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- **The comparison of the two right adjoints of restriction to an object of the big fppf site,
computed.**  `AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso` is the contraction
`SheafOfModules.pushforwardComp` of the iterated pushforward followed by the transport
`SheafOfModules.pushforwardCongr₂` along the isomorphism of sites of Stacks 04IR: the product with
`T` inside the big fppf category over `S` is the fibre product over `S` with the scheme of `T`, and
the three structure sheaves match.

This is what the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/RightAdjointComparison.lean` record as
missing — "that isomorphism of functors of sites does not exist in the trees".  It does now, at an
arbitrary site, where it is `CategoryTheory.starIteratedSliceForwardIsoPullback` of Stacks 04IR;
and the comparison of right adjoints at the big fppf site is its instance, by
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso_eq_rightAdjointUniq_overMap` and
`Stacks.SheafOfModules.rightAdjointUniq_overMapStarAdjunction`. -/
public theorem objRestrictRightAdjointIso_eq :
    objRestrictRightAdjointIso B S hS T =
      overMapStarPushforwardIsoOverPullback (J := B.topology) T.hom B.structureSheaf :=
  (objRestrictRightAdjointIso_eq_rightAdjointUniq_overMap B S hS T).trans
    (rightAdjointUniq_overMapStarAdjunction (J := B.topology) T.hom B.structureSheaf)

end AlgebraicGeometry.BigFppfOver

end
