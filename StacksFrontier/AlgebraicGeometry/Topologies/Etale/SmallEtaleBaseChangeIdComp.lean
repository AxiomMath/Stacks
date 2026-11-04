module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality

/-!
# The left unit law for the composition of small étale base changes

For `b : X ⟶ Y` in a big étale site, base change along `𝟙 X` after base change along `b` is
compared with base change along `𝟙 X ≫ b = b` by
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`, and base change along `𝟙 X` is
compared with the identity functor by `AlgebraicGeometry.smallEtaleBaseChange_idIso`.  This file
proves that **the two comparisons agree at every object**: the composition comparison at the
left-hand identity *is* the identity comparison, whiskered.

Both comparisons are pinned down by their images under the fully faithful inclusion of the small
étale category into the slice, where they become `CategoryTheory.Over.pullbackComp (𝟙 X) b` and
`CategoryTheory.Over.pullbackId`.  Mathlib defines both of those by `conjugateIsoEquiv` from
`CategoryTheory.Over.mapComp` and `CategoryTheory.Over.mapId` and proves no coherence between
them — there is no unitality, associativity or component lemma for either in Mathlib, and the
`Under` duals have none either — so the comparison is made here.

The proof is a fibre-product chase, and it is short because the two projections of the target
are both already available.  Both sides are morphisms **into** the fibre product
`X ×_Y (X ×_X W)`, so `CategoryTheory.Limits.pullback.hom_ext` applies: the first projection of
the composition comparison is
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst`, which at the left-hand
identity is literally the first projection of the identity comparison, and the second projection
of either side is its structure morphism over `X`, by `CategoryTheory.Over.w`.  The one new
ingredient is `CategoryTheory.Over.pullbackId_hom_app_left`, which computes the identity
comparison on underlying objects as the first projection; that follows from
`CategoryTheory.conjugateEquiv_adjunction_id` and
`CategoryTheory.Over.mapPullbackAdj_counit_app`.

## Main results

* `CategoryTheory.Over.pullbackId_hom_app_left`: the comparison of pullback along an identity
  with the identity functor is, on underlying objects, the first projection.
* `AlgebraicGeometry.smallEtaleBaseChange_idIso_hom_app_left`: the same for the small étale
  comparison `AlgebraicGeometry.smallEtaleBaseChange_idIso`.
* `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_id_left_hom_app` and
  `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_id_left_inv_app`: **the left unit
  law**, in its `hom` and `inv` forms.  The `inv` form is the one the sections of a pushforward
  consume, since pushforward along `ε_a` is restriction along base change.

## Implementation notes

No `@[stacks]` attribute is claimed.  Stacks 021J is the composition law for the morphisms of
topoi attached to a morphism of schemes; its registrations sit on
`AlgebraicGeometry.smallEtaleBaseChange_compIso` and the four comparison functors derived from
it in
`StacksFrontier/AlgebraicGeometry/Topologies/Etale/MorphismComposition.lean`.  The unit law proved
here is the coherence that *accompanies* that composition law rather than a clause of the
source's statement, so it is left untagged.

## References

* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Over

variable {C : Type*} [Category C] {P : C} [Limits.HasPullbacksAlong (𝟙 P)]

/-- **The comparison of pullback along an identity with the identity functor, on underlying
objects.**  `CategoryTheory.Over.pullbackId` is the conjugate of `CategoryTheory.Over.mapId`,
whose components are identities, so its own components are the counit of
`CategoryTheory.Over.mapPullbackAdj`, which is the first projection. -/
theorem pullbackId_hom_app_left (V : Over P) :
    ((Over.pullbackId (X := P)).hom.app V).left = Limits.pullback.fst V.hom (𝟙 P) := by
  rw [Over.pullbackId]
  simp [Over.mapPullbackAdj_counit_app]

end CategoryTheory.Over

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (b : X ⟶ Y)

/-- **`AlgebraicGeometry.smallEtaleBaseChange_idIso`, on underlying objects.**  Forgetting the
étale condition, the identification of base change along `𝟙 X` with the identity functor is the
first projection of the fibre product with `𝟙 X`. -/
public theorem smallEtaleBaseChange_idIso_hom_app_left (W : SmallEtale B X.obj X.property) :
    ((SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_idIso B X).hom.app W)).left =
      Limits.pullback.fst W.obj.hom (𝟙 X) := by
  rw [smallEtaleBaseChange_idIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Over.comp_left, Over.id_left,
    Over.pullbackId_hom_app_left]
  exact Category.id_comp _

/-- **The left unit law for the composition of small étale base changes.**  Base changing along
`b` and then along `𝟙 X`, compared with base change along the composite `𝟙 X ≫ b = b`, is the
comparison of base change along `𝟙 X` with the identity functor.

The inclusion of the small étale category into the slice is faithful, and both sides land in the
fibre product with `𝟙 X`, so it suffices to compare the two projections.  The first is
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst` on the left and
`AlgebraicGeometry.smallEtaleBaseChange_idIso_hom_app_left` on the right, and these are the same
morphism; the second is, on either side, the structure morphism of the common source over
`X`. -/
public theorem smallEtaleBaseChange_factoredCompIso_id_left_hom_app
    (V : SmallEtale B Y.obj Y.property) :
    (smallEtaleBaseChange_factoredCompIso B X X Y (𝟙 X) b b (Category.id_comp b)).hom.app V =
      (smallEtaleBaseChange_idIso B X).hom.app ((smallEtaleBaseChange B b).obj V) := by
  apply (SmallEtale.inclusion B X.obj X.property).map_injective
  refine Over.OverMorphism.ext (Limits.pullback.hom_ext ?_ ?_)
  · rw [smallEtaleBaseChange_idIso_hom_app_left]
    exact smallEtaleBaseChange_factoredCompIso_hom_app_fst B X X Y (𝟙 X) b b
      (Category.id_comp b) V
  · exact (Over.w ((SmallEtale.inclusion B X.obj X.property).map
      ((smallEtaleBaseChange_factoredCompIso B X X Y (𝟙 X) b b
        (Category.id_comp b)).hom.app V))).trans
      (Over.w ((SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_idIso B X).hom.app
          ((smallEtaleBaseChange B b).obj V)))).symm

/-- **The left unit law for the composition of small étale base changes, in its `inv` form.**

This is `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_id_left_hom_app` with
`CategoryTheory.Iso.inv` applied to both sides.  It is the form the sections of a pushforward of
sheaves of modules along `ε` consume: pushing forward is restriction along base change, and the
compositor of the pushforwards restricts along the *inverse* of the comparison. -/
public theorem smallEtaleBaseChange_factoredCompIso_id_left_inv_app
    (V : SmallEtale B Y.obj Y.property) :
    (smallEtaleBaseChange_factoredCompIso B X X Y (𝟙 X) b b (Category.id_comp b)).inv.app V =
      (smallEtaleBaseChange_idIso B X).inv.app ((smallEtaleBaseChange B b).obj V) := by
  have h : (smallEtaleBaseChange_factoredCompIso B X X Y (𝟙 X) b b
        (Category.id_comp b)).app V =
      (smallEtaleBaseChange_idIso B X).app ((smallEtaleBaseChange B b).obj V) :=
    Iso.ext (smallEtaleBaseChange_factoredCompIso_id_left_hom_app B b V)
  exact congrArg Iso.inv h

end AlgebraicGeometry

end
