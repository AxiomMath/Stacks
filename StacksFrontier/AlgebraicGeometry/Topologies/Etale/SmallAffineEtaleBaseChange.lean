module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.AffineSiteFinalObject
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Base change between small affine étale sites

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of its underlying category with
both `S` and `T` affine. Pulling an affine étale `S`-scheme back along `f` gives an affine étale
`T`-scheme — the fibre product of two affine schemes over an affine scheme is affine — so base
change restricts from the small étale categories to the small *affine* étale categories, and it
is continuous there.

`StacksFrontier/AlgebraicGeometry/Topologies/Etale/SmallEtaleBaseChange.lean` carries base change
and its continuity on the small étale sites. That functor is not usable on the small affine
étale sites without the restriction performed here, because the affine étale objects do not form
a sieve-closed part of the étale ones: base change is what has to be checked to stay inside them.

## Main definitions

* `AlgebraicGeometry.smallAffineEtaleBaseChange` — base change along `f` on small affine étale
  categories.

## Main results

* `AlgebraicGeometry.smallAffineEtaleBaseChange_comp_inclusion` — the restriction composed with
  the inclusion into the small étale category is the small étale base change on the nose, so
  every preservation property transports across an equality of functors rather than across an
  isomorphism.
* `AlgebraicGeometry.smallAffineEtaleBaseChange_isCovering` — base change carries a standard
  étale covering family to one.
* `AlgebraicGeometry.preservesFiniteLimits_smallAffineEtaleBaseChange` and
  `AlgebraicGeometry.smallAffineEtaleBaseChange_isContinuous` — base change preserves finite
  limits, hence is representably flat, hence is continuous for the small affine étale
  topologies.
* `AlgebraicGeometry.smallAffineEtaleBaseChangeId` and
  `AlgebraicGeometry.smallAffineEtaleBaseChangeComp` — **its pseudofunctoriality**: base change
  along an identity is the identity and base change along a composite is the composite of the
  base changes. The small étale forms `AlgebraicGeometry.smallEtaleBaseChangeId` and
  `AlgebraicGeometry.smallEtaleBaseChangeComp`, which are the inputs, are recorded here too.

## Implementation notes

Affineness of the base change is read off the pullback square in schemes: the structure morphism
of an affine étale object over an affine `S` is a morphism of affine schemes, hence affine, and
`AlgebraicGeometry.IsAffineHom` is stable under base change, so the second projection is affine
and its target `T` is affine.

Finite limits are transported along the inclusion of the small affine étale category into the
small étale one, which *creates* fibre products
(`AlgebraicGeometry.createsLimitsOfShape_smallAffineEtaleInclusion`) and carries the final object
of an affine base to the final object; the inclusion is fully faithful, so it reflects limits and
`CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves` applies.

Both pseudofunctoriality isomorphisms are obtained from `CategoryTheory.Over.pullbackId` and
`CategoryTheory.Over.pullbackComp` by cancelling the fully faithful inclusions on the right
(`CategoryTheory.Functor.fullyFaithfulCancelRight`): the composites with the inclusions are
equal to the slice pullbacks on the nose, by `smallAffineEtaleBaseChange_comp_inclusion` and
`AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion`, so no `eqToHom` enters.

## References

* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03PX](https://stacks.math.columbia.edu/tag/03PX)

Tags covered: none.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u})

/-- The source of a pullback square whose left-hand morphism is affine and whose lower-right
corner is affine is itself affine. -/
public lemma isAffine_of_isPullback_of_isAffineHom {P V W Z : Scheme.{u}}
    {p₁ : P ⟶ V} {p₂ : P ⟶ W} {g : V ⟶ Z} {h : W ⟶ Z}
    (sq : IsPullback p₁ p₂ g h) [IsAffineHom g] [IsAffine W] : IsAffine P :=
  let : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom.{u}) :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
  let : IsAffineHom p₂ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  AlgebraicGeometry.isAffine_of_isAffineHom p₂

section

variable {S T : B.Scheme} (f : T ⟶ S) [IsAffine S.obj] [IsAffine T.obj]

/-- The base change along `f` of an affine object of the small étale category of `S` is affine:
its structure morphism to `S` is a morphism of affine schemes, hence affine, and affine
morphisms are stable under base change. -/
public lemma isAffine_smallEtaleBaseChange_obj (X : SmallEtale B S.obj S.property)
    (hX : IsAffine ((SmallEtale.toScheme B S.obj S.property).obj X)) :
    IsAffine
      ((SmallEtale.toScheme B T.obj T.property).obj ((smallEtaleBaseChange B f).obj X)) := by
  have : IsAffine (B.inclusion.obj X.obj.left) := hX
  have : IsAffine (B.inclusion.obj S) := ‹IsAffine S.obj›
  have : IsAffine (B.inclusion.obj T) := ‹IsAffine T.obj›
  exact isAffine_of_isPullback_of_isAffineHom
    ((IsPullback.of_hasPullback X.obj.hom f).map B.inclusion)

/-- **Base change between small affine étale categories.** Along a morphism `f : T ⟶ S` of a big
étale site between affine schemes, base change restricts from the small étale categories to the
small affine étale categories. -/
public noncomputable def smallAffineEtaleBaseChange :
    SmallAffineEtale B S.obj S.property ⥤ SmallAffineEtale B T.obj T.property :=
  (SmallEtale.IsAffine B T.obj T.property).lift
    (SmallAffineEtale.inclusion B S.obj S.property ⋙ smallEtaleBaseChange B f)
    fun X => isAffine_smallEtaleBaseChange_obj B f X.obj X.property

/-- The restriction composed with the inclusion into the small étale category is the small étale
base change, on objects and on morphisms. -/
public theorem smallAffineEtaleBaseChange_comp_inclusion :
    smallAffineEtaleBaseChange B f ⋙ SmallAffineEtale.inclusion B T.obj T.property =
      SmallAffineEtale.inclusion B S.obj S.property ⋙ smallEtaleBaseChange B f :=
  rfl

/-- The underlying object over `T` is the usual pullback of the object over `S`. -/
@[simp]
public theorem smallAffineEtaleBaseChange_obj_obj (X : SmallAffineEtale B S.obj S.property) :
    ((smallAffineEtaleBaseChange B f).obj X).obj.obj = (Over.pullback f).obj X.obj.obj :=
  rfl

/-- **Base change carries a standard étale covering family to a standard étale covering
family.** The underlying family is covering by `AlgebraicGeometry.smallEtaleBaseChange_isCovering`
and the index type is unchanged, so finiteness is preserved. -/
public theorem smallAffineEtaleBaseChange_isCovering
    (E : Covering (SmallAffineEtale B S.obj S.property))
    (hE : SmallAffineEtale.IsCovering B S.obj S.property E) :
    SmallAffineEtale.IsCovering B T.obj T.property
      ⟨(smallAffineEtaleBaseChange B f).obj E.1,
        E.2.map (smallAffineEtaleBaseChange B f)⟩ :=
  ⟨smallEtaleBaseChange_isCovering B f
      ⟨(SmallAffineEtale.inclusion B S.obj S.property).obj E.1,
        E.2.map (SmallAffineEtale.inclusion B S.obj S.property)⟩ hE.1,
    hE.2⟩

/-- The inclusion of the small affine étale category into the small étale category preserves
fibre products: the small affine étale category has them, the composite with the functor to
schemes preserves them, and the functor to schemes reflects them. -/
public instance preservesPullbacks_smallAffineEtaleInclusion :
    PreservesLimitsOfShape WalkingCospan (SmallAffineEtale.inclusion B S.obj S.property) :=
  preservesLimitsOfShape_of_reflects_of_preserves
    (SmallAffineEtale.inclusion B S.obj S.property)
    (SmallEtale.toScheme B S.obj S.property)

/-- The inclusion of the small affine étale category of an affine scheme preserves the final
object: it carries `S / S` to `S / S`. -/
public instance preservesTerminal_smallAffineEtaleInclusion :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SmallAffineEtale.inclusion B S.obj S.property) :=
  Functor.preservesLimitsOfShape_pempty_of_isTerminal _
    (SmallAffineEtale.finalIsTerminal B S.obj S.property)
    (SmallEtale.finalIsTerminal B S.obj S.property)

/-- Base change between small affine étale categories preserves fibre products. -/
public instance preservesPullbacks_smallAffineEtaleBaseChange :
    PreservesLimitsOfShape WalkingCospan (smallAffineEtaleBaseChange B f) := by
  have : PreservesLimitsOfShape WalkingCospan
      (smallAffineEtaleBaseChange B f ⋙ SmallAffineEtale.inclusion B T.obj T.property) := by
    rw [smallAffineEtaleBaseChange_comp_inclusion]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (smallAffineEtaleBaseChange B f) (SmallAffineEtale.inclusion B T.obj T.property)

/-- Base change between small affine étale categories preserves the final object. -/
public instance preservesTerminal_smallAffineEtaleBaseChange :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (smallAffineEtaleBaseChange B f) := by
  have : PreservesLimitsOfShape (Discrete PEmpty.{1})
      (smallAffineEtaleBaseChange B f ⋙ SmallAffineEtale.inclusion B T.obj T.property) := by
    rw [smallAffineEtaleBaseChange_comp_inclusion]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (smallAffineEtaleBaseChange B f) (SmallAffineEtale.inclusion B T.obj T.property)

/-- **Base change between small affine étale categories preserves finite limits.** -/
public instance preservesFiniteLimits_smallAffineEtaleBaseChange :
    PreservesFiniteLimits (smallAffineEtaleBaseChange B f) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- Base change between small affine étale categories is representably flat. -/
public instance representablyFlat_smallAffineEtaleBaseChange :
    RepresentablyFlat (smallAffineEtaleBaseChange B f) :=
  flat_of_preservesFiniteLimits _

/-- Base change between small affine étale categories carries covering sieves to covering
sieves. -/
private lemma coverPreserving_smallAffineEtaleBaseChange :
    CoverPreserving (SmallAffineEtale.topology B S.obj S.property)
      (SmallAffineEtale.topology B T.obj T.property) (smallAffineEtaleBaseChange B f) := by
  apply coverPreserving_of_generators
    (smallAffineEtaleBaseChange B f) (SmallAffineEtale.precoverage B S.obj S.property)
    (SmallAffineEtale.topology B T.obj T.property)
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := (SmallAffineEtale.mem_precoverage_iff B S.obj S.property).1 hR
  rw [← PreZeroHypercover.sieve₀_map]
  exact Precoverage.generate_mem_toGrothendieck
    ((SmallAffineEtale.mem_precoverage_iff B T.obj T.property).2
      ⟨E.map (smallAffineEtaleBaseChange B f), rfl,
        smallAffineEtaleBaseChange_isCovering B f ⟨X, E⟩ hE⟩)

/-- **Base change between small affine étale sites is continuous.** It is representably flat and
carries covering sieves to covering sieves. -/
public instance smallAffineEtaleBaseChange_isContinuous :
    Functor.IsContinuous (smallAffineEtaleBaseChange B f)
      (SmallAffineEtale.topology B S.obj S.property)
      (SmallAffineEtale.topology B T.obj T.property) :=
  Functor.isContinuous_iff_coverPreserving.2 (coverPreserving_smallAffineEtaleBaseChange B f)

end

/-! ### Pseudofunctoriality -/

section Pseudofunctor

variable {S T U : B.Scheme}

/-- Base change along an identity is the identity, on small étale categories. -/
public noncomputable def smallEtaleBaseChangeId :
    smallEtaleBaseChange B (𝟙 S) ≅ 𝟭 (SmallEtale B S.obj S.property) :=
  Functor.fullyFaithfulCancelRight (SmallEtale.inclusion B S.obj S.property)
    (Functor.isoWhiskerLeft (SmallEtale.inclusion B S.obj S.property) Over.pullbackId ≪≫
      (SmallEtale.inclusion B S.obj S.property).rightUnitor ≪≫
      (SmallEtale.inclusion B S.obj S.property).leftUnitor.symm)

/-- Base change along a composite is the composite of the base changes, on small étale
categories. -/
public noncomputable def smallEtaleBaseChangeComp (f : T ⟶ S) (g : U ⟶ T) :
    smallEtaleBaseChange B (g ≫ f) ≅
      smallEtaleBaseChange B f ⋙ smallEtaleBaseChange B g :=
  Functor.fullyFaithfulCancelRight (SmallEtale.inclusion B U.obj U.property)
    (Functor.isoWhiskerLeft (SmallEtale.inclusion B S.obj S.property)
      (Over.pullbackComp g f))

variable [IsAffine S.obj] [IsAffine T.obj] [IsAffine U.obj]

/-- **Base change along an identity is the identity**, on small affine étale categories. -/
public noncomputable def smallAffineEtaleBaseChangeId :
    smallAffineEtaleBaseChange B (𝟙 S) ≅ 𝟭 (SmallAffineEtale B S.obj S.property) :=
  Functor.fullyFaithfulCancelRight (SmallAffineEtale.inclusion B S.obj S.property)
    (Functor.isoWhiskerLeft (SmallAffineEtale.inclusion B S.obj S.property)
        (smallEtaleBaseChangeId B) ≪≫
      (SmallAffineEtale.inclusion B S.obj S.property).rightUnitor ≪≫
      (SmallAffineEtale.inclusion B S.obj S.property).leftUnitor.symm)

/-- **Base change along a composite is the composite of the base changes**, on small affine
étale categories. -/
public noncomputable def smallAffineEtaleBaseChangeComp (f : T ⟶ S) (g : U ⟶ T) :
    smallAffineEtaleBaseChange B (g ≫ f) ≅
      smallAffineEtaleBaseChange B f ⋙ smallAffineEtaleBaseChange B g :=
  Functor.fullyFaithfulCancelRight (SmallAffineEtale.inclusion B U.obj U.property)
    (Functor.isoWhiskerLeft (SmallAffineEtale.inclusion B S.obj S.property)
      (smallEtaleBaseChangeComp B f g))

end Pseudofunctor

end AlgebraicGeometry

end
