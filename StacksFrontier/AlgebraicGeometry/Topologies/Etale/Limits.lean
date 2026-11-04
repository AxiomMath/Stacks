module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineCreatesPullbacks
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# Fibre products and final objects in the étale sites

Let `B` be a big étale site containing a scheme `S`. The underlying category of `B`, the big
and small étale categories over `S`, and their affine full subcategories all admit fibre
products, and the canonical functors from them to schemes preserve fibre products. The big and
small étale categories over `S` also have `S / S` as a final object.

This is what makes these categories sites in the strong sense: having fibre products, the
base-change axiom can be stated using honest fibre products, and the final object gives the
terminal sheaf.

## Main definitions

* `AlgebraicGeometry.SmallEtale.final` — the object `S / S` of the small étale category.

## Main results

* The `hasPullbacks_*` instances give fibre products in the four full subcategories for which
  this is not already supplied by the general theory of slice categories.
* The `preservesPullbacks_*` instances say that the relevant canonical functors preserve fibre
  products.
* `AlgebraicGeometry.SmallEtale.finalIsTerminal` identifies `S / S` as final in the small
  étale category.
* `AlgebraicGeometry.hasFiniteLimits_smallEtale` concludes that the small étale category has
  all finite limits.

## Implementation notes

The big étale category over `S` is definitionally a slice, so its fibre products, the
preservation of fibre products by its forgetful functor, and its final object are exactly
Mathlib's general results for slice categories; those declarations are referenced directly
rather than restated. Preservation by the composite functor from that slice to schemes then
follows from preservation by its two factors.

Fibre products in the size-bounded category of `B` and in the affine full subcategories are
obtained by *creating* them: the fibre product is formed in the larger category and the cutoff
or affineness condition is checked on it — a fibre product of schemes below a cardinal cutoff
is again below it, and a fibre product of affines is affine. The remaining preservation
statements are given for the canonical functors to schemes, which is the form the subsequent
site constructions use.

## References

* [Stacks Project, Tag 021D](https://stacks.math.columbia.edu/tag/021D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private noncomputable instance createsPullbacks_bigEtaleSite :
    CreatesLimitsOfShape WalkingCospan B.inclusion where
  CreatesLimit := fun {F} => by
    let D := F ⋙ B.inclusion
    let t := pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    exact createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm (limit.isLimit _))
      (Scheme.size_pullback_lt _ _ (F.obj .left).property (F.obj .right).property)

/-- The underlying category of a big étale site admits fibre products. -/
@[stacks 021D "fibre products in the big étale site"]
public instance hasPullbacks_bigEtaleSite : HasPullbacks B.Scheme :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape B.inclusion

private abbrev EtaleInBigSite (B : AlgebraicGeometry.BigEtaleSite.{u}) :
    MorphismProperty B.Scheme := MorphismProperty.inverseImage (@Etale) B.inclusion

private instance : (EtaleInBigSite B).IsStableUnderComposition where
  comp_mem f g hf hg := by
    simpa only [EtaleInBigSite, MorphismProperty.inverseImage, Functor.map_comp] using
      (@Etale.etale_comp _ _ (B.inclusion.map f) _ (B.inclusion.map g) hf hg)

private instance : (EtaleInBigSite B).IsStableUnderBaseChange where
  of_isPullback h hg := by
    change Etale _ at hg ⊢
    exact MorphismProperty.of_isPullback (P := @Etale) (h.map B.inclusion) hg

private instance : (EtaleInBigSite B).HasOfPostcompProperty (EtaleInBigSite B) where
  of_postcomp f g hg hfg := by
    change Etale (B.inclusion.map (f ≫ g)) at hfg
    apply MorphismProperty.of_postcomp @Etale (B.inclusion.map f) (B.inclusion.map g) hg
    simpa only [Functor.map_comp] using hfg

add_to_stacks 021D "fibre products in the big étale slice"
  CategoryTheory.Over.instHasPullbacks

/-- The small étale category of `S` admits fibre products. -/
@[stacks 021D "fibre products in the small étale site"]
public instance hasPullbacks_smallEtale :
    HasPullbacks (SmallEtale B S hS) := by
  change HasPullbacks (((EtaleInBigSite B).overObj (X := B.obj S hS)).FullSubcategory)
  infer_instance

/-- The full inclusion of the small étale category into the big étale category over `S`
preserves fibre products. -/
public instance preservesPullbacks_smallEtaleInclusion :
    PreservesLimitsOfShape WalkingCospan (SmallEtale.inclusion B S hS) := by
  change PreservesLimitsOfShape WalkingCospan
    (((EtaleInBigSite B).overObj (X := B.obj S hS)).ι)
  infer_instance

/-- The canonical functor from the small étale category of `S` to schemes preserves fibre
products. -/
@[stacks 021D "preservation by the small étale functor to schemes"]
public instance preservesPullbacks_smallEtaleToScheme :
    PreservesLimitsOfShape WalkingCospan (SmallEtale.toScheme B S hS) := by
  apply comp_preservesLimitsOfShape

private noncomputable instance createsPullbacks_bigAffineEtale :
    CreatesLimitsOfShape WalkingCospan (BigAffineEtale.inclusion B S hS) :=
  affineCreatesPullbacks (BigEtaleOver.toScheme B S hS)

/-- The category of affine objects in the big étale category over `S` admits fibre
products. -/
@[stacks 021D "fibre products in the big affine étale site"]
public instance hasPullbacks_bigAffineEtale :
    HasPullbacks (BigAffineEtale B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (BigAffineEtale.inclusion B S hS)

private noncomputable instance createsPullbacks_smallAffineEtale :
    CreatesLimitsOfShape WalkingCospan (SmallAffineEtale.inclusion B S hS) :=
  affineCreatesPullbacks (SmallEtale.toScheme B S hS)

/-- The affine small étale category of `S` admits fibre products. -/
@[stacks 021D "fibre products in the affine small étale site"]
public instance hasPullbacks_smallAffineEtale :
    HasPullbacks (SmallAffineEtale B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (SmallAffineEtale.inclusion B S hS)

/-- The inclusion of a big étale site's underlying category into schemes preserves fibre
products. -/
@[stacks 021D "preservation by the big étale site inclusion"]
public instance preservesPullbacks_bigEtaleSiteInclusion :
    PreservesLimitsOfShape WalkingCospan B.inclusion := by infer_instance

add_to_stacks 021D "preservation by the big étale slice forgetful functor"
  CategoryTheory.Over.preservesLimitsOfShape_forget_of_isConnected

add_to_stacks 021D "preservation under composition for the big étale slice functor"
  CategoryTheory.Limits.comp_preservesLimitsOfShape

/-- The canonical functor from affine objects over `S` to schemes preserves fibre products. -/
@[stacks 021D "preservation by the big affine étale functor to schemes"]
public instance preservesPullbacks_bigAffineEtaleToScheme :
    PreservesLimitsOfShape WalkingCospan (BigAffineEtale.toScheme B S hS) := by
  infer_instance

/-- The canonical functor from the affine small étale category of `S` to schemes preserves
fibre products. -/
@[stacks 021D "preservation by the affine small étale functor to schemes"]
public instance preservesPullbacks_smallAffineEtaleToScheme :
    PreservesLimitsOfShape WalkingCospan
      (SmallAffineEtale.toScheme B S hS) := by
  infer_instance

add_to_stacks 021D "the final object of the big étale slice"
  CategoryTheory.Over.mkIdTerminal

/-- The object `S / S`, with identity structure morphism, in the small étale category. -/
public def SmallEtale.final : SmallEtale B S hS :=
  ⟨Over.mk (𝟙 (B.obj S hS)), by
    dsimp [BigEtaleOver.IsEtaleOver]
    infer_instance⟩

/-- The object `S / S` is final in the small étale category of `S`. -/
@[stacks 021D "the final object of the small étale site"]
public noncomputable def SmallEtale.finalIsTerminal :
    IsTerminal (SmallEtale.final B S hS) :=
  IsTerminal.ofUniqueHom (fun X => ObjectProperty.homMk (Over.homMk X.obj.hom)) fun _ _ =>
    (SmallEtale.inclusion B S hS).map_injective
      ((Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj S hS)))).hom_ext _ _)

/-- The small étale category has a final object. -/
public instance hasTerminal_smallEtale :
    HasTerminal (SmallEtale B S hS) :=
  (SmallEtale.finalIsTerminal B S hS).hasTerminal

/-- The small étale category of `S` admits all finite limits: it has a final object and fibre
products. -/
public instance hasFiniteLimits_smallEtale :
    HasFiniteLimits (SmallEtale B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The inclusion of the small étale category carries its final object to the
final object of the big étale slice. -/
@[stacks 021G "preservation of the final object"]
public instance smallEtaleInclusion_preservesTerminal :
    PreservesLimit (Functor.empty.{0} (SmallEtale B S hS))
      (SmallEtale.inclusion B S hS) := by
  apply preservesTerminal_of_iso (SmallEtale.inclusion B S hS)
  have ht : IsTerminal ((SmallEtale.inclusion B S hS).obj (SmallEtale.final B S hS)) := by
    simpa [SmallEtale.inclusion, SmallEtale.final] using
      (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj S hS))))
  exact (SmallEtale.inclusion B S hS).mapIso
      ((terminalIsTerminal (C := SmallEtale B S hS)).uniqueUpToIso
        (SmallEtale.finalIsTerminal B S hS)) ≪≫
    ht.uniqueUpToIso (terminalIsTerminal (C := BigEtaleOver B S hS))

end AlgebraicGeometry
