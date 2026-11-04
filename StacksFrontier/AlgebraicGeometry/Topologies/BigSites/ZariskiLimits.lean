module

public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineCreatesPullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites

/-!
# Fibre products and final objects in the Zariski sites

Let `B` be a big Zariski site containing a scheme `S`. The underlying category of `B`, the
big and small Zariski categories over `S`, and their affine full subcategories all admit
fibre products, and the canonical functors from them to schemes preserve fibre products. The
big and small Zariski categories over `S` also have `S / S` as a final object.

Having fibre products is what lets the base-change axiom of a site be stated with honest
fibre products, and the final object is what gives the terminal sheaf.

## Main definitions

* `AlgebraicGeometry.SmallZariski.final` — the object `S / S` of the small Zariski category.

## Main results

* The `hasPullbacks_*` instances give fibre products in the categories for which this is not
  already supplied by the general theory of slice categories.
* The `preservesPullbacks_*` instances say that the relevant canonical functors preserve
  fibre products, and `AlgebraicGeometry.preservesTerminal_smallZariskiInclusion` says that
  the inclusion of the small Zariski category preserves the final object.
* `AlgebraicGeometry.SmallZariski.finalIsTerminal` identifies `S / S` as final in the small
  Zariski category.

## Implementation notes

The big Zariski category over `S` is definitionally a slice, so its fibre products, the
preservation of fibre products by its forgetful functor, and its final object are Mathlib's
general results for slice categories; those declarations are referenced directly rather than
restated.

Fibre products in the size-bounded category of `B` and in the affine full subcategories are
obtained by *creating* them: the fibre product is formed in the larger category and the
cutoff or affineness condition is checked on it — a fibre product of schemes below a cardinal
cutoff is again below it, and a fibre product of affines is affine. In the small Zariski
category the condition is instead that the structure morphism is an open immersion, which is
stable under base change and has the two-out-of-three property needed for the slice to be
closed under fibre products.

## References

* [Stacks Project, Tag 020V](https://stacks.math.columbia.edu/tag/020V)
* [Stacks Project, Tag 020Z](https://stacks.math.columbia.edu/tag/020Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private noncomputable instance createsPullbacks_bigZariskiSite :
    CreatesLimitsOfShape WalkingCospan B.inclusion where
  CreatesLimit := fun {F} => by
    let D := F ⋙ B.inclusion
    let t := pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    exact createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm (limit.isLimit _))
      (Scheme.size_pullback_lt _ _ (F.obj .left).property (F.obj .right).property)

/-- Morphisms of a big Zariski site whose image in schemes is an open immersion. -/
private abbrev OpenInBigZariskiSite (B : BigZariskiSite.{u}) :
    MorphismProperty B.Schemes := MorphismProperty.inverseImage (@IsOpenImmersion) B.inclusion

private instance openInBigZariskiSite_isStableUnderBaseChange (B : BigZariskiSite.{u}) :
    (OpenInBigZariskiSite B).IsStableUnderBaseChange where
  of_isPullback h hg := by
    change IsOpenImmersion (B.inclusion.map _) at hg ⊢
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (h.map B.inclusion) hg

private instance openInBigZariskiSite_hasOfPostcompProperty (B : BigZariskiSite.{u}) :
    (OpenInBigZariskiSite B).HasOfPostcompProperty (OpenInBigZariskiSite B) where
  of_postcomp f g hg hfg := by
    change IsOpenImmersion (B.inclusion.map (f ≫ g)) at hfg
    apply MorphismProperty.of_postcomp @IsOpenImmersion (B.inclusion.map f)
      (B.inclusion.map g) hg
    simpa only [Functor.map_comp] using hfg

/-- The underlying category of a big Zariski site has fibre products. -/
@[stacks 020V "fibre products in the big Zariski site"]
public instance hasPullbacks_bigZariskiSite : HasPullbacks B.Schemes :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape B.inclusion

private instance openZariskiOver_closedUnderPullbacks (B : BigZariskiSite.{u})
    (X : B.Schemes) :
    (OpenInBigZariskiSite B).overObj (X := X).IsClosedUnderLimitsOfShape WalkingCospan :=
  Over.closedUnderLimitsOfShape_pullback (P := OpenInBigZariskiSite B) (X := X)

add_to_stacks 020V "fibre products in the big Zariski slice"
  CategoryTheory.Over.instHasPullbacks

/-- The small Zariski category of `S` has fibre products. -/
@[stacks 020V "fibre products in the small Zariski site"]
public instance hasPullbacks_smallZariski : HasPullbacks (SmallZariski B S hS) := by
  let P := OpenInBigZariskiSite B
  change HasPullbacks ((P.overObj (X := (⟨S, hS⟩ : B.Schemes))).FullSubcategory)
  exact hasLimitsOfShape_of_closedUnderLimits WalkingCospan
    (P.overObj (X := (⟨S, hS⟩ : B.Schemes)))

/-- The full inclusion of the small Zariski category into the big Zariski category over `S`
preserves fibre products. -/
@[stacks 020Z "preservation of site pullbacks"]
public instance preservesPullbacks_smallZariskiInclusion :
    PreservesLimitsOfShape WalkingCospan (SmallZariski.inclusion B S hS) := by
  let P := OpenInBigZariskiSite B
  change PreservesLimitsOfShape WalkingCospan (P.overObj (X := (⟨S, hS⟩ : B.Schemes))).ι
  infer_instance

private noncomputable instance createsPullbacks_bigAffineZariskiInclusion :
    CreatesLimitsOfShape WalkingCospan (BigAffineZariski.inclusion B S hS) :=
  affineCreatesPullbacks (BigZariskiOver.toScheme B S hS)

/-- The category of affine objects in the big Zariski category over `S` has fibre products. -/
@[stacks 020V "fibre products in the big affine Zariski site"]
public instance hasPullbacks_bigAffineZariski : HasPullbacks (BigAffineZariski B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (BigAffineZariski.inclusion B S hS)

private noncomputable instance createsPullbacks_smallAffineZariskiInclusion :
    CreatesLimitsOfShape WalkingCospan (SmallAffineZariski.inclusion B S hS) := by
  let G := SmallZariski.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan G := by
    change PreservesLimitsOfShape WalkingCospan
      (SmallZariski.inclusion B S hS ⋙ BigZariskiOver.toScheme B S hS)
    apply comp_preservesLimitsOfShape
  exact affineCreatesPullbacks G

/-- The affine small Zariski category of `S` has fibre products. -/
@[stacks 020V "fibre products in the small affine Zariski site"]
public instance hasPullbacks_smallAffineZariski : HasPullbacks (SmallAffineZariski B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (SmallAffineZariski.inclusion B S hS)

/-- The inclusion of a big Zariski site's underlying category into schemes preserves fibre
products. -/
@[stacks 020V "preservation by the big Zariski site inclusion"]
public instance preservesPullbacks_bigZariskiSiteInclusion :
    PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance

add_to_stacks 020V "preservation by the big Zariski slice forgetful functor"
  CategoryTheory.Over.preservesLimitsOfShape_forget_of_isConnected
add_to_sga "4 IV 5.10" "more general"
  CategoryTheory.Over.preservesLimitsOfShape_forget_of_isConnected
add_to_sga "4 IV 5.3" "partial" CategoryTheory.Over.preservesLimitsOfShape_forget_of_isConnected

add_to_stacks 020V "preservation under composition for the big Zariski slice functor"
  CategoryTheory.Limits.comp_preservesLimitsOfShape

/-- The canonical functor from the small Zariski category to schemes preserves fibre
products. -/
@[stacks 020V "preservation by the small Zariski functor to schemes"]
public instance preservesPullbacks_smallZariskiToScheme :
    PreservesLimitsOfShape WalkingCospan (SmallZariski.toScheme B S hS) := by
  let P := OpenInBigZariskiSite B
  change PreservesLimitsOfShape WalkingCospan
    ((P.overObj (X := (⟨S, hS⟩ : B.Schemes))).ι ⋙ BigZariskiOver.toScheme B S hS)
  apply comp_preservesLimitsOfShape

/-- The canonical functor from affine objects over `S` to schemes preserves fibre products. -/
@[stacks 020V "preservation by the big affine Zariski functor to schemes"]
public instance preservesPullbacks_bigAffineZariskiToScheme :
    PreservesLimitsOfShape WalkingCospan (BigAffineZariski.toScheme B S hS) := inferInstance

/-- The canonical functor from affine open objects over `S` to schemes preserves fibre
products. -/
@[stacks 020V "preservation by the small affine Zariski functor to schemes"]
public instance preservesPullbacks_smallAffineZariskiToScheme :
    PreservesLimitsOfShape WalkingCospan (SmallAffineZariski.toScheme B S hS) := inferInstance

add_to_stacks 020V "the final object of the big Zariski slice"
  CategoryTheory.Over.mkIdTerminal

/-- The object `S / S`, with identity structure morphism, in the small Zariski category. -/
public def SmallZariski.final : SmallZariski B S hS :=
  ⟨Over.mk (𝟙 (⟨S, hS⟩ : B.Schemes)), by
    dsimp [IsOpenOver]
    infer_instance⟩

/-- The object `S / S` is final in the small Zariski category of `S`. -/
@[stacks 020V "the final object of the small Zariski site"]
public noncomputable def SmallZariski.finalIsTerminal :
    IsTerminal (SmallZariski.final B S hS) :=
  IsTerminal.ofUniqueHom (fun X => ObjectProperty.homMk (Over.homMk X.obj.hom)) fun _ _ =>
    (SmallZariski.inclusion B S hS).map_injective <|
      (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (⟨S, hS⟩ : B.Schemes)))).hom_ext _ _

/-- The small Zariski category has a final object. -/
public instance hasTerminal_smallZariski : HasTerminal (SmallZariski B S hS) :=
  (SmallZariski.finalIsTerminal B S hS).hasTerminal

/-- The full inclusion of the small Zariski category into the big Zariski category over `S`
carries `S / S` to the final object of the slice, hence preserves the final object. -/
@[stacks 020Z "preservation of the final object"]
public instance preservesTerminal_smallZariskiInclusion :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (SmallZariski.inclusion B S hS) := by
  let i := SmallZariski.inclusion B S hS
  have ht : IsTerminal (i.obj (SmallZariski.final B S hS)) := by
    simpa [i, SmallZariski.inclusion, SmallZariski.final] using
      (Over.mkIdTerminal (X := (⟨S, hS⟩ : B.Schemes)))
  have : PreservesLimit (Functor.empty.{0} (SmallZariski B S hS)) i :=
    preservesTerminal_of_iso i
      (i.mapIso ((terminalIsTerminal (C := SmallZariski B S hS)).uniqueUpToIso
        (SmallZariski.finalIsTerminal B S hS)) ≪≫ ht.uniqueUpToIso terminalIsTerminal)
  exact preservesLimitsOfShape_pempty_of_preservesTerminal i

end AlgebraicGeometry
