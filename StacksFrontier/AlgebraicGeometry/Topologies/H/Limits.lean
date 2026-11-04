module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineCreatesPullbacks
public import StacksFrontier.AlgebraicGeometry.Topologies.H.BigSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibre products and a final object in the h sites

Let `B` be a big h site containing a scheme `S`. The underlying category of `B`, the big h
category over `S`, and the big affine h category over `S` all admit fibre products, and the
canonical functors from each of them to schemes preserve fibre products. The big h category
over `S` moreover has `S / S` as a final object.

This is what makes these categories sites in the strong sense: having fibre products, the
base-change axiom can be stated using honest fibre products, and the final object gives the
terminal sheaf.

## Main definitions

* `AlgebraicGeometry.BigHOver.final` — the object `S / S` of the big h category over `S`.

## Main results

* `AlgebraicGeometry.hasPullbacks_bigHSite`,
  `AlgebraicGeometry.hasPullbacks_bigHOver` and
  `AlgebraicGeometry.hasPullbacks_bigAffineH` give fibre products in the three categories.
* `AlgebraicGeometry.preservesPullbacks_bigHSiteInclusion`,
  `AlgebraicGeometry.preservesPullbacks_bigHOverToScheme` and
  `AlgebraicGeometry.preservesPullbacks_bigAffineHToScheme` say that the canonical functors
  to schemes preserve fibre products.
* `AlgebraicGeometry.BigHOver.finalIsTerminal` identifies `S / S` as final in the big h
  category over `S`.
* `AlgebraicGeometry.bigHSites_hasPullbacks_preservesPullbacks_final` — Stacks 0EU3 in full:
  all of the above in one statement.

## Implementation notes

The big h category over `S` is definitionally a slice of the size-bounded category, so its
fibre products and its final object are Mathlib's general results for slice categories;
preservation of fibre products by the composite functor to schemes then follows from
preservation by its two factors.

Fibre products in the size-bounded category of `B` and in its affine full subcategory are
obtained by *creating* them: the fibre product is formed in the larger category and the
cutoff or affineness condition is checked on it — a fibre product of schemes below a
cardinal cutoff is again below it, by Stacks 000R (1), and a fibre product of affines is
affine.

## References

* [Stacks Project, Tag 0EU3](https://stacks.math.columbia.edu/tag/0EU3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private noncomputable instance createsPullbacks_bigHSite :
    CreatesLimitsOfShape WalkingCospan B.inclusion where
  CreatesLimit := fun {F} => by
    let D := F ⋙ B.inclusion
    let t := pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    exact createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm (limit.isLimit _))
      (Scheme.size_pullback_lt _ _ (F.obj .left).property (F.obj .right).property)

/-- The underlying category of a big h site admits fibre products. -/
public instance hasPullbacks_bigHSite : HasPullbacks B.Schemes :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape B.inclusion

/-- The big h category over `S` admits fibre products. -/
public instance hasPullbacks_bigHOver : HasPullbacks (BigHOver B S hS) :=
  inferInstance

private noncomputable instance createsPullbacks_bigAffineH :
    CreatesLimitsOfShape WalkingCospan (BigAffineH.inclusion B S hS) :=
  affineCreatesPullbacks (BigHOver.toScheme B S hS)

/-- The big affine h category over `S` admits fibre products. -/
public instance hasPullbacks_bigAffineH : HasPullbacks (BigAffineH B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (BigAffineH.inclusion B S hS)

/-- The inclusion of a big h site's underlying category into all schemes
preserves fibre products. -/
public instance preservesPullbacks_bigHSiteInclusion :
    PreservesLimitsOfShape WalkingCospan B.inclusion :=
  inferInstance

/-- The canonical functor from the big h category over `S` to schemes
preserves fibre products. -/
public instance preservesPullbacks_bigHOverToScheme :
    PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS) := by
  apply comp_preservesLimitsOfShape

/-- The canonical functor from the big affine h category over `S` to
schemes preserves fibre products. -/
public instance preservesPullbacks_bigAffineHToScheme :
    PreservesLimitsOfShape WalkingCospan (BigAffineH.toScheme B S hS) :=
  inferInstance

/-- The object `S / S`, with identity structure morphism, of the big h category over `S`. -/
public abbrev BigHOver.final : BigHOver B S hS := Over.mk (𝟙 (B.obj S hS))

/-- The object `S / S` is final in the big h category over `S`. -/
public noncomputable def BigHOver.finalIsTerminal :
    IsTerminal (BigHOver.final B S hS) :=
  Over.mkIdTerminal

/-- The big h category over `S` has a final object. -/
public instance hasTerminal_bigHOver : HasTerminal (BigHOver B S hS) :=
  (BigHOver.finalIsTerminal B S hS).hasTerminal

/-- The big h category over `S` admits all finite limits: it has a final object and fibre
products. -/
public instance hasFiniteLimits_bigHOver : HasFiniteLimits (BigHOver B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- **Stacks 0EU3.** Let `B` be a big h site containing the scheme `S`. The underlying
categories of the big h site, of the big h site over `S`, and of the big affine h site over `S`
have fibre products; in each case the canonical functor to the category of all schemes
commutes with fibre products; and `S / S` is a final object of the big h site over `S`. -/
@[stacks 0EU3]
public theorem bigHSites_hasPullbacks_preservesPullbacks_final :
    (HasPullbacks B.Schemes ∧ HasPullbacks (BigHOver B S hS) ∧
        HasPullbacks (BigAffineH B S hS)) ∧
      (PreservesLimitsOfShape WalkingCospan B.inclusion ∧
        PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS) ∧
        PreservesLimitsOfShape WalkingCospan (BigAffineH.toScheme B S hS)) ∧
      Nonempty (IsTerminal (Over.mk (𝟙 (B.obj S hS)) : BigHOver B S hS)) :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance⟩, ⟨BigHOver.finalIsTerminal B S hS⟩⟩

end AlgebraicGeometry

end
