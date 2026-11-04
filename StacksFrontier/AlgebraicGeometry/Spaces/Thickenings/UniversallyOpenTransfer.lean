module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective

/-!
# Universal openness against a surjective closed immersion of algebraic spaces

A *thickening* of algebraic spaces over `S` is a surjective closed immersion. This file proves
the two facts about universal openness (**Stacks 03Z2**, part (2)) that a thickening makes
available, and which the diagonal clauses of **Stacks 0BPV** consume:

* a thickening is itself universally open, because a surjective closed embedding of topological
  spaces is a homeomorphism and every base change of a thickening is again one;
* universal openness *cancels* the first factor of a composite whose first factor is surjective.

The second is the cancellation shape that
`AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_spaceCancelFirst` asks for, and only
surjectivity of the first factor is used for it: an open map that factors through a continuous
surjection has open second factor.

## Main results

* `AlgebraicGeometry.Space.isOpenMorphism_of_isClosedImmersion_of_isSurjective`: a surjective
  closed immersion of algebraic spaces over `S` is open on points.
* `AlgebraicGeometry.Space.universallyOpen_of_isClosedImmersion_of_isSurjective`: and is
  universally open.
* `AlgebraicGeometry.Space.exists_isSurjective_comp_pullback_fst`: the comparison over the base
  between the base change of a composite and the base change of its second factor is a base
  change of the first factor, hence surjective when that is.
* `AlgebraicGeometry.Space.universallyOpen_of_isSurjective_comp`: universal openness cancels a
  surjective first factor.
* `AlgebraicGeometry.Space.universallyOpen_isLocalAtTarget_fppf`: **Stacks 041P** read at the
  fppf precoverage, which is the instance the relative properties of **Stacks 03YK** ask for.

## Implementation notes

`AlgebraicGeometry.Space.exists_isSurjective_comp_pullback_fst` is the geometry shared by every
cancellation of this shape: the same comparison morphism is built inside
`AlgebraicGeometry.Space.universallyClosed_of_isSurjective_comp` (**Stacks 08AJ**) and inside
`AlgebraicGeometry.Space.universallyInjective_of_isSurjective_comp`, each time from scratch.
Only the new cancellation below is routed through it; pointing the other two at it would invert
the import order of `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper` and this file.

The point topology of Stacks 03BX is a local instance here, as in the other files about openness
on points.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03Z2](https://stacks.math.columbia.edu/tag/03Z2)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Target-locality at the fppf precoverage -/

/-- **Stacks 041P at the fppf precoverage.** Universal openness, as a property of morphisms of
algebraic spaces over `S`, is local on the target for the fppf precoverage.

The relative properties of **Stacks 03YK** are stated at the fppf precoverage and take locality
at the target as an instance argument, so this is what instance search needs in order to state
them for this property; the content is the fpqc statement
`AlgebraicGeometry.Space.universallyOpen_isLocalAtTarget_fpqc`. -/
instance universallyOpen_isLocalAtTarget_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (universallyOpenMorphismProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, u} B S hS) :=
  (universallyOpen_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
    (fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A surjective closed immersion is universally open -/

section Thickening

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A surjective closed immersion of algebraic spaces over `S` is open on points.** The map it
induces on the point spaces of Stacks 03BX is a closed embedding — an embedding by **Stacks
0ABJ** and with closed image by **Stacks 04CD** — and a surjective closed embedding of
topological spaces is a homeomorphism. -/
theorem isOpenMorphism_of_isClosedImmersion_of_isSurjective
    (hX : IsAlgebraicSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (hsurj : IsSurjective B S hS i) :
    IsOpenMorphism B S hS i := by
  have hemb : Topology.IsClosedEmbedding (pointsMap B S hS Y i) :=
    ⟨isEmbedding_pointsMap_of_isImmersion B S hS hX i
        (isImmersion_of_isClosedImmersion B S hS hi),
      isClosed_range_pointsMap_of_isClosedImmersion B S hS hX i hi⟩
  exact (isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨continuous_pointsMap B S hS i, hemb.isClosedMap, hemb.injective, hsurj⟩).isOpenMap

/-- **A surjective closed immersion of algebraic spaces over `S` is universally open.** Every
base change of it is again a surjective closed immersion — being a closed immersion by **Stacks
02YW** and surjective by **Stacks 03MH** — so
`AlgebraicGeometry.Space.isOpenMorphism_of_isClosedImmersion_of_isSurjective` applies to each.

This is the universally open clause of a thickening of algebraic spaces, the input the universal
openness part of **Stacks 09ZY** needs for the comparison morphism. -/
theorem universallyOpen_of_isClosedImmersion_of_isSurjective
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (hsurj : IsSurjective B S hS i) :
    UniversallyOpen B S hS i := by
  intro W hW k
  exact isOpenMorphism_of_isClosedImmersion_of_isSurjective B S hS hW
    (isClosedImmersion_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk k : (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
        (ObjectProperty.homMk i : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)).flip hi)
    (isSurjective_pullback_fst B S hS hW hX hY k i hsurj)

end Thickening

/-! ### Cancelling a surjective first factor -/

section Cancel

variable {X Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The comparison of two base changes along one morphism to the base.** For morphisms
`f : X ⟶ Y` and `q : Y ⟶ T` of algebraic spaces over `S` and `k : W ⟶ T`, the base change
`W ×_T X` of the composite maps to the base change `W ×_T Y` of the second factor over `W`, and
that comparison is a base change of `f`, hence surjective when `f` is (**Stacks 03MH**). -/
theorem exists_isSurjective_comp_pullback_fst
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (f : X ⟶ Y) (q : Y ⟶ T)
    (hf : IsSurjective B S hS f) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (k : W ⟶ T) :
    ∃ r : pullback k (f ≫ q) ⟶ pullback k q,
      r ≫ pullback.fst k q = pullback.fst k (f ≫ q) ∧ IsSurjective B S hS r := by
  set r : pullback k (f ≫ q) ⟶ pullback k q :=
    pullback.lift (pullback.fst k (f ≫ q)) (pullback.snd k (f ≫ q) ≫ f)
      (by rw [Category.assoc, pullback.condition])
  have hrfst : r ≫ pullback.fst k q = pullback.fst k (f ≫ q) := pullback.lift_fst _ _ _
  have hsquare : IsPullback r (pullback.snd k (f ≫ q)) (pullback.snd k q) f :=
    IsPullback.of_right (by rw [hrfst]; exact IsPullback.of_hasPullback k (f ≫ q))
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback k q)
  refine ⟨r, hrfst, ?_⟩
  let Rₐ : AlgebraicSpaces B S hS :=
    ⟨pullback k (f ≫ q), isAlgebraicSpace_pullback B S hS k (f ≫ q) hW hX hT⟩
  let Pₐ : AlgebraicSpaces B S hS := ⟨pullback k q, isAlgebraicSpace_pullback B S hS k q hW hY hT⟩
  let Xₐ : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Yₐ : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  have hA : IsPullback
      (ObjectProperty.homMk (pullback.snd k (f ≫ q)) : Rₐ ⟶ Xₐ)
      (ObjectProperty.homMk r : Rₐ ⟶ Pₐ)
      (ObjectProperty.homMk f : Xₐ ⟶ Yₐ)
      (ObjectProperty.homMk (pullback.snd k q) : Pₐ ⟶ Yₐ) :=
    IsPullback.of_map (ObjectProperty.ι _)
      (ObjectProperty.hom_ext _ hsquare.flip.w) hsquare.flip
  exact isSurjective_of_isPullback B S hS hA hf

/-- **Universal openness cancels a surjective first factor.** Let `X ⟶ Y ⟶ T` be morphisms of
algebraic spaces over `S`. If the composite is universally open and `X ⟶ Y` is surjective then
`Y ⟶ T` is universally open.

A base change of the composite maps onto the corresponding base change of the second factor by a
surjection (`AlgebraicGeometry.Space.exists_isSurjective_comp_pullback_fst`), and an open map
that factors through a continuous surjection has open second factor. This is the universal
openness counterpart of `AlgebraicGeometry.Space.universallyClosed_of_isSurjective_comp`
(**Stacks 08AJ**), and the cancellation that the universal openness part of **Stacks 09ZY**
needs. -/
theorem universallyOpen_of_isSurjective_comp
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (f : X ⟶ Y) (q : Y ⟶ T)
    (hfq : UniversallyOpen B S hS (f ≫ q)) (hf : IsSurjective B S hS f) :
    UniversallyOpen B S hS q := by
  intro W hW k
  obtain ⟨r, hrfst, hrsurj⟩ :=
    exists_isSurjective_comp_pullback_fst B S hS hX hY hT f q hf hW k
  refine IsOpenMap.of_comp (continuous_pointsMap B S hS r) hrsurj ?_
  have hgoal : IsOpenMap (pointsMap B S hS (pullback k (f ≫ q)) (r ≫ pullback.fst k q)) := by
    rw [hrfst]
    exact hfq W hW k
  rwa [pointsMap_comp] at hgoal

end Cancel

end AlgebraicGeometry.Space

end
