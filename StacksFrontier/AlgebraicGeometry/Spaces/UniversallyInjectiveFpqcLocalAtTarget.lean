module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# Universal injectivity of morphisms of algebraic spaces is fpqc local on the base

A morphism of algebraic spaces over `S` is universally injective when every base change of it
along an algebraic space induces an injective map on the points of Stacks 03BU; this is
Stacks 03MV. This file proves that the property is local on the base for the fpqc topology of
Stacks 03YH, which is **Stacks 041R**.

Universal injectivity is being universally injective on points, so the ascent half is formal.
The descent half rests on one observation about points: in a cartesian square a point of the
source and a point of the base lying over a common point of the target amalgamate to a point of
the fibre product (Stacks 03H4). Given two points of `X` with the same image in `Y`, lift that
image along the fpqc covering and amalgamate each of the two points with the lift; the two
amalgamations have the same image in the member of the covering, so the local injectivity
hypothesis identifies them, and projecting back identifies the original two points.

## Main definitions

* `AlgebraicGeometry.Space.injectiveOnPointsProperty`: injectivity of the induced map on points
  as a `CategoryTheory.MorphismProperty` on `AlgebraicGeometry.AlgebraicSpaces`.
* `AlgebraicGeometry.Space.universallyInjectiveMorphismProperty`: universal injectivity
  (Stacks 03MV) as a `CategoryTheory.MorphismProperty` on
  `AlgebraicGeometry.AlgebraicSpaces`, the companion of
  `AlgebraicGeometry.Space.universallyOpenMorphismProperty`.

## Main results

* `AlgebraicGeometry.Space.universallyInjective_iff_universally_injectiveOnPoints`: universal
  injectivity is being universally injective on points.
* `AlgebraicGeometry.Space.injective_pointsMap_of_fpqcCovering`: injectivity on points is
  itself local on the base for the fpqc topology.
* `AlgebraicGeometry.Space.universallyInjective_isLocalAtTarget_fpqc`: **Stacks 041R**.

## Implementation notes

Both halves of "fpqc local on the base" are carried by
`CategoryTheory.MorphismProperty.IsLocalAtTarget`: its `pullbackSnd` field is the ascent and
its `of_forall_pullbackSnd` field the descent. The ascent half here is
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for a `universally`-closed property,
as for the sibling results in `StacksFrontier/AlgebraicGeometry/Spaces/Descent/Fpqc/`.

The source argument reduces to the affine case through Stacks 041J and then descends along a
surjective flat morphism of affine schemes using the field-valued criterion of Stacks 03MU.
The argument here instead descends directly, on the points of Stacks 03BU, which is where the
field-valued criterion lives anyway; no hypothesis beyond the covering is carried.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03MU](https://stacks.math.columbia.edu/tag/03MU)
* [Stacks Project, Tag 03MV](https://stacks.math.columbia.edu/tag/03MV)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041R](https://stacks.math.columbia.edu/tag/041R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Injectivity on points as a property of morphisms of algebraic spaces -/

/-- Injectivity of the map induced on the points of Stacks 03BU, as a property of morphisms in
the category of algebraic spaces over `S`. -/
abbrev injectiveOnPointsProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun X _ f ↦ Function.Injective (pointsMap B S hS X.obj f.hom)

/-- Universal injectivity (**Stacks 03MV**), as a property of morphisms in the category of
algebraic spaces over `S`. -/
abbrev universallyInjectiveMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f ↦ UniversallyInjective B S hS f.hom

/-- Being universally injective (**Stacks 03MV**) is being universally injective on points: the
chosen fibre product of Stacks 02X2 realises each of the base changes that the definition
tests, and the comparison isomorphism of two cartesian squares on one cospan carries
injectivity on points between them. -/
theorem universallyInjective_iff_universally_injectiveOnPoints
    {X T : AlgebraicSpaces B S hS} (f : X ⟶ T) :
    UniversallyInjective B S hS f.hom ↔ (injectiveOnPointsProperty B S hS).universally f := by
  constructor
  · intro hf X' T' i₁ i₂ f' sq
    have hsq : IsPullback f'.hom i₁.hom i₂.hom f.hom :=
      AlgebraicSpaces.isPullback_hom B S hS sq
    exact injective_pointsMap_of_comp_isIso B S hS hsq.isoPullback.hom
      hsq.isoPullback_hom_fst (hf T'.obj T'.property i₂.hom)
  · intro hf Y' hY' g
    let k : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ T := ObjectProperty.homMk g
    exact hf _ k _ (AlgebraicSpaces.isPullback_fiberProduct B S hS k f)

/-! ### Injectivity on points descends along an fpqc covering -/

/-- Injectivity on points is local on the base for the fpqc topology: a morphism of algebraic
spaces over `S` whose base change along every member of an fpqc covering of the target is
injective on points is injective on points.

Two points of the source with a common image `t` in the target are compared after amalgamating
each of them with one and the same point of a member of the covering lying over `t`. -/
theorem injective_pointsMap_of_fpqcCovering
    {I : Type v} {W T : AlgebraicSpaces B S hS} {Ti : I → AlgebraicSpaces B S hS}
    (π : ∀ i, Ti i ⟶ T) (hπ : IsFpqcCovering B S hS (fun i ↦ (π i).hom)) (p : W ⟶ T)
    (h : ∀ i, Function.Injective
      (pointsMap B S hS (pullback p (π i)).obj (pullback.snd p (π i)).hom)) :
    Function.Injective (pointsMap B S hS W.obj p.hom) := by
  intro a b hab
  obtain ⟨i, s, hs⟩ := jointly_surjective_points_of_fpqcCovering B S hS
    (fun i ↦ (π i).hom) hπ (pointsMap B S hS W.obj p.hom a)
  obtain ⟨wa, hwa₁, hwa₂⟩ := exists_point_of_isPullback B S hS
    (IsPullback.of_hasPullback p (π i)) a s hs.symm
  obtain ⟨wb, hwb₁, hwb₂⟩ := exists_point_of_isPullback B S hS
    (IsPullback.of_hasPullback p (π i)) b s (hab.symm.trans hs.symm)
  rw [← hwa₁, ← hwb₁, h i (hwa₂.trans hwb₂.symm)]

/-! ### Stacks 041R -/

/-- **Stacks 041R.** Universal injectivity of morphisms of algebraic spaces over `S` is local
on the base for the fpqc topology. -/
@[stacks 041R]
instance universallyInjective_isLocalAtTarget_fpqc :
    (universallyInjectiveMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have heq : universallyInjectiveMorphismProperty B S hS =
      (injectiveOnPointsProperty B S hS).universally := by
    funext X T g
    exact propext (universallyInjective_iff_universally_injectiveOnPoints B S hS g)
  rw [heq]
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff ?_
  intro X Y f R hR
  refine ⟨fun hf U g _ _ ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f g) hf, fun hlocal ↦ ?_⟩
  obtain ⟨I, Yi, gi, rfl, -, -, hcover⟩ := hR
  intro X' T' pX pT f' sq
  refine injective_pointsMap_of_fpqcCovering B S hS (fun i ↦ pullback.fst pT (gi i))
    (isFpqcCovering_pullback_fst B S hS Yi gi hcover T' pT) f' fun i ↦ ?_
  have houter : IsPullback (pullback.snd f' (pullback.fst pT (gi i)))
      (pullback.fst f' (pullback.fst pT (gi i)) ≫ pX)
      (pullback.fst pT (gi i) ≫ pT) f :=
    (IsPullback.of_hasPullback f' (pullback.fst pT (gi i))).flip.paste_vert sq
  rw [(IsPullback.of_hasPullback pT (gi i)).w] at houter
  exact hlocal (gi i) (Presieve.ofArrows.mk i) _ (pullback.snd pT (gi i)) _
    (houter.of_bot' (IsPullback.of_hasPullback f (gi i)).flip)

end AlgebraicGeometry.Space

end
