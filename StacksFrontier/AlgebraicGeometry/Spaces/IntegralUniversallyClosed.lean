module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Integral morphisms of algebraic spaces are the affine universally closed ones (Stacks 0414, 0415)

Integrality and finiteness of a morphism of algebraic spaces, Stacks 03ZP, are stated by
testing the base changes along the morphisms out of the objects of the site whose underlying
scheme is *affine*. Universal closedness, Stacks 03HI, is a condition on the map of point sets
of *every* base change, and the route to it from the represented base changes,
`AlgebraicGeometry.Space.universallyClosed_of_presheafIsClosedMap`, asks for relative
representability over every object of the site. Passing from the affine test objects to all of
them is the affine-local-to-global step, and it is exactly relative Tag 03JH, available for a
morphism of algebraic spaces with no containment hypothesis as
`AlgebraicGeometry.Space.presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`.

This file performs that passage for integrality: an integral morphism of algebraic spaces is
relatively representable with integral represented base changes, an integral morphism of
schemes is universally closed and hence closed, and the point-set condition follows. The
finite case is the corollary along "finite implies integral".

## Main results

* `AlgebraicGeometry.Space.IsFinite.isIntegralHom`: a finite morphism of algebraic spaces is
  integral. This is the first assertion of Tag 0414.
* `AlgebraicGeometry.Space.isFinite_of_isIntegralHom_of_isLocallyOfFiniteType`: an integral
  morphism of algebraic spaces which is locally of finite type is finite. This is the second
  assertion of Tag 0414.
* `AlgebraicGeometry.Space.universallyClosed_of_isIntegralHom`: an integral morphism of
  algebraic spaces is universally closed.
* `AlgebraicGeometry.Space.universallyClosed_of_isFinite`: a finite morphism of algebraic
  spaces is universally closed.
* `AlgebraicGeometry.Space.isIntegralHom_iff_isAffineHom_and_universallyClosed`: a morphism of
  algebraic spaces is integral if and only if it is affine and universally closed (Tag 0415).

## Implementation notes

Over an affine test object `Z`, integrality asks for `AlgebraicGeometry.IsIntegralHom` of the
projection `p : W ⟶ Z`, whose universal closedness in Mathlib quantifies over base changes along
arbitrary schemes over `Z`, while Stacks 03HI quantifies only over the algebraic spaces of the
site. For a relatively representable morphism, Stacks 03XD
(`AlgebraicGeometry.Space.presheaf_universallyClosed_iff`) identifies the two conditions, so both
directions of Tag 0415 are `AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom`
on the represented base changes, reached by Stacks 03ZQ for integrality, Stacks 03WG for
affineness and Stacks 03XD for universal closedness.

The second assertion of Tag 0414 is read on the represented base changes, where
`AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType` splits finiteness of a
morphism of schemes into integrality and local finite type. Integrality (Stacks 03ZP, over the
affine objects of the site) and local finite type (Stacks 03XF, over the étale chart squares)
are moved onto this family by Stacks 03ZQ and Stacks 03MJ respectively, the latter using that
local finite type is étale local on the source and target (Stacks 04R3).

## References

* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03XD](https://stacks.math.columbia.edu/tag/03XD)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 0414](https://stacks.math.columbia.edu/tag/0414)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finite morphisms are integral -/

/-- A finite morphism of algebraic spaces is integral. -/
@[stacks 0414 "first assertion: a finite morphism is integral"]
theorem IsFinite.isIntegralHom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : IsFinite B S hS f) : IsIntegralHom B S hS f := by
  intro Z hZ g
  obtain ⟨W, p, q, hW, hp, hpb⟩ := hf Z hZ g
  exact ⟨W, p, q, hpb, hW, inferInstance⟩

/-- An integral morphism of algebraic spaces which is locally of finite type is finite. -/
@[stacks 0414 "second assertion: an integral morphism locally of finite type is finite"]
theorem isFinite_of_isIntegralHom_of_isLocallyOfFiniteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsIntegralHom B S hS f) (hft : IsLocallyOfFiniteType B S hS f) :
    IsFinite B S hS f := by
  obtain ⟨hrep, hint⟩ := (isIntegralHom_iff_representable B S hS f hX hY).mp hf
  have hft' := (holdsOnEveryEtaleChart_iff_relative B S hS
    (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget hX hY f
    hrep).mp hft
  refine (isFinite_iff_representable B S hS f hX hY).mpr ⟨hrep, hrep, ?_⟩
  intro U V g fst snd hpb
  exact (_root_.AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨hint.property g fst snd hpb, hft'.property g fst snd hpb⟩

/-! ### Universal closedness -/

/-- An integral morphism of algebraic spaces over `S` is universally closed. -/
@[ega "II 6.1.10" "more general", ega "IV 18.12.8" "more general"]
theorem universallyClosed_of_isIntegralHom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsIntegralHom B S hS f) :
    UniversallyClosed B S hS f := by
  have hle : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ≤
      MorphismProperty.inverseImage
        (topologically @IsClosedMap : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) := by
    intro _ _ p hp
    have : _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map p) := hp
    exact ((BigFppfOver.toScheme B S hS).map p).isClosedMap
  exact universallyClosed_of_presheafIsClosedMap B S hS hX hY f
    (MorphismProperty.relative_monotone hle _
      (presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS
        isZariskiLocalAtTarget_isIntegralHom hX hY
        ((isIntegralHom_iff_holdsOnAffineBaseChange f).1 hf)))

/-- A finite morphism of algebraic spaces over `S` is universally closed. -/
theorem universallyClosed_of_isFinite {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsFinite B S hS f) :
    UniversallyClosed B S hS f :=
  universallyClosed_of_isIntegralHom B S hS hX hY (IsFinite.isIntegralHom B S hS hf)

/-! ### Integral morphisms are exactly the affine universally closed ones -/

/-- A morphism of algebraic spaces over `S` is integral if and only if it is affine and
universally closed. -/
@[stacks 0415, ega "IV 18.12.8" "more general", ega "II 6.1.10"]
theorem isIntegralHom_iff_isAffineHom_and_universallyClosed
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsIntegralHom B S hS f ↔
      IsAffineHom B S hS f ∧ UniversallyClosed B S hS f := by
  have hAffine :
      (yoneda.relativelyRepresentable f ∧
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f) ↔ IsAffineHom B S hS f :=
    (isAffineHom_tfae_of_isAlgebraicSpace B S hS f hX hY).out 1 2
  rw [isIntegralHom_iff_representable B S hS f hX hY]
  constructor
  · rintro ⟨hrep, hf⟩
    have h := MorphismProperty.relative_monotone
      (fun _ _ p hp => (_root_.AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom
        (f := (BigFppfOver.toScheme B S hS).map p)).mp hp) _ hf
    exact ⟨hAffine.mp ⟨hrep, hrep, fun _ _ g a b hpb => (h.property g a b hpb).2⟩,
      (presheaf_universallyClosed_iff B S hS hX hY hrep).mp
        ⟨hrep, fun _ _ g a b hpb => (h.property g a b hpb).1⟩⟩
  · rintro ⟨ha, hc⟩
    obtain ⟨hrep, ha'⟩ := hAffine.mpr ha
    have hc' := (presheaf_universallyClosed_iff B S hS hX hY hrep).mpr hc
    exact ⟨hrep, hrep, fun _ _ g a b hpb =>
      (_root_.AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom
        (f := (BigFppfOver.toScheme B S hS).map b)).mpr
        ⟨hc'.property g a b hpb, ha'.property g a b hpb⟩⟩

end AlgebraicGeometry.Space

end
