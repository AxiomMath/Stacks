module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal

/-!
# The family of projective lines over a fibre product

Let `f : X ⟶ Y` and `g : T ⟶ Y` be morphisms of schemes and let `sY : Y ⟶ S` present `Y`, and
hence `T` through `q = g ≫ sY`, as a scheme over `S`. Write `P = T ×_S ℙ¹_S` for the family of
projective lines over `T` and `P ⟶ Y` for its projection to `T` followed by `g`. The fibre
product `X ×_Y T` is a scheme over `S` through `f`, and this file identifies its family of
projective lines `(X ×_Y T) ×_S ℙ¹_S` with the fibre product `X ×_Y P`, compatibly with the
constant sections on both sides.

## Main definitions

* `Stacks.Chow.familyProductBaseChange`: the morphism `(X ×_Y T) ×_S ℙ¹_S ⟶ T ×_S ℙ¹_S` induced
  by the projection `X ×_Y T ⟶ T`, which is a morphism over `S`.
* `Stacks.Chow.familyProductComparison` and `Stacks.Chow.familyProductIso`: the comparison
  morphism `(X ×_Y T) ×_S ℙ¹_S ⟶ X ×_Y (T ×_S ℙ¹_S)` and the isomorphism it induces.
* `Stacks.Chow.sectionComparison`: the morphism `X ×_Y T ⟶ X ×_Y (T ×_S ℙ¹_S)` which is the
  identity on the first factor and a constant section of `T ×_S ℙ¹_S ⟶ T` on the second.

## Main results

* `Stacks.Chow.isPullback_familyProductComparison`: the family over `X ×_Y T` is the fibre
  product of `X ⟶ Y` and `T ×_S ℙ¹_S ⟶ Y`, so `Stacks.Chow.familyProductComparison` is an
  isomorphism.
* `Stacks.Chow.constantSection_comp_familyProductIso`, with its zero and infinity cases: under
  that identification a constant section of the family over `X ×_Y T` is
  `Stacks.Chow.sectionComparison`.
* `Stacks.Chow.isPullback_sectionComparison` and `Stacks.Chow.ker_sectionComparison_zero`: the
  section comparison is the base change of a constant section of `T ×_S ℙ¹_S ⟶ T`, so the closed
  subscheme it cuts out is the inverse image of the one cut out by that section.

## Implementation notes

The scheme `X ×_Y T` is given its structure morphism to `S` through `f`, that is as
`pullback.fst f g ≫ f ≫ sY`; `Stacks.Chow.snd_comp_eq` is the identity with the other reading
`pullback.snd f g ≫ g ≫ sY`, and is what lets the two descriptions of the family be compared.

As in `StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineBaseChange`, every
identification is stated as a cartesian square and the isomorphisms are produced one at a time
by `CategoryTheory.IsPullback.isoPullback` and never composed, so that no limit cone of a
pullback of pullbacks has to be unfolded.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X Y S T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (sY : Y ⟶ S)

/-- The two readings of the structure morphism of `X ×_Y T` over `S` agree: going through `T`
gives the same morphism as going through `X`. -/
theorem snd_comp_eq :
    pullback.snd f g ≫ g ≫ sY = pullback.fst f g ≫ f ≫ sY := by
  rw [← Category.assoc, ← Category.assoc, pullback.condition]

/-- A constant section of `T ×_S ℙ¹_S ⟶ T`, followed by the projection of the family to `Y`, is
the morphism `g : T ⟶ Y` itself. -/
@[reassoc (attr := simp)]
theorem constantSection_comp_familyProjection
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    constantSection (g ≫ sY) e ≫
        pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g = g := by
  rw [← Category.assoc, constantSection_comp_fst, Category.id_comp]

/-! ### The family over the fibre product as a fibre product of families -/

/-- The morphism `(X ×_Y T) ×_S ℙ¹_S ⟶ T ×_S ℙ¹_S` induced by the projection `X ×_Y T ⟶ T`: it
is that projection on the first factor and the identity on `ℙ¹_S`. -/
def familyProductBaseChange :
    projectiveLineProduct (pullback.fst f g ≫ f ≫ sY) ⟶ projectiveLineProduct (g ≫ sY) :=
  pullback.lift
    (pullback.fst (pullback.fst f g ≫ f ≫ sY) (relativeProjectiveLine S ↘ S) ≫
      pullback.snd f g)
    (pullback.snd (pullback.fst f g ≫ f ≫ sY) (relativeProjectiveLine S ↘ S))
    (by rw [Category.assoc, snd_comp_eq, pullback.condition])

/-- On the `X ×_Y T`-factor, `Stacks.Chow.familyProductBaseChange` is the projection
`X ×_Y T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem familyProductBaseChange_comp_fst :
    familyProductBaseChange f g sY ≫ pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) =
      pullback.fst (pullback.fst f g ≫ f ≫ sY) (relativeProjectiveLine S ↘ S) ≫
        pullback.snd f g :=
  pullback.lift_fst _ _ _

/-- On the `ℙ¹_S`-factor, `Stacks.Chow.familyProductBaseChange` is the identity. -/
@[reassoc (attr := simp)]
theorem familyProductBaseChange_comp_snd :
    familyProductBaseChange f g sY ≫ pullback.snd (g ≫ sY) (relativeProjectiveLine S ↘ S) =
      pullback.snd (pullback.fst f g ≫ f ≫ sY) (relativeProjectiveLine S ↘ S) :=
  pullback.lift_snd _ _ _

/-- The family over `X ×_Y T` is the base change of the family over `T` along the projection
`X ×_Y T ⟶ T`: the square

```
(X ×_Y T) ×_S ℙ¹_S ---> T ×_S ℙ¹_S
        |                    |
        v                    v
     X ×_Y T  ----------->   T
```

is cartesian. -/
theorem isPullback_familyProductBaseChange :
    IsPullback (pullback.fst (pullback.fst f g ≫ f ≫ sY) (relativeProjectiveLine S ↘ S))
      (familyProductBaseChange f g sY) (pullback.snd f g)
      (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S)) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd (g ≫ sY) (relativeProjectiveLine S ↘ S))
    (v₂₂ := g ≫ sY) ?_ ((familyProductBaseChange_comp_fst f g sY).symm)
    (IsPullback.of_hasPullback (g ≫ sY) (relativeProjectiveLine S ↘ S))
  rw [familyProductBaseChange_comp_snd, snd_comp_eq]
  exact IsPullback.of_hasPullback (pullback.fst f g ≫ f ≫ sY) (relativeProjectiveLine S ↘ S)

/-- The comparison morphism `(X ×_Y T) ×_S ℙ¹_S ⟶ X ×_Y (T ×_S ℙ¹_S)`: it is the projection to
`X` on the first factor and `Stacks.Chow.familyProductBaseChange` on the second. -/
def familyProductComparison :
    projectiveLineProduct (pullback.fst f g ≫ f ≫ sY) ⟶
      pullback f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g) :=
  pullback.lift
    (pullback.fst (pullback.fst f g ≫ f ≫ sY) (relativeProjectiveLine S ↘ S) ≫
      pullback.fst f g)
    (familyProductBaseChange f g sY)
    (by
      rw [← Category.assoc (familyProductBaseChange f g sY), familyProductBaseChange_comp_fst,
        Category.assoc, Category.assoc, pullback.condition])

/-- On the `X`-factor, `Stacks.Chow.familyProductComparison` is the projection
`(X ×_Y T) ×_S ℙ¹_S ⟶ X`. -/
@[reassoc (attr := simp)]
theorem familyProductComparison_comp_fst :
    familyProductComparison f g sY ≫
        pullback.fst f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g) =
      pullback.fst (pullback.fst f g ≫ f ≫ sY) (relativeProjectiveLine S ↘ S) ≫
        pullback.fst f g :=
  pullback.lift_fst _ _ _

/-- On the `T ×_S ℙ¹_S`-factor, `Stacks.Chow.familyProductComparison` is
`Stacks.Chow.familyProductBaseChange`. -/
@[reassoc (attr := simp)]
theorem familyProductComparison_comp_snd :
    familyProductComparison f g sY ≫
        pullback.snd f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g) =
      familyProductBaseChange f g sY :=
  pullback.lift_snd _ _ _

/-- **The family of projective lines over `X ×_Y T` is `X ×_Y (T ×_S ℙ¹_S)`.** The square

```
(X ×_Y T) ×_S ℙ¹_S ---> T ×_S ℙ¹_S
        |                    |
        v                    v
        X  --------- f ---->  Y
```

whose vertical arrows are `Stacks.Chow.familyProductBaseChange` and the projection to `X`, is
cartesian; it is obtained by pasting `Stacks.Chow.isPullback_familyProductBaseChange` with the
defining square of `X ×_Y T`. -/
theorem isPullback_familyProductComparison :
    IsPullback (pullback.fst (pullback.fst f g ≫ f ≫ sY) (relativeProjectiveLine S ↘ S) ≫
        pullback.fst f g) (familyProductBaseChange f g sY) f
      (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g) :=
  (isPullback_familyProductBaseChange f g sY).paste_horiz (IsPullback.of_hasPullback f g)

/-- **The identification `(X ×_Y T) ×_S ℙ¹_S ≅ X ×_Y (T ×_S ℙ¹_S)`**, read off from the
cartesian square `Stacks.Chow.isPullback_familyProductComparison`. -/
def familyProductIso :
    projectiveLineProduct (pullback.fst f g ≫ f ≫ sY) ≅
      pullback f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g) :=
  (isPullback_familyProductComparison f g sY).isoPullback

/-- The identification carries the projection to `X` to the projection to `X`. -/
@[reassoc (attr := simp)]
theorem familyProductIso_hom_fst :
    (familyProductIso f g sY).hom ≫
        pullback.fst f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g) =
      pullback.fst (pullback.fst f g ≫ f ≫ sY) (relativeProjectiveLine S ↘ S) ≫
        pullback.fst f g :=
  (isPullback_familyProductComparison f g sY).isoPullback_hom_fst

/-- The identification carries `Stacks.Chow.familyProductBaseChange` to the projection to
`T ×_S ℙ¹_S`. -/
@[reassoc (attr := simp)]
theorem familyProductIso_hom_snd :
    (familyProductIso f g sY).hom ≫
        pullback.snd f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g) =
      familyProductBaseChange f g sY :=
  (isPullback_familyProductComparison f g sY).isoPullback_hom_snd

/-- The identification is the comparison morphism. -/
theorem familyProductIso_hom :
    (familyProductIso f g sY).hom = familyProductComparison f g sY := by
  refine pullback.hom_ext ?_ ?_
  · rw [familyProductIso_hom_fst, familyProductComparison_comp_fst]
  · rw [familyProductIso_hom_snd, familyProductComparison_comp_snd]

/-! ### The two distinguished sections under the identification -/

/-- The section `X ×_Y T ⟶ X ×_Y (T ×_S ℙ¹_S)` attached to an integral point `e` of `ℙ¹_ℤ`: it
is the projection to `X` on the first factor and the constant section at `e` of
`T ×_S ℙ¹_S ⟶ T` on the second. -/
def sectionComparison (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    pullback f g ⟶ pullback f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g) :=
  pullback.lift (pullback.fst f g) (pullback.snd f g ≫ constantSection (g ≫ sY) e)
    (by rw [Category.assoc, constantSection_comp_familyProjection, pullback.condition])

/-- On the `X`-factor, `Stacks.Chow.sectionComparison` is the projection `X ×_Y T ⟶ X`. -/
@[reassoc (attr := simp)]
theorem sectionComparison_comp_fst (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    sectionComparison f g sY e ≫
        pullback.fst f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g) =
      pullback.fst f g :=
  pullback.lift_fst _ _ _

/-- On the `T ×_S ℙ¹_S`-factor, `Stacks.Chow.sectionComparison` is the constant section at
`e`. -/
@[reassoc (attr := simp)]
theorem sectionComparison_comp_snd (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    sectionComparison f g sY e ≫
        pullback.snd f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g) =
      pullback.snd f g ≫ constantSection (g ≫ sY) e :=
  pullback.lift_snd _ _ _

/-- The constant sections are compatible with the morphism induced on families by the
projection `X ×_Y T ⟶ T`. -/
theorem constantSection_comp_familyProductBaseChange
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    constantSection (pullback.fst f g ≫ f ≫ sY) e ≫ familyProductBaseChange f g sY =
      pullback.snd f g ≫ constantSection (g ≫ sY) e := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, familyProductBaseChange_comp_fst, ← Category.assoc,
      constantSection_comp_fst, Category.id_comp, Category.assoc, constantSection_comp_fst,
      Category.comp_id]
  · rw [Category.assoc, familyProductBaseChange_comp_snd, Category.assoc,
      constantSection_comp_snd, constantSection_comp_snd]
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, snd_comp_eq]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, terminal.comp_from_assoc]

/-- **A constant section of the family over `X ×_Y T` is the corresponding section comparison.**
This is the compatibility of `Stacks.Chow.familyProductIso` with the data that Stacks 02S4 and
02S5 are about, and not merely with the projections. -/
theorem constantSection_comp_familyProductIso
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    constantSection (pullback.fst f g ≫ f ≫ sY) e ≫ (familyProductIso f g sY).hom =
      sectionComparison f g sY e := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, familyProductIso_hom_fst, ← Category.assoc, constantSection_comp_fst,
      Category.id_comp, sectionComparison_comp_fst]
  · rw [Category.assoc, familyProductIso_hom_snd, constantSection_comp_familyProductBaseChange,
      sectionComparison_comp_snd]

/-- The zero section of the family over `X ×_Y T` is the section comparison at `0`. -/
theorem zeroSection_comp_familyProductIso :
    zeroSection (pullback.fst f g ≫ f ≫ sY) ≫ (familyProductIso f g sY).hom =
      sectionComparison f g sY integralZeroSection :=
  constantSection_comp_familyProductIso f g sY integralZeroSection

/-- The infinity section of the family over `X ×_Y T` is the section comparison at `∞`. -/
theorem infinitySection_comp_familyProductIso :
    infinitySection (pullback.fst f g ≫ f ≫ sY) ≫ (familyProductIso f g sY).hom =
      sectionComparison f g sY integralInfinitySection :=
  constantSection_comp_familyProductIso f g sY integralInfinitySection

/-! ### The section comparison as a base change -/

/-- The section comparison is the base change of the constant section of `T ×_S ℙ¹_S ⟶ T` along
the projection `X ×_Y (T ×_S ℙ¹_S) ⟶ T ×_S ℙ¹_S`. -/
theorem isPullback_sectionComparison (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    IsPullback (sectionComparison f g sY e) (pullback.snd f g)
      (pullback.snd f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g))
      (constantSection (g ≫ sY) e) := by
  refine IsPullback.of_right
    (h₁₂ := pullback.fst f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g)) ?_
    (sectionComparison_comp_snd f g sY e) (IsPullback.of_hasPullback _ _)
  rw [sectionComparison_comp_fst, constantSection_comp_familyProjection]
  exact IsPullback.of_hasPullback f g

/-- The section comparison at `0` is the base change of the zero section of
`T ×_S ℙ¹_S ⟶ T`. -/
theorem isPullback_sectionComparison_zero :
    IsPullback (sectionComparison f g sY integralZeroSection) (pullback.snd f g)
      (pullback.snd f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g))
      (zeroSection (g ≫ sY)) :=
  isPullback_sectionComparison f g sY integralZeroSection

/-- The section comparison at `∞` is the base change of the infinity section of
`T ×_S ℙ¹_S ⟶ T`. -/
theorem isPullback_sectionComparison_infinity :
    IsPullback (sectionComparison f g sY integralInfinitySection) (pullback.snd f g)
      (pullback.snd f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g))
      (infinitySection (g ≫ sY)) :=
  isPullback_sectionComparison f g sY integralInfinitySection

/-- The section comparison at `0` is a closed immersion, being a base change of the zero
section. -/
instance isClosedImmersion_sectionComparison_zero :
    IsClosedImmersion (sectionComparison f g sY integralZeroSection) :=
  MorphismProperty.of_isPullback (isPullback_sectionComparison_zero f g sY).flip inferInstance

/-- The section comparison at `∞` is a closed immersion, being a base change of the infinity
section. -/
instance isClosedImmersion_sectionComparison_infinity :
    IsClosedImmersion (sectionComparison f g sY integralInfinitySection) :=
  MorphismProperty.of_isPullback
    (isPullback_sectionComparison_infinity f g sY).flip inferInstance

/-- The closed subscheme of `X ×_Y T` cut out by the section comparison at `0` is the inverse
image of the one cut out by the zero section of `T ×_S ℙ¹_S ⟶ T`. -/
theorem ker_sectionComparison_zero :
    (sectionComparison f g sY integralZeroSection).ker =
      (zeroSection (g ≫ sY)).ker.comap
        (pullback.snd f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g)) :=
  AlgebraicGeometry.ker_eq_comap_ker_of_isPullback (isPullback_sectionComparison_zero f g sY)

/-- The closed subscheme of `X ×_Y T` cut out by the section comparison at `∞` is the inverse
image of the one cut out by the infinity section of `T ×_S ℙ¹_S ⟶ T`. -/
theorem ker_sectionComparison_infinity :
    (sectionComparison f g sY integralInfinitySection).ker =
      (infinitySection (g ≫ sY)).ker.comap
        (pullback.snd f (pullback.fst (g ≫ sY) (relativeProjectiveLine S ↘ S) ≫ g)) :=
  AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
    (isPullback_sectionComparison_infinity f g sY)

end Stacks.Chow

end
