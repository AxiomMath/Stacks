module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Permanence properties of proper morphisms of algebraic spaces

Properness of a morphism of algebraic spaces over a scheme `S`, Stacks 03ZM, is the
conjunction of separatedness, finite type and universal closedness. This file proves that it
is stable under composition, and that universal closedness over a base descends along a
surjection, so that a separated finite-type surjective image of a universally closed
algebraic space is proper over the base.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isFiniteType_comp`: a composite of finite-type morphisms of
  algebraic spaces over `S` is of finite type.
* `AlgebraicGeometry.Space.isProper_comp`: **Stacks 04XY**, a composite of proper morphisms of
  algebraic spaces over `S` is proper.
* `AlgebraicGeometry.Space.universallyClosed_of_isSurjective_comp`: **Stacks 08AJ**, if
  `X ⟶ T` is universally closed and `X ⟶ Y` is surjective, then `Y ⟶ T` is universally
  closed.
* `AlgebraicGeometry.Space.isProper_of_isSurjective_comp`: **Stacks 08AJ**, under the same
  hypotheses, if `Y ⟶ T` is in addition separated and of finite type then it is proper.

## Implementation notes

Composition is proved conjunct by conjunct: separatedness is
`AlgebraicGeometry.Space.isSeparated_comp` of Stacks 03KQ, universal closedness is
`AlgebraicGeometry.Space.universallyClosed_comp` of Stacks 03IU, and finite type splits
further into `AlgebraicGeometry.Space.isLocallyOfFiniteType_comp` of Stacks 03XG and
`AlgebraicGeometry.Space.isQuasiCompact_comp` of Stacks 03HG; that last pairing is recorded
separately as `AlgebraicGeometry.Space.isFiniteType_comp`, which is the finite-type case of
Stacks 03XG. The separatedness half needs no algebraicity hypotheses, the other two do, and
the composite statement carries the three which they require.

Descent of universal closedness along a surjection is the point-set argument of Stacks 08AJ.
Given `k : Z ⟶ T` from an algebraic space, the base change `Z ×_T X ⟶ Z ×_T Y` of the
surjection `X ⟶ Y` is again surjective on points — `AlgebraicGeometry.Space.IsSurjective` is
stable under base change by Stacks 03MH, which is stated in the category of algebraic spaces,
so the Cartesian square of presheaves is transported there along
`CategoryTheory.IsPullback.of_map` for the full inclusion — and it is continuous on points by
clause (2) of Stacks 03BX. Its composite with the projection `Z ×_T Y ⟶ Z` is the projection
`Z ×_T X ⟶ Z`, which is closed by hypothesis, and a map whose composite with a continuous
surjection is closed is itself closed.

## References

* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on `BigFppfOver B S hS`, stated once: instance search for them
times out at the default heartbeat limit under Mathlib v4.35.0. -/
local instance hasPullbacks_presheaf_Proper : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- Every cospan of presheaves on `BigFppfOver B S hS` has a limit, found directly from
`hasPullbacks_presheaf_Proper` ahead of the slower general search. -/
local instance (priority := high) hasPullback_presheaf_Proper {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : P ⟶ R) (b : Q ⟶ R) : HasLimit (cospan a b) :=
  HasLimitsOfShape.has_limit (cospan a b)

/-! ### Composition -/

/-- **Stacks 03XG, finite type.** The composite of two morphisms of algebraic spaces over `S`
which are of finite type is of finite type: it is locally of finite type by Stacks 03XG and
quasi-compact by Stacks 03HG. -/
@[stacks 03XG "finite type"]
theorem isFiniteType_comp (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsFiniteType B S hS f) (hg : IsFiniteType B S hS g) :
    IsFiniteType B S hS (f ≫ g) :=
  ⟨isLocallyOfFiniteType_comp B S hS hX hY hZ f g hf.1 hg.1,
    isQuasiCompact_comp B S hS hY hZ f g hf.2 hg.2⟩

/-- **Stacks 04XY.** The composite of two proper morphisms of algebraic spaces over `S` is
proper.

The tag is registered on `AlgebraicGeometry.Space.isProper_comp'` of
`StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence`, which concludes the same thing without
the algebraicity hypothesis on the source; none of the three conjuncts of properness uses it,
so this form carries a hypothesis the tag does not need. -/
theorem isProper_comp (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProper B S hS f) (hg : IsProper B S hS g) :
    IsProper B S hS (f ≫ g) :=
  ⟨isSeparated_comp B S hS f g hf.1 hg.1,
    isFiniteType_comp B S hS hX hY hZ f g hf.2.1 hg.2.1,
    universallyClosed_comp B S hS hY hZ f g hf.2.2 hg.2.2⟩

/-! ### Universally closed images -/

/-- **Stacks 08AJ, universally closed image.** Let `X ⟶ Y ⟶ T` be morphisms of algebraic
spaces over `S`. If `X` is universally closed over `T` and `X ⟶ Y` is surjective, then `Y` is
universally closed over `T`. -/
@[stacks 08AJ "universally closed image"]
theorem universallyClosed_of_isSurjective_comp
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (f : X ⟶ Y) (q : Y ⟶ T)
    (hfq : UniversallyClosed B S hS (f ≫ q)) (hf : IsSurjective B S hS f) :
    UniversallyClosed B S hS q := by
  intro W hW k
  set r : pullback k (f ≫ q) ⟶ pullback k q :=
    pullback.lift (pullback.fst k (f ≫ q)) (pullback.snd k (f ≫ q) ≫ f)
      (pullback.condition.trans (Category.assoc _ _ _).symm)
  have hrfst : r ≫ pullback.fst k q = pullback.fst k (f ≫ q) := pullback.lift_fst _ _ _
  have hrsnd : r ≫ pullback.snd k q = pullback.snd k (f ≫ q) ≫ f := pullback.lift_snd _ _ _
  have hsquare : IsPullback r (pullback.snd k (f ≫ q)) (pullback.snd k q) f :=
    IsPullback.of_right (by rw [hrfst]; exact IsPullback.of_hasPullback k (f ≫ q)) hrsnd
      (IsPullback.of_hasPullback k q)
  have hsurj : IsSurjective B S hS r := by
    let Rₐ : AlgebraicSpaces B S hS :=
      ⟨pullback k (f ≫ q), isAlgebraicSpace_pullback B S hS k (f ≫ q) hW hX hT⟩
    let Pₐ : AlgebraicSpaces B S hS :=
      ⟨pullback k q, isAlgebraicSpace_pullback B S hS k q hW hY hT⟩
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
  let _tR := pointTopology B S hS (pullback k (f ≫ q))
  let _tP := pointTopology B S hS (pullback k q)
  let _tW := pointTopology B S hS W
  refine IsClosedMap.of_comp_surjective hsurj (continuous_pointsMap B S hS r) ?_
  rw [← pointsMap_comp, hrfst]
  exact hfq W hW k

/-- **Stacks 08AJ, properness of the image.** Let `X ⟶ Y ⟶ T` be morphisms of algebraic
spaces over `S`. If `X` is universally closed over `T`, the morphism `X ⟶ Y` is surjective and
`Y` is separated and of finite type over `T`, then `Y` is proper over `T`. -/
@[stacks 08AJ "properness of the image"]
theorem isProper_of_isSurjective_comp
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (f : X ⟶ Y) (q : Y ⟶ T)
    (hfq : UniversallyClosed B S hS (f ≫ q)) (hf : IsSurjective B S hS f)
    (hsep : IsSeparated B S hS q) (hft : IsFiniteType B S hS q) :
    IsProper B S hS q :=
  ⟨hsep, hft, universallyClosed_of_isSurjective_comp B S hS hX hY hT f q hfq hf⟩

end AlgebraicGeometry.Space

end
