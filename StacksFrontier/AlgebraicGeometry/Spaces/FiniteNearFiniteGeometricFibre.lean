module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDiscreteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# A proper morphism is finite near a finite geometric fibre

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S` and let `ȳ` be a
geometric point of `Y`. Stacks 0A4W says that, for `Y` locally Noetherian, if the geometric fibre
`X_ȳ` has finitely many points then `f` is finite over an open neighbourhood of `ȳ`.

The proof follows the source. A proper morphism is separated, hence quasi-separated, hence decent
(Stacks 03M5); for a decent morphism locally of finite type a finite field fibre has discrete
point space (Stacks 0ACK, condition (4) implies condition (5)), and discreteness of that fibre is
quasi-finiteness of `f` at every point of `|X|` above the image of `ȳ` (Stacks 0ACK, conditions
(5) and (8)). Stacks 0A4Y then produces the neighbourhood. None of this uses the Noetherian
hypothesis of the source, so the statement here holds for every target.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_isFinite_pullback_snd_of_finite_geometricFibre`:
  **Stacks 0A4W**.

## Implementation notes

The geometric fibre `X_ȳ` is the pullback of `f` along the morphism out of the spectrum of the
algebraically closed field presented by `ȳ`, and an open neighbourhood of `ȳ` is an open subspace
of `Y` whose point set contains the image of `ȳ` in `|Y|`. The restriction `f^{-1}(V) ⟶ V` is
the second projection of the pullback of `f` along the inclusion of `V`, as in Stacks 0A4Y.

## References

* [Stacks Project, Tag 0A4W](https://stacks.math.columbia.edu/tag/0A4W)
* [Stacks Project, Tag 0A4Y](https://stacks.math.columbia.edu/tag/0A4Y)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
* [Stacks Project, Tag 03M5](https://stacks.math.columbia.edu/tag/03M5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_FiniteNearFiniteGeometricFibre :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_FiniteNearFiniteGeometricFibre
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 0A4W.** Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` and let
`ȳ` be a geometric point of `Y` whose geometric fibre `X_ȳ` has finitely many points. Then `ȳ`
has an open neighbourhood `V ⊆ Y` over which `f` becomes finite, in the sense that the base
change `f^{-1}(V) ⟶ V` is finite.

The source assumes `Y` locally Noetherian; the conclusion holds for every target. A proper
morphism is decent, so the finite fibre `X_ȳ` has discrete point space by Stacks 0ACK, hence `f`
is quasi-finite at every point of `|X|` over the image of `ȳ`, and Stacks 0A4Y applies. -/
@[stacks 0A4W]
theorem exists_isOpenSubspace_isFinite_pullback_snd_of_finite_geometricFibre
    (spaceX : IsAlgebraicSpace B S hS X) (spaceY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (proper : IsProper B S hS f) (y : GeometricPoint B S hS Y)
    (finiteFibre : Finite (points B S hS (pullback f (yonedaEquiv.symm y.val.value)))) :
    ∃ V : Subfunctor Y, IsOpenSubspace B S hS V ∧
      y.image ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      IsFinite B S hS (pullback.snd f V.ι) := by
  have hlft : IsLocallyOfFiniteType B S hS f := proper.2.1.1
  have hdecent : IsDecent B S hS f :=
    isDecent_of_isReasonable B S hS spaceX spaceY f
      (isReasonable_of_isVeryReasonable B S hS spaceX spaceY
        (isVeryReasonable_of_isQuasiSeparated B S hS spaceX spaceY
          (isQuasiSeparated_of_isSeparated B S hS proper.1)))
  have hdisc : DiscreteTopology (points B S hS (fieldFibre B S hS f y.val)) :=
    discreteTopology_points_fieldFibre_of_finite_of_isDecent B S hS spaceX spaceY f y.val hlft
      hdecent (Set.finite_univ_iff.mpr finiteFibre)
  refine exists_isOpenSubspace_isFinite_pullback_snd_of_isProper B S hS spaceX spaceY f proper
    y.image fun x hx ↦ ?_
  exact (isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS spaceX spaceY
    hlft y.val).mp hdisc x hx

end AlgebraicGeometry.Space

end
