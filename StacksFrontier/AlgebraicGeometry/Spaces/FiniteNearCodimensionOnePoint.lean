module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteCodimensionOne

/-!
# Finiteness of a proper morphism near a point of codimension at most one

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S`, with `Y` locally
Noetherian, and let `y` be a point of `|Y|` whose local ring has dimension at most one. Write
`X⁰` for the set of points of `|X|` whose local ring has dimension zero. Stacks 0AD2 says that
`y` has an open neighbourhood in `Y` over which `f` becomes finite, as soon as one of four
generic conditions holds: the transcendence degree of `x` over `f(x)` is zero for every `x` of
`X⁰`, or for every such `x` whose image specializes to `y`, or `f` is quasi-finite at every
point of `X⁰`, or `f` is quasi-finite at a dense set of points of `|X|`.

The proof is the composition of two results. Each of the four generic conditions forces `f` to
be quasi-finite at every point of `|X|` above `y`, which is Stacks 0AD1 applied to the locally
finite type morphism underlying the proper `f`; and a proper morphism which is quasi-finite
above a single point of its target is finite over an open neighbourhood of that point, which is
Stacks 0A4Y.

## Main results

* `exists_isOpenSubspace_isFinite_pullback_snd_of_localRingDimension_le_one`: **Stacks 0AD2**.

## References

* [Stacks Project, Tag 0AD2](https://stacks.math.columbia.edu/tag/0AD2)
* [Stacks Project, Tag 0AD1](https://stacks.math.columbia.edu/tag/0AD1)
* [Stacks Project, Tag 0A4Y](https://stacks.math.columbia.edu/tag/0A4Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance hasPullbacks_presheaf_finiteNearCodimensionOnePoint :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance (priority := high) hasPullback_presheaf_finiteNearCodimensionOnePoint
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks Project, Tag 0AD2.** Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over
`S` with `Y` locally Noetherian, and let `y` be a point of `|Y|` whose local ring has dimension
at most one. If one of the four generic quasi-finiteness conditions of Stacks 0AD1 holds, then
`y` has an open neighbourhood `V ⊆ Y` over which the base change `f^{-1}(V) ⟶ V` is finite. -/
@[stacks 0AD2]
theorem exists_isOpenSubspace_isFinite_pullback_snd_of_localRingDimension_le_one
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hp : IsProper B S hS f)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (y : points B S hS Y) (hy : localRingDimension B S hS y ≤ 1)
    (hgeneric :
      (∀ x : points B S hS X, localRingDimension B S hS x = 0 →
        HasTranscendenceDegreeAt B S hS f x 0) ∨
      (∀ x : points B S hS X, localRingDimension B S hS x = 0 →
        pointsMap B S hS X f x ⤳ y → HasTranscendenceDegreeAt B S hS f x 0) ∨
      (∀ x : points B S hS X, localRingDimension B S hS x = 0 →
        IsQuasiFiniteAt B S hS f x) ∨
      Dense {x : points B S hS X | IsQuasiFiniteAt B S hS f x}) :
    ∃ V : Subfunctor Y, IsOpenSubspace B S hS V ∧
      y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      IsFinite B S hS (pullback.snd f V.ι) :=
  exists_isOpenSubspace_isFinite_pullback_snd_of_isProper B S hS hX hY f hp y
    (isQuasiFiniteAt_of_localRingDimension_le_one B S hS hX hY f hp.2.1.1 hNoeth y hy hgeneric)

end AlgebraicGeometry.Space

end
