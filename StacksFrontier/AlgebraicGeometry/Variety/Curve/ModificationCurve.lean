module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionDominant
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A modification of a curve is a curve

Let `k` be a field and `X` a curve over `k`. If `g : X' ⟶ X` is a modification — proper,
birational, with `X'` integral ([Stacks, Tag 0AAZ]) — then `X'` is a curve over `k` as well.

The variety conditions are stable under composition with the proper morphism `g`. For the
dimension, a birational morphism of integral schemes is dominant
(`AlgebraicGeometry.IsBirational.isDominant`) and induces an isomorphism of
function fields, so the transcendence degree of `k(X')` over `k(X)` is zero, and a proper
morphism is closed; the dimension formula for a closed dominant morphism ([Stacks, Tag 02JX],
`AlgebraicGeometry.topologicalKrullDim_eq_add_trdeg_of_isClosedMap`) then gives
`dim X' = dim X = 1`.

## Main results

* `AlgebraicGeometry.IsBirational.surjective_functionFieldMap` — a birational morphism of
  integral schemes induces a surjection of function fields.
* `AlgebraicGeometry.IsBirational.topologicalKrullDim_eq_of_isClosedMap` — a closed birational
  morphism of integral schemes, locally of finite type over a locally Noetherian target,
  preserves dimension.
* `AlgebraicGeometry.isCurve_comp_of_isModification` — a modification of a curve is a curve.

## References

* [Stacks Project, Tag 0AAZ](https://stacks.math.columbia.edu/tag/0AAZ)
* [Stacks Project, Tag 02JX](https://stacks.math.columbia.edu/tag/02JX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A birational morphism of integral schemes induces a surjection of function fields**: the
stalk map at the generic point is an isomorphism. -/
theorem IsBirational.surjective_functionFieldMap {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] {f : X ⟶ Y} [IsDominant f] (hf : IsBirational f) :
    Function.Surjective (functionFieldMap f) := by
  have : IsIso (f.stalkMap (genericPoint X)) := hf.isIso_stalkMap _ (by
    rw [genericPoints_eq_singleton]
    rfl)
  exact (asIso ((Y.presheaf.stalkCongr
    (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).hom ≫
      f.stalkMap (genericPoint X))).commRingCatIsoToRingEquiv.surjective

/-- **A closed birational morphism of integral schemes preserves dimension**, for a morphism
locally of finite type to a locally Noetherian scheme: the function field extension is trivial,
so the transcendence degree term of the dimension formula of [Stacks, Tag 02JX] vanishes. -/
@[ega "IV 5.6.6" "special case"]
theorem IsBirational.topologicalKrullDim_eq_of_isClosedMap {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] {f : X ⟶ Y} [LocallyOfFiniteType f]
    (hf : IsBirational f) (hcl : IsClosedMap f) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  have := hf.isDominant
  let := (functionFieldMap f).toAlgebra
  have : Algebra.IsAlgebraic Y.functionField X.functionField := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hf.surjective_functionFieldMap x
    exact isAlgebraic_algebraMap a⟩
  rw [topologicalKrullDim_eq_add_trdeg_of_isClosedMap f hcl, trdeg_eq_zero]
  simp

/-- **A modification of a curve is a curve.** If `f : X ⟶ Spec k` is a curve and `g : X' ⟶ X`
is a modification, then `g ≫ f` is a curve: `X'` is integral by definition, the composite is
separated, quasi-compact and locally of finite type because `g` is proper, and `X'` has the
dimension of `X` by `AlgebraicGeometry.IsBirational.topologicalKrullDim_eq_of_isClosedMap`. -/
theorem isCurve_comp_of_isModification (k : Type u) [Field k] {X X' : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] (g : X' ⟶ X) (hg : IsModification g) :
    IsCurve k (g ≫ f) := by
  have : IsIntegral X' := hg.2.2
  have : IsProper g := hg.2.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine (isCurve_iff k (g ≫ f)).2 ⟨{ toIsIntegral := ‹_› }, ?_⟩
  rw [hg.1.topologicalKrullDim_eq_of_isClosedMap g.isClosedMap]
  exact IsCurve.topologicalKrullDim_eq_one f

end AlgebraicGeometry

end
