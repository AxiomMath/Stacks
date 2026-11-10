module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion

/-!
# The valuative criterion is stable under composition

Both halves of the valuative criterion pass to composites: if `f` and `g` are composable
morphisms of presheaves on the big fppf site of `S` and each satisfies the existence
(respectively uniqueness) half of the valuative criterion, then so does `f ≫ g`.

For existence one chains the two dominating extensions: a valuative square for `f ≫ g`
becomes a valuative square for `g` by composing its generic point with `f`, and the lift
produced there becomes the bottom edge of a valuative square for `f`. For uniqueness one
runs the same chaining backwards, first identifying the two candidate lifts after
composing with `f` and then identifying them outright.

## Main results

* `AlgebraicGeometry.Space.valuativeCriterionExistence_comp`
* `AlgebraicGeometry.Space.valuativeCriterion_uniqueness_comp`

## Implementation notes

Neither argument uses any property of the presheaves involved beyond the equations of a
valuative square, so both results are stated for arbitrary presheaves on the big fppf site
rather than only for algebraic spaces.

## References

* [Stacks Project, Tag 03IZ](https://stacks.math.columbia.edu/tag/03IZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A valuative square for `f ≫ g` gives one for `g` by composing its generic point with `f`. -/
private noncomputable abbrev compSquare (f : X ⟶ Y) (g : Y ⟶ Z) (q : ValuativeSquare (f ≫ g)) :
    ValuativeSquare g where
  R := q.R
  K := q.K
  ring_mem := q.ring_mem
  field_mem := q.field_mem
  base := q.base
  generic := q.generic ≫ f
  special := q.special
  comm := by simpa only [Category.assoc] using q.comm

/-- Composing a lift for `f ≫ g` with `f` gives a lift for the associated square for `g`. -/
private noncomputable def compLift (f : X ⟶ Y) (g : Y ⟶ Z) {q : ValuativeSquare (f ≫ g)}
    (x : q.Lift) :
    (compSquare f g q).Lift where
  map := x.map ≫ f
  generic_comm := by rw [← Category.assoc, x.generic_comm]
  special_comm := by simpa only [Category.assoc] using x.special_comm

/-- The existence part of the valuative criterion is preserved under composition. -/
@[stacks 03IZ "composition_valuative_existence"]
public theorem valuativeCriterionExistence_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ValuativeCriterion.Existence f)
    (hg : ValuativeCriterion.Existence g) :
    ValuativeCriterion.Existence (f ≫ g) := by
  intro q
  obtain ⟨e₁, ⟨l₁⟩⟩ := hg (compSquare f g q)
  let qf : ValuativeSquare f := {
    R := e₁.square.R, K := e₁.square.K, ring_mem := e₁.square.ring_mem
    field_mem := e₁.square.field_mem, base := e₁.square.base
    generic := yoneda.map e₁.genericOver ≫ q.generic, special := l₁.map
    comm := by
      simpa only [Category.assoc] using e₁.generic_comm.symm.trans l₁.generic_comm.symm
  }
  obtain ⟨e₂, ⟨l₂⟩⟩ := hf qf
  let qfinal : ValuativeSquare (f ≫ g) := {
    R := e₂.square.R, K := e₂.square.K, ring_mem := e₂.square.ring_mem
    field_mem := e₂.square.field_mem, base := e₂.square.base
    generic := e₂.square.generic, special := e₂.square.special ≫ g
    comm := by simpa only [Category.assoc] using congrArg (· ≫ g) e₂.square.comm
  }
  let e : q.DominatingExtension := {
    square := qfinal
    ringMap := e₂.ringMap.comp e₁.ringMap
    fieldMap := e₂.fieldMap.comp e₁.fieldMap
    isLocalHom := by
      have : IsLocalHom e₁.ringMap := e₁.isLocalHom
      have : IsLocalHom e₂.ringMap := e₂.isLocalHom
      exact RingHom.isLocalHom_comp e₂.ringMap e₁.ringMap
    fraction_comm := by
      change (algebraMap e₂.square.R e₂.square.K).comp (e₂.ringMap.comp e₁.ringMap) = _
      rw [← RingHom.comp_assoc, e₂.fraction_comm, RingHom.comp_assoc, e₁.fraction_comm]
      simp only [compSquare, RingHom.comp_assoc]
    base_comm := by
      rw [e₂.base_comm, e₁.base_comm, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
    genericOver := e₂.genericOver ≫ e₁.genericOver
    genericOver_left := by
      change (B.inclusion).map (e₂.genericOver.left ≫ e₁.genericOver.left) = _
      rw [Functor.map_comp, e₂.genericOver_left, e₁.genericOver_left, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
    specialOver := e₂.specialOver ≫ e₁.specialOver
    specialOver_left := by
      change (B.inclusion).map (e₂.specialOver.left ≫ e₁.specialOver.left) = _
      rw [Functor.map_comp, e₂.specialOver_left, e₁.specialOver_left, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
    generic_comm := by
      simpa only [qfinal, qf, yoneda.map_comp, Category.assoc] using e₂.generic_comm
    special_comm := by
      change e₂.square.special ≫ g = _
      rw [e₂.special_comm, Category.assoc, l₁.special_comm, e₁.special_comm]
      simp only [compSquare, yoneda.map_comp, Category.assoc]
  }
  exact ⟨e, ⟨{
    map := l₂.map
    generic_comm := by simpa [qfinal] using l₂.generic_comm
    special_comm := by
      simpa only [Category.assoc, qfinal] using (congrArg (· ≫ g) l₂.special_comm)
  }⟩⟩

/-- Uniqueness of lifts in valuative squares is stable under composition. -/
@[stacks 03IZ "composition_valuative_uniqueness"]
public lemma valuativeCriterion_uniqueness_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ValuativeCriterion.Uniqueness f)
    (hg : ValuativeCriterion.Uniqueness g) :
    ValuativeCriterion.Uniqueness (f ≫ g) := by
  intro q
  refine ⟨fun x₁ x₂ => ?_⟩
  have hmap : x₁.map ≫ f = x₂.map ≫ f := by
    simpa [compLift] using
      congrArg ValuativeSquare.Lift.map ((hg (compSquare f g q)).elim (compLift f g x₁)
        (compLift f g x₂))
  let qf : ValuativeSquare f := {
    R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem
    base := q.base, generic := q.generic, special := x₁.map ≫ f
    comm := by simpa only [Category.assoc] using (congrArg (· ≫ f) x₁.generic_comm).symm
  }
  let hxf₁ : qf.Lift := { map := x₁.map, generic_comm := x₁.generic_comm, special_comm := rfl }
  let hxf₂ : qf.Lift :=
    { map := x₂.map, generic_comm := x₂.generic_comm, special_comm := hmap.symm }
  have hxmap : x₁.map = x₂.map := by
    simpa [hxf₁, hxf₂] using congrArg ValuativeSquare.Lift.map ((hf qf).elim hxf₁ hxf₂)
  cases x₁
  cases x₂
  cases hxmap
  rfl

end AlgebraicGeometry.Space

end
