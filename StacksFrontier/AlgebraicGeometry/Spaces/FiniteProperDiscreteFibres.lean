module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite

/-!
# Finite morphisms as proper morphisms with discrete fibres

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. Stacks 0A4V says that,
for `Y` locally Noetherian, `f` is finite exactly when it is proper and the point space of its
fibre `X_k` over every morphism `Spec k ⟶ Y` from the spectrum of a field is discrete.

The source proves this with the theorem on formal functions. The same equivalence holds with
no hypothesis on `Y`: it is the comparison of conditions (1) and (3) of Stacks 0A4X, which
rests on Zariski's main theorem instead. The statement here is that general form.

## Main results

* `AlgebraicGeometry.Space.isFinite_iff_isProper_and_discreteFibres`: **Stacks 0A4V**.

## Implementation notes

The fibre over a field-valued point `p` of `Y` is the pullback of `f` along the morphism out of
the field spectrum presented by `p`, the same proposition as condition (3) of Stacks 0A4X in
`AlgebraicGeometry.Space.isFinite_tfae`, and the discreteness clause quantifies over all
field-valued points of `Y`.

## References

* [Stacks Project, Tag 0A4V](https://stacks.math.columbia.edu/tag/0A4V)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
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
local instance hasPullbacks_presheaf_FiniteProperDiscreteFibres :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_FiniteProperDiscreteFibres
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 0A4V.** A morphism `f : X ⟶ Y` of algebraic spaces over `S` is finite exactly when
it is proper and the point space of its fibre over every field-valued point of `Y` is discrete.

The source assumes `Y` locally Noetherian; the equivalence holds for every target, as conditions
(1) and (3) of Stacks 0A4X. -/
@[stacks 0A4V]
theorem isFinite_iff_isProper_and_discreteFibres
    (spaceX : IsAlgebraicSpace B S hS X) (spaceY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsFinite B S hS f ↔
      IsProper B S hS f ∧ ∀ p : FieldValuedPoint B S hS Y,
        DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f)) :=
  ⟨isProper_and_discreteFibres_of_isFinite B S hS spaceX spaceY f, fun h ↦
    have h' := (isProper_and_isLocallyQuasiFinite_iff_isProper_and_discreteFibres
      B S hS spaceX spaceY f).mpr h
    isFinite_of_isProper_of_isLocallyQuasiFinite B S hS spaceX spaceY f h'.1 h'.2⟩

end AlgebraicGeometry.Space

end
