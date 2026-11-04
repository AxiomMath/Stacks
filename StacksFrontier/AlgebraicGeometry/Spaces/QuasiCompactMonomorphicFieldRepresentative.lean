module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Points with a quasi-compact monomorphic field-valued representative

Stacks 03JV lists six equivalent conditions on a point `x` of an algebraic space `X` over a
scheme `S`. Condition (4) is that `x` is in the equivalence class of a *quasi-compact
monomorphism* `Spec k ⟶ X` with `k` a field. That condition is the one Stacks 03I8 uses to
define a decent algebraic space, and this file states it.

## Main definitions

* `AlgebraicGeometry.Space.HasQuasiCompactMonomorphicFieldRepresentative` is condition (4)
  of Stacks 03JV.

## Main results

* `HasQuasiCompactMonomorphicFieldRepresentative.hasMonomorphicFieldRepresentative`:
  condition (4) of Stacks 03JV implies condition (4) of Stacks 03JU, which drops
  quasi-compactness.
* `HasQuasiCompactMonomorphicFieldRepresentative.exists_mono_isQuasiCompact`: the field-free
  form — some quasi-compact monomorphism from a representable presheaf has `x` in its image
  on points.

## Implementation notes

Only condition (4) is stated. The other five conditions of Stacks 03JV, and all five of its
equivalences, are not formalized here, which is why the tag carries the comment
`"part (4)"`: the declaration *is* that condition of the source statement, and claims
nothing about the equivalences.

Quasi-compactness is `AlgebraicGeometry.Space.IsQuasiCompact`, the morphism property of
Tag 03HE, and the monomorphism condition is taken in the presheaf category, where the
morphism out of the Yoneda image of the field spectrum lives. Both are applied to
`AlgebraicGeometry.Space.fieldMorphism`, the morphism presented by a field-valued point of
Tag 03BU. The predicate is a `def`, as in the tagged statement, so a proof of the 03JV
equivalences folds onto it unchanged.

## References

* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 03JV, condition (4).** A point of `F` has a *quasi-compact monomorphic
field-valued representative* when some field-valued point in its class presents it by a
morphism which is both a monomorphism and quasi-compact. -/
@[stacks 03JV "part (4)"]
def HasQuasiCompactMonomorphicFieldRepresentative (x : points B S hS F) : Prop :=
  ∃ p : FieldValuedPoint B S hS F,
    p.class B S hS F = x ∧
    Mono (fieldMorphism B S hS F p) ∧
    IsQuasiCompact B S hS (fieldMorphism B S hS F p)

/-- Condition (4) of Stacks 03JV implies condition (4) of Stacks 03JU: forgetting
quasi-compactness leaves a monomorphic field-valued representative. -/
theorem HasQuasiCompactMonomorphicFieldRepresentative.hasMonomorphicFieldRepresentative
    {x : points B S hS F}
    (h : HasQuasiCompactMonomorphicFieldRepresentative B S hS F x) :
    HasMonomorphicFieldRepresentative B S hS F x := by
  obtain ⟨p, hpx, hmono, -⟩ := h
  exact ⟨p, hpx, hmono⟩

/-- The field-free form of condition (4) of Stacks 03JV: some quasi-compact monomorphism
from a representable presheaf has `x` in its image on points. -/
theorem HasQuasiCompactMonomorphicFieldRepresentative.exists_mono_isQuasiCompact
    {x : points B S hS F}
    (h : HasQuasiCompactMonomorphicFieldRepresentative B S hS F x) :
    ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
      Mono f ∧ IsQuasiCompact B S hS f ∧
        ∃ y : points B S hS (yoneda.obj U), pointsMap B S hS (yoneda.obj U) f y = x := by
  obtain ⟨p, hpx, hmono, hqc⟩ := h
  refine ⟨p.siteObject, fieldMorphism B S hS F p, hmono, hqc,
    (p.tautologicalPoint B S hS F).class B S hS (yoneda.obj p.siteObject), ?_⟩
  rw [pointsMap_fieldMorphism_tautologicalPoint]
  exact hpx

end AlgebraicGeometry.Space

end
