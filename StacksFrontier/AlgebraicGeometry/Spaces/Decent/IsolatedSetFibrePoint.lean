module

public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FibreOverFieldPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FieldFibreTopologicalDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality

/-!
# Isolated points of the set-theoretic fibre

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `y` be a point of `|Y|`, and let `F = f^{-1}({y}) ⊆ |X|` carry the topology induced
from `|X|`. Of the eight conditions on a point `x` of `F` compared by Stacks 0ACB, three are
conditions on `F` itself:

* (1) `F` has local Krull dimension zero at `x`;
* (2) `x` is isolated in `F`;
* (3) `x` is closed in `F` and admits no nontrivial generalization there.

This file compares those three with condition (8), quasi-finiteness of `f` at `x`. Conditions
(2) and (3) are equivalent to (8) as soon as `Y` is decent, and condition (1) joins them when
`f` is moreover a decent morphism.

## Main results

* `AlgebraicGeometry.Space.isIsolatedPoint_fibre_iff_isQuasiFiniteAt`: conditions (2)
  and (8).
* `AlgebraicGeometry.Space.isClosedNoGeneralization_fibre_iff_isQuasiFiniteAt`: conditions (3)
  and (8).
* `AlgebraicGeometry.Space.topologicalKrullDimAt_fibre_eq_zero_iff_isQuasiFiniteAt`:
  conditions (1) and (8).

Conditions (2) and (3) are therefore equivalent to each other, and — through
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.IsolatedFibrePoint` and
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.FieldFibreTopologicalDimension`, which compare
conditions (4) to (8) — to the four conditions on the field fibre. Together the three files
compare all eight conditions of Stacks 0ACB.

## Implementation notes

A decent algebraic space carries, at every one of its points, a quasi-compact monomorphism
`Spec k' ⟶ Y` in the equivalence class of that point. For such a representative the comparison
map `|X_{k'}| → |X|` is a topological embedding, by Stacks 0AC8, with image exactly `F`, so it
is a homeomorphism `|X_{k'}| ≃ F`. Each of the three conditions is a homeomorphism invariant,
so transporting it across turns it into the corresponding condition (4), (5) or (6) on
`|X_{k'}|`, and those are compared with quasi-finiteness of `f` at `x` elsewhere.

Condition (1) is stated for a decent *morphism* rather than for a decent source, which is the
hypothesis of the source statement; the two are related by Stacks 0ABX, in the form
`AlgebraicGeometry.Space.isDecent_of_isDecentSpace_source`. Only the implication from
condition (1) to condition (2) uses the hypothesis at all.

The set-theoretic fibre is spelled `pointsMap B S hS X f ⁻¹' {y}` and the conditions are
stated at a point of that subtype, so the induced topology of the source statement is the
subspace topology.

## References

* [Stacks Project, Tag 0ACB](https://stacks.math.columbia.edu/tag/0ACB)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Transport of the conditions along a homeomorphism -/

section Transport

variable {A C : Type*} [TopologicalSpace A] [TopologicalSpace C]

private theorem isIsolatedPoint_homeomorph (e : A ≃ₜ C) (a : A) :
    IsIsolatedPoint (e a) ↔ IsIsolatedPoint a := by
  have h : e ⁻¹' ({e a} : Set C) = {a} := by ext b; simp
  rw [isIsolatedPoint_iff, isIsolatedPoint_iff, ← e.isOpen_preimage (s := ({e a} : Set C)), h]

private theorem isClosedNoGeneralization_homeomorph (e : A ≃ₜ C) (a : A) :
    (IsClosed ({e a} : Set C) ∧ ∀ c : C, c ⤳ e a → c = e a) ↔
      (IsClosed ({a} : Set A) ∧ ∀ b : A, b ⤳ a → b = a) := by
  have h : e ⁻¹' ({e a} : Set C) = {a} := by ext b; simp
  refine and_congr ?_ ⟨fun hc b hb ↦ ?_, fun hb c hc ↦ ?_⟩
  · rw [← e.isClosed_preimage (s := ({e a} : Set C)), h]
  · exact e.injective (hc (e b) (e.isInducing.specializes_iff.mpr hb))
  · obtain ⟨b, rfl⟩ := e.surjective c
    rw [hb b (e.isInducing.specializes_iff.mp hc)]

end Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site needs a larger budget
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_isolatedSetFibrePoint :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_isolatedSetFibrePoint
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The conditions on the field fibre, in terms of quasi-finiteness -/

private theorem isIsolatedPoint_pullback_iff_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (w : points B S hS (pullback f (fieldMorphism B S hS Y p))) :
    IsIsolatedPoint w ↔
      IsQuasiFiniteAt B S hS f
        (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
          (pullback.fst f (fieldMorphism B S hS Y p)) w) :=
  (isIsolatedPoint_fieldFibre_iff_isClosedNoGeneralization hX hY f hf p w).trans
    ((isClosedNoGeneralization_fieldFibre_iff_dimensionAtPoint_eq_zero hX hY f hf p w).trans
      (dimensionAtPoint_fieldFibre_eq_zero_iff_isQuasiFiniteAt hX hY f hf p w))

private theorem isClosedNoGeneralization_pullback_iff_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (w : points B S hS (pullback f (fieldMorphism B S hS Y p))) :
    (IsClosed ({w} : Set (points B S hS (pullback f (fieldMorphism B S hS Y p)))) ∧
        ∀ w' : points B S hS (pullback f (fieldMorphism B S hS Y p)), w' ⤳ w → w' = w) ↔
      IsQuasiFiniteAt B S hS f
        (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
          (pullback.fst f (fieldMorphism B S hS Y p)) w) :=
  (isClosedNoGeneralization_fieldFibre_iff_dimensionAtPoint_eq_zero hX hY f hf p w).trans
    (dimensionAtPoint_fieldFibre_eq_zero_iff_isQuasiFiniteAt hX hY f hf p w)

private theorem topologicalKrullDimAt_pullback_eq_zero_iff_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hd : IsDecent B S hS f)
    (p : FieldValuedPoint B S hS Y)
    (w : points B S hS (pullback f (fieldMorphism B S hS Y p))) :
    topologicalKrullDimAt (points B S hS (pullback f (fieldMorphism B S hS Y p))) w = 0 ↔
      IsQuasiFiniteAt B S hS f
        (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
          (pullback.fst f (fieldMorphism B S hS Y p)) w) :=
  Iff.trans
    ⟨isIsolatedPoint_fieldFibre_of_topologicalKrullDimAt_eq_zero B S hS hX hY f hf hd p w,
      topologicalKrullDimAt_eq_zero_of_isIsolatedPoint w⟩
    (isIsolatedPoint_pullback_iff_isQuasiFiniteAt B S hS hX hY f hf p w)

/-! ### The comparison homeomorphism onto the set-theoretic fibre -/

private theorem range_pointsMap_pullback_eq_preimage (f : X ⟶ Y) (y : points B S hS Y)
    (p : FieldValuedPoint B S hS Y) (hpy : p.class B S hS Y = y) :
    Set.range (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
        (pullback.fst f (fieldMorphism B S hS Y p))) =
      pointsMap B S hS X f ⁻¹' {y} := by
  rw [range_pointsMap_fibre_fieldMorphism B S hS f p]
  ext x
  simp [hpy]

/-- The comparison map from the field fibre to the set-theoretic fibre, as a homeomorphism,
given that it is a topological embedding. -/
private noncomputable def setFibreComparison (f : X ⟶ Y) (y : points B S hS Y)
    (p : FieldValuedPoint B S hS Y) (hpy : p.class B S hS Y = y)
    (hemb : Topology.IsEmbedding
      (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
        (pullback.fst f (fieldMorphism B S hS Y p)))) :
    points B S hS (pullback f (fieldMorphism B S hS Y p)) ≃ₜ
      ↥(pointsMap B S hS X f ⁻¹' {y}) :=
  hemb.toHomeomorph.trans
    (Homeomorph.setCongr (range_pointsMap_pullback_eq_preimage B S hS f y p hpy))

private theorem coe_setFibreComparison (f : X ⟶ Y) (y : points B S hS Y)
    (p : FieldValuedPoint B S hS Y) (hpy : p.class B S hS Y = y)
    (hemb : Topology.IsEmbedding
      (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
        (pullback.fst f (fieldMorphism B S hS Y p))))
    (w : points B S hS (pullback f (fieldMorphism B S hS Y p))) :
    (setFibreComparison B S hS f y p hpy hemb w : points B S hS X) =
      pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
        (pullback.fst f (fieldMorphism B S hS Y p)) w :=
  rfl

private theorem pointsMap_symm_setFibreComparison (f : X ⟶ Y) (y : points B S hS Y)
    (p : FieldValuedPoint B S hS Y) (hpy : p.class B S hS Y = y)
    (hemb : Topology.IsEmbedding
      (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
        (pullback.fst f (fieldMorphism B S hS Y p))))
    (x : ↥(pointsMap B S hS X f ⁻¹' {y})) :
    pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
        (pullback.fst f (fieldMorphism B S hS Y p))
        ((setFibreComparison B S hS f y p hpy hemb).symm x) = (x : points B S hS X) := by
  rw [← coe_setFibreComparison B S hS f y p hpy hemb, Homeomorph.apply_symm_apply]

/-! ### The conditions on the set-theoretic fibre, given the embedding -/

private theorem isIsolatedPoint_fibre_iff_isQuasiFiniteAt_of_embedding
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (y : points B S hS Y)
    (p : FieldValuedPoint B S hS Y) (hpy : p.class B S hS Y = y)
    (hemb : Topology.IsEmbedding
      (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
        (pullback.fst f (fieldMorphism B S hS Y p))))
    (x : ↥(pointsMap B S hS X f ⁻¹' {y})) :
    IsIsolatedPoint x ↔ IsQuasiFiniteAt B S hS f (x : points B S hS X) := by
  have hiso := isIsolatedPoint_homeomorph (setFibreComparison B S hS f y p hpy hemb)
    ((setFibreComparison B S hS f y p hpy hemb).symm x)
  rw [Homeomorph.apply_symm_apply] at hiso
  rw [hiso, isIsolatedPoint_pullback_iff_isQuasiFiniteAt B S hS hX hY f hf p,
    pointsMap_symm_setFibreComparison B S hS f y p hpy hemb x]

private theorem isClosedNoGeneralization_fibre_iff_isQuasiFiniteAt_of_embedding
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (y : points B S hS Y)
    (p : FieldValuedPoint B S hS Y) (hpy : p.class B S hS Y = y)
    (hemb : Topology.IsEmbedding
      (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
        (pullback.fst f (fieldMorphism B S hS Y p))))
    (x : ↥(pointsMap B S hS X f ⁻¹' {y})) :
    (IsClosed ({x} : Set ↥(pointsMap B S hS X f ⁻¹' {y})) ∧
        ∀ x' : ↥(pointsMap B S hS X f ⁻¹' {y}), x' ⤳ x → x' = x) ↔
      IsQuasiFiniteAt B S hS f (x : points B S hS X) := by
  have hcl := isClosedNoGeneralization_homeomorph (setFibreComparison B S hS f y p hpy hemb)
    ((setFibreComparison B S hS f y p hpy hemb).symm x)
  rw [Homeomorph.apply_symm_apply] at hcl
  rw [hcl, isClosedNoGeneralization_pullback_iff_isQuasiFiniteAt B S hS hX hY f hf p,
    pointsMap_symm_setFibreComparison B S hS f y p hpy hemb x]

private theorem topologicalKrullDimAt_fibre_eq_zero_iff_isQuasiFiniteAt_of_embedding
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hd : IsDecent B S hS f) (y : points B S hS Y)
    (p : FieldValuedPoint B S hS Y) (hpy : p.class B S hS Y = y)
    (hemb : Topology.IsEmbedding
      (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
        (pullback.fst f (fieldMorphism B S hS Y p))))
    (x : ↥(pointsMap B S hS X f ⁻¹' {y})) :
    topologicalKrullDimAt (↥(pointsMap B S hS X f ⁻¹' {y})) x = 0 ↔
      IsQuasiFiniteAt B S hS f (x : points B S hS X) := by
  rw [topologicalKrullDimAt_eq_of_homeomorph (setFibreComparison B S hS f y p hpy hemb).symm x,
    topologicalKrullDimAt_pullback_eq_zero_iff_isQuasiFiniteAt B S hS hX hY f hf hd p,
    pointsMap_symm_setFibreComparison B S hS f y p hpy hemb x]

/-! ### The conditions on the set-theoretic fibre, for a decent target -/

/-- **Stacks 0ACB, conditions (2) and (8).** Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite type with decent target, let `y` be a point of
`|Y|` and let `F = f^{-1}({y})` carry the topology induced from `|X|`. A point of `F` is
isolated in `F` exactly when `f` is quasi-finite at it.

A decent target carries a quasi-compact monomorphism `Spec k' ⟶ Y` in the equivalence class
of `y`, and for such a representative the comparison map `|X_{k'}| → |X|` is a homeomorphism
onto `F`, by Stacks 0AC8. Being isolated is a homeomorphism invariant, so the condition
becomes condition (5) on `|X_{k'}|`, which is condition (8). -/
@[stacks 0ACB "conditions (2) and (8), for a decent target"]
theorem isIsolatedPoint_fibre_iff_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hYdec : IsDecentSpace B S hS Y)
    (y : points B S hS Y) (x : ↥(pointsMap B S hS X f ⁻¹' {y})) :
    IsIsolatedPoint x ↔ IsQuasiFiniteAt B S hS f (x : points B S hS X) := by
  obtain ⟨p, hpy, hmono, hqc⟩ := hYdec y
  exact isIsolatedPoint_fibre_iff_isQuasiFiniteAt_of_embedding B S hS hX hY f hf y p hpy
    (isEmbedding_pointsMap_fibre_fieldMorphism B S hS hX hY f p hmono hqc) x

/-- **Stacks 0ACB, conditions (3) and (8).** In the situation above, a point of
`F = f^{-1}({y})` is closed in `F` and admits no nontrivial generalization there exactly when
`f` is quasi-finite at it.

Both halves of the condition are homeomorphism invariants, so the comparison homeomorphism
`|X_{k'}| ≃ F` of Stacks 0AC8 turns the condition into condition (6) on `|X_{k'}|`, which is
condition (8). -/
@[stacks 0ACB "conditions (3) and (8), for a decent target"]
theorem isClosedNoGeneralization_fibre_iff_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hYdec : IsDecentSpace B S hS Y)
    (y : points B S hS Y) (x : ↥(pointsMap B S hS X f ⁻¹' {y})) :
    (IsClosed ({x} : Set ↥(pointsMap B S hS X f ⁻¹' {y})) ∧
        ∀ x' : ↥(pointsMap B S hS X f ⁻¹' {y}), x' ⤳ x → x' = x) ↔
      IsQuasiFiniteAt B S hS f (x : points B S hS X) := by
  obtain ⟨p, hpy, hmono, hqc⟩ := hYdec y
  exact isClosedNoGeneralization_fibre_iff_isQuasiFiniteAt_of_embedding B S hS hX hY f hf y p
    hpy (isEmbedding_pointsMap_fibre_fieldMorphism B S hS hX hY f p hmono hqc) x

/-- **Stacks 0ACB, conditions (1) and (8).** For a decent morphism of algebraic spaces over
`S` which is locally of finite type and has decent target, the set-theoretic fibre
`F = f^{-1}({y})` has local Krull dimension zero at a point exactly when `f` is quasi-finite
there.

The comparison homeomorphism `|X_{k'}| ≃ F` of Stacks 0AC8 turns the condition into
condition (4) on `|X_{k'}|`, the local Krull dimension being a homeomorphism invariant, and
condition (4) implies condition (5) for a decent morphism. The source states this for a
decent source `X`, which gives a decent morphism by Stacks 0ABX. -/
@[stacks 0ACB "conditions (1) and (8), for a decent morphism with decent target"]
theorem topologicalKrullDimAt_fibre_eq_zero_iff_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hd : IsDecent B S hS f)
    (hYdec : IsDecentSpace B S hS Y) (y : points B S hS Y)
    (x : ↥(pointsMap B S hS X f ⁻¹' {y})) :
    topologicalKrullDimAt (↥(pointsMap B S hS X f ⁻¹' {y})) x = 0 ↔
      IsQuasiFiniteAt B S hS f (x : points B S hS X) := by
  obtain ⟨p, hpy, hmono, hqc⟩ := hYdec y
  exact topologicalKrullDimAt_fibre_eq_zero_iff_isQuasiFiniteAt_of_embedding B S hS hX hY f hf
    hd y p hpy (isEmbedding_pointsMap_fibre_fieldMorphism B S hS hX hY f p hmono hqc) x

end AlgebraicGeometry.Space

end
