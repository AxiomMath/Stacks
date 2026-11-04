module

public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Eight conditions on a fibre of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `p` be a field-valued point of `Y` with field of definition `k`, and let `y` be the point
of `|Y|` it represents. [Stacks, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK) compares
eight conditions on the fibre of `f` above `y`: four about the set-theoretic fibre
`F = f^{-1}({y}) ⊂ |X|` and the point set of the field fibre `X_k = Spec(k) ×_Y X`, two about their
dimensions, one about the dimension of `X_k` as an algebraic space, and one about quasi-finiteness
of `f` above `y`.

Here `F` carries the topology induced from the point topology of `|X|`, and the dimension of a
topological space is `topologicalKrullDim`, under which the empty space has dimension `⊥`; so
discreteness implies dimension zero only for a nonempty fibre.

## Main definitions

* `AlgebraicGeometry.Space.IsDiscreteSetFibre` is condition (2): `F` is discrete.
* `AlgebraicGeometry.Space.IsZeroDimensionalSetFibre` is condition (3): `dim(F) = 0`.
* `AlgebraicGeometry.Space.IsDiscreteFieldFibrePoints` is condition (5): `|X_k|` is discrete.
* `AlgebraicGeometry.Space.IsZeroDimensionalFieldFibrePoints` is condition (6):
  `dim(|X_k|) = 0`.
* `AlgebraicGeometry.Space.IsZeroDimensionalFieldFibre` is condition (7): `dim(X_k) = 0`,
  the dimension of Tag 04N6 of the algebraic space `X_k`.
* `AlgebraicGeometry.Space.IsQuasiFiniteAboveFieldValuedPoint` is condition (8): `f` is
  quasi-finite at every point of `|X|` above `y`.

Conditions (1) and (4), finiteness of `F` and of `|X_k|`, are the conclusion and the hypothesis of
`AlgebraicGeometry.Space.finite_setFibre_of_finite_fieldFibre`.

## Main results

* `AlgebraicGeometry.Space.nonempty_points_fieldFibre_iff`: the field fibre has a point
  exactly when the set-theoretic fibre is nonempty.
* `AlgebraicGeometry.Space.isZeroDimensionalSetFibre_of_isDiscreteSetFibre` and
  `AlgebraicGeometry.Space.isZeroDimensionalFieldFibrePoints_of_isDiscreteFieldFibrePoints`:
  condition (2) implies condition (3), and condition (5) implies condition (6), for a
  nonempty fibre.
* `AlgebraicGeometry.Space.isQuasiFiniteAboveFieldValuedPoint_of_isLocallyQuasiFinite`: a
  locally quasi-finite morphism out of an algebraic space satisfies condition (8) above every
  field-valued point of its target.

## References

* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Conditions (2), (3), (5) and (6): the two fibres as topological spaces -/

/-- The set-theoretic fibre `F = f^{-1}({y})`, with the topology induced from `|X|`, is a discrete
topological space. -/
@[stacks 0ACK "condition (2)"]
def IsDiscreteSetFibre (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) : Prop :=
  DiscreteTopology (setFibre B S hS f p)

/-- The set-theoretic fibre `F = f^{-1}({y})`, with the topology induced from `|X|`, has dimension
zero. -/
@[stacks 0ACK "condition (3)"]
def IsZeroDimensionalSetFibre (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) : Prop :=
  topologicalKrullDim (setFibre B S hS f p) = 0

/-- The point set of the field fibre `X_k` is a discrete topological space. -/
@[stacks 0ACK "condition (5)"]
def IsDiscreteFieldFibrePoints (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) : Prop :=
  DiscreteTopology (points B S hS (fieldFibre B S hS f p))

/-- The point set of the field fibre `X_k` has dimension zero. -/
@[stacks 0ACK "condition (6)"]
def IsZeroDimensionalFieldFibrePoints (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) : Prop :=
  topologicalKrullDim (points B S hS (fieldFibre B S hS f p)) = 0

/-! ### Condition (7): the dimension of the field fibre as an algebraic space -/

/-- The field fibre `X_k`, as an algebraic space over `S`, has dimension zero in the sense of Tag
04N6. -/
@[stacks 0ACK "condition (7)"]
def IsZeroDimensionalFieldFibre (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p)) : Prop :=
  dimension B S hS (fieldFibre B S hS f p) hXk = 0

/-! ### Condition (8): quasi-finiteness above the point -/

/-- The morphism `f` is quasi-finite, in the sense of part (2) of Tag 03XJ, at every point of `|X|`
lying above the point of `|Y|` represented by `p`. -/
@[stacks 0ACK "condition (8)"]
def IsQuasiFiniteAboveFieldValuedPoint (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) : Prop :=
  ∀ x ∈ setFibre B S hS f p, IsQuasiFiniteAt B S hS f x

/-! ### Nonemptiness of the two fibres -/

/-- The field fibre `X_k` has a point exactly when the set-theoretic fibre `f^{-1}({y})` is
nonempty. -/
theorem nonempty_points_fieldFibre_iff (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    Nonempty (points B S hS (fieldFibre B S hS f p)) ↔ (setFibre B S hS f p).Nonempty := by
  rw [← range_pointsMap_fst_fieldFibre B S hS f p]
  exact Set.range_nonempty_iff_nonempty.symm

/-! ### Condition (2) implies condition (3), and condition (5) implies condition (6) -/

/-- A nonempty topological space has nonnegative Krull dimension. -/
private theorem zero_le_topologicalKrullDim (T : Type*) [TopologicalSpace T] [Nonempty T] :
    0 ≤ topologicalKrullDim T := by
  have : Nonempty (TopologicalSpace.IrreducibleCloseds T) :=
    ⟨⟨closure {Classical.arbitrary T}, isIrreducible_iff_closure.2 isIrreducible_singleton,
      isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

/-- A discrete set-theoretic fibre has dimension at most zero. -/
theorem topologicalKrullDim_setFibre_le_zero_of_isDiscreteSetFibre (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (h : IsDiscreteSetFibre B S hS f p) :
    topologicalKrullDim (setFibre B S hS f p) ≤ 0 :=
  have : DiscreteTopology (setFibre B S hS f p) := h
  topologicalKrullDim_zero_of_discreteTopology _

/-- A nonempty discrete set-theoretic fibre has dimension zero. -/
@[stacks 0ACK "condition (2) implies condition (3), nonempty fibre"]
theorem isZeroDimensionalSetFibre_of_isDiscreteSetFibre (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (h : IsDiscreteSetFibre B S hS f p)
    (hne : (setFibre B S hS f p).Nonempty) :
    IsZeroDimensionalSetFibre B S hS f p :=
  have : Nonempty (setFibre B S hS f p) := hne.to_subtype
  le_antisymm (topologicalKrullDim_setFibre_le_zero_of_isDiscreteSetFibre B S hS f p h)
    (zero_le_topologicalKrullDim _)

/-- A discrete point set of the field fibre has dimension at most zero. -/
theorem topologicalKrullDim_points_fieldFibre_le_zero_of_isDiscreteFieldFibrePoints
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) (h : IsDiscreteFieldFibrePoints B S hS f p) :
    topologicalKrullDim (points B S hS (fieldFibre B S hS f p)) ≤ 0 :=
  have : DiscreteTopology (points B S hS (fieldFibre B S hS f p)) := h
  topologicalKrullDim_zero_of_discreteTopology _

/-- A nonempty discrete point set of the field fibre has dimension zero. -/
@[stacks 0ACK "condition (5) implies condition (6), nonempty fibre"]
theorem isZeroDimensionalFieldFibrePoints_of_isDiscreteFieldFibrePoints (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (h : IsDiscreteFieldFibrePoints B S hS f p)
    (hne : Nonempty (points B S hS (fieldFibre B S hS f p))) :
    IsZeroDimensionalFieldFibrePoints B S hS f p :=
  have := hne
  le_antisymm
    (topologicalKrullDim_points_fieldFibre_le_zero_of_isDiscreteFieldFibrePoints B S hS f p h)
    (zero_le_topologicalKrullDim _)

/-! ### An introduction rule for condition (8) -/

/-- A locally quasi-finite morphism out of an algebraic space is quasi-finite at every point of its
source. -/
theorem isQuasiFiniteAt_of_isLocallyQuasiFinite (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (hf : IsLocallyQuasiFinite B S hS f) (x : points B S hS X) :
    IsQuasiFiniteAt B S hS f x := by
  have hiso : IsIso (Subfunctor.ι (⊤ : Subfunctor X)) := inferInstance
  refine ⟨⊤, isOpenSubspace_top hX,
    pointsMap B S hS X (inv (Subfunctor.ι (⊤ : Subfunctor X))) x, ?_, ?_⟩
  · rw [← Function.comp_apply (f := pointsMap B S hS _ (Subfunctor.ι (⊤ : Subfunctor X))),
      ← pointsMap_comp, IsIso.inv_hom_id, pointsMap_id, id_eq]
  · intro U V a b h ha hb hsq
    refine hf U V (a ≫ Subfunctor.ι (⊤ : Subfunctor X)) b h ?_ hb ?_
    · exact MorphismProperty.RespectsIso.postcomp _ _ a ha
    · rw [Category.assoc]
      exact hsq

/-- A locally quasi-finite morphism out of an algebraic space is quasi-finite at every point above
every field-valued point of the target. -/
theorem isQuasiFiniteAboveFieldValuedPoint_of_isLocallyQuasiFinite
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y} (hf : IsLocallyQuasiFinite B S hS f)
    (p : FieldValuedPoint B S hS Y) :
    IsQuasiFiniteAboveFieldValuedPoint B S hS f p :=
  fun x _ ↦ isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS hX hf x

end AlgebraicGeometry.Space

end
