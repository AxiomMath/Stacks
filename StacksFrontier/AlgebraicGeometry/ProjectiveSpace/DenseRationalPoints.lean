module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rational points off a proper closed subset are dense

This file supplies the topological half of the exercise in the proof of [Stacks, Tag 0AEM]. The
orbit statement proved in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/PowerMatrixTwoTransitive.lean` says *which*
rational points of a power of projective space the group reaches; what is needed in addition is
that those points are Zariski dense. They are the rational points lying off the union of the
partial diagonals, and that union is a proper closed subset, so the following suffices:

**in an irreducible Jacobson space the closed points outside a proper closed subset are dense**,

together with the fact that over an algebraically closed field the closed points of a scheme
locally of finite type are exactly the images of its rational points.

The irreducibility that this is applied to is that of a product, and the second half of the file
records it: over a separably closed field a product of two irreducible schemes is irreducible.
That statement exists in the library only as a `private` lemma inside
`StacksFrontier/AlgebraicGeometry/Groupoids/OverField/IrreducibleComponents.lean`
(`irreducibleSpace_pullback_of_isSepClosed` there), so it is proved again here — by the same two
lines, geometric irreducibility of each factor by Stacks 020J and then Mathlib's instance for the
fibre product.

## Main results

* `AlgebraicGeometry.dense_closedPoints_diff`: **in a preirreducible Jacobson space the closed
  points outside a proper closed subset are dense.** Pure topology.
* `AlgebraicGeometry.range_apply_closedPoint`: over an algebraically closed field the image points
  of the rational points of a scheme locally of finite type are exactly its closed points.
* `AlgebraicGeometry.dense_setOf_rationalPoint_notMem`: **the two combined** — the points of an
  irreducible scheme locally of finite type over an algebraically closed field which come from a
  rational point and avoid a given proper closed subset are dense.
* `AlgebraicGeometry.irreducibleSpace_pullback_of_isSepClosed` and
  `AlgebraicGeometry.irreducibleSpace_prod_left`: over a separably closed field a fibre product of
  two irreducible schemes is irreducible, and so is a binary product taken in the slice category.

## Implementation notes

The topological statement is the one place where irreducibility is used, and it is used only
through `IsOpen.dense`: a nonempty open subset of a preirreducible space is dense, hence meets the
complement of any proper closed subset. The closed point inside the resulting nonempty open set
then comes from `TopologicalSpace.nonempty_inter_closedPoints`, Mathlib's form of the Jacobson
condition for locally closed subsets. No Chevalley-style constructibility and no scheme-theoretic
density enter.

## References

* [Stacks Project, Tag 005U](https://stacks.math.columbia.edu/tag/005U)
* [Stacks Project, Tag 020J](https://stacks.math.columbia.edu/tag/020J)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Closed points off a proper closed subset -/

/-- **In a preirreducible Jacobson space the closed points outside a proper closed subset are
dense.**

A nonempty open set `U` is dense, so it meets the complement of the closed set `Z`; the resulting
nonempty open set `U \ Z` is locally closed, so by the Jacobson condition it contains a closed
point, which lies in `U` and outside `Z`. -/
theorem dense_closedPoints_diff {X : Type*} [TopologicalSpace X] [PreirreducibleSpace X]
    [JacobsonSpace X] {Z : Set X} (hZ : IsClosed Z) (hZ' : ∃ x : X, x ∉ Z) :
    Dense (closedPoints X \ Z) := by
  refine dense_iff_inter_open.2 fun U hU hUne => ?_
  obtain ⟨x, hx⟩ := hZ'
  have hUZ : (U \ Z).Nonempty := by
    obtain ⟨z, hz₁, hz₂⟩ := (hU.dense hUne).inter_open_nonempty Zᶜ hZ.isOpen_compl ⟨x, hx⟩
    exact ⟨z, hz₂, hz₁⟩
  obtain ⟨y, hy₁, hy₂⟩ :=
    nonempty_inter_closedPoints hUZ (hU.inter hZ.isOpen_compl).isLocallyClosed
  exact ⟨y, hy₁.1, hy₂, hy₁.2⟩

/-! ### Rational points and closed points over an algebraically closed field -/

section RationalPoints

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- **Over an algebraically closed field the image points of the rational points of a scheme
locally of finite type are exactly its closed points.** This is
`AlgebraicGeometry.pointEquivClosedPoint` read as an equality of subsets of the point space. -/
@[ega "IV 10.10.3" "partial"]
theorem range_apply_closedPoint {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] :
    Set.range (fun p : {p : Spec (CommRingCat.of K) ⟶ X // p ≫ f = 𝟙 _} =>
        p.1 (IsLocalRing.closedPoint K)) = closedPoints X := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro x ⟨p, rfl⟩
    exact (pointEquivClosedPoint f p).2
  · intro x hx
    exact ⟨(pointEquivClosedPoint f).symm ⟨x, hx⟩,
      congrArg Subtype.val ((pointEquivClosedPoint f).apply_symm_apply ⟨x, hx⟩)⟩

/-- **The points of an irreducible scheme locally of finite type over an algebraically closed
field which come from a rational point and avoid a given proper closed subset are dense.**

This is the shape the contraction step of [Stacks, Tag 0AEM] consumes: the group moves a pair of
rational points to every rational point off the partial diagonals, and this says that those points
are Zariski dense. -/
@[ega "IV 10.4.8" "partial"]
theorem dense_setOf_rationalPoint_notMem {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [PreirreducibleSpace X] {Z : Set X} (hZ : IsClosed Z)
    (hZ' : ∃ x : X, x ∉ Z) :
    Dense {x : X | (∃ p : Spec (CommRingCat.of K) ⟶ X,
      p ≫ f = 𝟙 _ ∧ p (IsLocalRing.closedPoint K) = x) ∧ x ∉ Z} := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hset : {x : X | (∃ p : Spec (CommRingCat.of K) ⟶ X,
      p ≫ f = 𝟙 _ ∧ p (IsLocalRing.closedPoint K) = x) ∧ x ∉ Z} = closedPoints X \ Z := by
    rw [← range_apply_closedPoint K f]
    ext x
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hxZ⟩
      exact ⟨⟨⟨p, hp⟩, rfl⟩, hxZ⟩
    · rintro ⟨⟨⟨p, hp⟩, rfl⟩, hxZ⟩
      exact ⟨⟨p, hp, rfl⟩, hxZ⟩
  rw [hset]
  exact dense_closedPoints_diff hZ hZ'

end RationalPoints

/-! ### Irreducibility of a product over a separably closed field -/

section Product

variable (K : Type u) [Field K] [IsSepClosed K]

/-- **Over a separably closed field a fibre product of two irreducible schemes is irreducible.**
Each factor is geometrically irreducible by [Stacks, Tag 020J], and a fibre product of
geometrically irreducible schemes along universally open structure morphisms is irreducible.

The library has this only as a `private` lemma inside
`StacksFrontier/AlgebraicGeometry/Groupoids/OverField/IrreducibleComponents.lean`, so it is restated
here. -/
@[ega "IV 4.4.4" "more general", ega "IV 4.5.21" "more general", ega "IV 4.5.8" "(i), special case"]
theorem irreducibleSpace_pullback_of_isSepClosed {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (g : Y ⟶ Spec (CommRingCat.of K))
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    IrreducibleSpace ↥(pullback f g) := by
  have : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K X f
  have : GeometricallyIrreducible g :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K Y g
  exact inferInstance

/-- **A binary product of irreducible schemes over a separably closed field, taken in the slice
category, has irreducible underlying scheme.** The product in `Over (Spec K)` is the fibre product
over `Spec K`. -/
theorem irreducibleSpace_prod_left (A B : Over (Spec (CommRingCat.of K)))
    [IrreducibleSpace A.left] [IrreducibleSpace B.left] :
    IrreducibleSpace ↥(A ⨯ B).left :=
  ObjectProperty.prop_of_iso (P := fun W : Scheme.{u} => IrreducibleSpace ↥W)
    (Over.prodLeftIsoPullback A B).symm
    (irreducibleSpace_pullback_of_isSepClosed K A.hom B.hom)

end Product

end AlgebraicGeometry

end
