module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ClosedPointBound
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closed points of the schemes of the Moving Lemma

The line `ℓ`, the ambient product `ℓ ×_k 𝐏(V)` and the triple product `𝐏(V) ×_k (ℓ ×_k 𝐏(V))` are
all of finite type over the ground field, hence Jacobson spaces: the closed points are dense in
every closed subset. Two consequences are used throughout the construction of the family `C'`.
First, a closed subset is determined by its closed points, so an identity between closed subsets
may be checked on closed points only. Second, a morphism between schemes of finite type over an
algebraically closed field carries closed points to closed points, because a closed point is a
`k`-point and a `k`-point of the target composes to a `k`-point.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.jacobsonSpace_movingLine`,
  `…jacobsonSpace_movingAmbient`, `…jacobsonSpace_movingProd`: the three schemes are Jacobson.
* `AlgebraicGeometry.eq_of_inter_closedPoints_eq`: two closed subsets of a Jacobson space with
  the same closed points are equal.
* `AlgebraicGeometry.exists_isClosed_singleton_mem`: a nonempty closed subset of a Jacobson space
  contains a point closed in the ambient space.
* `AlgebraicGeometry.closure_eq_univ_of_closedPoints_subset`: a subset of a Jacobson space
  containing every closed point is dense.
* `AlgebraicGeometry.isIrreducible_of_isClosedMap_of_unique_closedPoint`: a closed set with
  irreducible image under a closed map, having at most one closed point over each point of that
  image, is irreducible.
* `AlgebraicGeometry.isClosed_singleton_image_of_isClosed_singleton`: a morphism over `Spec k`,
  with `k` algebraically closed and both schemes locally of finite type, carries closed points to
  closed points.

## Implementation notes

Jacobsonness comes from `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace` together with the
Jacobsonness of the spectrum of a field; the structure morphisms are locally of finite type
because they are proper, which is recorded in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProduct`.

The image of a closed point is computed through `AlgebraicGeometry.pointOfClosedPoint`, the
`k`-point attached to a closed point over an algebraically closed field, and
`AlgebraicGeometry.pointEquivClosedPoint`, which says that the `k`-points of a scheme locally of
finite type over `k` are exactly its closed points. No residue-field computation is carried out
by hand.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- **A closed subset of a Jacobson space is determined by its closed points.** -/
public theorem eq_of_inter_closedPoints_eq {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    {S T : Set X} (hS : IsClosed S) (hT : IsClosed T)
    (h : S ∩ closedPoints X = T ∩ closedPoints X) : S = T := by
  rw [← hS.closure_eq, ← hT.closure_eq, ← JacobsonSpace.closure_inter_closedPoints_eq_closure
    hS.isLocallyClosed, ← JacobsonSpace.closure_inter_closedPoints_eq_closure hT.isLocallyClosed,
    h]

/-- **A nonempty locally closed subset of a Jacobson space contains a point closed in the
ambient space.** Such a subset meets the closed points of the ambient space, which in a Jacobson
space are dense in every locally closed subset. -/
@[ega "IV 10.1.2" "implication a′ ⇒ a"]
public theorem exists_isClosed_singleton_mem_of_isLocallyClosed {X : Type*}
    [TopologicalSpace X] [JacobsonSpace X] {S : Set X} (hSne : S.Nonempty)
    (hS : IsLocallyClosed S) : ∃ x ∈ S, IsClosed ({x} : Set X) := by
  obtain ⟨x, hxS, hxc⟩ := nonempty_inter_closedPoints hSne hS
  exact ⟨x, hxS, mem_closedPoints_iff.mp hxc⟩

/-- **A nonempty closed subset of a Jacobson space contains a point closed in the ambient
space.** -/
public theorem exists_isClosed_singleton_mem {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    {S : Set X} (hSne : S.Nonempty) (hS : IsClosed S) :
    ∃ x ∈ S, IsClosed ({x} : Set X) :=
  exists_isClosed_singleton_mem_of_isLocallyClosed hSne hS.isLocallyClosed

/-- **A subset of a Jacobson space containing every closed point is dense.** -/
public theorem closure_eq_univ_of_closedPoints_subset {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {S : Set X} (h : closedPoints X ⊆ S) : closure S = Set.univ :=
  Set.eq_univ_of_univ_subset (closure_closedPoints (X := X) ▸ closure_mono h)

/-- **A closed set with irreducible image and at most one closed point over each point of that
image is irreducible.** Let `f` be a closed map on a Jacobson space, `N` a nonempty closed set
whose image is irreducible, and suppose two closed points of `N` with the same image agree. If
`N = A ∪ B` with `A`, `B` closed, the image of one of them, say `A`, is the whole image; then
every closed point of `N` lies in `A`, because the nonempty closed set of points of `A` over its
image contains a closed point, which by uniqueness is that very point. So `A` contains every
closed point of `N` and therefore all of `N`.

This is what makes the graph of a family irreducible: its closed points are in bijection with
those of the base, and a point of the graph that is closed is determined by its image. -/
public theorem isIrreducible_of_isClosedMap_of_unique_closedPoint {Z W : Type*}
    [TopologicalSpace Z] [TopologicalSpace W] [JacobsonSpace Z] {f : Z → W}
    (hf : IsClosedMap f) {N : Set Z} (hN : IsClosed N) (hNne : N.Nonempty)
    (himg : IsIrreducible (f '' N))
    (hclosed : ∀ t ∈ N, IsClosed ({t} : Set Z) → IsClosed ({f t} : Set W))
    (huniq : ∀ t ∈ N, ∀ t' ∈ N, IsClosed ({t} : Set Z) → IsClosed ({t'} : Set Z) →
      f t = f t' → t = t')
    (hcont : Continuous f) :
    IsIrreducible N := by
  refine ⟨hNne, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro A B hA hB hsub
  have himgsub : f '' N ⊆ f '' (A ∩ N) ∪ f '' (B ∩ N) := by
    rintro _ ⟨t, htN, rfl⟩
    rcases hsub htN with h | h
    · exact Or.inl ⟨t, ⟨h, htN⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨h, htN⟩, rfl⟩
  have key : ∀ A' : Set Z, IsClosed A' → f '' N ⊆ f '' (A' ∩ N) → N ⊆ A' := by
    intro A' hA' hA'img
    refine Set.subset_of_isClosed_of_closedPoints_subset hN hA' fun t htN htc => ?_
    obtain ⟨t', ⟨ht'A, ht'N⟩, ht'⟩ := hA'img ⟨t, htN, rfl⟩
    have hft : IsClosed ({f t} : Set W) := hclosed t htN htc
    have hne : (A' ∩ N ∩ f ⁻¹' {f t}).Nonempty := ⟨t', ⟨ht'A, ht'N⟩, ht'⟩
    obtain ⟨t'', ⟨⟨ht''A, ht''N⟩, ht''f⟩, ht''c⟩ :=
      exists_isClosed_singleton_mem hne ((hA'.inter hN).inter (hft.preimage hcont))
    rw [huniq t htN t'' ht''N htc ht''c (Set.mem_singleton_iff.mp ht''f).symm]
    exact ht''A
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp himg.2 _ _
    (hf _ (hA.inter hN)) (hf _ (hB.inter hN)) himgsub with h | h
  · exact Or.inl (key A hA h)
  · exact Or.inr (key B hB h)

/-- **A morphism over an algebraically closed field carries closed points to closed points.**
A closed point of the source is a `k`-point; composing it with the morphism gives a `k`-point of
the target, whose underlying point is therefore closed. -/
public theorem isClosed_singleton_image_of_isClosed_singleton {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ Spec (.of k))
    (gY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType gX] [LocallyOfFiniteType gY]
    (hfg : f ≫ gY = gX) (x : X) (hx : IsClosed ({x} : Set X)) :
    IsClosed ({f.base x} : Set Y) := by
  have hcomp : (pointOfClosedPoint gX x hx ≫ f) ≫ gY = 𝟙 _ := by
    rw [Category.assoc, hfg, pointOfClosedPoint_comp]
  have hmem := ((pointEquivClosedPoint gY) ⟨_, hcomp⟩).property
  convert mem_closedPoints_iff.mp hmem using 2
  exact (congrArg f.base (pointOfClosedPoint_apply gX x hx (IsLocalRing.closedPoint k))).symm

namespace ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- The line is a Jacobson space: it is of finite type over the ground field. -/
public instance jacobsonSpace_movingLine : JacobsonSpace (movingLine k V L) :=
  LocallyOfFiniteType.jacobsonSpace (movingLineToSpec k V L)

/-- The ambient product `ℓ × 𝐏(V)` is a Jacobson space. -/
public instance jacobsonSpace_movingAmbient : JacobsonSpace (movingAmbient k V L) :=
  LocallyOfFiniteType.jacobsonSpace (movingAmbientToSpec k V L)

/-- The triple product is a Jacobson space. -/
public instance jacobsonSpace_movingProd : JacobsonSpace (movingProd k V L) :=
  LocallyOfFiniteType.jacobsonSpace (movingProdToSpec k V L)

/-- `𝐏(V)` is a Jacobson space. -/
public instance jacobsonSpace_projectiveSpaceOfModule :
    JacobsonSpace (projectiveSpaceOfModule k V) :=
  LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
