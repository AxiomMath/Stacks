module

public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
public import StacksFrontier.Topology.Dimension.NowhereDense
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension of the closure of the image of a morphism of schemes over a field

Let `f : X ⟶ Y` be a morphism of schemes locally of finite type over a field `k`, with `X` a
Noetherian space. Then for every closed `A ⊆ X` the closure of `f '' A` has dimension at most
that of `A`; in particular the closure of the image of `f` has dimension at most `dim X`.

No such bound holds for a general continuous map, nor even for a general morphism of schemes:
the inclusion of the generic point `Spec K ⟶ Spec R` of a discrete valuation ring has
zero-dimensional source and image closure all of `Spec R`. What makes the statement true here
is that every point of the closure of the image is a specialization of the image of one of the
finitely many generic points, and that over a field the dimension of the closure of a point is
the transcendence degree of its residue field, which only drops along a morphism.

## Main results

* `AlgebraicGeometry.trdeg_residueField_map_le`: along a morphism of schemes over `k` the
  transcendence degree of the residue field of the target at `f x` is at most that of the
  residue field of the source at `x`, because `κ(f x) ↪ κ(x)` is a map of `k`-algebras.
* `AlgebraicGeometry.topologicalKrullDim_closure_singleton_image_le`: the closure of the image
  of a point has dimension at most that of the closure of the point.
* `AlgebraicGeometry.topologicalKrullDim_closure_image_le`: **the image dimension bound** for a
  closed subset, `dim (closure (f '' A)) ≤ dim A`.
* `AlgebraicGeometry.topologicalKrullDim_closure_range_le`: the same for the whole image,
  `dim (closure (range f)) ≤ dim X`.

## Implementation notes

The chain combinatorics is done once and for all by
`topologicalKrullDim_le_of_forall_closure`: on a quasi-sober space the dimension of a closed
subset is bounded by the dimensions of the closures of its points. So the proof only has to
bound `dim (closure {y})` for `y` in the closure of the image. A closed subset of a Noetherian
space is a finite union of irreducible closed sets
(`TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`), each of which is
the closure of a point `η ∈ A` because a scheme is sober; the finite union of the closed sets
`closure {f η}` then already contains the closure of `f '' A`, so `closure {y} ⊆ closure {f η}`
for one such `η`, and the right-hand side has dimension
`trdeg_k κ(f η) ≤ trdeg_k κ(η) = dim (closure {η}) ≤ dim A`.

The `k`-algebra structure on a residue field is not an instance: as in
`StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg`, each statement introduces it with
a `letI` as the composite of global sections with evaluation at the point.
-/

@[expose] public section

open CategoryTheory Set TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Along a morphism `f : X ⟶ Y` of schemes over a field `k`, the residue field of `Y` at
`f x` embeds into the residue field of `X` at `x` compatibly with `k`, so its transcendence
degree over `k` is at most that of `κ(x)`. -/
theorem trdeg_residueField_map_le (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (hf : f ≫ sY = sX) (x : X) :
    letI : Algebra k (Y.residueField (f x)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation (f x)).hom.toAlgebra
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Algebra.trdeg k (Y.residueField (f x)) ≤ Algebra.trdeg k (X.residueField x) := by
  let : Algebra k (Y.residueField (f x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation (f x)).hom.toAlgebra
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have hcomm : ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation (f x)) ≫
      f.residueFieldMap x =
      (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation x := by
    rw [← hf, Scheme.Hom.comp_appTop]
    simp only [Category.assoc, Scheme.Γevaluation_naturality]
  let φ : Y.residueField (f x) →ₐ[k] X.residueField x :=
    { (f.residueFieldMap x).hom with
      commutes' := fun r => ConcreteCategory.congr_hom hcomm r }
  exact trdeg_le_of_injective φ (f.residueFieldMap x).hom.injective

/-- The closure of the image of a point of a scheme locally of finite type over a field has
dimension at most that of the closure of the point itself. -/
theorem topologicalKrullDim_closure_singleton_image_le (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (hf : f ≫ sY = sX) (x : X) :
    topologicalKrullDim (closure ({f x} : Set Y)) ≤
      topologicalKrullDim (closure ({x} : Set X)) := by
  let : Algebra k (Y.residueField (f x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation (f x)).hom.toAlgebra
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  rw [topologicalKrullDim_closure_singleton_eq_trdeg k Y sY (f x),
    topologicalKrullDim_closure_singleton_eq_trdeg k X sX x]
  exact WithBot.coe_le_coe.mpr
    (OrderHomClass.mono Cardinal.toENat (trdeg_residueField_map_le k f sX sY hf x))

/-- **The image dimension bound.** Let `f : X ⟶ Y` be a morphism of schemes locally of finite
type over a field `k`, with `X` a Noetherian space, and let `A ⊆ X` be closed. Then the closure
of `f '' A` has dimension at most that of `A`. -/
@[ega "IV 5.4.2" "partial"]
theorem topologicalKrullDim_closure_image_le (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [NoetherianSpace X]
    (hf : f ≫ sY = sX) {A : Set X} (hA : IsClosed A) :
    topologicalKrullDim (closure (f.base '' A) : Set Y) ≤ topologicalKrullDim A := by
  classical
  obtain ⟨S, hSfin, hScl, hSirr, hSA⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hA
  have : Finite S := hSfin
  -- a generic point for each irreducible piece of `A`
  choose η hη using fun t : S ↦ QuasiSober.sober (hSirr t.1 t.2) (hScl t.1 t.2)
  have hmem : ∀ t : S, closure ({η t} : Set X) ⊆ A := fun t ↦ by
    rw [hη t, hSA]; exact subset_sUnion_of_mem t.2
  -- the finite union of the closures of the images of those generic points
  have hUclosed : IsClosed (⋃ t : S, closure ({f (η t)} : Set Y)) :=
    isClosed_iUnion_of_finite fun _ ↦ isClosed_closure
  have himg : f.base '' A ⊆ ⋃ t : S, closure ({f (η t)} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hSA] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    refine mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    have hx' : x ∈ closure ({η ⟨t, ht⟩} : Set X) := by rw [hη ⟨t, ht⟩]; exact hxt
    exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hx').map f.base.hom.continuous)
  refine topologicalKrullDim_le_of_forall_closure isClosed_closure fun y hy ↦ ?_
  obtain ⟨t, hyt⟩ := mem_iUnion.mp (closure_minimal himg hUclosed hy)
  calc topologicalKrullDim (closure ({y} : Set Y))
      ≤ topologicalKrullDim (closure ({f (η t)} : Set Y)) :=
        topologicalKrullDim_le_of_subset
          (closure_minimal (singleton_subset_iff.mpr hyt) isClosed_closure)
    _ ≤ topologicalKrullDim (closure ({η t} : Set X)) :=
        topologicalKrullDim_closure_singleton_image_le k f sX sY hf (η t)
    _ ≤ topologicalKrullDim A :=
        topologicalKrullDim_le_of_subset (hmem t)

/-- **The image dimension bound.** Let `f : X ⟶ Y` be a morphism of schemes locally of finite
type over a field `k` with `X` a Noetherian space. Then the closure of the image of `f` has
dimension at most that of `X`. -/
@[ega "IV 5.4.2" "partial"]
theorem topologicalKrullDim_closure_range_le (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [NoetherianSpace X]
    (hf : f ≫ sY = sX) :
    topologicalKrullDim (closure (Set.range f.base) : Set Y) ≤ topologicalKrullDim X := by
  have h := topologicalKrullDim_closure_image_le k f sX sY hf
    (isClosed_univ : IsClosed (Set.univ : Set X))
  rwa [Set.image_univ, topologicalKrullDim_univ] at h

end AlgebraicGeometry

end
