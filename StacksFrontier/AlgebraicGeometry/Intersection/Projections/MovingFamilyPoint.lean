module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyClosedPoints
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySection

/-!
# The point of the triple product over a triple of closed points

Over an algebraically closed field a closed point of a scheme locally of finite type is a
`k`-point, and the `k`-points of a fibre product over `Spec k` are pairs of `k`-points. So a
source point, a point of the line and a target point, all closed, determine one closed point of
the triple product `𝐏(V) ×_k (ℓ ×_k 𝐏(V))`, and its image in `ℓ ×_k 𝐏(V)` is the value of the
section at the point of the line. This is the bookkeeping that lets a statement about the fibre of
a subset of `ℓ × 𝐏(V)` over a closed point of the line be read off from the triple product and
back.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.ambientPoint`: the `k`-point of `ℓ ×_k 𝐏(V)`
  attached to a closed point of the line and a closed point of `𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.prodPoint`: the `k`-point of the triple product
  attached to three closed points.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.lineSection_comp_pointOfClosedPoint`: the section at
  a closed point of the line carries the `k`-point of `𝐏(V)` at `y` to `ambientPoint`. This is
  the uniqueness of a `k`-point of a fibre product with prescribed projections, which is
  `CategoryTheory.Limits.pullback.hom_ext`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.prSource_prodPoint`,
  `…prLine_prodPoint`, `…prTarget_prodPoint`: the three projections of that point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.prAmbient_prodPoint`: its image in `ℓ × 𝐏(V)` is
  the value of the section at `y`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_prodPoint`: it is a closed point.

## Implementation notes

Everything is `CategoryTheory.Limits.pullback.lift` of `AlgebraicGeometry.pointOfClosedPoint`s,
and every identity is either `CategoryTheory.Limits.pullback.lift_fst`/`lift_snd` or
`CategoryTheory.Limits.pullback.hom_ext`. The last is what replaces a description of the points
of a fibre product: two morphisms from `Spec k` into `ℓ ×_k 𝐏(V)` with the same two projections
are equal, so no identification of the set of points of the product is needed.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- **The `k`-point of `ℓ ×_k 𝐏(V)` attached to a closed point of the line and a closed point of
`𝐏(V)`.** -/
public def ambientPoint (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) (hy : IsClosed ({y} : Set _)) :
    Spec (.of k) ⟶ movingAmbient k V L :=
  pullback.lift (pointOfClosedPoint (movingLineToSpec k V L) lam hlam)
    (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) y hy)
    (by rw [pointOfClosedPoint_comp, pointOfClosedPoint_comp])

/-- The line coordinate of that point. -/
@[reassoc (attr := simp)]
public theorem ambientPoint_comp_ambLine (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set _)) :
    ambientPoint k V L lam hlam y hy ≫ ambLine k V L =
      pointOfClosedPoint (movingLineToSpec k V L) lam hlam :=
  pullback.lift_fst _ _ _

/-- The `𝐏(V)` coordinate of that point. -/
@[reassoc (attr := simp)]
public theorem ambientPoint_comp_ambPoint (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set _)) :
    ambientPoint k V L lam hlam y hy ≫ ambPoint k V L =
      pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) y hy :=
  pullback.lift_snd _ _ _

/-- **The section at a closed point of the line carries the `k`-point at `y` to the `k`-point of
the product at `(λ, y)`.** Both morphisms from `Spec k` have the same two projections, so they
agree. -/
public theorem lineSection_comp_pointOfClosedPoint (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set _)) :
    pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) y hy ≫
        lineSection k V L lam hlam =
      ambientPoint k V L lam hlam y hy := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, lineSection_comp_ambLine, ambientPoint_comp_ambLine,
      ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  · rw [Category.assoc, lineSection_comp_ambPoint, ambientPoint_comp_ambPoint,
      Category.comp_id]

/-- **The `k`-point of the triple product attached to three closed points.** -/
public def prodPoint (x : projectiveSpaceOfModule k V) (hx : IsClosed ({x} : Set _))
    (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) (hy : IsClosed ({y} : Set _)) :
    Spec (.of k) ⟶ movingProd k V L :=
  pullback.lift (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) x hx)
    (ambientPoint k V L lam hlam y hy)
    (by
      rw [pointOfClosedPoint_comp, movingAmbientToSpec, ← Category.assoc,
        ambientPoint_comp_ambLine, pointOfClosedPoint_comp])

/-- The source coordinate of that point. -/
@[reassoc (attr := simp)]
public theorem prodPoint_comp_prSource (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set _)) (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) (hy : IsClosed ({y} : Set _)) :
    prodPoint k V L x hx lam hlam y hy ≫ prSource k V L =
      pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) x hx :=
  pullback.lift_fst _ _ _

/-- The ambient coordinate of that point. -/
@[reassoc (attr := simp)]
public theorem prodPoint_comp_prAmbient (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set _)) (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) (hy : IsClosed ({y} : Set _)) :
    prodPoint k V L x hx lam hlam y hy ≫ prAmbient k V L =
      ambientPoint k V L lam hlam y hy :=
  pullback.lift_snd _ _ _

/-- A composite identity of morphisms of schemes gives the identity on underlying points. -/
private theorem base_apply_eq_of_comp_eq {X Y Z : Scheme} {m : X ⟶ Y} {f : Y ⟶ Z} {n : X ⟶ Z}
    (h : m ≫ f = n) (a : X) : f.base (m.base a) = n.base a := by
  rw [← h]
  rfl

/-- The source point of the triple point is `x`. -/
public theorem prSource_prodPoint (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set _)) (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) (hy : IsClosed ({y} : Set _))
    (a : Spec (.of k)) :
    (prSource k V L).base ((prodPoint k V L x hx lam hlam y hy).base a) = x := by
  rw [base_apply_eq_of_comp_eq (prodPoint_comp_prSource k V L x hx lam hlam y hy)]
  simp

/-- The ambient coordinate of the triple point, on points. -/
public theorem prAmbient_base_prodPoint (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set _)) (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) (hy : IsClosed ({y} : Set _))
    (a : Spec (.of k)) :
    (prAmbient k V L).base ((prodPoint k V L x hx lam hlam y hy).base a) =
      (ambientPoint k V L lam hlam y hy).base a :=
  base_apply_eq_of_comp_eq (prodPoint_comp_prAmbient k V L x hx lam hlam y hy) a

/-- The line coordinate of the triple point is `λ`. -/
public theorem prLine_prodPoint (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set _)) (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) (hy : IsClosed ({y} : Set _))
    (a : Spec (.of k)) :
    (prLine k V L).base ((prodPoint k V L x hx lam hlam y hy).base a) = lam := by
  change (ambLine k V L).base ((prAmbient k V L).base _) = lam
  rw [prAmbient_base_prodPoint,
    base_apply_eq_of_comp_eq (ambientPoint_comp_ambLine k V L lam hlam y hy)]
  simp

/-- The target point of the triple point is `y`. -/
public theorem prTarget_prodPoint (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set _)) (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) (hy : IsClosed ({y} : Set _))
    (a : Spec (.of k)) :
    (prTarget k V L).base ((prodPoint k V L x hx lam hlam y hy).base a) = y := by
  change (ambPoint k V L).base ((prAmbient k V L).base _) = y
  rw [prAmbient_base_prodPoint,
    base_apply_eq_of_comp_eq (ambientPoint_comp_ambPoint k V L lam hlam y hy)]
  simp

/-- **The image of the triple point in `ℓ × 𝐏(V)` is the value of the section at `y`.** -/
public theorem prAmbient_prodPoint (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set _)) (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) (hy : IsClosed ({y} : Set _))
    (a : Spec (.of k)) :
    (prAmbient k V L).base ((prodPoint k V L x hx lam hlam y hy).base a) =
      (lineSection k V L lam hlam).base y := by
  rw [prAmbient_base_prodPoint,
    ← base_apply_eq_of_comp_eq (lineSection_comp_pointOfClosedPoint k V L lam hlam y hy)]
  simp

/-- **The triple point is a closed point of the triple product.** -/
public theorem isClosed_prodPoint (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set _)) (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) (hy : IsClosed ({y} : Set _)) :
    IsClosed ({(prodPoint k V L x hx lam hlam y hy).base
      (IsLocalRing.closedPoint k)} : Set (movingProd k V L)) := by
  have hcomp : prodPoint k V L x hx lam hlam y hy ≫ movingProdToSpec k V L = 𝟙 _ := by
    rw [movingProdToSpec, ← Category.assoc, prodPoint_comp_prAmbient, movingAmbientToSpec,
      ← Category.assoc, ambientPoint_comp_ambLine, pointOfClosedPoint_comp]
  exact mem_closedPoints_iff.mp
    ((pointEquivClosedPoint (movingProdToSpec k V L)
      ⟨prodPoint k V L x hx lam hlam y hy, hcomp⟩).property)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
