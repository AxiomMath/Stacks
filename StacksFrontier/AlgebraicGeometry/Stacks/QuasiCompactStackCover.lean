module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackCover
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack

/-!
# Quasi-compactness of an algebraic stack covered by open substacks (Stacks 04YD)

An algebraic stack covered by finitely many quasi-compact open substacks is quasi-compact: the
points of the substacks cover the points of the stack, so its space of points, with the
canonical topology of Tag 04XL, is the image of a finite disjoint union of compact spaces.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactStack_of_finite_jointly_surjective`: a finite family of
  1-morphisms out of quasi-compact algebraic stacks which is jointly surjective on points has
  quasi-compact target.
* `AlgebraicGeometry.Stack.exists_pointsMap_fullSubcategoryInclusion_eq_of_isOpenSubstackCover`:
  a family of open substacks covering an algebraic stack is jointly surjective on points.
* `AlgebraicGeometry.Stack.isQuasiCompactStack_of_isOpenSubstackCover`: **Stacks 04YD**,
  quasi-compactness of an algebraic stack covered by finitely many quasi-compact open substacks.

## Implementation notes

**The finite union of Tag 04YD.** A finite disjoint union of algebraic stacks is, in the
2-category of Tag 03YP, covered by its members as pairwise disjoint open substacks, so the
quasi-compactness assertion of Tag 04YD is stated for an algebraic stack carrying a finite
covering family of open substacks in the sense of
`AlgebraicGeometry.Stack.IsOpenSubstackCover`. That drops disjointness of the members, which the
argument does not use, and it refers to no coproduct of algebraic stacks: the coproduct of a
family of algebraic stacks is not in the library, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackCover` record, and with it the assertion of
Tag 04YD that the disjoint union *is* an algebraic stack, which is therefore not proved here.

Joint surjectivity on points comes from the covering hypothesis exactly as in Tag 06QI: the
covering sieve of a field object contains an arrow from a field object
(`AlgebraicGeometry.Stack.exists_isFieldObject_arrow_of_mem_topology`), and the restriction of
the object along it lies in one of the substacks.

## References

* [Stacks Project, Tag 04YD](https://stacks.math.columbia.edu/tag/04YD)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A finite family of 1-morphisms out of quasi-compact algebraic stacks which is jointly
surjective on points has quasi-compact target.** The map out of the disjoint union of the point
spaces of the sources is continuous by clause (1) of Tag 04XL on each summand, that disjoint
union is compact because the index type is finite, and the target point space is its image. -/
theorem isQuasiCompactStack_of_finite_jointly_surjective
    {ι : Type*} [Finite ι] {𝒰 : ι → AlgebraicStacks.{u, w} B S hS}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : ∀ i, 𝒰 i ⟶ 𝒳)
    (h𝒰 : ∀ i, IsQuasiCompactStack.{u, w} B S hS (𝒰 i).val (𝒰 i).property)
    (hf : ∀ x, ∃ i y, AlgebraicStacks.pointsMap B S hS (f i) y = x) :
    IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property :=
  let : ∀ i, TopologicalSpace (points B S hS (𝒰 i).val.val (𝒰 i).val.property) :=
    fun i => pointTopology B S hS (𝒰 i).val
  let : TopologicalSpace (points B S hS 𝒳.val.val 𝒳.val.property) :=
    pointTopology B S hS 𝒳.val
  let : ∀ i, CompactSpace (points B S hS (𝒰 i).val.val (𝒰 i).val.property) := h𝒰
  Function.Surjective.compactSpace
    (f := fun p : Σ i, points B S hS (𝒰 i).val.val (𝒰 i).val.property =>
      pointsMap B S hS (𝒰 p.1).val.val (𝒰 p.1).val.property 𝒳.val.property
        (f p.1).hom.hom p.2)
    (continuous_sigma fun i => continuous_pointsMap B S hS (𝒰 i).val 𝒳.val (f i).hom.hom)
    fun x => by obtain ⟨i, y, hy⟩ := hf x; exact ⟨⟨i, y⟩, hy⟩

/-- **An algebraic stack covered by open substacks is covered by the points of those
substacks.** A point of `𝒳` is represented by an object over the spectrum of a field; the
covering sieve supplied by the covering hypothesis contains an arrow from the spectrum of a
field, and the restriction of the object along that arrow lies in one of the substacks, so it is
a field-valued point of that substack refining the given one. -/
theorem exists_pointsMap_fullSubcategoryInclusion_eq_of_isOpenSubstackCover
    {ι : Type*} (𝒳 : AlgebraicStacks.{u, w} B S hS) (𝒰 : ι → OpenSubstack 𝒳)
    (hcover : IsOpenSubstackCover 𝒳 𝒰) (x : AlgebraicStacks.points B S hS 𝒳) :
    ∃ (i : ι) (y : AlgebraicStacks.points B S hS
        (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic)),
      AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic) y = x := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨q, hq⟩ := Quotient.exists_rep x
  have hqField : IsFieldObject B S hS q.base := ⟨q.carrier, q.field, ⟨q.isSpec⟩⟩
  obtain ⟨R, hR, hmem⟩ := hcover q.base ⟨q.obj, q.over⟩
  obtain ⟨V, g, hV, hgR⟩ := exists_isFieldObject_arrow_of_mem_topology B S hS hqField hR
  obtain ⟨i, hi⟩ := hmem g hgR
  obtain ⟨k, hk, ⟨e⟩⟩ := hV
  let _ : Field k := hk
  let p : FieldValuedPoint B S hS (fullSubcategoryBased 𝒳 (𝒰 i).property) :=
    { carrier := k,
      field := hk,
      base := V,
      isSpec := e,
      obj := ⟨_, hi⟩,
      «over» := Functor.IsPreFibered.pullbackObj_proj q.over g }
  refine ⟨i, pointClass B S hS _ _ p, ?_⟩
  rw [← hq]
  exact (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val _ _ q).2
    ⟨_, ⟨𝟙 _⟩, ⟨Functor.IsPreFibered.pullbackMap q.over g⟩⟩

/-- **Stacks 04YD**, quasi-compactness. An algebraic stack covered by finitely many
quasi-compact open substacks is quasi-compact; in particular a finite disjoint union of
quasi-compact algebraic stacks is quasi-compact, disjointness of the members playing no role.
The points of the substacks cover the points of `𝒳`, so this is the topological fact that a
finite union of quasi-compact subsets is quasi-compact. -/
@[stacks 04YD "the union is quasi-compact"]
theorem isQuasiCompactStack_of_isOpenSubstackCover
    {ι : Type*} [Finite ι] (𝒳 : AlgebraicStacks.{u, w} B S hS) (𝒰 : ι → OpenSubstack 𝒳)
    (hcover : IsOpenSubstackCover 𝒳 𝒰)
    (h𝒰 : ∀ i, IsQuasiCompactStack.{u, w} B S hS
      (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val
      (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).property) :
    IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property :=
  isQuasiCompactStack_of_finite_jointly_surjective B S hS
    (fun i => fullSubcategoryInclusion 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic) h𝒰
    (exists_pointsMap_fullSubcategoryInclusion_eq_of_isOpenSubstackCover B S hS 𝒳 𝒰 hcover)

end AlgebraicGeometry.Stack

end
