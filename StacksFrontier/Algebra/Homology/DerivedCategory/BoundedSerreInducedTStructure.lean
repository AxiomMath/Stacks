module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# The canonical t-structure induces one on `D^b_B(A)`

Let `A` be an abelian category with a derived category and let `B` be a weak Serre subcategory
of `A`. The full subcategory `D^b_B(A)` of `D(A)` of cohomologically bounded objects with
cohomology in `B` is stable under the truncation functors of the canonical t-structure, so the
t-structure descends to it.

## The argument

`CategoryTheory.ObjectProperty.HasInducedTStructure.mk'` reduces the statement to the stability
of `D^b_B(A)` under `τ^{≤n}` and `τ^{≥n}`, and `τ^{≤n} = τ^{<n+1}` by definition, so only the
pair `τ^{<c}`, `τ^{≥c}` has to be treated. For either of them both halves of membership —
cohomological boundedness and membership of each cohomology object in `B` — are read off the
same two facts about the cohomology of a truncation, already available as
`DerivedCategory.truncLTCompHomologyFunctorIso` and
`DerivedCategory.truncGECompHomologyFunctorIso`: in the degrees a truncation retains, its
cohomology is that of the object, and in the degrees it discards its cohomology vanishes, the
latter being the defining `IsLE`/`IsGE` property of the truncation. So `τ^{<c}K` inherits the
lower bound of `K` and acquires the upper bound `c - 1`, `τ^{≥c}K` inherits the upper bound of
`K` and acquires the lower bound `c`, and in every degree each has cohomology either isomorphic
to one of `K` or zero — and a zero object lies in any weak Serre subcategory.

## Main results

* `DerivedCategoryB.derivedCategoryB_truncLT_obj` and
  `DerivedCategoryB.derivedCategoryB_truncGE_obj`: the cohomology of a truncation of an object
  of `D_B(A)` stays in `B`.
* `DerivedCategoryB.isBounded_truncLT_obj` and `DerivedCategoryB.isBounded_truncGE_obj`: a
  truncation of a cohomologically bounded object is cohomologically bounded.
* `DerivedCategoryB.hasInducedTStructure_derivedCategoryBBounded`: **the canonical t-structure
  on `D(A)` induces one on `D^b_B(A)`**, in the form instance search can use; the induced
  t-structure itself is then `CategoryTheory.ObjectProperty.tStructure`.

## References

* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace DerivedCategoryB

open DerivedCategory ObjectProperty WeakSerre

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **The cohomology of `τ^{<c}K` stays in a weak Serre subcategory `B` when that of `K`
does.** Below `c` it is the cohomology of `K`, and at and above `c` it vanishes. -/
theorem derivedCategoryB_truncLT_obj (B : ObjectProperty A) (hB : IsWeakSerre B) (c : ℤ)
    (K : DerivedCategory A) (hK : derivedCategoryB B K) :
    derivedCategoryB B ((TStructure.t.truncLT c).obj K) := by
  intro i
  by_cases hi : i < c
  · exact hB.isClosedUnderIsomorphisms.of_iso
      ((truncLTCompHomologyFunctorIso c i hi).app K).symm (hK i)
  · exact zero_mem_of_isWeakSerre B hB _
      (isZero_of_isLE ((TStructure.t.truncLT c).obj K) (c - 1) i (by omega))

/-- **The cohomology of `τ^{≥c}K` stays in a weak Serre subcategory `B` when that of `K`
does.** At and above `c` it is the cohomology of `K`, and below `c` it vanishes. -/
theorem derivedCategoryB_truncGE_obj (B : ObjectProperty A) (hB : IsWeakSerre B) (c : ℤ)
    (K : DerivedCategory A) (hK : derivedCategoryB B K) :
    derivedCategoryB B ((TStructure.t.truncGE c).obj K) := by
  intro i
  by_cases hi : c ≤ i
  · exact hB.isClosedUnderIsomorphisms.of_iso
      ((truncGECompHomologyFunctorIso c i hi).app K) (hK i)
  · exact zero_mem_of_isWeakSerre B hB _
      (isZero_of_isGE ((TStructure.t.truncGE c).obj K) c i (by omega))

/-- **`τ^{<c}K` is cohomologically bounded when `K` is.** It is bounded above by `c - 1`
because that is what the truncation means, and it inherits the lower bound of `K` because
below `c` its cohomology is that of `K` and at and above `c` it vanishes. -/
theorem isBounded_truncLT_obj (c : ℤ) (K : DerivedCategory A) (hK : IsBounded K) :
    IsBounded ((TStructure.t.truncLT c).obj K) := by
  obtain ⟨n₀, hn₀⟩ := hK.1
  refine ⟨⟨n₀, fun i hi => ?_⟩, ⟨c - 1, fun i hi => ?_⟩⟩
  · by_cases hic : i < c
    · exact (hn₀ i hi).of_iso ((truncLTCompHomologyFunctorIso c i hic).app K)
    · exact isZero_of_isLE ((TStructure.t.truncLT c).obj K) (c - 1) i (by omega)
  · exact isZero_of_isLE ((TStructure.t.truncLT c).obj K) (c - 1) i hi

/-- **`τ^{≥c}K` is cohomologically bounded when `K` is.** It is bounded below by `c` because
that is what the truncation means, and it inherits the upper bound of `K` because at and above
`c` its cohomology is that of `K` and below `c` it vanishes. -/
theorem isBounded_truncGE_obj (c : ℤ) (K : DerivedCategory A) (hK : IsBounded K) :
    IsBounded ((TStructure.t.truncGE c).obj K) := by
  obtain ⟨n₀, hn₀⟩ := hK.2
  refine ⟨⟨c, fun i hi => ?_⟩, ⟨n₀, fun i hi => ?_⟩⟩
  · exact isZero_of_isGE ((TStructure.t.truncGE c).obj K) c i hi
  · by_cases hic : c ≤ i
    · exact (hn₀ i hi).of_iso ((truncGECompHomologyFunctorIso c i hic).app K).symm
    · exact isZero_of_isGE ((TStructure.t.truncGE c).obj K) c i (by omega)

/-- **`D^b_B(A)` is stable under `τ^{<c}`.** -/
theorem derivedCategoryBBounded_truncLT_obj (B : ObjectProperty A) (hB : IsWeakSerre B) (c : ℤ)
    (K : DerivedCategory A) (hK : derivedCategoryBBounded B K) :
    derivedCategoryBBounded B ((TStructure.t.truncLT c).obj K) :=
  ⟨isBounded_truncLT_obj c K hK.1, derivedCategoryB_truncLT_obj B hB c K hK.2⟩

/-- **`D^b_B(A)` is stable under `τ^{≥c}`.** -/
theorem derivedCategoryBBounded_truncGE_obj (B : ObjectProperty A) (hB : IsWeakSerre B) (c : ℤ)
    (K : DerivedCategory A) (hK : derivedCategoryBBounded B K) :
    derivedCategoryBBounded B ((TStructure.t.truncGE c).obj K) :=
  ⟨isBounded_truncGE_obj c K hK.1, derivedCategoryB_truncGE_obj B hB c K hK.2⟩

/-- **The canonical t-structure on `D(A)` induces one on `D^b_B(A)`** when `B` is a weak Serre
subcategory of `A`, in the form instance search can use. The two truncations of an object of
`D^b_B(A)` cut out by the t-structure are again in `D^b_B(A)` — on the nose, so the
`CategoryTheory.ObjectProperty.isoClosure` the definition allows is not needed — which is the
content of `CategoryTheory.ObjectProperty.HasInducedTStructure.mk'`.

The induced t-structure itself is `CategoryTheory.ObjectProperty.tStructure` applied to this
instance. -/
instance hasInducedTStructure_derivedCategoryBBounded (B : ObjectProperty A)
    [B.IsWeakSerreClass] :
    (derivedCategoryBBounded B).HasInducedTStructure (DerivedCategory.TStructure.t (C := A)) :=
  have hB : IsWeakSerre B := isWeakSerre_of_isWeakSerreClass B
  HasInducedTStructure.mk' fun K hK n =>
    ⟨derivedCategoryBBounded_truncLT_obj B hB (n + 1) K hK,
      derivedCategoryBBounded_truncGE_obj B hB n K hK⟩

end DerivedCategoryB

end
