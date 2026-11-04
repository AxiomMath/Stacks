module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory

/-!
# A weak Serre subcategory read along a distinguished triangle

Let `A` be an abelian category with a derived category and let `B` be a weak Serre subcategory of
`A` ([Stacks, Tag 02MO]).  The strictly full subcategory `D_B(A) ⊆ D(A)` of objects all of whose
cohomology objects lie in `B` ([Stacks, Tag 06UP]) is closed under cones: in a distinguished
triangle `K ⟶ L ⟶ M ⟶ K[1]` with `K` and `L` in `D_B(A)`, the third vertex `M` is in `D_B(A)`.

`DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished`
(`StacksFrontier/Algebra/Homology/DerivedCategory/SerreSubcategory.lean`) is the *middle* vertex
form of this closure, read off the five-term exact sequence of the triangle in cohomology.  The
cone form is that statement rotated once, the rotation of a distinguished triangle being
distinguished and `D_B(A)` being stable under the shift; both inputs are proved beside it.

## Main results

* `DerivedCategoryB.derivedCategoryB_mem_obj₃_of_distinguished`: **`D_B(A)` is closed under
  cones.**
* `DerivedCategoryB.derivedCategoryB_singleFunctor_obj`: an object of `B` placed in a single
  degree lies in `D_B(A)`.

## Implementation notes

The rotation `T.rotate` of `T` has `obj₁ = T.obj₂`, `obj₂ = T.obj₃` and `obj₃ = T.obj₁⟦1⟧` by
definition, so no transport along an isomorphism of triangles is needed; what the rotation costs
is the shift, supplied by `DerivedCategoryB.derivedCategoryB_shift_mem`.

`derivedCategoryB_singleFunctor_obj` needs the weak Serre hypothesis only to know that a zero
object lies in `B` (`DerivedCategoryB.zero_mem_of_isWeakSerre`): outside the single degree the
cohomology vanishes, by the `DerivedCategory.IsLE` and `DerivedCategory.IsGE` instances of
`DerivedCategory.singleFunctor`, and in that degree it is the object itself by Mathlib's
`DerivedCategory.singleFunctorCompHomologyFunctorIso`.

## References

* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategoryB

open WeakSerre

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **The objects of `D(A)` with cohomology in a weak Serre subcategory `B` are closed under
cones.**  Let `T` be a distinguished triangle of `D(A)`.  If every cohomology object of `T.obj₁`
and of `T.obj₂` lies in `B`, then so does every cohomology object of `T.obj₃`.

This is `DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished` applied to `T.rotate`,
whose middle vertex is `T.obj₃` and whose third vertex is `T.obj₁⟦1⟧`. -/
public theorem derivedCategoryB_mem_obj₃_of_distinguished
    (B : ObjectProperty A) (hB : IsWeakSerre B)
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A))
    (h₁ : derivedCategoryB B T.obj₁) (h₂ : derivedCategoryB B T.obj₂) :
    derivedCategoryB B T.obj₃ :=
  derivedCategoryB_mem_obj₂_of_distinguished B hB T.rotate (rot_of_distTriang T hT) h₂
    (derivedCategoryB_shift_mem B hB 1 h₁)

/-- **An object of `B` placed in a single degree has all its cohomology in `B`.**  For `M` in `B`
and `q : ℤ`, the object `M[-q]` of `D(A)` — `M` in cohomological degree `q` — lies in `D_B(A)`:
its cohomology is `M` in degree `q` and zero elsewhere. -/
public theorem derivedCategoryB_singleFunctor_obj
    (B : ObjectProperty A) (hB : IsWeakSerre B) (q : ℤ) {M : A} (hM : B M) :
    derivedCategoryB B ((DerivedCategory.singleFunctor A q).obj M) := by
  intro n
  rcases lt_trichotomy n q with h | h | h
  · exact zero_mem_of_isWeakSerre B hB _ (DerivedCategory.isZero_of_isGE _ q n h)
  · subst h
    exact hB.isClosedUnderIsomorphisms.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso A n).app M).symm hM
  · exact zero_mem_of_isWeakSerre B hB _ (DerivedCategory.isZero_of_isLE _ q n h)

end DerivedCategoryB

end
