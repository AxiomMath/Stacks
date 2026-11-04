module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Reading off a summand or a quotient from a truncation

Let `t` be a t-structure on a triangulated category `C` and let `b` be an integer.

* If `X ⟶ Z ⟶ G ⟶ X[1]` is a distinguished triangle with `X ∈ C^{≤ b}` and `G ∈ C^{≥ b+1}`,
  then `G ≅ τ^{≥ b+1} Z`.
* If `Z ≅ A ⊞ D` with `A ∈ C^{≥ b+1}` and `D ∈ C^{≤ b}`, then `A ≅ τ^{≥ b+1} Z`.

Together they identify two objects which are each the part of a common object above a degree:
if `Z ≅ D ⊞ A ≅ D' ⊞ A'` with `A, A' ∈ C^{≥ b+1}` and `D, D' ∈ C^{≤ b}`, then `A ≅ A'`.

## Main results

* `CategoryTheory.Triangulated.TStructure.nonempty_iso_truncGE_of_distTriang`
* `CategoryTheory.Triangulated.TStructure.nonempty_iso_truncGE_of_iso_biprod`
* `CategoryTheory.Triangulated.TStructure.nonempty_iso_of_iso_biprod_of_iso_biprod`
* `DerivedCategory.nonempty_iso_of_iso_biprod_of_iso_biprod`: the same in `D(A)`, with the degree
  conditions stated through the cohomology objects.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (t : TStructure C)

/-- **The third vertex of a triangle whose first vertex lies in degrees `≤ b` and whose third
lies in degrees `≥ b + 1` is the truncation `τ^{≥ b+1}` of its second vertex.** -/
theorem nonempty_iso_truncGE_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C) (b : ℤ)
    (h₁ : t.IsLE T.obj₁ b) (h₃ : t.IsGE T.obj₃ (b + 1)) :
    Nonempty (T.obj₃ ≅ (t.truncGE (b + 1)).obj T.obj₂) := by
  have := t.isIso₂_truncGE_map_of_isLE T hT b (b + 1) rfl h₁
  exact ⟨(asIso ((t.truncGEπ (b + 1)).app T.obj₃)) ≪≫
    (asIso ((t.truncGE (b + 1)).map T.mor₂)).symm⟩

/-- **A direct summand lying in degrees `≥ b + 1` whose complement lies in degrees `≤ b` is the
truncation `τ^{≥ b+1}` of the sum.** -/
theorem nonempty_iso_truncGE_of_iso_biprod {Z A D : C} [HasBinaryBiproduct D A] (e : Z ≅ D ⊞ A)
    (b : ℤ) (hA : t.IsGE A (b + 1)) (hD : t.IsLE D b) :
    Nonempty (A ≅ (t.truncGE (b + 1)).obj Z) := by
  obtain ⟨φ⟩ := t.nonempty_iso_truncGE_of_distTriang _ (binaryBiproductTriangle_distinguished D A)
    b hD hA
  exact ⟨φ ≪≫ (t.truncGE (b + 1)).mapIso e.symm⟩

/-- **Two decompositions of one object into a part in degrees `≤ b` and a part in degrees
`≥ b + 1` have isomorphic high parts**: if `Z ≅ D ⊞ A` and `Z ≅ D' ⊞ A'` with `A, A'` in degrees
`≥ b + 1` and `D, D'` in degrees `≤ b`, then `A ≅ A'`, both being `τ^{≥ b+1} Z`. -/
theorem nonempty_iso_of_iso_biprod_of_iso_biprod {Z A D A' D' : C} [HasBinaryBiproduct D A]
    [HasBinaryBiproduct D' A'] (e : Z ≅ D ⊞ A) (e' : Z ≅ D' ⊞ A') (b : ℤ)
    (hA : t.IsGE A (b + 1)) (hD : t.IsLE D b) (hA' : t.IsGE A' (b + 1)) (hD' : t.IsLE D' b) :
    Nonempty (A ≅ A') := by
  obtain ⟨φ⟩ := t.nonempty_iso_truncGE_of_iso_biprod e b hA hD
  obtain ⟨φ'⟩ := t.nonempty_iso_truncGE_of_iso_biprod e' b hA' hD'
  exact ⟨φ ≪≫ φ'.symm⟩

end CategoryTheory.Triangulated.TStructure

namespace DerivedCategory

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- **Two decompositions of an object of `D(A)` into a part with cohomology in degrees `≤ b` and a
part with cohomology in degrees `> b` have isomorphic high parts.** -/
theorem nonempty_iso_of_iso_biprod_of_iso_biprod {Z H L H' L' : DerivedCategory A}
    (e : Z ≅ L ⊞ H) (e' : Z ≅ L' ⊞ H') (b : ℤ)
    (hH : ∀ i ≤ b, IsZero ((homologyFunctor A i).obj H))
    (hL : ∀ i, b < i → IsZero ((homologyFunctor A i).obj L))
    (hH' : ∀ i ≤ b, IsZero ((homologyFunctor A i).obj H'))
    (hL' : ∀ i, b < i → IsZero ((homologyFunctor A i).obj L')) :
    Nonempty (H ≅ H') :=
  TStructure.t.nonempty_iso_of_iso_biprod_of_iso_biprod e e' b
    ((isGE_iff H (b + 1)).2 fun i hi => hH i (by lia)) ((isLE_iff L b).2 hL)
    ((isGE_iff H' (b + 1)).2 fun i hi => hH' i (by lia)) ((isLE_iff L' b).2 hL')

end DerivedCategory
