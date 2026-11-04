module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Two derived tensor products agree at every pair of objects

Let `P` be a property of complexes such that every object of `D(A)` is the image of a complex
satisfying `P`. Two bifunctors `T₁`, `T₂` on `D(A)` together with isomorphisms

`Tᵢ(Q K, Q L) ≅ Q (W(K, L))`

for all `K`, `L` satisfying `P` (for instance, derived tensor products with `P` being K-flatness
and `W` the tensor product of complexes) are isomorphic at every pair of objects. The isomorphism
depends on a choice of representatives and is not asserted to be natural.

## Main results

* `CategoryTheory.nonempty_bifunctorObjIso_of_kFlatComparisons`: two bifunctors on `D(A)`
  agreeing on the images of complexes satisfying a property `P`, in the presence of enough
  `P`-representatives, are isomorphic at each pair of objects.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

/-- Two bifunctors `T₁`, `T₂` on `D(A)` with isomorphisms `Tᵢ(Q K, Q L) ≅ Q (W K L)` for all
complexes `K`, `L` satisfying `P` are isomorphic at every pair of objects, provided every object
of `D(A)` is the image of a complex satisfying `P`. -/
theorem nonempty_bifunctorObjIso_of_kFlatComparisons
    (P : CochainComplex A ℤ → Prop)
    (hex : ∀ Z : DerivedCategory A, ∃ K : CochainComplex A ℤ,
      P K ∧ Nonempty (DerivedCategory.Q.obj K ≅ Z))
    (T₁ T₂ : DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A)
    (W : CochainComplex A ℤ → CochainComplex A ℤ → CochainComplex A ℤ)
    (c₁ : ∀ K L : CochainComplex A ℤ, P K → P L →
      ((T₁.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
        DerivedCategory.Q.obj (W K L)))
    (c₂ : ∀ K L : CochainComplex A ℤ, P K → P L →
      ((T₂.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
        DerivedCategory.Q.obj (W K L)))
    (Z₁ Z₂ : DerivedCategory A) :
    Nonempty ((T₁.obj Z₁).obj Z₂ ≅ (T₂.obj Z₁).obj Z₂) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hex Z₁
  obtain ⟨L, hL, ⟨eL⟩⟩ := hex Z₂
  exact ⟨((T₁.mapIso eK).app Z₂).symm ≪≫
    ((T₁.obj (DerivedCategory.Q.obj K)).mapIso eL).symm ≪≫
    c₁ K L hK hL ≪≫ (c₂ K L hK hL).symm ≪≫
    (T₂.obj (DerivedCategory.Q.obj K)).mapIso eL ≪≫ (T₂.mapIso eK).app Z₂⟩

end CategoryTheory

end
