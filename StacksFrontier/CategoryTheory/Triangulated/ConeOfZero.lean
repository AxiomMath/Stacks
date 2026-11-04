module

public import StacksFrontier.CategoryTheory.Triangulated.Elementary

/-!
# The cone of a zero morphism and the cone of a partial identity

Let `C` be a pre-triangulated category with binary biproducts.

If `X --0--> Y --g--> Z --h--> X⟦1⟧` is a distinguished triangle whose first morphism is zero,
then `h` admits a right inverse `s` and `g ⊕ s : Y ⊞ X⟦1⟧ ⟶ Z` is an isomorphism: the cone of a
zero morphism is `Y ⊞ X⟦1⟧`.

If instead the first morphism is the *partial identity*
`biprod.map (𝟙 A) 0 : A ⊞ B ⟶ A ⊞ B` — the identity on one summand and zero on the other — then
its cone is `B ⊞ B⟦1⟧`: the summand on which the map is the identity is annihilated, and the
summand on which it is zero contributes a cone of a zero morphism.

## Main results

* `CategoryTheory.Pretriangulated.exists_isIso_biprod_desc_of_mor₁_eq_zero`: for a `Triangle`
  whose `mor₁` vanishes, `mor₃` has a right inverse `s` and `biprod.desc mor₂ s` is an
  isomorphism.
* `CategoryTheory.Pretriangulated.nonempty_iso_biprod_shift_of_mor₁_eq_zero`: the same
  isomorphism, as `Nonempty (T.obj₂ ⊞ T.obj₁⟦1⟧ ≅ T.obj₃)`.
* `CategoryTheory.Pretriangulated.nonempty_iso_biprod_shift_of_cone_zero`: the same, for the
  triangle `Triangle.mk (0 : X ⟶ Y) g h`.
* `CategoryTheory.Pretriangulated.nonempty_iso_biprod_shift_of_cone_biprod_map_id_zero`: the
  cone of `biprod.map (𝟙 A) (0 : B ⟶ B)` is `B ⊞ B⟦1⟧`.

## References

* [Stacks Project, Tag 05QT](https://stacks.math.columbia.edu/tag/05QT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasBinaryBiproducts C]

/-- **The cone of a zero morphism splits.** Let `T = (X, Y, Z, f, g, h)` be a distinguished
triangle in a pre-triangulated category with `f = 0`. Then `h : Z ⟶ X⟦1⟧` admits a right
inverse `s : X⟦1⟧ ⟶ Z`, and for that `s` the map `g ⊕ s : Y ⊞ X⟦1⟧ ⟶ Z` is an isomorphism. -/
theorem exists_isIso_biprod_desc_of_mor₁_eq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (hf : T.mor₁ = 0) :
    ∃ s : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃, s ≫ T.mor₃ = 𝟙 (T.obj₁⟦(1 : ℤ)⟧) ∧
      IsIso (biprod.desc T.mor₂ s : T.obj₂ ⊞ T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃) :=
  Stacks05QT_split T.rotate (rot_of_distTriang T hT)
    (by rw [Triangle.rotate_mor₃, hf, Functor.map_zero]; exact neg_zero)

/-- **The cone of a zero morphism is the biproduct of the target with the shifted source.**
For a distinguished triangle `T = (X, Y, Z, 0, g, h)` there is an isomorphism
`Y ⊞ X⟦1⟧ ≅ Z`, namely `g ⊕ s` for a right inverse `s` of `h`. -/
theorem nonempty_iso_biprod_shift_of_mor₁_eq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (hf : T.mor₁ = 0) :
    Nonempty (T.obj₂ ⊞ T.obj₁⟦(1 : ℤ)⟧ ≅ T.obj₃) :=
  let ⟨s, _, _⟩ := exists_isIso_biprod_desc_of_mor₁_eq_zero T hT hf
  ⟨asIso (biprod.desc T.mor₂ s)⟩

/-- **The cone of `0 : X ⟶ Y` is `Y ⊞ X⟦1⟧`.** If `Triangle.mk (0 : X ⟶ Y) g h` is
distinguished, then `Y ⊞ X⟦1⟧ ≅ Z`. -/
theorem nonempty_iso_biprod_shift_of_cone_zero {X Y Z : C} (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (0 : X ⟶ Y) g h ∈ distTriang C) :
    Nonempty (Y ⊞ X⟦(1 : ℤ)⟧ ≅ Z) :=
  nonempty_iso_biprod_shift_of_mor₁_eq_zero (Triangle.mk (0 : X ⟶ Y) g h) hT rfl

/-- **The cone of a partial identity.** Let `A`, `B` be objects of a pre-triangulated category
with binary biproducts and let
`A ⊞ B --diag(𝟙_A, 0)--> A ⊞ B --g--> Z --h--> (A ⊞ B)⟦1⟧` be a distinguished triangle. Then
`Z ≅ B ⊞ B⟦1⟧`: the summand carrying the identity is annihilated and the summand carrying the
zero morphism contributes the cone of a zero morphism. -/
theorem nonempty_iso_biprod_shift_of_cone_biprod_map_id_zero {A B Z : C} (g : A ⊞ B ⟶ Z)
    (h : Z ⟶ (A ⊞ B)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.map (𝟙 A) (0 : B ⟶ B)) g h ∈ distTriang C) :
    Nonempty (B ⊞ B⟦(1 : ℤ)⟧ ≅ Z) := by
  have h12 : biprod.map (𝟙 A) (0 : B ⟶ B) ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have h31 : h ≫ (biprod.map (𝟙 A) (0 : B ⟶ B))⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ hT
  have hinlg : (biprod.inl : A ⟶ A ⊞ B) ≫ g = 0 := by simpa using biprod.inl ≫= h12
  have hg : (biprod.snd : A ⊞ B ⟶ B) ≫ (biprod.inr ≫ g) = g := by ext <;> simp [hinlg]
  have hhfst : h ≫ (biprod.fst : A ⊞ B ⟶ A)⟦(1 : ℤ)⟧' = 0 := by
    simpa [← Functor.map_comp] using h31 =≫ (biprod.fst : A ⊞ B ⟶ A)⟦(1 : ℤ)⟧'
  have hh : (h ≫ (biprod.snd : A ⊞ B ⟶ B)⟦(1 : ℤ)⟧') ≫
      (biprod.inr : B ⟶ A ⊞ B)⟦(1 : ℤ)⟧' = h := by
    conv_rhs =>
      rw [← Category.comp_id h, ← CategoryTheory.Functor.map_id (shiftFunctor C (1 : ℤ)),
        ← biprod.total]
    rw [Functor.map_add, Functor.map_comp, Functor.map_comp, Preadditive.comp_add,
      ← Category.assoc, ← Category.assoc, hhfst, zero_comp, zero_add]
  let S : Triangle C := Triangle.mk (0 : B ⟶ B) (biprod.inr ≫ g)
    (h ≫ (biprod.snd : A ⊞ B ⟶ B)⟦(1 : ℤ)⟧')
  have hS : S ∈ distTriang C :=
    retract_distinguished hT
      { i := Triangle.homMk S _ biprod.inr biprod.inr (𝟙 Z) (by simp [S]) (by simp [S])
              (by simpa [S] using hh)
        r := Triangle.homMk _ S biprod.snd biprod.snd (𝟙 Z) (by simp [S])
              (by simpa [S] using hg.symm) (by simp [S])
        retract := by ext <;> simp [S] }
  exact nonempty_iso_biprod_shift_of_mor₁_eq_zero S hS rfl

end CategoryTheory.Pretriangulated

end
