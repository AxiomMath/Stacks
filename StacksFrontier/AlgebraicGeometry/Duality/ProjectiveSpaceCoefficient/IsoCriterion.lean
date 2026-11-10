module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Formal lemmas for the comparison map of duality on `ℙⁿ_R`

Three purely categorical facts used to prove that the comparison map
`(𝒪(-n-1) ⊗ p^*M~)[n] ⟶ p^×(M~)` is an isomorphism.

## Main results

* `Stacks.Duality.ProjCoeff.bijective_map_of_isIso_unit`: if the unit of `F ⊣ U` is an isomorphism
  at `Z`, then `U` is bijective on the maps out of `F Z`.
* `Stacks.Duality.ProjCoeff.bijective_comp_homEquiv`: for `U ⊣ A`, an isomorphism
  `t : U G ⟶ N` and an object `X` on whose maps into `G` the functor `U` is bijective, composition
  with the adjoint `G ⟶ A N` of `t` is bijective on the maps out of `X`.
* `Stacks.Duality.ProjCoeff.eq_zero_of_bijective_comp`: in a pretriangulated category, if
  `W ≅ W'⟦1⟧` and composition with `T.mor₁` is surjective on the maps out of `W` and injective on
  the maps out of `W'`, then every map from `W` into the third object of the triangle `T` is zero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Duality.ProjCoeff

universe v₁ v₂ u₁ u₂

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Precomposition with an isomorphism `e : X ⟶ Y` is a bijection `(Y ⟶ W) → (X ⟶ W)`. -/
theorem bijective_comp_left_of_isIso {X Y W : C} (e : X ⟶ Y) [IsIso e] :
    Function.Bijective (fun ψ : Y ⟶ W => e ≫ ψ) :=
  Function.bijective_iff_has_inverse.2
    ⟨fun ψ => inv e ≫ ψ, fun _ => by simp, fun _ => by simp⟩

/-- Postcomposition with an isomorphism `e : X ⟶ Y` is a bijection `(W ⟶ X) → (W ⟶ Y)`. -/
theorem bijective_comp_right_of_isIso {X Y W : C} (e : X ⟶ Y) [IsIso e] :
    Function.Bijective (fun ψ : W ⟶ X => ψ ≫ e) :=
  Function.bijective_iff_has_inverse.2
    ⟨fun ψ => ψ ≫ inv e, fun _ => by simp, fun _ => by simp⟩

/-- If the unit of `F ⊣ U` is an isomorphism at `Z`, then `U` is bijective on the maps out of
`F Z`. -/
theorem bijective_map_of_isIso_unit {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) (Z : C)
    [IsIso (adj.unit.app Z)] (G : D) :
    Function.Bijective (fun φ : F.obj Z ⟶ G => U.map φ) := by
  have h : (fun φ : F.obj Z ⟶ G => U.map φ) =
      (fun ψ => inv (adj.unit.app Z) ≫ ψ) ∘ adj.homEquiv Z G := by
    funext φ
    simp [Adjunction.homEquiv_unit]
  rw [h]
  exact (bijective_comp_left_of_isIso _).comp (adj.homEquiv Z G).bijective

/-- A map out of `X'` that is bijective after transporting along `e : X' ≅ X` and a bijection `k`
from a map out of `X` is bijective. -/
private theorem bijective_of_iso_comp {X X' G : D} {β γ : Type*} (e : X' ≅ X) {f : (X ⟶ G) → β}
    {f' : (X' ⟶ G) → γ} {k : β → γ} (hk : Function.Bijective k)
    (hf' : ∀ φ, f' φ = k (f (e.inv ≫ φ))) (h : Function.Bijective f) : Function.Bijective f' := by
  rw [show f' = k ∘ f ∘ (fun φ => e.inv ≫ φ) from funext hf']
  exact hk.comp (h.comp (bijective_comp_left_of_isIso _))

/-- Bijectivity of `U` on the maps out of `X` only depends on `X` up to isomorphism. -/
theorem bijective_map_of_iso (U : D ⥤ C) {X X' : D} (e : X' ≅ X) (G : D)
    (h : Function.Bijective (fun φ : X ⟶ G => U.map φ)) :
    Function.Bijective (fun φ : X' ⟶ G => U.map φ) :=
  bijective_of_iso_comp e (bijective_comp_left_of_isIso (U.map e.hom)) (fun φ => by simp) h

/-- Composition with a fixed map is bijective on the maps out of `X` as soon as it is on the maps
out of an isomorphic object. -/
theorem bijective_comp_of_iso {X X' G B : D} (c : G ⟶ B) (e : X' ≅ X)
    (h : Function.Bijective (fun φ : X ⟶ G => φ ≫ c)) :
    Function.Bijective (fun φ : X' ⟶ G => φ ≫ c) :=
  bijective_of_iso_comp e (bijective_comp_left_of_isIso e.hom) (fun φ => by simp) h

/-- **The comparison map through an adjunction.** For `U ⊣ A`, an isomorphism `t : U G ⟶ N` and an
object `X` such that `U` is bijective on the maps `X ⟶ G`, composition with the adjoint
`G ⟶ A N` of `t` is bijective on the maps `X ⟶ G`. -/
theorem bijective_comp_homEquiv {U : D ⥤ C} {A : C ⥤ D} (adj : U ⊣ A) {X G : D} {N : C}
    (t : U.obj G ⟶ N) [IsIso t] (hff : Function.Bijective (fun φ : X ⟶ G => U.map φ)) :
    Function.Bijective (fun φ : X ⟶ G => φ ≫ adj.homEquiv _ _ t) := by
  have h : (fun φ : X ⟶ G => φ ≫ adj.homEquiv _ _ t) =
      (adj.homEquiv X N) ∘ (fun ψ : U.obj X ⟶ U.obj G => ψ ≫ t) ∘
        (fun φ : X ⟶ G => U.map φ) := by
    funext φ
    exact (adj.homEquiv_naturality_left φ t).symm
  rw [h]
  exact (adj.homEquiv X N).bijective.comp ((bijective_comp_right_of_isIso t).comp hff)

/-- If `U` commutes with the shifts, the unit of `F ⊣ U` is an isomorphism at `Z⟦a⟧` as soon as
it is one at `Z`. -/
theorem isIso_unit_app_shift {A : Type*} [AddGroup A] [HasShift C A] [HasShift D A]
    {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) [U.CommShift A] (Z : C) [IsIso (adj.unit.app Z)]
    (a : A) : IsIso (adj.unit.app (Z⟦a⟧)) := by
  let := adj.leftAdjointCommShift A
  have := adj.commShift_of_rightAdjoint A
  have h := adj.unit_app_commShiftIso_hom_app A a Z
  have : IsIso (adj.unit.app (Z⟦a⟧) ≫ ((F ⋙ U).commShiftIso a).hom.app Z) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (((F ⋙ U).commShiftIso a).hom.app Z)

/-- With the shift structure on `F` induced by that of its right adjoint `U`,
`F (Z⟦a⟧) ≅ (F Z)⟦a⟧`. -/
noncomputable def leftAdjointShiftIso {A : Type*} [AddGroup A] [HasShift C A] [HasShift D A]
    {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) [U.CommShift A] (Z : C) (a : A) :
    F.obj (Z⟦a⟧) ≅ (F.obj Z)⟦a⟧ :=
  letI := adj.leftAdjointCommShift A
  (F.commShiftIso a).app Z

end Adjunction

section Triangle

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Detecting the cone by maps.** Let `T` be a distinguished triangle and `W ≅ W'⟦1⟧`. If
composition with `T.mor₁` is surjective on the maps out of `W` and injective on the maps out of
`W'`, every map from `W` into `T.obj₃` is zero. -/
theorem eq_zero_of_bijective_comp (T : Triangle C) (hT : T ∈ distTriang C) {W W' : C}
    (e : W ≅ W'⟦(1 : ℤ)⟧) (h₁ : Function.Surjective (fun φ : W ⟶ T.obj₁ => φ ≫ T.mor₁))
    (h₂ : Function.Injective (fun φ : W' ⟶ T.obj₁ => φ ≫ T.mor₁)) (f : W ⟶ T.obj₃) :
    f = 0 := by
  let g' : W' ⟶ T.obj₁ := (shiftFunctor C (1 : ℤ)).preimage (e.inv ≫ f ≫ T.mor₃)
  have hg'₁ : (g' ≫ T.mor₁)⟦(1 : ℤ)⟧' = 0 := by
    simp only [Functor.map_comp, g', Functor.map_preimage, Category.assoc,
      comp_distTriang_mor_zero₃₁ T hT, comp_zero]
  have hg'₂ : g' ≫ T.mor₁ = 0 :=
    (shiftFunctor C (1 : ℤ)).map_injective (by rw [hg'₁, Functor.map_zero])
  have hg' : g' = 0 := h₂ (by simp only [hg'₂, zero_comp])
  have hf : f ≫ T.mor₃ = 0 := by
    have : e.inv ≫ f ≫ T.mor₃ = 0 := by
      rw [← (shiftFunctor C (1 : ℤ)).map_preimage (e.inv ≫ f ≫ T.mor₃)]
      change (g')⟦(1 : ℤ)⟧' = 0
      rw [hg', Functor.map_zero]
    simpa using e.hom ≫= this
  obtain ⟨k, rfl⟩ := Triangle.coyoneda_exact₃ T hT f hf
  obtain ⟨l, rfl⟩ := h₁ k
  simp [comp_distTriang_mor_zero₁₂ T hT]

end Triangle

end Stacks.Duality.ProjCoeff
