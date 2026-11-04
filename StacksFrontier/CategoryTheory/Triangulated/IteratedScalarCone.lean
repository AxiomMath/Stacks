module

public import StacksFrontier.CategoryTheory.Triangulated.ScalarNilpotence
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Coning off a finite family of scalars, keeping a summand of the image

Let `C` and `D` be triangulated categories, linear over a ring `A` with `A`-linear shift
functors, and let `R : C ⥤ D` be an `A`-linear triangulated functor. Let `g_1, …, g_s` be elements
of `A` and let `E₀` be an object of `C` such that each `g_j` has a power killing the identity of
`R.obj E₀`.

Coning off multiplication by a power of `g_1` on `E₀`, then by a power of `g_2` on the result,
and so on, produces an object `E` of `C` on which each `g_j` has a power killing the identity, in
`C` and not only after `R`. At every step the image of the cone is the biproduct of the image of
the previous object and its shift, because the morphism being coned off becomes zero there; so a
summand `F` of `R.obj E₀` survives as a summand of `R.obj E`.

## Main definitions

* `Stacks.Triangulated.biprodSwapOuterIso`: the isomorphism `(S ⊞ F) ⊞ N ≅ (S ⊞ N) ⊞ F`.

## Main results

* `Stacks.Triangulated.exists_iso_biprod_of_mor₁_eq_zero`: the third object of a distinguished
  triangle whose first morphism vanishes is the biproduct of the second object and the shift of
  the first.
* `Stacks.Triangulated.smul_id_biprod_eq_zero`, `Stacks.Triangulated.smul_id_shift_one_eq_zero`:
  a scalar killing the identities of two objects kills the identity of their biproduct, and a
  scalar killing the identity of an object kills the identity of its shift.
* `Stacks.Triangulated.exists_iteratedCone_biprod_summand`: coning off a list of scalars, for a
  running object `E₀` with `S₀ ⊞ F ≅ R.obj E₀`.
* `Stacks.Triangulated.exists_iteratedCone_biprod_summand_of_smul_id_biprod_iso`: coning off a
  list of scalars, starting from `F ⊞ F⟦1⟧ ≅ R.obj E₀` and a power of each scalar killing the
  identity of `F`.

## Implementation notes

The property preserved along the iteration is an arbitrary predicate `P` on `C` closed under
cones. The family of scalars is a `List`, which needs no `DecidableEq` on `A`.

## References

* [Stacks Project, Lemma 36.13.10 (Tag 08EK)](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Lemma 13.4.5 (Tag 05QP)](https://stacks.math.columbia.edu/tag/05QP)
* [Stacks Project, Lemma 13.4.11 (Tag 05QT)](https://stacks.math.columbia.edu/tag/05QT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Triangulated

universe v₂ u₂ v u

section Biprod

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- **Moving the second summand of a biproduct past a third.** -/
def biprodSwapOuterIso (S F N : C) : (S ⊞ F) ⊞ N ≅ (S ⊞ N) ⊞ F :=
  biprod.associator S F N ≪≫ biprod.mapIso (Iso.refl S) (biprod.braiding F N) ≪≫
    (biprod.associator S N F).symm

variable {A : Type*} [Semiring A] [Linear A C]

/-- **A scalar killing the identities of two objects kills the identity of their biproduct.** -/
theorem smul_id_biprod_eq_zero {M N : C} {a : A} (hM : a • 𝟙 M = 0) (hN : a • 𝟙 N = 0) :
    a • 𝟙 (M ⊞ N) = 0 := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · simpa using congrArg (· ≫ (biprod.inl : M ⟶ M ⊞ N)) hM
  · simpa using congrArg (· ≫ (biprod.inr : N ⟶ M ⊞ N)) hN

/-- **If `a ^ k * a ^ k` kills the identity of an object, so does a power of `a`.** -/
private theorem exists_pow_smul_id_eq_zero_of_sq {E : Type*} [Category E] [Preadditive E]
    [Linear A E] {M : E} {a : A} {k : ℕ} (h : (a ^ k * a ^ k) • 𝟙 M = 0) :
    ∃ n : ℕ, a ^ n • 𝟙 M = 0 :=
  ⟨k + k, by rw [pow_add]; exact h⟩

end Biprod

section Cone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The third object of a distinguished triangle whose first morphism vanishes is the
biproduct of the second object and the shift of the first.** -/
theorem exists_iso_biprod_of_mor₁_eq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (h : T.mor₁ = 0) : Nonempty (T.obj₃ ≅ T.obj₂ ⊞ T.obj₁⟦(1 : ℤ)⟧) := by
  obtain ⟨e, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang T.rotate
    (rot_of_distTriang T hT) (by simp [h]; rfl)
  exact ⟨e⟩

variable {A : Type*} [Semiring A] [Linear A C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Linear A]

/-- **A scalar killing the identity of an object kills the identity of its shift.** -/
theorem smul_id_shift_one_eq_zero {M : C} {a : A} (h : a • 𝟙 M = 0) :
    a • 𝟙 (M⟦(1 : ℤ)⟧) = 0 := by
  rw [← shift_smul_id a M, h, CategoryTheory.Functor.map_zero]

end Cone

section Iterate

variable {A : Type*} [Ring A] {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] [Linear A C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Linear A]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D] [Linear A D]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Linear A]

/-- **Coning off a list of scalars while keeping a summand of the image.** Let `P` be a
predicate on `C` closed under cones, `R : C ⥤ D` an `A`-linear triangulated functor and `F` an
object of `D`. Let `t` and `u` be lists of scalars and `E₀` an object of `C` with `P E₀`
and `S₀ ⊞ F ≅ R.obj E₀`, such that a power of every
element of `t` kills the identity of `R.obj E₀` and a power of every element of `u` kills the
identity of `E₀` itself. Then there is an object `E` of `C` with `P E`, on which a power of
every element of `t ++ u` kills the identity, and whose image under `R` still has `F` as a
second summand. -/
theorem exists_iteratedCone_biprod_summand (P : C → Prop)
    (hP : ∀ T : Triangle C, T ∈ distTriang C → P T.obj₁ → P T.obj₂ → P T.obj₃)
    (R : C ⥤ D) [R.CommShift ℤ] [R.IsTriangulated] [R.Linear A] (F : D) (t : List A) :
    ∀ (u : List A) (E₀ : C) (S₀ : D), P E₀ → (S₀ ⊞ F ≅ R.obj E₀) →
      (∀ a ∈ t, ∃ m : ℕ, a ^ m • 𝟙 (R.obj E₀) = 0) →
      (∀ a ∈ u, ∃ k : ℕ, a ^ k • 𝟙 E₀ = 0) →
      ∃ (E : C) (S : D), P E ∧ (∀ a ∈ t ++ u, ∃ k : ℕ, a ^ k • 𝟙 E = 0) ∧
        Nonempty (S ⊞ F ≅ R.obj E) := by
  induction t with
  | nil =>
    intro u E₀ S₀ hE₀ ε _ hu
    exact ⟨E₀, S₀, hE₀, by simpa using hu, ⟨ε⟩⟩
  | cons a t' ih =>
    intro u E₀ S₀ hE₀ ε ht hu
    obtain ⟨m, hm⟩ := ht a (List.mem_cons_self ..)
    obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle (a ^ m • 𝟙 E₀)
    have hPZ : P Z := hP (Triangle.mk (a ^ m • 𝟙 E₀) v w) hT hE₀ hE₀
    have hRT : R.mapTriangle.obj (Triangle.mk (a ^ m • 𝟙 E₀) v w) ∈ distTriang D :=
      R.map_distinguished _ hT
    have hRzero : (R.mapTriangle.obj (Triangle.mk (a ^ m • 𝟙 E₀) v w)).mor₁ = 0 := by
      show R.map (a ^ m • 𝟙 E₀) = 0
      rw [Functor.map_smul, CategoryTheory.Functor.map_id, hm]
    obtain ⟨e⟩ := exists_iso_biprod_of_mor₁_eq_zero _ hRT hRzero
    have ε₁ : (S₀ ⊞ (R.obj E₀)⟦(1 : ℤ)⟧) ⊞ F ≅ R.obj Z :=
      (e ≪≫ biprod.mapIso ε.symm (Iso.refl _) ≪≫
        biprodSwapOuterIso S₀ F ((R.obj E₀)⟦(1 : ℤ)⟧)).symm
    have ht' : ∀ b ∈ t', ∃ m' : ℕ, b ^ m' • 𝟙 (R.obj Z) = 0 := by
      intro b hb
      obtain ⟨m', hm'⟩ := ht b (List.mem_cons_of_mem _ hb)
      exact exists_pow_smul_id_eq_zero_of_sq (smul_id_obj₃_sq_eq_zero _ hRT (b ^ m') hm' hm')
    have hu' : ∀ b ∈ a :: u, ∃ k : ℕ, b ^ k • 𝟙 Z = 0 := by
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact exists_pow_smul_id_eq_zero_of_sq
          (smul_id_obj₃_sq_eq_zero_of_mor₁_eq_smul_id (b ^ m) v w hT)
      · obtain ⟨k, hk⟩ := hu b hb
        exact exists_pow_smul_id_eq_zero_of_sq (smul_id_obj₃_sq_eq_zero _ hT (b ^ k) hk hk)
    obtain ⟨E, S, hPE, hkill, hiso⟩ := ih (a :: u) Z _ hPZ ε₁ ht' hu'
    refine ⟨E, S, hPE, fun b hb => hkill b ?_, hiso⟩
    simp only [List.mem_append, List.mem_cons] at hb ⊢
    tauto

/-- **Coning off a list of scalars, starting from `F ⊞ F⟦1⟧`.** Let `P` be a predicate on `C`
closed under cones, `R : C ⥤ D` an `A`-linear triangulated functor, `F` an object of `D` on whose
identity a power of each element of `t` acts as zero, and `E₀` an object of `C` with `P E₀` and
`F ⊞ F⟦1⟧ ≅ R.obj E₀`. Then there is an object `E` with `P E`, on whose identity a power of each
element of `t` acts as zero, and with `F` a second summand of `R.obj E`. -/
theorem exists_iteratedCone_biprod_summand_of_smul_id_biprod_iso (P : C → Prop)
    (hP : ∀ T : Triangle C, T ∈ distTriang C → P T.obj₁ → P T.obj₂ → P T.obj₃)
    (R : C ⥤ D) [R.CommShift ℤ] [R.IsTriangulated] [R.Linear A] (F : D) (t : List A) (E₀ : C)
    (hE₀ : P E₀) (e₀ : F ⊞ F⟦(1 : ℤ)⟧ ≅ R.obj E₀)
    (ht : ∀ a ∈ t, ∃ m : ℕ, a ^ m • 𝟙 F = 0) :
    ∃ (E : C) (S : D), P E ∧ (∀ a ∈ t, ∃ k : ℕ, a ^ k • 𝟙 E = 0) ∧
      Nonempty (S ⊞ F ≅ R.obj E) := by
  have ht' : ∀ a ∈ t, ∃ m : ℕ, a ^ m • 𝟙 (R.obj E₀) = 0 := by
    intro a ha
    obtain ⟨m, hm⟩ := ht a ha
    refine ⟨m, ?_⟩
    have hb : a ^ m • 𝟙 (F ⊞ F⟦(1 : ℤ)⟧) = 0 :=
      smul_id_biprod_eq_zero hm (smul_id_shift_one_eq_zero hm)
    have hconj : a ^ m • 𝟙 (R.obj E₀) = e₀.inv ≫ (a ^ m • 𝟙 (F ⊞ F⟦(1 : ℤ)⟧)) ≫ e₀.hom := by
      rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, e₀.inv_hom_id]
    rw [hconj, hb, Limits.zero_comp, Limits.comp_zero]
  obtain ⟨E, S, hPE, hkill, hiso⟩ := exists_iteratedCone_biprod_summand P hP R F t [] E₀
    (F⟦(1 : ℤ)⟧) hE₀ (biprod.braiding (F⟦(1 : ℤ)⟧) F ≪≫ e₀) ht' (by simp)
  exact ⟨E, S, hPE, fun a ha => hkill a (by simpa using ha), hiso⟩

end Iterate

end Stacks.Triangulated

end
