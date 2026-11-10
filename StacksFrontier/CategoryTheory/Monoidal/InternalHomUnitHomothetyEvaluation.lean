module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomUnitHomothety

/-!
# A morphism out of an object with commuting endomorphisms

Let `E` be an object whose endomorphisms commute, for instance an object isomorphic to the unit
object of a monoidal category (`CategoryTheory.MonoidalCategory.comp_comm_tensorUnit`). A
morphism `a : E ⟶ A` into an object isomorphic to `E` is invertible as soon as its image under
a bijective evaluation `x ↦ T.map x ≫ c` is invertible.

## Main results

* `CategoryTheory.isIso_of_isIso_map_comp_of_iso`
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

end CategoryTheory.MonoidalCategory

/-! ### A morphism out of an object with commuting endomorphisms -/

/-- **A morphism into an object isomorphic to `E`, out of `E`, is invertible when its image under
an evaluation is.** Let `E` be an object whose endomorphisms commute, let `T : C ⥤ D` be a
functor and `c : T.obj A ⟶ K` a morphism such that `x ↦ T.map x ≫ c` is a bijection
`(E ⟶ A) → (T.obj E ⟶ K)`, and let `A ≅ E` be an arbitrary isomorphism. Then a morphism
`a : E ⟶ A` is invertible as soon as `T.map a ≫ c` is.

This is the shape of the statement that a homothety `𝒪 ⟶ R𝓗om(K, K)` is invertible: no
equation pinning `a` down is needed, only that its evaluation is invertible, and `E` may be any
object isomorphic to a unit object of some monoidal structure
(`CategoryTheory.MonoidalCategory.comp_comm_tensorUnit`). -/
theorem CategoryTheory.isIso_of_isIso_map_comp_of_iso {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {E A : C} {K : D} (hE : ∀ f g : E ⟶ E, f ≫ g = g ≫ f)
    (c : T.obj A ⟶ K) (hc : Function.Bijective fun x : E ⟶ A => T.map x ≫ c)
    (ψ : A ≅ E) (a : E ⟶ A) (ha : IsIso (T.map a ≫ c)) : IsIso a := by
  set g : T.obj E ⟶ K := T.map ψ.inv ≫ c with hg
  have hΦ : Function.Bijective fun b : E ⟶ E => T.map b ≫ g := by
    have : (fun b : E ⟶ E => T.map b ≫ g) =
        (fun x : E ⟶ A => T.map x ≫ c) ∘ fun b : E ⟶ E => b ≫ ψ.inv := by
      funext b
      simp [hg]
    rw [this]
    exact hc.comp ⟨fun b b' h => by simpa using congrArg (· ≫ ψ.hom) h,
      fun x => ⟨x ≫ ψ.hom, by simp⟩⟩
  set s : E ⟶ E := a ≫ ψ.hom with hs
  have hφ : T.map a ≫ c = T.map s ≫ g := by
    simp [hs, hg]
  obtain ⟨t, ht⟩ := hΦ.2 (g ≫ inv (T.map a ≫ c) ≫ g)
  have hst : s ≫ t = 𝟙 E := by
    apply hΦ.1
    have ht' : T.map t ≫ g = g ≫ inv (T.map a ≫ c) ≫ g := ht
    change T.map (s ≫ t) ≫ g = T.map (𝟙 E) ≫ g
    rw [T.map_comp, Category.assoc, ht', T.map_id, Category.id_comp, ← Category.assoc,
      ← hφ, IsIso.hom_inv_id_assoc]
  have hiso : IsIso s := ⟨t, hst, by rw [hE]; exact hst⟩
  have : a = s ≫ ψ.inv := by simp [hs]
  rw [this]
  infer_instance

end
