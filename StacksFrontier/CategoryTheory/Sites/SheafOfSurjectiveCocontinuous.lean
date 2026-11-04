module

public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Sheaves along a cocontinuous functor which is surjective up to vertical isomorphisms

Let `F : C₀ ⥤ C` be a cocontinuous functor between sites which is surjective on objects and such
that every morphism into an object `F X₀` is an isomorphism followed by the image of a morphism
of `C₀`.  Then a presheaf `P` on `C` is a sheaf as soon as `F.op ⋙ P` is.  This is the situation
of a category fibred in groupoids `𝒮_U ⥤ [U/_pR]` with the same objects and more morphisms: a
matching family on a covering sieve of `C` restricts to one on the pulled back sieve, and its
amalgamation there is one upstairs because every member of the sieve differs from the image of a
member of the pulled back sieve by an isomorphism.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

universe w v₀ u₀ v u u' v'

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C : Type u} [Category.{v} C]
  {J₀ : GrothendieckTopology C₀} {J : GrothendieckTopology C}
  (F : C₀ ⥤ C) [F.IsCocontinuous J₀ J]

/-- **Sheaves of types along a cocontinuous functor which is surjective up to isomorphisms.** -/
theorem isSheaf_of_isSheaf_comp_of_factor (P : Cᵒᵖ ⥤ Type w)
    (hsurj : ∀ X : C, ∃ X₀ : C₀, F.obj X₀ = X)
    (hfac : ∀ {Y : C} {X₀ : C₀} (f : Y ⟶ F.obj X₀), ∃ (Y₀ : C₀) (θ : Y ⟶ F.obj Y₀) (g : Y₀ ⟶ X₀),
      IsIso θ ∧ θ ≫ F.map g = f)
    (hP : Presieve.IsSheaf J₀ (F.op ⋙ P)) : Presieve.IsSheaf J P := by
  intro X S hS
  obtain ⟨X₀, rfl⟩ := hsurj X
  intro x hx
  let y : Presieve.FamilyOfElements (F.op ⋙ P) (S.functorPullback F).arrows :=
    fun _ g hg => x (F.map g) hg
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact hx (F.map g₁) (F.map g₂) h₁ h₂ (by simp only [← F.map_comp, w])
  obtain ⟨s, hs, hsu⟩ := hP _ (F.cover_lift J₀ J hS) y hy
  refine ⟨s, ?_, ?_⟩
  · intro Y f hf
    obtain ⟨Y₀, θ, g, hθ, rfl⟩ := hfac f
    have hg : S.arrows (F.map g) := by simpa using S.downward_closed hf (inv θ)
    have h₁ : P.map (F.map g).op s = x (F.map g) hg := hs g hg
    rw [op_comp, FunctorToTypes.map_comp_apply, h₁]
    exact (hx.to_sieveCompatible (F.map g) θ hg).symm
  · intro s' hs'
    exact hsu s' fun _ g hg => hs' (F.map g) hg

/-- **Sheaves with values in an arbitrary category along a cocontinuous functor which is
surjective up to isomorphisms.** -/
theorem isSheaf_of_isSheaf_comp_of_factor' {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A)
    (hsurj : ∀ X : C, ∃ X₀ : C₀, F.obj X₀ = X)
    (hfac : ∀ {Y : C} {X₀ : C₀} (f : Y ⟶ F.obj X₀), ∃ (Y₀ : C₀) (θ : Y ⟶ F.obj Y₀) (g : Y₀ ⟶ X₀),
      IsIso θ ∧ θ ≫ F.map g = f)
    (hP : Presheaf.IsSheaf J₀ (F.op ⋙ P)) : Presheaf.IsSheaf J P := fun E =>
  isSheaf_of_isSheaf_comp_of_factor F (P ⋙ coyoneda.obj (op E)) hsurj hfac (hP E)

end CategoryTheory.Presheaf

end
