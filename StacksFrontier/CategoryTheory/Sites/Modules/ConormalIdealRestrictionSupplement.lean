module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence
import all StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction

/-!
# Additions to `ConormalIdealRestriction`

Declarations extending the module above, kept in their own module.
-/

@[expose] public section

open CategoryTheory

universe v u w z

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B)
  (G : SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))

namespace IdealRestriction

variable {φ G}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Two restriction data that agree on a generating set agree on the ideal it generates.**
The maps of a restriction datum are additive and linear over `𝒜` acting on `𝒢` through the
presentation, so agreement propagates from a set of generators to their span. This is what
reduces an agreement hypothesis on an ideal to one on its coefficients. -/
theorem app_eq_of_mem_span_of_subset (ρ σ : IdealRestriction φ G) (X : Cᵒᵖ)
    (s : Set ↥(A.obj.obj X)) (hs : s ⊆ (kernelIdeal φ.hom X : Set ↥(A.obj.obj X)))
    (hagree : ∀ (y : ↥(A.obj.obj X)) (hy : y ∈ s), ρ.app X ⟨y, hs hy⟩ = σ.app X ⟨y, hs hy⟩)
    (g : ↥(kernelIdeal φ.hom X)) (hg : (g : ↥(A.obj.obj X)) ∈ Ideal.span s) :
    ρ.app X g = σ.app X g := by
  have hspan : Ideal.span s ≤ kernelIdeal φ.hom X := Ideal.span_le.mpr hs
  have key : ∀ (y : ↥(A.obj.obj X)), y ∈ Ideal.span s →
      ∀ hk : y ∈ kernelIdeal φ.hom X, ρ.app X ⟨y, hk⟩ = σ.app X ⟨y, hk⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact fun _ ↦ hagree z hz
    | zero =>
      intro hk
      have h0 : (⟨(0 : ↥(A.obj.obj X)), hk⟩ : ↥(kernelIdeal φ.hom X)) = 0 := Subtype.ext rfl
      rw [h0, map_zero, map_zero]
    | add z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
      intro hk
      have hsum : (⟨z₁ + z₂, hk⟩ : ↥(kernelIdeal φ.hom X)) =
          ⟨z₁, hspan hz₁⟩ + ⟨z₂, hspan hz₂⟩ := Subtype.ext rfl
      rw [hsum, map_add, map_add, ih₁ (hspan hz₁), ih₂ (hspan hz₂)]
    | smul r z hz ih =>
      intro hk
      have hsmul : (⟨r • z, hk⟩ : ↥(kernelIdeal φ.hom X)) = r • ⟨z, hspan hz⟩ :=
        Subtype.ext rfl
      rw [hsmul, ρ.app_smul, σ.app_smul, ih (hspan hz)]
  exact key (g : ↥(A.obj.obj X)) hg g.2

end IdealRestriction

section Desc

variable [Presheaf.IsLocallySurjective J φ.hom]

variable (R : Sheaf J CommRingCat.{w}) (a : R ⟶ A)

end Desc

section Cocycle

variable [Presheaf.IsLocallySurjective J φ.hom]

end Cocycle

end Stacks.Sites.Conormal

end

