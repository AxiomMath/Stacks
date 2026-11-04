module

public import StacksFrontier.CategoryTheory.Sites.LocallyBijective

/-!
# A locally bijective map into a sheaf, read out of the sheafification

If `η : P ⟶ Q` is a locally injective and locally surjective morphism from a presheaf to a
sheaf, then any morphism `α : P^# ⟶ Q` with `toSheafify J P ≫ α = η` is an isomorphism.

## Main results

* `CategoryTheory.Presheaf.isIso_of_toSheafify_comp_eq_of_isLocallyBijective`.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

universe w v' v u u'

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
  (J : GrothendieckTopology C)

/-- **A locally bijective morphism from a presheaf to a sheaf induces an isomorphism out of the
sheafification.** If `η : P ⟶ Q` is locally injective and locally surjective, with `Q` a sheaf,
then a morphism `α : P^# ⟶ Q` with `toSheafify J P ≫ α = η` is an isomorphism: it is the
adjoint of `η`, which is the sheafification of `η` followed by the counit, and the sheafification
of a locally bijective morphism is an isomorphism. -/
theorem isIso_of_toSheafify_comp_eq_of_isLocallyBijective
    [HasWeakSheafify J D] [J.WEqualsLocallyBijective D] {P : Cᵒᵖ ⥤ D} {Q : Sheaf J D}
    (η : P ⟶ Q.obj) (α : (presheafToSheaf J D).obj P ⟶ Q)
    (hα : toSheafify J P ≫ α.hom = η)
    (h₁ : Presheaf.IsLocallyInjective J η) (h₂ : Presheaf.IsLocallySurjective J η) :
    IsIso α := by
  have h : α = ((sheafificationAdjunction J D).homEquiv P Q).symm η :=
    Sheaf.hom_ext_iff.mpr (sheafifyLift_unique J η Q.property α.hom hα)
  rw [h, Adjunction.homEquiv_counit]
  have : IsIso ((presheafToSheaf J D).map η) := by
    rw [← J.W_iff]
    exact (J.W_iff_isLocallyBijective η).mpr ⟨h₁, h₂⟩
  infer_instance

end CategoryTheory.Presheaf
