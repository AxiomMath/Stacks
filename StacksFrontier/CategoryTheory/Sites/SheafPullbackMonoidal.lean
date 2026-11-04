module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Functor.KanExtension.LanMonoidal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse image of sheaves along a flat continuous functor is monoidal

Let `G : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)` and `A` a monoidal
category for which the sheaf categories carry the localized tensor product
`CategoryTheory.Sheaf.monoidalCategory`. The inverse image `G.sheafPullback A J K`, the left
adjoint of the pushforward, satisfies `G.sheafPullback ∘ a_J ≅ a_K ∘ G.op.lan`, both sides being
left adjoint to `F ↦ G.op ⋙ F` on sheaves. When the comma categories
`CostructuredArrow G.op X` are filtered (for instance when `G` is representably flat) and the
tensor product of `A` commutes with their colimits, `G.op.lan` is monoidal
(`CategoryTheory.Functor.lanMonoidal`), hence so is `a_K ∘ G.op.lan`, and the universal property
of the localization `a_J` makes `G.sheafPullback` monoidal.

## Main definitions

* `CategoryTheory.Functor.presheafToSheafCompSheafPullbackIso`: `a_J ⋙ G.sheafPullback ≅
  G.op.lan ⋙ a_K`.
* `CategoryTheory.Functor.sheafPullbackMonoidal`: the monoidal structure on `G.sheafPullback`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open Limits MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ P : Cᵒᵖ ⥤ A, HasPointwiseLeftKanExtension G.op P]

/-- **Inverse image commutes with sheafification**: `a_J ⋙ G.sheafPullback ≅ G.op.lan ⋙ a_K`,
both functors being left adjoint to `F ↦ G.op ⋙ F` from sheaves on `D` to presheaves on `C`. -/
def presheafToSheafCompSheafPullbackIso :
    presheafToSheaf J A ⋙ G.sheafPullback A J K ≅ G.op.lan ⋙ presheafToSheaf K A :=
  ((sheafificationAdjunction J A).comp (G.sheafAdjunctionContinuous A J K)).leftAdjointUniq
    (((G.op.lanAdjunction A).comp (sheafificationAdjunction K A)).ofNatIsoRight (Iso.refl _))

variable [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]
  [∀ X : Dᵒᵖ, IsFiltered (CostructuredArrow G.op X)]
  [∀ (X : Dᵒᵖ) (M : A),
    PreservesColimitsOfShape (CostructuredArrow G.op X) ((curriedTensor A).obj M)]
  [∀ (X : Dᵒᵖ) (M : A),
    PreservesColimitsOfShape (CostructuredArrow G.op X) ((curriedTensor A).flip.obj M)]

attribute [local instance] Sheaf.monoidalCategory lanMonoidal

/-- **The inverse image of sheaves is monoidal** for the localized tensor products, when the
comma categories `CostructuredArrow G.op X` are filtered and the tensor product of `A` commutes
with their colimits in each variable. -/
@[instance_reducible, ega "0 4.3.3" "special case", ega "IV 10.2.8" "more general"]
def sheafPullbackMonoidal : (G.sheafPullback A J K).Monoidal :=
  letI : Localization.Lifting (presheafToSheaf J A) J.W (G.op.lan ⋙ presheafToSheaf K A)
      (G.sheafPullback A J K) := ⟨presheafToSheafCompSheafPullbackIso G A J K⟩
  Localization.Monoidal.functorMonoidalOfComp (presheafToSheaf J A) J.W
    (G.sheafPullback A J K) (G.op.lan ⋙ presheafToSheaf K A)

end CategoryTheory.Functor

end
