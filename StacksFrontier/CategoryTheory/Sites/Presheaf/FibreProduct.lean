module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# The fibre product of presheaves of sets, explicitly

For morphisms `mF : F ⟶ H` and `mG : G ⟶ H` of presheaves of sets on a category `C`, the fibre
product `F ×_H G` is the presheaf whose sections over `U` are the pairs `(a, b)` of sections of
`F` and `G` over `U` with `mF a = mG b`. This file writes that presheaf down and shows that the
two projections make it a fibre product, hence isomorphic to the pullback that the functor
category provides abstractly.

Writing it down is what makes it usable: a statement identifying a presheaf with a fibre product
is proved by exhibiting, section by section, the pair the section corresponds to, and that is a
statement about this presheaf and not about `CategoryTheory.Limits.pullback`.

## Main definitions

* `CategoryTheory.Presheaf.fibreProduct`: the presheaf `F ×_H G`.
* `CategoryTheory.Presheaf.fibreProductFst` and
  `CategoryTheory.Presheaf.fibreProductSnd`: its two projections.
* `CategoryTheory.Presheaf.fibreProductIsoPullback`: the comparison with
  `CategoryTheory.Limits.pullback`.

## Main results

* `CategoryTheory.Presheaf.isPullback_fibreProduct`: the two projections form a cartesian square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presheaf

universe v u a

variable {C : Type u} [Category.{v} C] {F G H : Cᵒᵖ ⥤ Type a} (mF : F ⟶ H) (mG : G ⟶ H)

/-- The fibre product `F ×_H G` of two presheaves of sets over a third: its sections over `U` are
the pairs of sections of `F` and `G` over `U` with the same image in `H`. -/
def fibreProduct : Cᵒᵖ ⥤ Type a where
  obj U := {ab : F.obj U × G.obj U // mF.app U ab.1 = mG.app U ab.2}
  map {_ V} k := ↾fun ab => ⟨(F.map k ab.1.1, G.map k ab.1.2), by
    change mF.app V (F.map k ab.1.1) = mG.app V (G.map k ab.1.2)
    rw [mF.naturality_apply, mG.naturality_apply, ab.2]⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro ab
    apply Subtype.ext
    apply Prod.ext <;> simp
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro ab
    apply Subtype.ext
    apply Prod.ext <;> simp

/-- The first projection of the fibre product of presheaves. -/
def fibreProductFst : fibreProduct mF mG ⟶ F where
  app _ := ↾fun ab => ab.1.1
  naturality _ _ _ := rfl

/-- The second projection of the fibre product of presheaves. -/
def fibreProductSnd : fibreProduct mF mG ⟶ G where
  app _ := ↾fun ab => ab.1.2
  naturality _ _ _ := rfl

/-- The value of the first projection on a section of the fibre product. -/
@[simp] theorem fibreProductFst_app_apply {U : Cᵒᵖ} (ab : (fibreProduct mF mG).obj U) :
    (fibreProductFst mF mG).app U ab = ab.1.1 :=
  rfl

/-- The value of the second projection on a section of the fibre product. -/
@[simp] theorem fibreProductSnd_app_apply {U : Cᵒᵖ} (ab : (fibreProduct mF mG).obj U) :
    (fibreProductSnd mF mG).app U ab = ab.1.2 :=
  rfl

/-- The morphism into the fibre product induced by a pair of morphisms agreeing in `H`. -/
def fibreProductLift {W : Cᵒᵖ ⥤ Type a} (φ : W ⟶ F) (ψ : W ⟶ G) (h : φ ≫ mF = ψ ≫ mG) :
    W ⟶ fibreProduct mF mG where
  app U := ↾fun x => ⟨(φ.app U x, ψ.app U x), congrArg (fun η : W ⟶ H => η.app U x) h⟩
  naturality U V k := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · change φ.app V (W.map k x) = F.map k (φ.app U x)
      exact NatTrans.naturality_apply φ k x
    · change ψ.app V (W.map k x) = G.map k (ψ.app U x)
      exact NatTrans.naturality_apply ψ k x

/-- **The explicit fibre product of presheaves is a fibre product.** -/
theorem isPullback_fibreProduct :
    IsPullback (fibreProductFst mF mG) (fibreProductSnd mF mG) mF mG := by
  refine IsPullback.mk' ?_ (fun {_} {φ φ'} hφ hψ => ?_)
    (fun {_} a b hab => ⟨fibreProductLift mF mG a b hab, rfl, rfl⟩)
  · ext U ab
    exact ab.2
  · ext U x
    exact Subtype.ext (Prod.ext (congrArg (fun η : _ ⟶ F => η.app U x) hφ)
      (congrArg (fun η : _ ⟶ G => η.app U x) hψ))

/-- The explicit fibre product of presheaves, compared with the pullback the functor category
provides. -/
noncomputable def fibreProductIsoPullback : fibreProduct mF mG ≅ pullback mF mG :=
  (isPullback_fibreProduct mF mG).isoPullback

end CategoryTheory.Presheaf

end
