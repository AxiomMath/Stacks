module

public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composing with an equivalence of categories over a base

Let `𝒮` be a category. For categories `𝒳`, `𝒴`, `𝒵` over `𝒮`, in any universes, a based functor
`F : 𝒳 ⥤ᵇ 𝒴` induces functors of categories of based functors by pre- and post-composition. When
`F` is part of an equivalence of categories over `𝒮` both are equivalences of categories.

These are the whiskering functors of the 2-category of categories over `𝒮` (Stacks 003Y),
written for categories in independent universes, which is what comparing a category over `𝒮`
with a model of it in other universes — a universe lift, or a model with shrunk hom types — needs.

## Main definitions

* `CategoryTheory.BasedFunctor.precompFunctor`: `g ↦ F ⋙ g`.
* `CategoryTheory.BasedFunctor.postcompFunctor`: `g ↦ g ⋙ F`.

## Main results

* `CategoryTheory.BasedCategory.Equivalence.isEquivalence_precompFunctor`,
  `CategoryTheory.BasedCategory.Equivalence.isEquivalence_postcompFunctor`: composing with the
  forward functor of an equivalence over `𝒮` is an equivalence of categories of based functors.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒵 : BasedCategory.{v₄, u₄} 𝒮}

namespace BasedFunctor

/-- Precomposition with a based functor, as a functor of categories of based functors. -/
@[simps, sga "4 Vbis 1.2.10"]
def precompFunctor (F : 𝒳 ⥤ᵇ 𝒴) (𝒵 : BasedCategory.{v₄, u₄} 𝒮) : (𝒴 ⥤ᵇ 𝒵) ⥤ (𝒳 ⥤ᵇ 𝒵) where
  obj g := F ⋙ g
  map θ := BasedCategory.whiskerLeft F θ

/-- Postcomposition with a based functor, as a functor of categories of based functors. -/
@[simps]
def postcompFunctor (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (F : 𝒴 ⥤ᵇ 𝒵) : (𝒳 ⥤ᵇ 𝒴) ⥤ (𝒳 ⥤ᵇ 𝒵) where
  obj g := g ⋙ F
  map θ := BasedCategory.whiskerRight θ F

end BasedFunctor

namespace BasedCategory.Equivalence

variable (E : BasedCategory.Equivalence 𝒳 𝒴)

/-- Precomposition with an equivalence over `𝒮` is an equivalence of categories, with
precomposition with the inverse as quasi-inverse. -/
@[sga "1 VI 4.5"]
noncomputable def precompEquivalence (𝒵 : BasedCategory.{v₄, u₄} 𝒮) : (𝒴 ⥤ᵇ 𝒵) ≌ (𝒳 ⥤ᵇ 𝒵) :=
  CategoryTheory.Equivalence.mk (BasedFunctor.precompFunctor E.functor 𝒵)
    (BasedFunctor.precompFunctor E.inverse 𝒵)
    (NatIso.ofComponents (fun g => BasedNatIso.mkNatIso
      (Functor.isoWhiskerRight (BasedFunctor.toFunctorIso E.inverse E.functor E.counitIso).symm
        g.toFunctor)
      (fun a => by
        have := E.counitIso.inv.isHomLift (a := a) rfl
        exact BasedFunctor.preserves_isHomLift g _ (E.counitIso.inv.toNatTrans.app a)))
      fun {g g'} θ => by
        ext a
        dsimp [BasedNatIso.mkNatIso]
        exact (θ.toNatTrans.naturality (E.counitIso.inv.toNatTrans.app a)).symm)
    (NatIso.ofComponents (fun g => BasedNatIso.mkNatIso
      (Functor.isoWhiskerRight (BasedFunctor.toFunctorIso E.functor E.inverse E.unitIso)
        g.toFunctor)
      (fun a => by
        have := E.unitIso.hom.isHomLift (a := a) rfl
        exact BasedFunctor.preserves_isHomLift g _ (E.unitIso.hom.toNatTrans.app _)))
      fun {g g'} θ => by
        ext a
        dsimp [BasedNatIso.mkNatIso]
        exact (θ.toNatTrans.naturality (E.unitIso.hom.toNatTrans.app _)).symm)

/-- The forward functor of `precompEquivalence` is precomposition with `E.functor`. -/
@[simp]
lemma precompEquivalence_functor (𝒵 : BasedCategory.{v₄, u₄} 𝒮) :
    (E.precompEquivalence 𝒵).functor = BasedFunctor.precompFunctor E.functor 𝒵 := rfl

/-- Precomposition with the forward functor of an equivalence over `𝒮` is an equivalence of
categories. -/
instance isEquivalence_precompFunctor (𝒵 : BasedCategory.{v₄, u₄} 𝒮) :
    (BasedFunctor.precompFunctor E.functor 𝒵).IsEquivalence :=
  (E.precompEquivalence 𝒵).isEquivalence_functor

/-- Postcomposition with an equivalence over `𝒮` is an equivalence of categories, with
postcomposition with the inverse as quasi-inverse. -/
@[sga "1 VI 4.5"]
noncomputable def postcompEquivalence (𝒵 : BasedCategory.{v₄, u₄} 𝒮) : (𝒵 ⥤ᵇ 𝒳) ≌ (𝒵 ⥤ᵇ 𝒴) :=
  CategoryTheory.Equivalence.mk (BasedFunctor.postcompFunctor 𝒵 E.functor)
    (BasedFunctor.postcompFunctor 𝒵 E.inverse)
    (NatIso.ofComponents (fun g => BasedNatIso.mkNatIso
      (Functor.isoWhiskerLeft g.toFunctor
        (BasedFunctor.toFunctorIso E.functor E.inverse E.unitIso).symm)
      (fun a => E.unitIso.inv.isHomLift (g.w_obj a))) fun {g g'} θ => by
        ext a
        have hn := (BasedFunctor.toFunctorIso E.functor E.inverse E.unitIso).inv.naturality
          (θ.toNatTrans.app a)
        dsimp at hn
        exact hn)
    (NatIso.ofComponents (fun g => BasedNatIso.mkNatIso
      (Functor.isoWhiskerLeft g.toFunctor
        (BasedFunctor.toFunctorIso E.inverse E.functor E.counitIso))
      (fun a => E.counitIso.hom.isHomLift (g.w_obj a))) fun {g g'} θ => by
        ext a
        have hn := (BasedFunctor.toFunctorIso E.inverse E.functor E.counitIso).hom.naturality
          (θ.toNatTrans.app a)
        dsimp at hn
        exact hn)

/-- The forward functor of `postcompEquivalence` is postcomposition with `E.functor`. -/
@[simp]
lemma postcompEquivalence_functor (𝒵 : BasedCategory.{v₄, u₄} 𝒮) :
    (E.postcompEquivalence 𝒵).functor = BasedFunctor.postcompFunctor 𝒵 E.functor := rfl

/-- Postcomposition with the forward functor of an equivalence over `𝒮` is an equivalence of
categories. -/
instance isEquivalence_postcompFunctor (𝒵 : BasedCategory.{v₄, u₄} 𝒮) :
    (BasedFunctor.postcompFunctor 𝒵 E.functor).IsEquivalence :=
  (E.postcompEquivalence 𝒵).isEquivalence_functor

end BasedCategory.Equivalence

end CategoryTheory

end
