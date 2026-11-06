module

public import Mathlib.AlgebraicTopology.CechNerve
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Cech
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CechOfCovering
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject

/-!
# Čech augmentations are hypercoverings

Let `C` be a category with fibre products, `J` a pretopology on `C` and `X` an object of `C`.
A simplicial object `W` of `C / X` gives an augmentation `W ⋙ Over.forget X ⟶ X`, whose
components are the structure morphisms of the `W_n`. If `W` is isomorphic to the Čech nerve
`n ↦ A^{n+1}` of an object `A` of `C / X` (products in `C / X`, that is fibre products over `X`),
and the structure morphism `W_0 ⟶ X` is a covering by itself, then this augmentation is a
hypercovering of `X` in the sense of Stacks 09X8: the Čech nerve is `0`-coskeletal, so every
matching morphism is an isomorphism.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.overAugmentation`: the augmentation of a simplicial object
  of `C / X`.
* `Stacks.CategoryTheory.Hypercovering.cechNerveTerminalFromCompInclIso`: the Čech nerve of `B`,
  read as one-summand formal coproducts, is the Čech object of the formal coproduct on `B`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.isHypercoveringAugmentation_of_iso_cechNerveTerminalFrom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe w v u v' u'

namespace Stacks.CategoryTheory.Hypercovering

section FormalCoproduct

variable {D : Type u} [Category.{v} D] [HasFiniteProducts D]

/-- The Čech nerve `n ↦ B^{n+1}` of an object `B`, read degreewise as one-summand formal
coproducts, is the Čech object of the formal coproduct with the single summand `B`. -/
def cechNerveTerminalFromCompInclIso (B : D) :
    cechNerveTerminalFrom B ⋙ FormalCoproduct.incl.{w} D ≅
      ((FormalCoproduct.incl.{w} D).obj B).cech :=
  NatIso.ofComponents
    (fun n => FormalCoproduct.isoOfComponents
      { toFun := fun _ _ => PUnit.unit.{w + 1}
        invFun := fun _ => PUnit.unit.{w + 1}
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } (fun _ => Iso.refl _))
    (fun {n m} φ => by
      refine FormalCoproduct.hom_ext rfl fun i => ?_
      refine Limits.Pi.hom_ext _ _ fun k => ?_
      change (((Limits.Pi.lift fun j : Fin (m.unop.len + 1) =>
          Limits.Pi.π (fun _ : Fin (n.unop.len + 1) => B) (φ.unop.toOrderHom j)) ≫
          𝟙 (∏ᶜ fun _ : Fin (m.unop.len + 1) => B)) ≫ 𝟙 (∏ᶜ fun _ : Fin (m.unop.len + 1) => B)) ≫
          Limits.Pi.π (fun _ : Fin (m.unop.len + 1) => B) k =
        (𝟙 (∏ᶜ fun _ : Fin (n.unop.len + 1) => B) ≫ Limits.Pi.lift fun j : Fin (m.unop.len + 1) =>
          Limits.Pi.π (fun _ : Fin (n.unop.len + 1) => B) (φ.unop.toOrderHom j)) ≫
          Limits.Pi.π (fun _ : Fin (m.unop.len + 1) => B) k
      simp)

end FormalCoproduct

section PreservesProducts

variable {D : Type u} [Category.{v} D] [HasFiniteProducts D] {D' : Type u'} [Category.{v'} D']
  [HasFiniteProducts D'] (G : D ⥤ D') [PreservesFiniteProducts G]

/-- A functor preserving finite products carries the Čech nerve `n ↦ A^{n+1}` to the Čech nerve
of the image of `A`. -/
def cechNerveTerminalFromCompIso (A : D) :
    cechNerveTerminalFrom A ⋙ G ≅ cechNerveTerminalFrom (G.obj A) :=
  NatIso.ofComponents
    (fun n => PreservesProduct.iso G (fun _ : Fin (n.unop.len + 1) => A))
    (fun {n m} φ => by
      refine Limits.Pi.hom_ext _ _ fun k => ?_
      simp only [Functor.comp_map, PreservesProduct.iso_hom]
      dsimp only [cechNerveTerminalFrom]
      simp only [Category.assoc, piComparison_comp_π, Limits.Pi.lift_comp_π, ← G.map_comp])

end PreservesProducts

section OverPullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C} (f : X ⟶ Y)

/-- Base change along `f : X ⟶ Y` of a morphism `h : A ⟶ A'` of `C / Y` sits in a cartesian
square over `h`, whose vertical sides are the first projections `A ×_Y X ⟶ A`. -/
theorem isPullback_overPullback_map_left {A A' : Over Y} (h : A ⟶ A') :
    IsPullback ((Over.pullback f).map h).left (pullback.fst A.hom f) (pullback.fst A'.hom f)
      h.left := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback A'.hom f).flip
  have h₁ : ((Over.pullback f).map h).left ≫ pullback.snd A'.hom f = pullback.snd A.hom f :=
    Over.w ((Over.pullback f).map h)
  have h₂ : h.left ≫ A'.hom = A.hom := Over.w h
  rw [h₁, h₂]
  exact (IsPullback.of_hasPullback A.hom f).flip

end OverPullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X : C}

/-- The augmentation to `X` of a simplicial object of `C / X`: its components are the structure
morphisms of the terms. -/
@[simps]
def overAugmentation (W : SimplicialObject (Over X)) :
    W ⋙ Over.forget X ⟶ (SimplicialObject.const C).obj X where
  app n := (W.obj n).hom
  naturality _ _ φ := by simp

/-- Lifting the augmentation of a simplicial object of `C / X` back to `C / X` recovers it. -/
def overLiftOverAugmentationIso (W : SimplicialObject (Over X)) :
    Over.lift (W ⋙ Over.forget X) (overAugmentation W) ≅ W :=
  NatIso.ofComponents (fun _ => Over.isoMk (Iso.refl _) (Category.id_comp _))
    (fun _ => by ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **A Čech augmentation is a hypercovering.** Let `W` be a simplicial object of `C / X`
isomorphic to the Čech nerve `n ↦ A^{n+1}` of an object `A` of `C / X`. If the structure
morphism `W_0 ⟶ X` alone is a covering of `X`, the augmentation `W ⋙ Over.forget X ⟶ X` is a
hypercovering of `X` (Stacks 09X8): its higher matching morphisms are isomorphisms. -/
theorem isHypercoveringAugmentation_of_iso_cechNerveTerminalFrom (J : Pretopology C)
    [HasFiniteProducts (Over X)] (W : SimplicialObject (Over X)) (A : Over X)
    (e : W ≅ cechNerveTerminalFrom A)
    (h₀ : Presieve.singleton (W.obj (op ⦋0⦌)).hom ∈ J X) :
    IsHypercoveringAugmentation J (W ⋙ Over.forget X) (overAugmentation W) := by
  rw [isHypercoveringAugmentation_iff_isHypercovering.{v}]
  let L := ((FormalCoproduct.incl.{v} (Over X)).obj A).cech
  let E : associatedSimplicialObject.{v} (W ⋙ Over.forget X) (overAugmentation W) ≅ L :=
    Functor.isoWhiskerRight (overLiftOverAugmentationIso W ≪≫ e) _ ≪≫
      cechNerveTerminalFromCompInclIso A
  have hL : IsIso ((SimplicialObject.coskAdj 0).unit.app L) :=
    (SimplicialObject.isCoskeletal_iff_isIso (X := L) (n := 0)).mp (cech_isCoskeletal _)
  refine IsCechHypercovering.isHypercovering
    ⟨isCoveringOver_terminal_from_of_mem J _ ?_,
      (SimplicialObject.truncation 0).obj L,
      ⟨E ≪≫ asIso ((SimplicialObject.coskAdj 0).unit.app L)⟩⟩
  show Presieve.ofArrows (fun _ : PUnit.{v + 1} => (W.obj (op ⦋0⦌)).left)
    (fun _ => (W.obj (op ⦋0⦌)).hom) ∈ J X
  rwa [Presieve.ofArrows_pUnit]

end Stacks.CategoryTheory.Hypercovering

end
