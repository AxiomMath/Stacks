module

public import StacksFrontier.CategoryTheory.Abelian.TowerStableImageLift

/-!
# Maps of towers into the image of the stable image tower under a functor

Let `T` be a tower in an abelian category `C` with the exact sequences of
`CategoryTheory.LAdicTower.LESData`, with stable images `Hₙ = Im(T_{n+β+1} ⟶ Tₙ)`, and let
`Φ : C ⥤ C'` preserve monomorphisms. A map of towers `α : P ⟶ T ⋙ Φ` from a tower `P` whose
transitions are epimorphisms factors uniquely through `n ↦ Φ(Hₙ)`
(`CategoryTheory.LAdicTower.LESData.liftStableImageComp`): `αₙ` composed with the epimorphism
`P_{n+β+1} ⟶ Pₙ` is `α_{n+β+1}` followed by `Φ(T_{n+β+1} ⟶ Tₙ)`, which factors through the
monomorphism `Φ(Hₙ) ⟶ Φ(Tₙ)`. For `Φ` the identity this is
`CategoryTheory.LAdicTower.LESData.liftStableImage`.

## Main definitions

* `CategoryTheory.LAdicTower.LESData.liftStableImageComp`: the factorisation of `α` through
  `n ↦ Φ(Hₙ)`.

## Main results

* `CategoryTheory.LAdicTower.LESData.liftStableImageComp_ι`: this factorisation followed by the
  image under `Φ` of the inclusion `Hₙ ⟶ Tₙ` is `α`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace CategoryTheory.LAdicTower

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C] {C' : Type u'} [Category.{v'} C'] [Abelian C']
  {T S : ℕᵒᵖ ⥤ C} {ℓ : ℕ} (D : LESData T S ℓ) [IsNoetherianObject (towerObj S 0)]
  (Φ : C ⥤ C') [Φ.PreservesMonomorphisms]
  {P : ℕᵒᵖ ⥤ C'} (hP : ∀ n, Epi (towerMap P (Nat.le_succ n))) (α : P ⟶ T ⋙ Φ)

include hP in
/-- The level-`n` component of `CategoryTheory.LAdicTower.LESData.liftStableImageComp`. -/
def LESData.liftStableImageCompApp (n : ℕ) :
    P.obj (op n) ⟶ (D.stableImageTower ⋙ Φ).obj (op n) :=
  have hn : n ≤ n + D.shift + 1 := by omega
  haveI : Epi (towerMap P hn) := epi_towerMap_of_epi_succ hP hn
  haveI : StrongEpi (towerMap P hn) := strongEpi_of_epi _
  (CommSq.mk (f := α.app (op (n + D.shift + 1)) ≫ Φ.map (D.stableImageRetraction n))
    (g := towerMap P hn) (h := Φ.map (D.stableImageι.app (op n)))
    (i := α.app (op n)) (by
      rw [Category.assoc, ← Φ.map_comp, D.stableImageRetraction_ι]
      exact (α.naturality (homOfLE hn).op).symm)).lift

/-- The level-`n` component of `CategoryTheory.LAdicTower.LESData.liftStableImageComp`, followed
by `Φ` applied to the inclusion `Hₙ ⟶ Tₙ`, is `αₙ`. -/
@[reassoc (attr := simp)]
theorem LESData.liftStableImageCompApp_ι (n : ℕ) :
    D.liftStableImageCompApp Φ hP α n ≫ Φ.map (D.stableImageι.app (op n)) = α.app (op n) := by
  have h : n ≤ n + D.shift + 1 := by omega
  have : Epi (towerMap P h) := epi_towerMap_of_epi_succ hP h
  have : StrongEpi (towerMap P h) := strongEpi_of_epi _
  exact CommSq.fac_right _

/-- **The factorisation through the image under `Φ` of the stable images** of a map of towers
out of a tower with surjective transitions. -/
def LESData.liftStableImageComp : P ⟶ D.stableImageTower ⋙ Φ where
  app n := D.liftStableImageCompApp Φ hP α n.unop
  naturality X Y f := by
    obtain ⟨x⟩ := X
    obtain ⟨y⟩ := Y
    rw [← cancel_mono (Φ.map (D.stableImageι.app (op y)))]
    simp only [Category.assoc, LESData.liftStableImageCompApp_ι]
    rw [Functor.comp_map, ← Φ.map_comp, D.stableImageι.naturality f, Φ.map_comp,
      LESData.liftStableImageCompApp_ι_assoc]
    exact α.naturality f

/-- `CategoryTheory.LAdicTower.LESData.liftStableImageComp` followed by `Φ` applied to the
inclusion of the stable image tower into `T` is `α`. -/
@[reassoc (attr := simp)]
theorem LESData.liftStableImageComp_ι :
    D.liftStableImageComp Φ hP α ≫ Functor.whiskerRight D.stableImageι Φ = α :=
  NatTrans.ext (funext fun n => D.liftStableImageCompApp_ι Φ hP α n.unop)

end CategoryTheory.LAdicTower

end
