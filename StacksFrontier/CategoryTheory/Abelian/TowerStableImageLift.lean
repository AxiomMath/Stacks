module

public import StacksFrontier.CategoryTheory.Abelian.TowerMittagLeffler

/-!
# Maps of towers with surjective transitions into the stable image tower

Let `T` be a tower in an abelian category with the exact sequences of
`CategoryTheory.LAdicTower.LESData`, so that its stable images `Hₙ = Im(T_{n+β+1} ⟶ Tₙ)` form a
tower (`CategoryTheory.LAdicTower.LESData.stableImageTower`). A map of towers `α : P ⟶ T` from a
tower `P` whose transitions are epimorphisms (for instance the tower of levels of an ℓ-adic
sheaf) factors uniquely through the stable images: `αₙ` composed with the epimorphism
`P_{n+β+1} ⟶ Pₙ` is `α_{n+β+1}` followed by `T_{n+β+1} ⟶ Tₙ`, which lands in `Hₙ`.

## Main definitions

* `CategoryTheory.LAdicTower.LESData.liftStableImage`: the factorisation.

## Main results

* `CategoryTheory.LAdicTower.LESData.liftStableImage_ι`: it is a factorisation.
* `CategoryTheory.LAdicTower.epi_towerMap_of_epi_succ`: the transitions of a tower whose
  successive transitions are epimorphisms are epimorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace CategoryTheory.LAdicTower

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

omit [Abelian C] in
/-- **The transitions of a tower with surjective successive transitions are surjective.** -/
theorem epi_towerMap_of_epi_succ {P : ℕᵒᵖ ⥤ C} (hP : ∀ n, Epi (towerMap P (Nat.le_succ n)))
    {a b : ℕ} (h : a ≤ b) : Epi (towerMap P h) := by
  induction b, h using Nat.le_induction with
  | base => rw [towerMap_self]; infer_instance
  | succ b hab ih =>
    rw [← towerMap_comp P hab (Nat.le_succ b)]
    exact epi_comp _ _

variable {T S : ℕᵒᵖ ⥤ C} {ℓ : ℕ} (D : LESData T S ℓ) [IsNoetherianObject (towerObj S 0)]
  {P : ℕᵒᵖ ⥤ C} (hP : ∀ n, Epi (towerMap P (Nat.le_succ n))) (α : P ⟶ T)

include hP in
/-- A map of towers out of a tower with surjective transitions lands in the stable images. -/
theorem LESData.stableImageSub_factors (n : ℕ) :
    (D.stableImageSub n).Factors (α.app (op n)) := by
  have h : n ≤ n + D.shift + 1 := by omega
  have : Epi (towerMap P h) := epi_towerMap_of_epi_succ hP h
  have : StrongEpi (towerMap P h) := strongEpi_of_epi _
  have sq : CommSq (α.app (op (n + D.shift + 1)) ≫ D.stableImageRetraction n)
      (towerMap P h) (D.stableImageι.app (op n)) (α.app (op n)) := ⟨by
    rw [Category.assoc, D.stableImageRetraction_ι]
    exact (α.naturality (homOfLE h).op).symm⟩
  exact (Subobject.factors_iff _ _).2 ⟨sq.lift, sq.fac_right⟩

/-- The component in degree `n` of the factorisation through the stable images of a map of towers
out of a tower with surjective transitions. -/
def LESData.liftStableImageApp (n : ℕ) : P.obj (op n) ⟶ D.stableImageTower.obj (op n) :=
  (D.stableImageSub n).factorThru (α.app (op n)) (D.stableImageSub_factors hP α n)

/-- The component `LESData.liftStableImageApp` followed by the inclusion of the stable image is
the component of `α`. -/
@[reassoc (attr := simp)]
theorem LESData.liftStableImageApp_ι (n : ℕ) :
    D.liftStableImageApp hP α n ≫ D.stableImageι.app (op n) = α.app (op n) :=
  Subobject.factorThru_arrow _ _ _

/-- **The factorisation through the stable images** of a map of towers out of a tower with
surjective transitions. -/
def LESData.liftStableImage : P ⟶ D.stableImageTower where
  app n := D.liftStableImageApp hP α n.unop
  naturality X Y f := by
    obtain ⟨x⟩ := X
    obtain ⟨y⟩ := Y
    rw [← cancel_mono (D.stableImageι.app (op y))]
    simp only [Category.assoc, D.stableImageι.naturality, LESData.liftStableImageApp_ι,
      LESData.liftStableImageApp_ι_assoc]
    exact α.naturality f

/-- The factorisation `LESData.liftStableImage` followed by the inclusion of the stable image
tower is `α`. -/
@[reassoc (attr := simp)]
theorem LESData.liftStableImage_ι : D.liftStableImage hP α ≫ D.stableImageι = α := by
  ext ⟨n⟩
  exact D.liftStableImageApp_ι hP α n

end CategoryTheory.LAdicTower

end
