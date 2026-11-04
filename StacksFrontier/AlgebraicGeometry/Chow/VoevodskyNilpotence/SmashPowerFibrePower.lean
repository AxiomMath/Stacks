module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerChernCap

/-!
# The fibre power of the smash power is the categorical fibre power

`Stacks.Chow.smashPointDifference` carries its `n`-th smash power on the fibre power `Xⁿ`
parenthesized from the left, `X^{n+1} = Xⁿ ×_k X`. The symmetric power map of Stacks 0B9G,
`Stacks.Hilbert.symmetricPowerMap`, starts from the categorical product
`∏ᶜ fun _ : Fin n => X` in `Over (Spec k)`. This file identifies the two, compatibly with the
projections: the `i`-th projection `Stacks.Chow.smashProjection` corresponds to the `i`-th
product projection, the last index being the newest factor.

## Main definitions

* `Stacks.Chow.smashToFibrePower` and `Stacks.Chow.fibrePowerToSmash` — the two comparison maps.
* `Stacks.Chow.smashFibrePowerIso` — the isomorphism.

## Main results

* `Stacks.Chow.smashFibrePowerIso_hom_left_comp_π` — `e ≫ prᵢ = smashProjection i`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] SmashPowerData.finiteType

variable (k : Type u) [Field k] (X : Over (fieldChowSituation k).S)
  [LocallyOfFiniteType X.hom] (x x' : (fieldChowSituation k).S ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _)
  (hx' : x' ≫ X.hom = 𝟙 _)

/-- The comparison map from the smash power's fibre power to the categorical fibre power, given
by the projections `smashProjection`. -/
def smashToFibrePower (n : ℕ) :
    (smashPointDifference k X.hom x x' hx hx' n).Y ⟶ ∏ᶜ fun _ : Fin n => X :=
  Pi.lift fun i => Over.homMk (smashProjection k X.hom x x' hx hx' n i)
    (smashProjection_comp k X.hom x x' hx hx' n i)

/-- The `i`-th product projection of `smashToFibrePower` is `smashProjection i`. -/
@[reassoc (attr := simp)]
theorem smashToFibrePower_π (n : ℕ) (i : Fin n) :
    smashToFibrePower k X x x' hx hx' n ≫ Pi.π (fun _ : Fin n => X) i =
      Over.homMk (smashProjection k X.hom x x' hx hx' n i)
        (smashProjection_comp k X.hom x x' hx hx' n i) :=
  Pi.lift_π _ _

/-- Forgetting the last factor of the categorical fibre power. -/
def fibrePowerInit (n : ℕ) :
    (∏ᶜ fun _ : Fin (n + 1) => X) ⟶ ∏ᶜ fun _ : Fin n => X :=
  Pi.lift fun i => Pi.π (fun _ : Fin (n + 1) => X) i.castSucc

/-- The comparison map from the categorical fibre power to the smash power's fibre power, built
by the recursion defining the latter. -/
def fibrePowerToSmash : (n : ℕ) →
    ((∏ᶜ fun _ : Fin n => X) ⟶ (smashPointDifference k X.hom x x' hx hx' n).Y)
  | 0 => Over.homMk (∏ᶜ fun _ : Fin 0 => X).hom (Category.comp_id _)
  | n + 1 => Over.homMk
      (pullback.lift (fibrePowerInit k X n ≫ fibrePowerToSmash n).left
        (Pi.π (fun _ : Fin (n + 1) => X) (Fin.last n)).left
        (by
          rw [Over.w]
          exact (Over.w (Pi.π (fun _ : Fin (n + 1) => X) (Fin.last n))).symm))
      (by
        rw [← Over.w (fibrePowerInit k X n ≫ fibrePowerToSmash n)]
        exact pullback.lift_fst_assoc _ _ _ _)

/-- Composing `fibrePowerToSmash` with `smashProjection i` gives the `i`-th product projection. -/
theorem fibrePowerToSmash_left_comp_smashProjection (n : ℕ) (i : Fin n) :
    (fibrePowerToSmash k X x x' hx hx' n).left ≫ smashProjection k X.hom x x' hx hx' n i =
      (Pi.π (fun _ : Fin n => X) i).left := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last =>
      rw [smashProjection_last]
      exact pullback.lift_snd _ _ _
    | cast i =>
      rw [smashProjection_castSucc]
      show pullback.lift _ _ _ ≫ pullback.fst _ X.hom ≫ _ = _
      rw [pullback.lift_fst_assoc, Over.comp_left, Category.assoc, ih, ← Over.comp_left,
        fibrePowerInit, Pi.lift_π]

/-- `smashToFibrePower` is a left inverse of `fibrePowerToSmash`. -/
theorem fibrePowerToSmash_comp_smashToFibrePower (n : ℕ) :
    fibrePowerToSmash k X x x' hx hx' n ≫ smashToFibrePower k X x x' hx hx' n = 𝟙 _ := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [Category.assoc, smashToFibrePower_π, Category.id_comp]
  ext
  rw [Over.comp_left]
  exact fibrePowerToSmash_left_comp_smashProjection k X x x' hx hx' n i

/-- Forgetting the last factor of the smash power's fibre power. -/
def smashInit (n : ℕ) :
    (smashPointDifference k X.hom x x' hx hx' (n + 1)).Y ⟶
      (smashPointDifference k X.hom x x' hx hx' n).Y :=
  Over.homMk (pullback.fst (smashPointDifference k X.hom x x' hx hx' n).Y.hom X.hom) rfl

/-- `smashToFibrePower` intertwines `smashInit` with `fibrePowerInit`. -/
theorem smashToFibrePower_comp_fibrePowerInit (n : ℕ) :
    smashToFibrePower k X x x' hx hx' (n + 1) ≫ fibrePowerInit k X n =
      smashInit k X x x' hx hx' n ≫ smashToFibrePower k X x x' hx hx' n := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [Category.assoc, fibrePowerInit, Pi.lift_π, smashToFibrePower_π, Category.assoc,
    smashToFibrePower_π]
  ext
  rw [Over.comp_left]
  exact smashProjection_castSucc k X.hom x x' hx hx' n i

/-- `fibrePowerToSmash` is a left inverse of `smashToFibrePower`. -/
theorem smashToFibrePower_comp_fibrePowerToSmash (n : ℕ) :
    smashToFibrePower k X x x' hx hx' n ≫ fibrePowerToSmash k X x x' hx hx' n = 𝟙 _ := by
  induction n with
  | zero =>
    ext
    rw [Over.comp_left]
    exact Over.w (smashToFibrePower k X x x' hx hx' 0)
  | succ n ih =>
    ext
    rw [Over.comp_left, Over.id_left]
    show _ ≫ pullback.lift _ _ _ = _
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Over.comp_left, ← Category.assoc,
        smashToFibrePower_comp_fibrePowerInit, Category.assoc, ih, Category.comp_id]
      exact (Category.id_comp _).symm
    · rw [Category.assoc, pullback.lift_snd, ← Over.comp_left, smashToFibrePower_π]
      exact (smashProjection_last k X.hom x x' hx hx' n).trans (Category.id_comp _).symm

/-- **The fibre power carrying the smash power is the categorical fibre power**, over `Spec k`,
compatibly with the projections. -/
def smashFibrePowerIso (n : ℕ) :
    (smashPointDifference k X.hom x x' hx hx' n).Y ≅ ∏ᶜ fun _ : Fin n => X where
  hom := smashToFibrePower k X x x' hx hx' n
  inv := fibrePowerToSmash k X x x' hx hx' n
  hom_inv_id := smashToFibrePower_comp_fibrePowerToSmash k X x x' hx hx' n
  inv_hom_id := fibrePowerToSmash_comp_smashToFibrePower k X x x' hx hx' n

/-- Under the identification, the `i`-th product projection is the `i`-th projection of the
smash power. -/
@[reassoc (attr := simp)]
theorem smashFibrePowerIso_hom_left_comp_π (n : ℕ) (i : Fin n) :
    (smashFibrePowerIso k X x x' hx hx' n).hom.left ≫
        (Pi.π (fun _ : Fin n => X) i).left =
      smashProjection k X.hom x x' hx hx' n i := by
  rw [← Over.comp_left]
  show (smashToFibrePower k X x x' hx hx' n ≫ _).left = _
  rw [smashToFibrePower_π]
  rfl

end Stacks.Chow

end
