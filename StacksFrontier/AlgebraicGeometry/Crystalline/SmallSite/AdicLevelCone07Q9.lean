module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# An adic completion as the limit of a tower through levelwise identifications

Let `N` be a module over a commutative ring `R`, `I` an ideal, `c` a natural number and
`D : ℕᵒᵖ ⥤ AddCommGrpCat` a tower of abelian groups.  Suppose given additive maps
`ψ_e : N → D(e)` killing `I^{c + e} N` and compatible with the transition maps of the tower.
They induce maps `N / I^{c + e} N → D(e)`, and the `I`-adic completion of `N` with the
components `x ↦ ψ_e(x_{c + e})` is a cone over `D`.  **If every induced map
`N / I^{c + e} N → D(e)` is bijective, the cone is a limit cone.**

This is the form in which the sections of a pulled back crystal over the levels of a Čech system
are identified with a completed base change in the proof of [Stacks, Tag 07Q9].

## Main definitions

* `AdicLevelCone07Q9.levelMap` — the map `N / I^{c + e} N → D(e)` induced by `ψ_e`.
* `AdicLevelCone07Q9.cone` — the cone with vertex the (universe-lifted) completion.

## Main results

* `AdicLevelCone07Q9.isLimit` — it is a limit cone when the level maps are bijective.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AdicLevelCone07Q9

variable {R : Type u} [CommRing R] (I : Ideal R) (N : Type u) [AddCommGroup N] [Module R N]
  (c : ℕ) (D : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (ψ : ∀ e : ℕ, N →+ D.obj (op e))
  (hψ : ∀ (e : ℕ), ∀ y ∈ (I ^ (c + e) • ⊤ : Submodule R N), ψ e y = 0)

/-- **The map `N / I^{c + e} N → D(e)` induced by `ψ_e`.** -/
def levelMap (e : ℕ) : N ⧸ (I ^ (c + e) • ⊤ : Submodule R N) →+ D.obj (op e) :=
  QuotientAddGroup.lift (I ^ (c + e) • ⊤ : Submodule R N).toAddSubgroup (ψ e)
    (fun y hy ↦ hψ e y hy)

/-- The level map on a class. -/
@[simp] theorem levelMap_mk (e : ℕ) (y : N) :
    levelMap I N c D ψ hψ e (Submodule.Quotient.mk y) = ψ e y := rfl

variable (hcomp : ∀ {e e' : ℕ} (h : e ≤ e') (y : N),
  D.map (homOfLE h).op (ψ e' y) = ψ e y)

include hcomp in
/-- The level maps commute with the transition maps. -/
theorem map_levelMap {e e' : ℕ} (h : e ≤ e')
    (z : N ⧸ (I ^ (c + e') • ⊤ : Submodule R N)) :
    D.map (homOfLE h).op (levelMap I N c D ψ hψ e' z) =
      levelMap I N c D ψ hψ e (AdicCompletion.transitionMap I N (Nat.add_le_add_left h c) z) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact hcomp h y

/-- **The completion as a cone over the tower**, with components `x ↦ ψ_e(x_{c + e})`. -/
def cone : Cone D where
  pt := AddCommGrpCat.of (ULift.{u + 1} (AdicCompletion I N))
  π :=
    { app := fun e ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦ levelMap I N c D ψ hψ e.unop (x.down.val (c + e.unop))
          map_zero' := map_zero _
          map_add' := fun x y ↦ map_add _ _ _ }
      naturality := fun e e' h ↦ AddCommGrpCat.ext fun x ↦ by
        change levelMap I N c D ψ hψ e'.unop (x.down.val (c + e'.unop)) =
          D.map h (levelMap I N c D ψ hψ e.unop (x.down.val (c + e.unop)))
        have hle : e'.unop ≤ e.unop := leOfHom h.unop
        obtain rfl : h = (homOfLE hle).op := rfl
        rw [map_levelMap I N c D ψ hψ hcomp hle, x.down.property] }

/-- The components of the cone. -/
@[simp] theorem cone_π_app (e : ℕ) (x : ULift.{u + 1} (AdicCompletion I N)) :
    ConcreteCategory.hom ((cone I N c D ψ hψ hcomp).π.app (op e)) x =
      levelMap I N c D ψ hψ e (x.down.val (c + e)) := rfl

variable (hbij : ∀ e : ℕ, Function.Bijective (levelMap I N c D ψ hψ e))

/-- The preimage at the level `c + e` of the component at `e` of a cone. -/
def liftLevel (s : Cone D) (y : s.pt) (e : ℕ) : N ⧸ (I ^ (c + e) • ⊤ : Submodule R N) :=
  (Equiv.ofBijective _ (hbij e)).symm (ConcreteCategory.hom (s.π.app (op e)) y)

/-- The preimage of a component maps to the component. -/
theorem levelMap_liftLevel (s : Cone D) (y : s.pt) (e : ℕ) :
    levelMap I N c D ψ hψ e (liftLevel I N c D ψ hψ hbij s y e) =
      ConcreteCategory.hom (s.π.app (op e)) y :=
  (Equiv.ofBijective _ (hbij e)).apply_symm_apply _

include hcomp in
/-- The preimages of the components of a cone are compatible. -/
theorem transitionMap_liftLevel (s : Cone D) (y : s.pt) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I N (Nat.add_le_add_left hmn c)
        (liftLevel I N c D ψ hψ hbij s y n) = liftLevel I N c D ψ hψ hbij s y m := by
  apply (hbij m).1
  rw [← map_levelMap I N c D ψ hψ hcomp hmn, levelMap_liftLevel, levelMap_liftLevel]
  exact ConcreteCategory.congr_hom (s.w (homOfLE hmn).op) y

include hcomp in
/-- The element of the completion attached to a compatible family of the tower. -/
def liftFun (s : Cone D) (y : s.pt) : AdicCompletion I N :=
  ⟨fun k ↦ AdicCompletion.transitionMap I N (Nat.le_add_left k c)
      (liftLevel I N c D ψ hψ hbij s y k),
    fun {m n} hmn ↦ by
      change AdicCompletion.transitionMap I N hmn (AdicCompletion.transitionMap I N
        (Nat.le_add_left n c) (liftLevel I N c D ψ hψ hbij s y n)) =
        AdicCompletion.transitionMap I N (Nat.le_add_left m c) (liftLevel I N c D ψ hψ hbij s y m)
      rw [← transitionMap_liftLevel I N c D ψ hψ hcomp hbij s y hmn]
      obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (liftLevel I N c D ψ hψ hbij s y n)
      rw [← hz]
      rfl⟩

include hcomp in
/-- The lift of a cone at the level `c + e` is the preimage of its component at `e`. -/
theorem liftFun_val (s : Cone D) (y : s.pt) (e : ℕ) :
    (liftFun I N c D ψ hψ hcomp hbij s y).val (c + e) = liftLevel I N c D ψ hψ hbij s y e :=
  transitionMap_liftLevel I N c D ψ hψ hcomp hbij s y (Nat.le_add_left e c)

include hbij in
/-- An element of the completion is determined by its images in the levels of the tower. -/
theorem ext_levelMap {x x' : AdicCompletion I N}
    (h : ∀ e, levelMap I N c D ψ hψ e (x.val (c + e)) = levelMap I N c D ψ hψ e (x'.val (c + e))) :
    x = x' :=
  AdicCompletion.ext fun k ↦ by
    rw [← x.property (Nat.le_add_left k c), ← x'.property (Nat.le_add_left k c), (hbij k).1 (h k)]

/-- **The completion is the limit of the tower.** -/
def isLimit : IsLimit (cone I N c D ψ hψ hcomp) where
  lift s := AddCommGrpCat.ofHom
    { toFun := fun y ↦ ULift.up (liftFun I N c D ψ hψ hcomp hbij s y)
      map_zero' := ULift.ext (ext_levelMap I N c D ψ hψ hbij fun e ↦ by
        rw [liftFun_val, levelMap_liftLevel, map_zero]
        exact (map_zero _).symm)
      map_add' := fun y y' ↦ ULift.ext (ext_levelMap I N c D ψ hψ hbij fun e ↦ by
        rw [liftFun_val, levelMap_liftLevel, map_add]
        change _ = levelMap I N c D ψ hψ e ((liftFun I N c D ψ hψ hcomp hbij s y).val (c + e) +
          (liftFun I N c D ψ hψ hcomp hbij s y').val (c + e))
        rw [map_add, liftFun_val, liftFun_val, levelMap_liftLevel, levelMap_liftLevel]) }
  fac s e := AddCommGrpCat.ext fun y ↦ by
    change levelMap I N c D ψ hψ e.unop ((liftFun I N c D ψ hψ hcomp hbij s y).val (c + e.unop))
      = _
    rw [liftFun_val, levelMap_liftLevel]
  uniq s m hm := AddCommGrpCat.ext fun y ↦ ULift.ext (ext_levelMap I N c D ψ hψ hbij fun e ↦ by
    change _ = levelMap I N c D ψ hψ e ((liftFun I N c D ψ hψ hcomp hbij s y).val (c + e))
    rw [liftFun_val, levelMap_liftLevel]
    exact congrArg (fun g ↦ (ConcreteCategory.hom g : s.pt → _) y) (hm (op e)))

end AdicLevelCone07Q9

end

end
