module

public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# The stalk map of a morphism of presheaves of modules

A morphism of presheaves of modules over a presheaf of commutative rings `R` on a topological
space induces, at each point, a map between the stalks of the underlying presheaves of abelian
groups. That map is additive, and it is linear over the stalk of `R`.

## Main definitions

* `AlgebraicGeometry.stalkMapAdd`: the induced map on stalks, as an additive homomorphism.
* `AlgebraicGeometry.stalkMapLinear`: the same map, as a linear map over the stalk of `R`.

## Implementation notes

The stalks are taken in `AddCommGrpCat`, with the module structure over the stalk of `R` provided
by `Mathlib.Algebra.Category.ModuleCat.Stalk`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The map on module stalks induced by a morphism of presheaves of modules, as a homomorphism
of additive groups. -/
noncomputable def stalkMapAdd
    {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (φ : M ⟶ N) (x : X) :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) →+
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map φ)).hom

/-- The map on module stalks induced by a morphism of presheaves of modules, as a linear map
over the stalk of the structure presheaf. -/
noncomputable def stalkMapLinear
    {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (φ : M ⟶ N) (x : X) :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) →ₗ[R.stalk x]
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) := by
  let ψ := stalkMapAdd M N φ x
  refine { toFun := ψ, map_add' := ψ.map_add, map_smul' := ?_ }
  intro r m
  obtain ⟨Ur, hUr, sr, hsr⟩ := R.exists_germ_eq r
  obtain ⟨Um, hUm, sm, hsm⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) M.presheaf m
  let U : TopologicalSpace.Opens X := Ur ⊓ Um
  let hU : x ∈ U := ⟨hUr, hUm⟩
  let iUr : U ⟶ Ur := homOfLE inf_le_left
  let iUm : U ⟶ Um := homOfLE inf_le_right
  let rU : R.obj (Opposite.op U) := (R.map iUr.op).hom sr
  let mU : M.obj (Opposite.op U) := (M.map iUm.op).hom sm
  have hgr : (R.germ U x hU).hom rU = r := by
    dsimp [rU]
    rw [TopCat.Presheaf.germ_res_apply R iUr x hU sr, hsr]
  have hgm : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hU).hom mU = m := by
    have hmU' : mU = (M.presheaf.map iUm.op).hom sm := rfl
    rw [hmU', TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.presheaf iUm x hU sm,
      hsm]
  rw [← hgr, ← hgm, ← PresheafOfModules.germ_smul M x U hU rU mU]
  have hnat (s : M.obj (Opposite.op U)) :
      ψ ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hU).hom s) =
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf U x hU).hom
          ((φ.app (Opposite.op U)).hom s) := by
    dsimp [ψ, stalkMapAdd]
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hU
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map φ) s
  rw [hnat (rU • mU), hnat mU, (φ.app (Opposite.op U)).hom.map_smul rU mU,
    PresheafOfModules.germ_smul N x U hU rU ((φ.app (Opposite.op U)).hom mU), hgr]
  simp

end AlgebraicGeometry

end
