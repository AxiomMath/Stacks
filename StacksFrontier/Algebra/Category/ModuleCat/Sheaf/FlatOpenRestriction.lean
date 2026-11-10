module

public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk

/-!
# Restriction to an open subspace preserves flatness

Let `(X, O_X)` be a ringed space, `U ⊆ X` open and `M` a flat sheaf of `O_X`-modules. Then the
restriction of `M` to the open subspace `(U, O_X|_U)` is a flat sheaf of `O_X|_U`-modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFlat_of_ringEquiv`: flatness of a module transported
  along a ring isomorphism of its scalars.
* `AlgebraicGeometry.SheafOfModules.isFlat_restrictMod`: **restriction to an open subspace
  preserves flatness.**

## References

* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- **Flatness transported along a ring isomorphism of the scalars.** If `M` is a flat
`S`-module, `e : R ≃+* S` and the `R`-action on `M` is the `S`-action read through `e`, then `M`
is a flat `R`-module. -/
theorem isFlat_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [Module.Flat S M]
    (e : R ≃+* S) (hsmul : ∀ (r : R) (m : M), r • m = e r • m) :
    Module.Flat R M := by
  let _inst : Algebra R S := e.toRingHom.toAlgebra
  have hmap : ∀ r : R, algebraMap R S r = e r := fun _ ↦ rfl
  have _hst : IsScalarTower R S M := by
    refine ⟨fun r s m ↦ ?_⟩
    rw [Algebra.smul_def, hmap, hsmul r (s • m), smul_smul]
  have _hRS : Module.Flat R S :=
    Module.Flat.of_linearEquiv
      { toFun := e.symm
        map_add' := fun x y ↦ map_add e.symm x y
        map_smul' := fun r s ↦ by
          change e.symm (r • s) = r * e.symm s
          rw [Algebra.smul_def, hmap, map_mul, e.symm_apply_apply]
        invFun := e
        left_inv := fun s ↦ e.apply_symm_apply s
        right_inv := fun r ↦ e.symm_apply_apply r }
  exact Module.Flat.trans R S M

/-- The restriction of a sheaf of commutative rings to an open subset, as a sheaf on the
subspace. -/
noncomputable def commRingRestrict {X : TopCat.{u}} (U : Opens X)
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    Sheaf (Opens.grothendieckTopology (TopCat.of (U : Type u))) CommRingCat.{u} :=
  ((LocallyFreeRank.inclF X U).sheafPushforwardContinuous CommRingCat.{u}
    (Opens.grothendieckTopology (TopCat.of (U : Type u)))
    (Opens.grothendieckTopology X)).obj O

/-- The stalk of the restriction of a sheaf of modules to an open subspace is a module over the
`CommRingCat`-valued stalk of the restricted structure sheaf. -/
noncomputable instance instModuleStalkRestrictModComm {X : TopCat.{u}} (U : Opens X)
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (M : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O)) (y : (U : Type u)) :
    Module (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (commRingRestrict U O).obj y))
      (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
        (LocallyFreeRank.restrictMod X U (LocallyFreeRank.toRingSheaf X O) M).val.presheaf y)) :=
  LocallyFreeRank.instModuleStalkF (TopCat.of (U : Type u)) (commRingRestrict U O)
    (LocallyFreeRank.restrictMod X U (LocallyFreeRank.toRingSheaf X O) M) y

/-- The stalk of `M` at a point of `U`, as a module over the stalk of the *restricted* sheaf of
rings, through `LocallyFreeRank.restrictStalkRingEquiv`. -/
noncomputable instance instModuleStalkRestrictStalkRing {X : TopCat.{u}} (U : Opens X)
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (M : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O)) (x : X) (hU : x ∈ U) :
    Module (LocallyFreeRank.restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
  Module.compHom _ (LocallyFreeRank.restrictStalkRingEquiv X O x hU).toRingHom

/-- The ring isomorphism between the stalk `LocallyFreeRank.restrictStalkRing` of the restricted
sheaf of rings and the `CommRingCat`-valued stalk of `commRingRestrict U O` at `⟨x, hU⟩`. -/
noncomputable def restrictCommStalkRingEquiv {X : TopCat.{u}} (U : Opens X)
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X) (hU : x ∈ U) :
    LocallyFreeRank.restrictStalkRing X O x U hU ≃+*
      ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (commRingRestrict U O).obj
        (⟨x, hU⟩ : (U : Type u))) :=
  SemilinearStalk.commStalkRingEquiv (commRingRestrict U O).obj (⟨x, hU⟩ : (U : Type u))

/-- The two actions of the restricted ring stalk on the stalk of a restricted sheaf of modules
agree through `restrictCommStalkRingEquiv`. -/
theorem restrictCommStalkRingEquiv_smul {X : TopCat.{u}} (U : Opens X)
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (M : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O)) (x : X) (hU : x ∈ U)
    (s : LocallyFreeRank.restrictStalkRing X O x U hU)
    (n : ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
      (LocallyFreeRank.restrictMod X U (LocallyFreeRank.toRingSheaf X O) M).val.presheaf
      (⟨x, hU⟩ : (U : Type u)))) :
    restrictCommStalkRingEquiv U O x hU s • n = s • n :=
  SemilinearStalk.comm_smul_eq (commRingRestrict U O).obj
    (⟨x, hU⟩ : (U : Type u))
    (LocallyFreeRank.restrictMod X U (LocallyFreeRank.toRingSheaf X O) M).val s n

/-- **Restriction to an open subspace preserves flatness of a sheaf of modules.** -/
theorem isFlat_restrictMod {X : TopCat.{u}} (U : Opens X)
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (M : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O))
    (hM : IsFlat.{u, u, u, u} (O := O) M) :
    IsFlat.{u, u, u, u} (O := commRingRestrict U O)
      (LocallyFreeRank.restrictMod X U (LocallyFreeRank.toRingSheaf X O) M) := by
  have hkey : ∀ y : (U : Type u),
      Module.Flat (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u})
          (commRingRestrict U O).obj y))
        (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          (LocallyFreeRank.restrictMod X U (LocallyFreeRank.toRingSheaf X O) M).val.presheaf
          y)) := by
    rintro ⟨x, hU⟩
    let e := (restrictCommStalkRingEquiv U O x hU).symm.trans
      (LocallyFreeRank.restrictStalkRingEquiv X O x (U := U) hU)
    let instMx : Module (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u})
          (commRingRestrict U O).obj (⟨x, hU⟩ : (U : Type u))))
        (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
      Module.compHom _ e.toRingHom
    have _hflat : Module.Flat (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u})
          (commRingRestrict U O).obj (⟨x, hU⟩ : (U : Type u))))
        (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
      @isFlat_of_ringEquiv _ _ _ _ _ _ _ _ ((isFlat_iff_stalk_flat O M).1 hM x) e (fun _ _ ↦ rfl)
    obtain ⟨eL⟩ :=
      LocallyFreeRank.Trivialization.stalk_restrictMod_linearEquiv X O M x (U := U) hU
    let eA : (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          (LocallyFreeRank.restrictMod X U (LocallyFreeRank.toRingSheaf X O) M).val.presheaf
          (⟨x, hU⟩ : (U : Type u)))) ≃+
        (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
      { toFun := eL.toFun
        invFun := eL.invFun
        left_inv := eL.left_inv
        right_inv := eL.right_inv
        map_add' := eL.map_add' }
    have hsm : ∀ (r : ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u})
          (commRingRestrict U O).obj (⟨x, hU⟩ : (U : Type u))))
        (n : ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          (LocallyFreeRank.restrictMod X U (LocallyFreeRank.toRingSheaf X O) M).val.presheaf
          (⟨x, hU⟩ : (U : Type u)))),
        eA (r • n) = r • eA n := by
      intro r n
      have h₁ : r • n = (restrictCommStalkRingEquiv U O x hU).symm r • n := by
        rw [← restrictCommStalkRingEquiv_smul U O M x hU
          ((restrictCommStalkRingEquiv U O x hU).symm r) n, RingEquiv.apply_symm_apply]
      rw [h₁]
      exact eL.map_smul' _ n
    exact Module.Flat.of_linearEquiv
      (eA.toLinearEquiv (R := ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u})
        (commRingRestrict U O).obj (⟨x, hU⟩ : (U : Type u)))) hsm)
  exact (isFlat_iff_stalk_flat (commRingRestrict U O)
    (LocallyFreeRank.restrictMod X U (LocallyFreeRank.toRingSheaf X O) M)).2 hkey

end AlgebraicGeometry.SheafOfModules

end
