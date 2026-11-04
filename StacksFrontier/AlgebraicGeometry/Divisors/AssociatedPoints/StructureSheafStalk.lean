module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk

/-!
# The stalk of the structure sheaf as a module over itself

The stalk at `x` of the structure sheaf of a scheme, viewed as an `𝒪_X`-module, is the local
ring `𝒪_{X, x}` itself.

## Main definitions

* `AlgebraicGeometry.structureSheafModule` is the structure sheaf read as a module over itself.
* `AlgebraicGeometry.structureSheafStalkLinearEquiv` is that identification, as a linear
  equivalence over `𝒪_{X, x}`.

## Main results

* `AlgebraicGeometry.commStalkRingEquiv_germ` compares the stalk of a presheaf of commutative
  rings with the stalk of the underlying presheaf of rings, on germs.

## Implementation notes

The underlying presheaf of modules of `SheafOfModules.unit X.ringCatSheaf` is the free module
of rank one, whose stalk is identified with the stalk of the sheaf of rings by
`LocallyFreeRank.unitStalkLEquiv`. That identification is stated for the `RingCat`-valued
presheaf obtained from `X.presheaf` by forgetting commutativity, so the scalars have to be
transported along `SemilinearStalk.commStalkRingEquiv`.

The compatibility of that transport with the two scalar actions on a stalk is
`SemilinearStalk.comm_smul_eq`, which is used as it stands.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- `SemilinearStalk.commStalkRingEquiv` is compatible with germs. -/
theorem commStalkRingEquiv_germ {Y : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} Y)
    (x : Y) (U : Opens Y) (hx : x ∈ U) (r : R.obj (op U)) :
    SemilinearStalk.commStalkRingEquiv R x
        (TopCat.Presheaf.germ (C := RingCat.{u}) (R ⋙ forget₂ CommRingCat RingCat) U x hx r) =
      R.germ U x hx r := by
  have h := ι_preservesColimitIso_inv (forget₂ CommRingCat.{u} RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R) (op ⟨U, hx⟩)
  exact congrArg (fun φ ↦ (ConcreteCategory.hom φ) r) h

/-- The structure sheaf of a scheme, read as a module over itself. -/
noncomputable abbrev structureSheafModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The stalk at `x` of the structure sheaf of `X`, read as an `𝒪_X`-module, is the local ring
`𝒪_{X, x}`. -/
noncomputable def structureSheafStalkLinearEquiv (X : Scheme.{u}) (x : X) :
    (TopCat.Presheaf.stalk (C := Ab.{u}) (structureSheafModule X).val.presheaf x)
      ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x := by
  let R := X.presheaf ⋙ forget₂ CommRingCat RingCat
  let : Module (TopCat.Presheaf.stalk (C := RingCat.{u}) R x)
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
      (SheafOfModules.unit X.ringCatSheaf).val x
  let eS : (TopCat.Presheaf.stalk (C := Ab.{u})
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf x)
      ≃ₗ[TopCat.Presheaf.stalk (C := RingCat.{u}) R x]
      TopCat.Presheaf.stalk (C := RingCat.{u}) R x :=
    LocallyFreeRank.unitStalkLEquiv R x
  let eR := SemilinearStalk.commStalkRingEquiv X.presheaf x
  refine
    { toFun := fun m ↦ eR (eS m)
      invFun := fun r ↦ eS.symm (eR.symm r)
      left_inv := fun m ↦ eS.injective (by simp)
      right_inv := fun r ↦ by simp
      map_add' := fun m n ↦ by simp
      map_smul' := ?_ }
  intro r m
  have hsmul : r • m = eR.symm r • m := by
    have h := SemilinearStalk.comm_smul_eq X.presheaf x
      ((SheafOfModules.unit X.ringCatSheaf).val :
        PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) (eR.symm r) m
    rwa [RingEquiv.apply_symm_apply] at h
  rw [hsmul, eS.map_smul]
  simp [eR, smul_eq_mul]

end AlgebraicGeometry
