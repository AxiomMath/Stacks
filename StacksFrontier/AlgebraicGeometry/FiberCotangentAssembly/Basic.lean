module

public import StacksFrontier.AlgebraicGeometry.FiberCotangentAssembly.Residue
public import StacksFrontier.AlgebraicGeometry.FiberCotangentIdentification.Kaehler
public import StacksFrontier.AlgebraicGeometry.FiberCotangentIdentification.Uniqueness

/-!
# The canonical identification in part (4) of Tag 01V9

Condition (4) of Stacks Tag 01V9 carries a displayed equality between the residue-field fibre
`κ(x) ⊗ Ω_{X/S,x}` of the stalk of the sheaf of relative differentials of `f : X ⟶ S` and the
corresponding space `κ(x) ⊗ Ω_{X_s/κ(s),x}` computed on the scheme-theoretic fibre through `x`.
This file constructs that identification, as a linear equivalence over `κ(x)`, and shows that it
is the unique one carrying germs of universal relative differentials to germs of universal
relative differentials.

## Main definitions

* `Stacks.FiberCotangentAssembly.fiberKaehlerBaseEquiv`: the relative differentials of the fibre
  read over `κ(s)` rather than over the stalk of `Spec κ(s)`.
* `Stacks.FiberCotangentAssembly.sourceCongr`, `middleCongr` and `fiberCongr`: the three steps
  of the comparison, and `fiberCotangentLinearEquiv` their composite, as a linear equivalence.

## Main results

* `Stacks.FiberCotangentAssembly.fiberCotangentLinearEquiv_tmul_germ_d`: the identification
  carries the germ of the universal relative differential of a local section to the germ of the
  universal relative differential of its pullback to the fibre.
* `Stacks.FiberCotangentAssembly.fiberDifferentialsTensorIdentification`: the identification
  together with that characterization and its uniqueness.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.SheafOfModules
open Stacks.FiberCotangentIdentification
open Stacks.RelativeDifferentialStalk Stacks.RelativeDifferentialStalkMap
open Stacks.SmoothAtJacobian
open scoped TensorProduct

universe u

namespace Stacks.FiberCotangentAssembly

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-! ### The scalar structures -/

/-- `κ(x)` as an algebra over `𝒪_{X,x}`, through `AlgebraicGeometry.Scheme.residue`. -/
public noncomputable abbrev algebraResidue :
    Algebra (ToType (X.sheaf.presheaf.stalk x)) (ToType (X.residueField x)) :=
  (X.residue x).hom.toAlgebra

/-- `𝒪_{X_s,x}` as an algebra over `𝒪_{X,x}`, through the inclusion of the fibre. -/
public noncomputable abbrev algebraStalkFiber :
    Algebra (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :=
  algebraStalkFiberStalk f x

/-- `𝒪_{X_s,x}` as an algebra over `𝒪_{S,f x}`, through `𝒪_{X,x}`. -/
public noncomputable abbrev algebraTargetFiber :
    Algebra (ToType (S.presheaf.stalk (f x)))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :=
  algebraTargetFiberStalk f x

/-- `𝒪_{X_s,x}` as an algebra over `κ(s)`. -/
public noncomputable abbrev algebraResidueFiber :
    Algebra (targetResidue f x)
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :=
  algebraResidueFiberStalk f x

/-- `κ(x)` as an algebra over the local ring of the fibre, through the canonical residue-field
point. -/
public noncomputable abbrev algebraFiberResidue :
    Algebra (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) :=
  (Scheme.stalkClosedPointTo (f.asFiberHom x)).hom.toAlgebra

/-- The module structure of `𝒪_{X,x}` on the stalk of the relative differentials,
`Stacks.SmoothAtJacobian.relativeDifferentialStalkModule`. -/
public noncomputable abbrev moduleStalk :
    Module (ToType (X.sheaf.presheaf.stalk x)) (relativeDifferentialStalk f x) :=
  relativeDifferentialStalkModule f x

/-- The stalk of `Spec κ(s)` acting on the local ring of the fibre through the fibre's structural
morphism. -/
public noncomputable abbrev algebraSpecStalkFiber :
    Algebra (ToType ((Spec (S.residueField (f x))).presheaf.stalk
        ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :=
  (Scheme.Hom.stalkMap (f.fiberToSpecResidueField (f x)) (fiberPoint f x)).hom.toAlgebra

/-- The scalar tower `𝒪_{S,f x} → 𝒪_{X,x} → 𝒪_{X_s,x}`. -/
public theorem isScalarTowerStalkFiber :
    letI := algebraStalkMap f x
    letI := algebraStalkFiber f x
    letI := algebraTargetFiber f x
    IsScalarTower (ToType (S.presheaf.stalk (f x))) (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) := by
  let := algebraStalkMap f x
  let := algebraStalkFiber f x
  let := algebraTargetFiber f x
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The scalar tower `𝒪_{S,f x} → κ(s) → 𝒪_{X_s,x}`. -/
public theorem isScalarTowerTargetResidueFiber :
    letI := algebraStalkMap f x
    letI := algebraResidueFiber f x
    letI := algebraTargetFiber f x
    IsScalarTower (ToType (S.presheaf.stalk (f x))) (targetResidue f x)
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) := by
  let := algebraStalkMap f x
  let := algebraResidueFiber f x
  let := algebraTargetFiber f x
  exact IsScalarTower.of_algebraMap_eq fun a =>
    (quotientEquivFiberStalk_mk f x ((f.stalkMap x).hom a)).symm

/-- The Kähler differentials of the local ring of the fibre over `κ(s)` are its Kähler
differentials over the stalk of `Spec κ(s)` at the image of the canonical point. -/
public noncomputable def fiberKaehlerBaseEquiv :
    letI := algebraStalkMap f x
    letI := algebraResidueFiber f x
    letI := algebraSpecStalkFiber f x
    letI := algebraSpecResidueStalk f x
    KaehlerDifferential (targetResidue f x)
        (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      ≃ₗ[ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))]
      KaehlerDifferential
        (ToType ((Spec (S.residueField (f x))).presheaf.stalk
          ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))
        (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) := by
  letI := algebraStalkMap f x
  letI := algebraResidueFiber f x
  letI := algebraSpecStalkFiber f x
  letI := algebraSpecResidueStalk f x
  have : IsScalarTower (targetResidue f x)
      (ToType ((Spec (S.residueField (f x))).presheaf.stalk
        ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :=
    isScalarTower_specResidueStalk f x
  exact kaehlerMapEquivOfSurjective _ _ _ (surjective_algebraMap_specResidueStalk f x)

/-- A composite of two linear equivalences, applied to an element. -/
public theorem trans_apply' {R : Type*} [Semiring R] {M N P : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    (e₁ : M ≃ₗ[R] N) (e₂ : N ≃ₗ[R] P) (m : M) : (e₁.trans e₂) m = e₂ (e₁ m) := rfl

/-- **The image in the local ring of the fibre of the germ of a section is the germ of its
pullback to the fibre**, through the comparison of the stalks at `x` and at the canonical
point. -/
public theorem germ_stalkToFiberStalk (U : X.Opens) (hxU : x ∈ U)
    (hxf : fiberPoint f x ∈ (f.fiberι (f x)) ⁻¹ᵁ U) :
    X.presheaf.germ U x hxU ≫ (X.presheaf.stalkCongr
        (Inseparable.of_eq (fiberι_fiberPoint f x).symm)).hom ≫
        Scheme.Hom.stalkMap (f.fiberι (f x)) (fiberPoint f x) =
      (f.fiberι (f x)).app U ≫
        (f.fiber (f x)).presheaf.germ ((f.fiberι (f x)) ⁻¹ᵁ U) (fiberPoint f x) hxf := by
  rw [germ_stalkCongr_assoc _ hxU _ hxf]
  exact Scheme.Hom.germ_stalkMap (f.fiberι (f x)) U (fiberPoint f x) hxf

/-- `Stacks.FiberCotangentAssembly.germ_stalkToFiberStalk` on an element. -/
public theorem stalkToFiberStalk_germ (U : X.Opens) (hxU : x ∈ U)
    (hxf : fiberPoint f x ∈ (f.fiberι (f x)) ⁻¹ᵁ U) (a : ToType (X.presheaf.obj (op U))) :
    stalkToFiberStalk f x ((X.presheaf.germ U x hxU).hom a) =
      ((f.fiber (f x)).presheaf.germ ((f.fiberι (f x)) ⁻¹ᵁ U) (fiberPoint f x) hxf).hom
        (((f.fiberι (f x)).app U).hom a) :=
  congrArg (fun z => CommRingCat.Hom.hom z a) (germ_stalkToFiberStalk f x U hxU hxf)

/-- The source side of the comparison: the residue-field fibre of the identification of the
stalk of the relative differentials with the Kähler differentials of the stalk map. -/
public noncomputable abbrev sourceCongr
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))] :
    letI := algebraStalkMap f x
    letI := algebraResidue x
    (ToType (X.residueField x) ⊗[ToType (X.sheaf.presheaf.stalk x)]
        ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials f).val.presheaf x))
      ≃ₗ[ToType (X.residueField x)]
      (ToType (X.residueField x) ⊗[ToType (X.sheaf.presheaf.stalk x)]
        KaehlerDifferential (ToType (S.presheaf.stalk (f x)))
          (ToType (X.sheaf.presheaf.stalk x))) :=
  letI := algebraStalkMap f x
  letI := algebraResidue x
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
    (relativeDifferentialsStalkKaehlerEquiv f x)

/-- The fibre side of the comparison: the residue-field fibre of
`Stacks.FiberCotangentAssembly.fiberKaehlerBaseEquiv` followed by the identification for the
fibre. -/
public noncomputable abbrev fiberCongr
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds (fiberPoint f x)))] :
    letI := algebraStalkMap f x
    letI := algebraResidueFiber f x
    letI := algebraFiberResidue f x
    (ToType (X.residueField x) ⊗[ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))]
        KaehlerDifferential (targetResidue f x)
          (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))))
      ≃ₗ[ToType (X.residueField x)]
      (ToType (X.residueField x) ⊗[ToType ((f.fiber (f x)).sheaf.presheaf.stalk
          (fiberPoint f x))]
        ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials
            (f.fiberToSpecResidueField (f x))).val.presheaf (fiberPoint f x))) :=
  letI := algebraStalkMap f x
  letI := algebraResidueFiber f x
  letI := algebraFiberResidue f x
  letI := algebraSpecStalkFiber f x
  letI := algebraSpecResidueStalk f x
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
    ((fiberKaehlerBaseEquiv f x).trans
      (relativeDifferentialsStalkKaehlerEquiv (f.fiberToSpecResidueField (f x))
        (fiberPoint f x)).symm)

/-- The middle step of the comparison: the relative cotangent space of a pushout square does not
depend on which side it is computed on.  This is
`Stacks.FiberCotangentIdentification.kaehlerTensorEquivOfIsPushout` at the pushout square
`Stacks.FiberCotangentIdentification.isPushout_fiberStalk`. -/
public noncomputable abbrev middleCongr :
    letI := algebraStalkMap f x
    letI := algebraStalkFiber f x
    letI := algebraTargetFiber f x
    letI := algebraResidueFiber f x
    letI := algebraFiberResidue f x
    letI := algebraResidue x
    (ToType (X.residueField x) ⊗[ToType (X.sheaf.presheaf.stalk x)]
        KaehlerDifferential (ToType (S.presheaf.stalk (f x)))
          (ToType (X.sheaf.presheaf.stalk x)))
      ≃ₗ[ToType (X.residueField x)]
      (ToType (X.residueField x) ⊗[ToType ((f.fiber (f x)).sheaf.presheaf.stalk
          (fiberPoint f x))]
        KaehlerDifferential (targetResidue f x)
          (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))) :=
  letI := algebraStalkMap f x
  letI := algebraStalkFiber f x
  letI := algebraTargetFiber f x
  letI := algebraResidueFiber f x
  letI := algebraFiberResidue f x
  letI := algebraResidue x
  have := isScalarTowerStalkFiber f x
  have := isScalarTowerTargetResidueFiber f x
  have : IsScalarTower (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) := isScalarTower_residueField f x
  have : Algebra.IsPushout (ToType (S.presheaf.stalk (f x))) (targetResidue f x)
      (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :=
    isPushout_fiberStalk f x
  kaehlerTensorEquivOfIsPushout _ _ _ _ _

/-- **The canonical identification of the two relative cotangent spaces of condition (4)**, as a
linear equivalence over `κ(x)`: the three steps composed. -/
public noncomputable abbrev fiberCotangentLinearEquiv
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds (fiberPoint f x)))] :
    letI := algebraStalkMap f x
    letI := algebraResidue x
    letI := algebraFiberResidue f x
    (ToType (X.residueField x) ⊗[ToType (X.sheaf.presheaf.stalk x)]
        ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials f).val.presheaf x))
      ≃ₗ[ToType (X.residueField x)]
      (ToType (X.residueField x) ⊗[ToType ((f.fiber (f x)).sheaf.presheaf.stalk
          (fiberPoint f x))]
        ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials
            (f.fiberToSpecResidueField (f x))).val.presheaf (fiberPoint f x))) :=
  letI := algebraStalkMap f x
  letI := algebraResidue x
  letI := algebraFiberResidue f x
  (sourceCongr f x).trans ((middleCongr f x).trans (fiberCongr f x))

/-- `Stacks.FiberCotangentAssembly.fiberKaehlerBaseEquiv` carries universal differentials to
universal differentials. -/
public theorem fiberKaehlerBaseEquiv_D
    (b : ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :
    letI := algebraStalkMap f x
    letI := algebraResidueFiber f x
    letI := algebraSpecStalkFiber f x
    letI := algebraSpecResidueStalk f x
    fiberKaehlerBaseEquiv f x
        (KaehlerDifferential.D (targetResidue f x)
          (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) b) =
      KaehlerDifferential.D
        (ToType ((Spec (S.residueField (f x))).presheaf.stalk
          ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))
        (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) b := by
  let := algebraStalkMap f x
  let := algebraResidueFiber f x
  let := algebraSpecStalkFiber f x
  let := algebraSpecResidueStalk f x
  let _ : IsScalarTower (targetResidue f x)
      (ToType ((Spec (S.residueField (f x))).presheaf.stalk
        ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :=
    isScalarTower_specResidueStalk f x
  exact kaehlerMapEquivOfSurjective_D _ _ _ (surjective_algebraMap_specResidueStalk f x) b

/-- **The image in the local ring of the fibre of the germ of a section is the germ of its
pullback**, as the structural algebra map. -/
public theorem algebraMap_germ (U : X.Opens) (hxU : x ∈ U)
    (hxf : fiberPoint f x ∈ (f.fiberι (f x)) ⁻¹ᵁ U)
    (a : ToType (X.presheaf.obj (op U))) :
    letI := algebraStalkFiber f x
    algebraMap (ToType (X.sheaf.presheaf.stalk x))
        (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
        ((X.presheaf.germ U x hxU).hom a) =
      ((f.fiber (f x)).presheaf.germ ((f.fiberι (f x)) ⁻¹ᵁ U) (fiberPoint f x) hxf).hom
        (((f.fiberι (f x)).app U).hom a) := by
  let := algebraStalkFiber f x
  exact stalkToFiberStalk_germ f x U hxU hxf a

/-- `Stacks.FiberCotangentAssembly.middleCongr` on `1 ⊗ d b`. -/
public theorem middleCongr_tmul_D (b : ToType (X.sheaf.presheaf.stalk x)) :
    letI := algebraStalkMap f x
    letI := algebraStalkFiber f x
    letI := algebraResidueFiber f x
    letI := algebraFiberResidue f x
    letI := algebraResidue x
    middleCongr f x ((1 : ToType (X.residueField x))
        ⊗ₜ[ToType (X.sheaf.presheaf.stalk x)]
        KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
          (ToType (X.sheaf.presheaf.stalk x)) b) =
      (1 : ToType (X.residueField x))
        ⊗ₜ[ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))]
        KaehlerDifferential.D (targetResidue f x)
          (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
          (algebraMap (ToType (X.sheaf.presheaf.stalk x))
            (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) b) := by
  let := algebraStalkMap f x
  let := algebraStalkFiber f x
  let := algebraTargetFiber f x
  let := algebraResidueFiber f x
  let := algebraFiberResidue f x
  let := algebraResidue x
  let := isScalarTowerStalkFiber f x
  let := isScalarTowerTargetResidueFiber f x
  let _ : IsScalarTower (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      (ToType (X.residueField x)) := isScalarTower_residueField f x
  let _ : Algebra.IsPushout (ToType (S.presheaf.stalk (f x))) (targetResidue f x)
      (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :=
    isPushout_fiberStalk f x
  exact kaehlerTensorEquivOfIsPushout_tmul_D _ _ _ _ _ b

/-- `Stacks.FiberCotangentAssembly.fiberCongr` on `1 ⊗ d c`. -/
public theorem fiberCongr_tmul_D
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds (fiberPoint f x)))]
    (c : ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) :
    letI := algebraStalkMap f x
    letI := algebraResidueFiber f x
    letI := algebraFiberResidue f x
    letI := algebraSpecStalkFiber f x
    fiberCongr f x ((1 : ToType (X.residueField x))
        ⊗ₜ[ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))]
        KaehlerDifferential.D (targetResidue f x)
          (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) c) =
      (1 : ToType (X.residueField x))
        ⊗ₜ[ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))]
        ((relativeDifferentialsStalkKaehlerEquiv (f.fiberToSpecResidueField (f x))
          (fiberPoint f x)).symm
          (KaehlerDifferential.D
            (ToType ((Spec (S.residueField (f x))).presheaf.stalk
              ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))
            (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))) c)) := by
  let := algebraStalkMap f x
  let := algebraResidueFiber f x
  let := algebraFiberResidue f x
  let := algebraSpecStalkFiber f x
  let := algebraSpecResidueStalk f x
  rw [TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, trans_apply',
    fiberKaehlerBaseEquiv_D]

/-- **The identification carries universal relative differentials to universal relative
differentials**: the germ at `x` of the universal differential of a local section `a` of `𝒪_X`
goes to the germ at the canonical point of the fibre of the universal differential of the
pullback of `a`. -/
public theorem fiberCotangentLinearEquiv_tmul_germ_d
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds (fiberPoint f x)))]
    (U : X.Opens) (hxU : x ∈ U) (hxf : fiberPoint f x ∈ (f.fiberι (f x)) ⁻¹ᵁ U)
    (a : ToType (X.presheaf.obj (op U))) :
    letI := algebraStalkMap f x
    letI := algebraResidue x
    letI := algebraFiberResidue f x
    fiberCotangentLinearEquiv f x
        ((1 : ToType (X.residueField x)) ⊗ₜ[ToType (X.sheaf.presheaf.stalk x)]
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (Scheme.Hom.relativeDifferentials f).val.presheaf U x hxU).hom
            ((Scheme.Hom.universalRelativeDerivation f).d a))) =
      (1 : ToType (X.residueField x))
        ⊗ₜ[ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))]
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials
            (f.fiberToSpecResidueField (f x))).val.presheaf
            ((f.fiberι (f x)) ⁻¹ᵁ U) (fiberPoint f x) hxf).hom
          ((Scheme.Hom.universalRelativeDerivation
            (f.fiberToSpecResidueField (f x))).d (((f.fiberι (f x)).app U).hom a))) := by
  let := algebraStalkMap f x
  let := algebraResidue x
  let := algebraStalkFiber f x
  let := algebraTargetFiber f x
  let := algebraResidueFiber f x
  let := algebraFiberResidue f x
  let := algebraSpecStalkFiber f x
  let := algebraSpecResidueStalk f x
  have hA : (relativeDifferentialsStalkKaehlerEquiv f x)
      ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf U x hxU).hom
        ((Scheme.Hom.universalRelativeDerivation f).d a)) =
      KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
        (ToType (X.sheaf.presheaf.stalk x)) ((X.presheaf.germ U x hxU).hom a) :=
    relativeDifferentialsStalkKaehlerEquiv_germ_d f x
      (OrderDual.toDual (⟨U, hxU⟩ : OpenNhds x)) a
  have hC : (relativeDifferentialsStalkKaehlerEquiv (f.fiberToSpecResidueField (f x))
        (fiberPoint f x))
      ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials
          (f.fiberToSpecResidueField (f x))).val.presheaf
          ((f.fiberι (f x)) ⁻¹ᵁ U) (fiberPoint f x) hxf).hom
        ((Scheme.Hom.universalRelativeDerivation
          (f.fiberToSpecResidueField (f x))).d (((f.fiberι (f x)).app U).hom a))) =
      KaehlerDifferential.D
        (ToType ((Spec (S.residueField (f x))).presheaf.stalk
          ((f.fiberToSpecResidueField (f x)) (fiberPoint f x))))
        (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
        (((f.fiber (f x)).presheaf.germ ((f.fiberι (f x)) ⁻¹ᵁ U) (fiberPoint f x) hxf).hom
          (((f.fiberι (f x)).app U).hom a)) :=
    relativeDifferentialsStalkKaehlerEquiv_germ_d (f.fiberToSpecResidueField (f x))
      (fiberPoint f x)
      (OrderDual.toDual (⟨(f.fiberι (f x)) ⁻¹ᵁ U, hxf⟩ : OpenNhds (fiberPoint f x)))
      (((f.fiberι (f x)).app U).hom a)
  rw [← algebraMap_germ f x U hxU hxf a] at hC
  rw [trans_apply', trans_apply',
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, hA,
    middleCongr_tmul_D f x ((X.presheaf.germ U x hxU).hom a)]
  exact (fiberCongr_tmul_D f x (algebraMap (ToType (X.sheaf.presheaf.stalk x))
      (ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x)))
      ((X.presheaf.germ U x hxU).hom a))).trans
    (congrArg (fun z => (1 : ToType (X.residueField x))
      ⊗ₜ[ToType ((f.fiber (f x)).sheaf.presheaf.stalk (fiberPoint f x))] z)
      ((LinearEquiv.symm_apply_eq _).2 hC.symm))

/-- `Stacks.FiberCotangentAssembly.fiberCotangentLinearEquiv` satisfies the specification
`Stacks.SmoothAtJacobian.IsFiberDifferentialsTensorEquiv`. -/
public theorem isFiberDifferentialsTensorEquiv_toModuleIso
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds (fiberPoint f x)))] :
    IsFiberDifferentialsTensorEquiv f x (fiberCotangentLinearEquiv f x).toModuleIso := by
  intro U hxU a
  exact fiberCotangentLinearEquiv_tmul_germ_d f x U hxU _ a

/-- The fibre of the sheaf of relative differentials at `x` is canonically identified with the
fibre of the relative differentials of the scheme-theoretic fibre. -/
@[stacks 01V9 "canonical identification in part (4)"]
public noncomputable def fiberDifferentialsTensorIdentification :
    FiberDifferentialsTensorIdentification f x := by
  classical
  exact
    { equiv := (fiberCotangentLinearEquiv f x).toModuleIso
      isCanonical := isFiberDifferentialsTensorEquiv_toModuleIso f x
      unique := fun e he => eq_of_isFiberDifferentialsTensorEquiv f x e _ he
        (isFiberDifferentialsTensorEquiv_toModuleIso f x) }

end Stacks.FiberCotangentAssembly

end
