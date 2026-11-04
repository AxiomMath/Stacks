module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionModule
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection

/-!
# The comparison `M̃ ⊗ 𝒪(i) ⟶ M(i)~` against the section of a homogeneous scalar

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `M = ⨁_{k ∈ ℤ} 𝒨 k` a graded
`S`-module and `X = Proj 𝒮`. A homogeneous element `a` of `S` of degree `i` gives both

* the operator `Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections`
  `Γ(X, M(n)~) → Γ(X, M(i + n)~)`, multiplication by `a` in every localized module fibre;
* the global section `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 i a` of the
  twist `𝒪_X(i)`.

The comparison map `Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap` for the shifted module
`M(n)`, evaluated against that section of `𝒪_X(i)`, agrees pointwise with the operator. The
statements are equations in the module fibres
`AlgebraicGeometry.ProjectiveSpectrum.Proj.ModuleFiber 𝒮 x`, since the targets of the two maps
are the associated sheaves of two gradings of `M` that are equal only propositionally.

## Main results

* `Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_tmul_degreeSection`: the comparison
  against the section of `𝒪(i)` given by `a` has value `a • s(x)` at every point `x`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_tmul_eq_homogeneousScalar`: the
  comparison against the section of `𝒪(i)` given by `a` has, at every point, the value of the
  homogeneous scalar action of `a` on shifted global sections.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_tmul_degreeNToGlobalSections`: the
  comparison takes the pure tensor of the section of `M(n)~` given by `m` with the section of
  `𝒪(i)` given by `a` to the section of `M(i + n)~` given by `a · m`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShifted (moduleTwistMap)
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (degreeNToGlobalSections degreeNToGlobalSections_apply homogeneousScalarGlobalSections
    homogeneousScalarGlobalSections_apply)
open Stacks.GradedLocalization
open Stacks.GradedModule (shiftedGrading)
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ModuleTwistIso

universe u w t

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S M : Type u} {σ : Type w} {τ : Type t} [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- A localized scalar with denominator `1` acts as its numerator. -/
private lemma mk_one_smul (P : Submonoid S) (a : S) (z : LocalizedModule P M) :
    LocalizedModule.mk a (1 : P) • z = a • z := by
  induction z using LocalizedModule.induction_on with
  | h m t =>
    refine (LocalizedModule.mk_smul_mk a m 1 t).trans ?_
    exact (congrArg (LocalizedModule.mk (a • m)) (one_mul t)).trans
      (LocalizedModule.smul'_mk a m t).symm

/-- The comparison `M(n)~ ⊗ 𝒪(i) ⟶ M(n)(i)~`, evaluated on `s ⊗ t` where `t` is the global
section of `𝒪(i)` given by a homogeneous element `a` of degree `i`, has value `a • s(x)` at every
point `x`. -/
theorem moduleTwistMap_tmul_degreeSection (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (s : moduleSections 𝒮 (shiftedGrading 𝒨 n) ⊤)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (((moduleTwistMap 𝒮 (shiftedGrading 𝒨 n) (i : ℤ)).val.app (op ⊤)).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n)) (twistingSheaf 𝒮 (i : ℤ)) (op ⊤)
          (s ⊗ₜ[_] degreeSection 𝒮 i a))).1 x =
      (a : S) • s.1 x := by
  have hvalue : (degreeSection 𝒮 i a).1 x =
      LocalizedModule.mk (a : S) (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply 𝒮 i a x
  refine (moduleTwistMap_tmul 𝒮 (shiftedGrading 𝒨 n) (i : ℤ) ⊤ s
    (degreeSection 𝒮 i a) x).trans ?_
  exact (congrArg (fun r => r • s.1 x) hvalue).trans (mk_one_smul (M := M) _ _ _)

/-- At every point of `Proj 𝒮`, the comparison `M(n)~ ⊗ 𝒪(i) ⟶ M(n)(i)~` evaluated on `s ⊗ t`,
where `t` is the global section of `𝒪(i)` given by a homogeneous element `a` of degree `i`, has
the same value in the module fibre as the homogeneous scalar action of `a` on `s`. -/
theorem moduleTwistMap_tmul_eq_homogeneousScalar (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (s : moduleSections 𝒮 (shiftedGrading 𝒨 n) ⊤)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (((moduleTwistMap 𝒮 (shiftedGrading 𝒨 n) (i : ℤ)).val.app (op ⊤)).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n)) (twistingSheaf 𝒮 (i : ℤ)) (op ⊤)
          (s ⊗ₜ[_] degreeSection 𝒮 i a))).1 x =
      ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 ((i : ℤ) + n)) ⊤).toFun
        (homogeneousScalarGlobalSections 𝒮 𝒨 i n a s)).1 x :=
  (moduleTwistMap_tmul_degreeSection 𝒮 𝒨 i n a s x).trans
    (homogeneousScalarGlobalSections_apply 𝒮 𝒨 i n a s x).symm

/-- The comparison `M(n)~ ⊗ 𝒪(i) ⟶ M(n)(i)~` takes the pure tensor of the global section of
`M(n)~` given by a homogeneous `m` of degree `n` with the global section of `𝒪(i)` given by a
homogeneous `a` of degree `i` to the global section of `M(i + n)~` given by any `am` of degree
`i + n` with underlying element `a • m`, pointwise on `Proj 𝒮`. -/
theorem moduleTwistMap_tmul_degreeNToGlobalSections (i : ℕ) (n : ℤ) (a : 𝒮 i) (m : 𝒨 n)
    (am : 𝒨 ((i : ℤ) + n)) (ham : (am : M) = (a : S) • (m : M))
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (((moduleTwistMap 𝒮 (shiftedGrading 𝒨 n) (i : ℤ)).val.app (op ⊤)).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n)) (twistingSheaf 𝒮 (i : ℤ)) (op ⊤)
          (degreeNToGlobalSections 𝒮 𝒨 n m ⊗ₜ[_] degreeSection 𝒮 i a))).1 x =
      ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 ((i : ℤ) + n)) ⊤).toFun
        (degreeNToGlobalSections 𝒮 𝒨 ((i : ℤ) + n) am)).1 x := by
  refine (moduleTwistMap_tmul_degreeSection 𝒮 𝒨 i n a
    (degreeNToGlobalSections 𝒮 𝒨 n m) x).trans ?_
  refine (congrArg (fun z => (a : S) • z) (degreeNToGlobalSections_apply 𝒮 𝒨 n m x.1)).trans
    ((degreeNToGlobalSections_apply 𝒮 𝒨 ((i : ℤ) + n) am x.1).trans ?_).symm
  rw [ham]
  exact (LocalizedModule.smul'_mk (a : S) (m : M) _).symm

end Stacks.AlgebraicGeometry.ModuleTwistIso

end
