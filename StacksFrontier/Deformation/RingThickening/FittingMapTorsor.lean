module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.Deformation.SquareZero.Diagram
public import StacksFrontier.Deformation.SquareZero.Problem
import StacksCore.Tactic.StacksAttribute

/-!
# Maps between square-zero deformations form a torsor

For a compatible diagram of square-zero deformation problems, the maps `B'₁ → B'₂` which fill
the diagram, when any exist, form a principal homogeneous space under the module of maps
`Hom_{B₁}(Ω_{B₁/A₁}, N₂)` from the relative Kähler differentials of the first algebra to the
module of the second problem.

The action and its inverse are both explicit. Two fitting maps differ by a map `B'₁ → N₂` that
kills the kernel of `B'₁ → B₁` and obeys the Leibniz rule, hence descends to a derivation of
`B₁` over `A₁` with values in `N₂` and so to a `B₁`-linear map out of `Ω_{B₁/A₁}`. Conversely a
`B₁`-linear map `α` out of `Ω_{B₁/A₁}` sends a fitting map `φ` to `x ↦ φ(x) + α(d (x mod N₁))`,
which is again a ring map because the kernel of `B'₂ → B₂` has square zero.

## Main results

* `Deformation.RingThickening.fittingMap_addTorsor_kaehlerDifferentialHom`: the torsor of maps
  filling a compatible square-zero deformation diagram.

## Implementation notes

A principal homogeneous space is Mathlib's `AddTorsor`. The `B₁`-module structure on `N₂` is
the restriction of scalars included in the compatible diagram; the `A₁`-module structure used
for the derivation is obtained from it along `A₁ → B₁`.

The statement bundles the torsor structure with its characteristic property rather than
asserting the mere existence of some torsor structure: the subtype records that subtracting two
fitting maps gives the unique differential map whose value on `d b` is the difference of their
values on any lift of `b`.

## References

* [Stacks Project, Tag 08S5](https://stacks.math.columbia.edu/tag/08S5)
-/

@[expose] public section

open Stacks.Deformation

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂

namespace Deformation.RingThickening

local instance (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
    v₁, v₂, v₃, v₄, w₁, w₂}) : Module D.S₁.A D.S₂.N :=
  Module.compHom _ (algebraMap D.S₁.A D.S₁.B)

local instance (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
    v₁, v₂, v₃, v₄, w₁, w₂}) : IsScalarTower D.S₁.A D.S₁.B D.S₂.N :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private lemma kernel_mul_eq_zero
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x y : RingHom.ker D.X₂.toB.toRingHom) :
    (x : D.X₂.B') * (y : D.X₂.B') = 0 := by
  have h : (x : D.X₂.B') * (y : D.X₂.B') ∈
      RingHom.ker D.X₂.toB.toRingHom ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul x.property y.property
  rw [D.X₂.sq_zero] at h
  simpa using h

/-- A fitting map commutes with the maps to `B`. -/
private lemma toB_fittingMap_apply
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ : D.FittingMap) (x : D.X₁.B') :
    D.X₂.toB (φ.toRingHom x) = algebraMap D.S₁.B D.S₂.B (D.X₁.toB x) :=
  congrArg (fun f : D.X₁.B' →+* D.S₂.B => f x) φ.toB_comm

/-- A fitting map commutes with the maps from `A'`. -/
private lemma fittingMap_algebraMap_apply
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ : D.FittingMap) (a : D.S₁.A') :
    φ.toRingHom (algebraMap D.S₁.A' D.X₁.B' a) =
      algebraMap D.S₂.A' D.X₂.B' (algebraMap D.S₁.A' D.S₂.A' a) :=
  congrArg (fun f : D.S₁.A' →+* D.X₂.B' => f a) φ.toA'_comm

/-- The image of an element of `A'` in `B` factors through `A`. -/
private lemma toB_algebraMap_apply
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (a : D.S₁.A') :
    D.X₁.toB (algebraMap D.S₁.A' D.X₁.B' a) =
      algebraMap D.S₁.A D.S₁.B (algebraMap D.S₁.A' D.S₁.A a) := by
  rw [D.X₁.toB.commutes, ← IsScalarTower.algebraMap_apply]

private def fittingMapDifference
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap) : D.X₁.B' →+ D.S₂.N :=
  D.X₂.kernelEquiv.symm.toAddMonoidHom.comp
    { toFun := fun x => ⟨φ.toRingHom x - ψ.toRingHom x, by
        rw [RingHom.mem_ker, map_sub]
        change D.X₂.toB (φ.toRingHom x) - D.X₂.toB (ψ.toRingHom x) = 0
        rw [toB_fittingMap_apply, toB_fittingMap_apply, sub_self]⟩
      map_zero' := by ext; simp
      map_add' := by
        intro x y
        ext
        simp only [map_add, Submodule.coe_add]
        abel }

private lemma fittingMapDifference_ker
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap)
    (x : RingHom.ker D.X₁.toB.toRingHom) :
    fittingMapDifference D φ ψ (x : D.X₁.B') = 0 := by
  obtain ⟨n, rfl⟩ := D.X₁.kernelEquiv.surjective x
  exact D.X₂.kernelEquiv.symm.map_eq_zero_iff.mpr
    (Subtype.ext (sub_eq_zero.mpr ((φ.kernel_comm n).trans (ψ.kernel_comm n).symm)))

private lemma fittingMapDifference_eq_of_toB_eq
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap)
    (x y : D.X₁.B') (h : D.X₁.toB x = D.X₁.toB y) :
    fittingMapDifference D φ ψ x = fittingMapDifference D φ ψ y := by
  have hker : x - y ∈ RingHom.ker D.X₁.toB.toRingHom := by
    rw [RingHom.mem_ker, map_sub]
    exact sub_eq_zero.mpr h
  have hz := fittingMapDifference_ker D φ ψ ⟨x - y, hker⟩
  simpa only [AddMonoidHom.map_sub, sub_eq_zero] using hz

private noncomputable def fittingMapDifferenceDesc
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap) :
    D.S₁.B → D.S₂.N :=
  fun b => fittingMapDifference D φ ψ (Classical.choose (D.X₁.surjective b))

private lemma fittingMapDifferenceDesc_apply
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap) (x : D.X₁.B') :
    fittingMapDifferenceDesc D φ ψ (D.X₁.toB x) =
      fittingMapDifference D φ ψ x :=
  fittingMapDifference_eq_of_toB_eq D φ ψ _ _
    (Classical.choose_spec (D.X₁.surjective (D.X₁.toB x)))

private def kernelInclusion
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) : D.S₂.N →+ D.X₂.B' where
  toFun n := (D.X₂.kernelEquiv n : D.X₂.B')
  map_zero' := congrArg Subtype.val (map_zero D.X₂.kernelEquiv)
  map_add' n m := congrArg Subtype.val (map_add D.X₂.kernelEquiv n m)

private lemma kernelInclusion_smul
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (z : D.X₂.B') (n : D.S₂.N) :
    kernelInclusion D (D.X₂.toB z • n) = z * kernelInclusion D n := by
  show ((D.X₂.kernelEquiv (D.X₂.toB z • n) :
    RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') =
    z * (D.X₂.kernelEquiv n : D.X₂.B')
  rw [map_smul, D.X₂.toB_smul_kernel]
  rfl

private lemma kernelInclusion_mul_eq_zero
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (n m : D.S₂.N) :
    kernelInclusion D n * kernelInclusion D m = 0 :=
  kernel_mul_eq_zero D (D.X₂.kernelEquiv n) (D.X₂.kernelEquiv m)

private lemma kernelInclusion_toB
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (n : D.S₂.N) :
    D.X₂.toB (kernelInclusion D n) = 0 :=
  (D.X₂.kernelEquiv n).property

private lemma kernelInclusion_fittingMapDifference
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap) (x : D.X₁.B') :
    kernelInclusion D (fittingMapDifference D φ ψ x) =
      φ.toRingHom x - ψ.toRingHom x := by
  show ((D.X₂.kernelEquiv (D.X₂.kernelEquiv.symm _)) : D.X₂.B') = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private lemma kernelInclusion_injective
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) : Function.Injective (kernelInclusion D) :=
  (Subtype.coe_injective).comp D.X₂.kernelEquiv.injective

private lemma kernelInclusion_smul_fitting
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ : D.FittingMap)
    (x : D.X₁.B') (n : D.S₂.N) :
    kernelInclusion D (D.X₁.toB x • n) =
      φ.toRingHom x * kernelInclusion D n := by
  rw [← IsScalarTower.algebraMap_smul D.S₂.B (D.X₁.toB x) n, ← toB_fittingMap_apply D φ x,
    kernelInclusion_smul]

private lemma fittingMapDifference_leibniz
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap)
    (x y : D.X₁.B') :
    fittingMapDifference D φ ψ (x * y) =
      D.X₁.toB x • fittingMapDifference D φ ψ y +
        D.X₁.toB y • fittingMapDifference D φ ψ x := by
  apply kernelInclusion_injective D
  calc
    kernelInclusion D (fittingMapDifference D φ ψ (x * y)) =
        φ.toRingHom (x * y) - ψ.toRingHom (x * y) :=
      kernelInclusion_fittingMapDifference D φ ψ (x * y)
    _ = φ.toRingHom x * (φ.toRingHom y - ψ.toRingHom y) +
          ψ.toRingHom y * (φ.toRingHom x - ψ.toRingHom x) := by
      simp only [map_mul]
      ring
    _ = kernelInclusion D
          (D.X₁.toB x • fittingMapDifference D φ ψ y +
            D.X₁.toB y • fittingMapDifference D φ ψ x) := by
      rw [map_add, kernelInclusion_smul_fitting D φ x,
        kernelInclusion_smul_fitting D ψ y,
        kernelInclusion_fittingMapDifference D φ ψ x,
        kernelInclusion_fittingMapDifference D φ ψ y]

private lemma fittingMapDifference_algebraMap
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap)
    (a : D.S₁.A') :
    fittingMapDifference D φ ψ (algebraMap D.S₁.A' D.X₁.B' a) = 0 := by
  apply kernelInclusion_injective D
  rw [kernelInclusion_fittingMapDifference]
  rw [fittingMap_algebraMap_apply, fittingMap_algebraMap_apply, sub_self, map_zero]

private lemma fittingMapDifferenceDesc_leibniz
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap)
    (b c : D.S₁.B) :
    fittingMapDifferenceDesc D φ ψ (b * c) =
      b • fittingMapDifferenceDesc D φ ψ c +
        c • fittingMapDifferenceDesc D φ ψ b := by
  obtain ⟨x, rfl⟩ := D.X₁.surjective b
  obtain ⟨y, rfl⟩ := D.X₁.surjective c
  have h := fittingMapDifference_leibniz D φ ψ x y
  simpa only [← map_mul, fittingMapDifferenceDesc_apply] using h

private lemma fittingMapDifferenceDesc_algebraMap
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap)
    (a : D.S₁.A) :
    fittingMapDifferenceDesc D φ ψ (algebraMap D.S₁.A D.S₁.B a) = 0 := by
  obtain ⟨a', rfl⟩ := D.S₁.surjective a
  rw [← toB_algebraMap_apply, fittingMapDifferenceDesc_apply, fittingMapDifference_algebraMap]

private noncomputable def fittingMapDifferenceDerivation
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap) :
    Derivation D.S₁.A D.S₁.B D.S₂.N :=
  Derivation.mk'
    { toFun := fittingMapDifferenceDesc D φ ψ
      map_add' := by
        intro b c
        obtain ⟨x, rfl⟩ := D.X₁.surjective b
        obtain ⟨y, rfl⟩ := D.X₁.surjective c
        simpa only [map_add, fittingMapDifferenceDesc_apply] using
          fittingMapDifferenceDesc_apply D φ ψ (x + y)
      map_smul' := by
        intro a b
        change fittingMapDifferenceDesc D φ ψ (a • b) =
          a • fittingMapDifferenceDesc D φ ψ b
        rw [Algebra.smul_def,
          fittingMapDifferenceDesc_leibniz,
          fittingMapDifferenceDesc_algebraMap,
          smul_zero, add_zero, IsScalarTower.algebraMap_smul] }
    (fittingMapDifferenceDesc_leibniz D φ ψ)

private noncomputable def fittingMapVsub
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap) :
    KaehlerDifferential D.S₁.A D.S₁.B →ₗ[D.S₁.B] D.S₂.N :=
  (KaehlerDifferential.linearMapEquivDerivation D.S₁.A D.S₁.B).symm
    (fittingMapDifferenceDerivation D φ ψ)

private def fittingRingHomAddDerivation
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (d : Derivation D.S₁.A D.S₁.B D.S₂.N) (φ : D.FittingMap) :
    D.X₁.B' →+* D.X₂.B' where
  toFun x := φ.toRingHom x + kernelInclusion D (d (D.X₁.toB x))
  map_zero' := by simp
  map_one' := by simp [d.map_one_eq_zero]
  map_add' x y := by
    simp only [map_add]
    abel
  map_mul' x y := by
    change φ.toRingHom (x * y) + kernelInclusion D (d (D.X₁.toB (x * y))) =
      (φ.toRingHom x + kernelInclusion D (d (D.X₁.toB x))) *
        (φ.toRingHom y + kernelInclusion D (d (D.X₁.toB y)))
    rw [map_mul, map_mul, d.leibniz, map_add,
      kernelInclusion_smul_fitting D φ x,
      kernelInclusion_smul_fitting D φ y]
    simp only [mul_add, add_mul, kernelInclusion_mul_eq_zero, add_zero]
    ring

private def fittingMapAddDerivation
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (d : Derivation D.S₁.A D.S₁.B D.S₂.N) (φ : D.FittingMap) : D.FittingMap where
  toRingHom := fittingRingHomAddDerivation D d φ
  toA'_comm := by
    ext a
    change φ.toRingHom (algebraMap D.S₁.A' D.X₁.B' a) +
      kernelInclusion D (d (D.X₁.toB (algebraMap D.S₁.A' D.X₁.B' a))) =
      algebraMap D.S₂.A' D.X₂.B' (algebraMap D.S₁.A' D.S₂.A' a)
    have hz : d (D.X₁.toB (algebraMap D.S₁.A' D.X₁.B' a)) = 0 := by
      rw [toB_algebraMap_apply]
      exact d.map_algebraMap (algebraMap D.S₁.A' D.S₁.A a)
    rw [hz, map_zero, add_zero]
    exact fittingMap_algebraMap_apply D φ a
  toB_comm := by
    ext x
    change D.X₂.toB (φ.toRingHom x + kernelInclusion D (d (D.X₁.toB x))) =
      algebraMap D.S₁.B D.S₂.B (D.X₁.toB x)
    rw [map_add, kernelInclusion_toB, add_zero]
    exact toB_fittingMap_apply D φ x
  kernel_comm := by
    intro n
    change φ.toRingHom (D.X₁.kernelEquiv n : D.X₁.B') +
      kernelInclusion D (d (D.X₁.toB (D.X₁.kernelEquiv n : D.X₁.B'))) =
      (D.X₂.kernelEquiv (D.mapN n) : D.X₂.B')
    have hz : D.X₁.toB (D.X₁.kernelEquiv n : D.X₁.B') = 0 :=
      (D.X₁.kernelEquiv n).property
    rw [hz, map_zero, map_zero, add_zero]
    exact φ.kernel_comm n

private noncomputable def fittingMapVadd
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (α : KaehlerDifferential D.S₁.A D.S₁.B →ₗ[D.S₁.B] D.S₂.N)
    (φ : D.FittingMap) : D.FittingMap :=
  fittingMapAddDerivation D
    (KaehlerDifferential.linearMapEquivDerivation D.S₁.A D.S₁.B α) φ

private lemma fittingMapVadd_apply
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (α : KaehlerDifferential D.S₁.A D.S₁.B →ₗ[D.S₁.B] D.S₂.N)
    (φ : D.FittingMap) (x : D.X₁.B') :
    (fittingMapVadd D α φ).toRingHom x =
      φ.toRingHom x + kernelInclusion D
        ((KaehlerDifferential.linearMapEquivDerivation D.S₁.A D.S₁.B α)
          (D.X₁.toB x)) := rfl

private lemma fittingMapVsub_derivation_apply
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap) (x : D.X₁.B') :
    (KaehlerDifferential.linearMapEquivDerivation D.S₁.A D.S₁.B
      (fittingMapVsub D φ ψ)) (D.X₁.toB x) =
        fittingMapDifference D φ ψ x := by
  rw [fittingMapVsub, LinearEquiv.apply_symm_apply]
  show fittingMapDifferenceDesc D φ ψ (D.X₁.toB x) = _
  exact fittingMapDifferenceDesc_apply D φ ψ x

private lemma fittingMap_ext
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap)
    (h : φ.toRingHom = ψ.toRingHom) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl

private lemma fittingMapVsub_vadd
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ ψ : D.FittingMap) :
    fittingMapVadd D (fittingMapVsub D φ ψ) ψ = φ := by
  apply fittingMap_ext D
  ext x
  rw [fittingMapVadd_apply, fittingMapVsub_derivation_apply,
    kernelInclusion_fittingMapDifference]
  abel

private lemma fittingMapVadd_vsub
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (α : KaehlerDifferential D.S₁.A D.S₁.B →ₗ[D.S₁.B] D.S₂.N)
    (φ : D.FittingMap) :
    fittingMapVsub D (fittingMapVadd D α φ) φ = α := by
  apply (KaehlerDifferential.linearMapEquivDerivation D.S₁.A D.S₁.B).injective
  ext b
  obtain ⟨x, rfl⟩ := D.X₁.surjective b
  rw [fittingMapVsub_derivation_apply]
  apply kernelInclusion_injective D
  rw [kernelInclusion_fittingMapDifference, fittingMapVadd_apply]
  abel

private lemma fittingMap_zero_vadd
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (φ : D.FittingMap) :
    fittingMapVadd D 0 φ = φ := by
  apply fittingMap_ext D
  ext x
  simp [fittingMapVadd_apply]

private lemma fittingMap_add_vadd
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (α β : KaehlerDifferential D.S₁.A D.S₁.B →ₗ[D.S₁.B] D.S₂.N)
    (φ : D.FittingMap) :
    fittingMapVadd D (α + β) φ =
      fittingMapVadd D α (fittingMapVadd D β φ) := by
  apply fittingMap_ext D
  ext x
  rw [fittingMapVadd_apply, fittingMapVadd_apply, fittingMapVadd_apply]
  simp only [map_add, Derivation.coe_add, Pi.add_apply]
  abel

@[instance_reducible]
private noncomputable def fittingMapAddTorsor
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (h : Nonempty D.FittingMap) :
    AddTorsor
      (KaehlerDifferential D.S₁.A D.S₁.B →ₗ[D.S₁.B] D.S₂.N)
      D.FittingMap :=
  { vadd := fittingMapVadd D
    add_vadd := fittingMap_add_vadd D
    zero_vadd := fittingMap_zero_vadd D
    vsub := fittingMapVsub D
    nonempty := h
    vsub_vadd' := fittingMapVsub_vadd D
    vadd_vsub' := fittingMapVadd_vsub D }

/-- If a map filling a compatible square-zero deformation diagram exists, all such maps
form a principal homogeneous space under `Hom_{B₁}(Ω_{B₁/A₁}, N₂)`. Subtracting
two fitting maps gives the unique differential map whose value on `d b` is the
difference of their values on any lift of `b`. -/
@[stacks 08S5 "torsor",
  ega "IV 16.5.17" "special case",
  sga "1 III 5.3" "special case",
  sga "3 III 0.1.8" "(a), special case"]
theorem fittingMap_addTorsor_kaehlerDifferentialHom
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (h : Nonempty D.FittingMap) :
    Nonempty
      {t : AddTorsor
          (KaehlerDifferential D.S₁.A D.S₁.B →ₗ[D.S₁.B] D.S₂.N)
          D.FittingMap //
        letI : AddTorsor
            (KaehlerDifferential D.S₁.A D.S₁.B →ₗ[D.S₁.B] D.S₂.N)
            D.FittingMap := t
        ∀ (φ ψ : D.FittingMap) (b' : D.X₁.B'),
          ((D.X₂.kernelEquiv
            ((φ -ᵥ ψ) (KaehlerDifferential.D D.S₁.A D.S₁.B (D.X₁.toB b'))) :
              RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') =
            φ.toRingHom b' - ψ.toRingHom b'} := by
  refine ⟨⟨fittingMapAddTorsor D h, ?_⟩⟩
  intro φ ψ b'
  show kernelInclusion D
      ((KaehlerDifferential.linearMapEquivDerivation D.S₁.A D.S₁.B
        (fittingMapVsub D φ ψ))
        (D.X₁.toB b')) = φ.toRingHom b' - ψ.toRingHom b'
  rw [fittingMapVsub_derivation_apply]
  exact kernelInclusion_fittingMapDifference D φ ψ b'

end Deformation.RingThickening

end
