module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import StacksFrontier.Deformation.SquareZero.Obstruction.RelationDifference

/-!
# Fitting maps from agreement on relations

Total maps out of the polynomial presentation into a square-zero extension, and the construction
of a fitting map of a compatible square-zero deformation diagram from two evaluations that agree
on the relation ideal, together with the converse.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- `Algebra.Generators.toExtension` is a semireducible `def`, so the two spellings of its
-- polynomial ring -- `P.toExtension.Ring` and `P.Ring` -- do not unify at the transparency
-- that `simp` and `rw` use. Making it implicit-reducible here lets both spellings match.
attribute [local implicit_reducible] Algebra.Generators.toExtension

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂

namespace Stacks.Deformation
attribute [local instance] HasDerivedCategory.standard

/-- The kernel inclusion in the first extension, linear over the polynomial presentation. -/
public noncomputable def presentationKernelMap₁
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    let P := MvPolynomial D.S₁.B D.S₁.A'
    letI : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
    letI : Algebra P D.X₁.B' := (presentationEval₁ D).toRingHom.toAlgebra
    D.S₁.N →ₗ[P] D.X₁.B' := by
  let P := MvPolynomial D.S₁.B D.S₁.A'
  let : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
  let : Algebra P D.X₁.B' := (presentationEval₁ D).toRingHom.toAlgebra
  let g : D.S₁.N → D.X₁.B' := fun n ↦ (D.X₁.kernelEquiv n).1
  refine
    { toFun := g
      map_add' := fun x y ↦ congrArg Subtype.val (map_add D.X₁.kernelEquiv x y)
      map_smul' := fun p n ↦ ?_ }
  change ((D.X₁.kernelEquiv ((presentationToB D p) • n) :
    RingHom.ker D.X₁.toB.toRingHom) : D.X₁.B') =
      (presentationEval₁ D) p *
        ((D.X₁.kernelEquiv n : RingHom.ker D.X₁.toB.toRingHom) : D.X₁.B')
  rw [map_smul]
  have hp := DFunLike.congr_fun (presentationEval₁_toB D) p
  change D.X₁.toB ((presentationEval₁ D) p) = presentationToB D p at hp
  rw [← hp]
  exact congrArg Subtype.val
    (D.X₁.toB_smul_kernel ((presentationEval₁ D) p) (D.X₁.kernelEquiv n))

/-- The polynomial ring together with the square-zero kernel presents the first extension. -/
public noncomputable def presentationTotal₁
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    let P := MvPolynomial D.S₁.B D.S₁.A'
    letI : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
    letI : Module Pᵐᵒᵖ D.S₁.N :=
      Module.compHom D.S₁.N
        (RingHom.fromOpposite (RingHom.id P) (fun _ _ ↦ Commute.all _ _))
    letI : IsCentralScalar P D.S₁.N := ⟨fun _ _ ↦ rfl⟩
    TrivSqZeroExt P D.S₁.N →+* D.X₁.B' := by
  let P := MvPolynomial D.S₁.B D.S₁.A'
  let : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
  let : Module Pᵐᵒᵖ D.S₁.N :=
    Module.compHom D.S₁.N
      (RingHom.fromOpposite (RingHom.id P) (fun _ _ ↦ Commute.all _ _))
  let : IsCentralScalar P D.S₁.N := ⟨fun _ _ ↦ rfl⟩
  let : Algebra P D.X₁.B' := (presentationEval₁ D).toRingHom.toAlgebra
  let g := presentationKernelMap₁ D
  have hg : ∀ x y : D.S₁.N, g x * g y = 0 := fun x y ↦
    squareZero_kernel_mul D.X₁.toB.toRingHom D.X₁.sq_zero
      (D.X₁.kernelEquiv x) (D.X₁.kernelEquiv y)
  exact (TrivSqZeroExt.liftEquivOfComm ⟨g, hg⟩).toRingHom

/-- `presentationTotal₁` sends `(p, n)` to the evaluation of `p` plus `n` viewed in the kernel
of the first extension. -/
public theorem presentationTotal₁_apply
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (p : MvPolynomial D.S₁.B D.S₁.A') (n : D.S₁.N) :
    presentationTotal₁ D (p, n) =
      (presentationEval₁ D) p +
        ((D.X₁.kernelEquiv n : RingHom.ker D.X₁.toB.toRingHom) : D.X₁.B') :=
  rfl

/-- The polynomial ring together with the square-zero kernel surjects onto the first
extension. -/
public theorem presentationTotal₁_surjective
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    Function.Surjective (presentationTotal₁ D) := by
  intro x
  let b := D.X₁.toB x
  let p : MvPolynomial D.S₁.B D.S₁.A' := MvPolynomial.X b
  have hp : D.X₁.toB ((presentationEval₁ D) p) = b := by
    simp [p, presentationEval₁, lift₁_spec]
  have hk : x - (presentationEval₁ D) p ∈ RingHom.ker D.X₁.toB.toRingHom := by
    change D.X₁.toB (x - (presentationEval₁ D) p) = 0
    simp [b, hp]
  let n := D.X₁.kernelEquiv.symm ⟨x - (presentationEval₁ D) p, hk⟩
  refine ⟨(p, n), ?_⟩
  rw [presentationTotal₁_apply]
  have hn : ((D.X₁.kernelEquiv n : RingHom.ker D.X₁.toB.toRingHom) :
      D.X₁.B') = x - (presentationEval₁ D) p :=
    congrArg Subtype.val (D.X₁.kernelEquiv.apply_symm_apply
      ⟨x - (presentationEval₁ D) p, hk⟩)
  rw [hn]
  abel

/-- Polynomial evaluation in the second extension at a specified family of lifts. -/
public noncomputable def presentationEval₂With
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B') :
    MvPolynomial D.S₁.B D.S₁.A' →+* D.X₂.B' := by
  let : Algebra D.S₁.A' D.X₂.B' :=
    ((algebraMap D.S₂.A' D.X₂.B').comp
      (algebraMap D.S₁.A' D.S₂.A')).toAlgebra
  exact (MvPolynomial.aeval z).toRingHom

/-- Evaluating at a family of lifts `z` and then reducing to `B₂` is the presentation map
`A'₁[B₁] → B₁` followed by `B₁ → B₂`. -/
public theorem presentationEval₂With_toB
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b) :
    D.X₂.toB.toRingHom.comp (presentationEval₂With D z) =
      (algebraMap D.S₁.B D.S₂.B).comp (presentationToB D) := by
  calc
    _ = D.X₂.toB.toRingHom.comp (presentationEval₂ D) := by
      apply MvPolynomial.ringHom_ext'
      · ext a
        simp [presentationEval₂With, presentationEval₂]
      · intro b
        simp [presentationEval₂With, presentationEval₂, hz b, lift₂_spec]
    _ = _ := presentationEval₂_toB D

/-- The prescribed map of kernels, linear over the second polynomial evaluation. -/
public noncomputable def presentationKernelMap₂
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b) :
    let P := MvPolynomial D.S₁.B D.S₁.A'
    letI : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
    letI : Algebra P D.X₂.B' := (presentationEval₂With D z).toAlgebra
    D.S₁.N →ₗ[P] D.X₂.B' := by
  let P := MvPolynomial D.S₁.B D.S₁.A'
  let : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
  let : Algebra P D.X₂.B' := (presentationEval₂With D z).toAlgebra
  let g : D.S₁.N → D.X₂.B' :=
    fun n ↦ (D.X₂.kernelEquiv (D.mapN n)).1
  refine { toFun := g
           map_add' x y := congrArg Subtype.val
             ((congrArg D.X₂.kernelEquiv (map_add D.mapN x y)).trans
               (map_add D.X₂.kernelEquiv _ _))
           map_smul' := fun p n ↦ ?_ }
  change ((D.X₂.kernelEquiv (D.mapN ((presentationToB D p) • n)) :
    RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') =
      (presentationEval₂With D z) p *
        ((D.X₂.kernelEquiv (D.mapN n) : RingHom.ker D.X₂.toB.toRingHom) :
          D.X₂.B')
  rw [map_smul, ← IsScalarTower.algebraMap_smul (A := D.S₂.B)
    (presentationToB D p) (D.mapN n), map_smul]
  have hp := DFunLike.congr_fun (presentationEval₂With_toB D z hz) p
  change D.X₂.toB ((presentationEval₂With D z) p) =
    algebraMap D.S₁.B D.S₂.B (presentationToB D p) at hp
  rw [← hp]
  exact congrArg Subtype.val
    (D.X₂.toB_smul_kernel ((presentationEval₂With D z) p)
      (D.X₂.kernelEquiv (D.mapN n)))

/-- The map from the trivial square-zero extension `A'₁[B₁] ⊕ N₁` to the second extension
given by evaluation at the lifts `z` and by `N₁ → N₂` on the kernel. -/
public noncomputable def presentationTotal₂With
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b) :
    let P := MvPolynomial D.S₁.B D.S₁.A'
    letI : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
    letI : Module Pᵐᵒᵖ D.S₁.N :=
      Module.compHom D.S₁.N
        (RingHom.fromOpposite (RingHom.id P) (fun _ _ ↦ Commute.all _ _))
    letI : IsCentralScalar P D.S₁.N := ⟨fun _ _ ↦ rfl⟩
    TrivSqZeroExt P D.S₁.N →+* D.X₂.B' := by
  let P := MvPolynomial D.S₁.B D.S₁.A'
  let : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
  let : Module Pᵐᵒᵖ D.S₁.N :=
    Module.compHom D.S₁.N
      (RingHom.fromOpposite (RingHom.id P) (fun _ _ ↦ Commute.all _ _))
  let : IsCentralScalar P D.S₁.N := ⟨fun _ _ ↦ rfl⟩
  let : Algebra P D.X₂.B' := (presentationEval₂With D z).toAlgebra
  let g := presentationKernelMap₂ D z hz
  exact (TrivSqZeroExt.liftEquivOfComm ⟨g, fun x y ↦ squareZero_kernel_mul D.X₂.toB.toRingHom
    D.X₂.sq_zero (D.X₂.kernelEquiv (D.mapN x)) (D.X₂.kernelEquiv (D.mapN y))⟩).toRingHom

/-- `presentationTotal₂With` sends `(p, n)` to the evaluation of `p` at `z` plus the image of
`n` in the kernel of the second extension. -/
public theorem presentationTotal₂With_apply
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (p : MvPolynomial D.S₁.B D.S₁.A') (n : D.S₁.N) :
    presentationTotal₂With D z hz (p, n) =
      (presentationEval₂With D z) p +
        ((D.X₂.kernelEquiv (D.mapN n) : RingHom.ker D.X₂.toB.toRingHom) :
          D.X₂.B') := by
  rfl

/-- Adding an element of the kernel of a ring homomorphism does not change its value. -/
private theorem map_add_ker {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a : R)
    (k : RingHom.ker f) : f (a + k) = f a := by
  rw [map_add, RingHom.mem_ker.mp k.2, add_zero]

/-- `presentationTotal₁ D (p, n)` reduces in `B₁` to the reduction of `p`. -/
public theorem presentationTotal₁_toB
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (p : MvPolynomial D.S₁.B D.S₁.A') (n : D.S₁.N) :
    D.X₁.toB (presentationTotal₁ D (p, n)) = presentationToB D p := by
  rw [presentationTotal₁_apply]
  exact (map_add_ker D.X₁.toB.toRingHom _ _).trans
    (DFunLike.congr_fun (presentationEval₁_toB D) p)

/-- `presentationTotal₂With D z hz (p, n)` reduces in `B₂` to the image of the reduction of
`p`. -/
public theorem presentationTotal₂With_toB
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (p : MvPolynomial D.S₁.B D.S₁.A') (n : D.S₁.N) :
    D.X₂.toB (presentationTotal₂With D z hz (p, n)) =
      algebraMap D.S₁.B D.S₂.B (presentationToB D p) := by
  rw [presentationTotal₂With_apply]
  exact (map_add_ker D.X₂.toB.toRingHom _ _).trans
    (DFunLike.congr_fun (presentationEval₂With_toB D z hz) p)

/-- If evaluation at the lifts `z` agrees on relations with the image of their first evaluation,
then the kernel of `presentationTotal₁` is contained in that of `presentationTotal₂With`. -/
public theorem presentationTotal_ker_le
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (hrel : ∀ x : RingHom.ker (presentationToB D),
      (presentationEval₂With D z) x.1 =
        ((D.X₂.kernelEquiv (D.mapN (relationEval₁ D x)) :
          RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B')) :
    let P := MvPolynomial D.S₁.B D.S₁.A'
    letI : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
    letI : Module Pᵐᵒᵖ D.S₁.N :=
      Module.compHom D.S₁.N
        (RingHom.fromOpposite (RingHom.id P) (fun _ _ ↦ Commute.all _ _))
    letI : IsCentralScalar P D.S₁.N := ⟨fun _ _ ↦ rfl⟩
    RingHom.ker (presentationTotal₁ D) ≤
      RingHom.ker (presentationTotal₂With D z hz) := by
  let P := MvPolynomial D.S₁.B D.S₁.A'
  let : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
  let : Module Pᵐᵒᵖ D.S₁.N :=
    Module.compHom D.S₁.N
      (RingHom.fromOpposite (RingHom.id P) (fun _ _ ↦ Commute.all _ _))
  let : IsCentralScalar P D.S₁.N := ⟨fun _ _ ↦ rfl⟩
  change RingHom.ker (presentationTotal₁ D) ≤
    RingHom.ker (presentationTotal₂With D z hz)
  intro u hu
  obtain ⟨p, n⟩ := u
  have hp : p ∈ RingHom.ker (presentationToB D) := by
    apply RingHom.mem_ker.mpr
    have h := congrArg D.X₁.toB (RingHom.mem_ker.mp hu)
    simpa only [presentationTotal₁_toB, map_zero] using h
  let x : RingHom.ker (presentationToB D) := ⟨p, hp⟩
  have hsrc : relationEval₁ D x + n = 0 := by
    apply D.X₁.kernelEquiv.injective
    apply Subtype.ext
    rw [map_add, map_zero]
    have h := RingHom.mem_ker.mp hu
    change presentationTotal₁ D (p, n) = 0 at h
    rwa [presentationTotal₁_apply, ← relationEval₁_spec D x] at h
  apply RingHom.mem_ker.mpr
  change presentationTotal₂With D z hz (p, n) = 0
  rw [presentationTotal₂With_apply, hrel x]
  have h : ((D.X₂.kernelEquiv
      (D.mapN (relationEval₁ D x) + D.mapN n) :
        RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') =
      ((D.X₂.kernelEquiv (D.mapN (relationEval₁ D x)) :
        RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') +
      ((D.X₂.kernelEquiv (D.mapN n) :
        RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') :=
    congrArg Subtype.val
      (map_add D.X₂.kernelEquiv (D.mapN (relationEval₁ D x)) (D.mapN n))
  rw [← h, ← map_add D.mapN, hsrc, map_zero, map_zero]
  rfl

/-- A map from a presentation ring descends to a fitting map when it kills the relations
and satisfies the three diagram identities on presentation representatives. -/
public noncomputable def fittingMap_of_presentation
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    {P : Type*} [CommRing P]
    (q : P →+* D.X₁.B') (hq : Function.Surjective q)
    (g : P →+* D.X₂.B') (hker : RingHom.ker q ≤ RingHom.ker g)
    (s : D.S₁.A' →+* P)
    (hs : q.comp s = algebraMap D.S₁.A' D.X₁.B')
    (hgs : g.comp s =
      (algebraMap D.S₂.A' D.X₂.B').comp (algebraMap D.S₁.A' D.S₂.A'))
    (hB : D.X₂.toB.toRingHom.comp g =
      ((algebraMap D.S₁.B D.S₂.B).comp D.X₁.toB.toRingHom).comp q)
    (hN : ∀ (n : D.S₁.N) (p : P),
      q p = ((D.X₁.kernelEquiv n : RingHom.ker D.X₁.toB.toRingHom) : D.X₁.B') →
      g p = ((D.X₂.kernelEquiv (D.mapN n) : RingHom.ker D.X₂.toB.toRingHom) :
        D.X₂.B')) : D.FittingMap where
  toRingHom := (q.liftOfSurjective hq) ⟨g, hker⟩
  toA'_comm := by
    refine RingHom.ext fun a ↦ ?_
    have hsa : q (s a) = algebraMap D.S₁.A' D.X₁.B' a :=
      DFunLike.congr_fun hs a
    simpa only [RingHom.coe_comp, Function.comp_apply, ← hsa,
      q.liftOfSurjective_comp_apply] using DFunLike.congr_fun hgs a
  toB_comm := by
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨p, rfl⟩ := hq x
    simpa only [RingHom.coe_comp, Function.comp_apply, q.liftOfSurjective_comp_apply]
      using DFunLike.congr_fun hB p
  kernel_comm := by
    intro n
    obtain ⟨p, hp⟩ := hq
      ((D.X₁.kernelEquiv n : RingHom.ker D.X₁.toB.toRingHom) : D.X₁.B')
    rw [← hp, q.liftOfSurjective_comp_apply]
    exact hN n p hp

/-- Equal evaluations on the relations descend from the polynomial presentation to a
fitting map of square-zero deformations. -/
public noncomputable def fittingMap_of_relation_agreement
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (hrel : ∀ x : RingHom.ker (presentationToB D),
      (presentationEval₂With D z) x.1 =
        ((D.X₂.kernelEquiv (D.mapN (relationEval₁ D x)) :
          RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B')) :
    D.FittingMap := by
  let P := MvPolynomial D.S₁.B D.S₁.A'
  let : Module P D.S₁.N := Module.compHom D.S₁.N (presentationToB D)
  let : Module Pᵐᵒᵖ D.S₁.N :=
    Module.compHom D.S₁.N
      (RingHom.fromOpposite (RingHom.id P) (fun _ _ ↦ Commute.all _ _))
  let : IsCentralScalar P D.S₁.N := ⟨fun _ _ ↦ rfl⟩
  let T := TrivSqZeroExt P D.S₁.N
  let q : T →+* D.X₁.B' := presentationTotal₁ D
  let g : T →+* D.X₂.B' := presentationTotal₂With D z hz
  have hker : RingHom.ker q ≤ RingHom.ker g :=
    presentationTotal_ker_le D z hz hrel
  let s : D.S₁.A' →+* T :=
    (TrivSqZeroExt.inlHom P D.S₁.N).comp MvPolynomial.C
  refine fittingMap_of_presentation D q (presentationTotal₁_surjective D) g hker s ?_ ?_ ?_ ?_
  · refine RingHom.ext fun a ↦ ?_
    change presentationTotal₁ D (MvPolynomial.C a, 0) =
      algebraMap D.S₁.A' D.X₁.B' a
    rw [presentationTotal₁_apply, map_zero]
    simp [presentationEval₁]
  · refine RingHom.ext fun a ↦ ?_
    change presentationTotal₂With D z hz (MvPolynomial.C a, 0) =
      algebraMap D.S₂.A' D.X₂.B' (algebraMap D.S₁.A' D.S₂.A' a)
    rw [presentationTotal₂With_apply]
    have hzero : ((D.X₂.kernelEquiv (D.mapN (0 : D.S₁.N)) :
        RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') = 0 := by
      rw [map_zero D.mapN, map_zero D.X₂.kernelEquiv]
      rfl
    rw [hzero, add_zero]
    simp [presentationEval₂With]
    rfl
  · refine RingHom.ext fun u ↦ ?_
    obtain ⟨p, n⟩ := u
    simp only [RingHom.coe_comp]
    change D.X₂.toB (presentationTotal₂With D z hz (p, n)) =
      algebraMap D.S₁.B D.S₂.B (D.X₁.toB (presentationTotal₁ D (p, n)))
    rw [presentationTotal₂With_toB, presentationTotal₁_toB]
  · intro n u hu
    let v : T := (0, n)
    have hqv : q v =
        ((D.X₁.kernelEquiv n : RingHom.ker D.X₁.toB.toRingHom) : D.X₁.B') := by
      change presentationTotal₁ D (0, n) = _
      rw [presentationTotal₁_apply, map_zero, zero_add]
    have hgv : g v =
        ((D.X₂.kernelEquiv (D.mapN n) : RingHom.ker D.X₂.toB.toRingHom) :
          D.X₂.B') := by
      change presentationTotal₂With D z hz (0, n) = _
      rw [presentationTotal₂With_apply, map_zero, zero_add]
    have hd : u - v ∈ RingHom.ker q := by
      apply RingHom.mem_ker.mpr
      rw [map_sub, hu, hqv, sub_self]
    have hd' := RingHom.mem_ker.mp (hker hd)
    rw [map_sub, sub_eq_zero] at hd'
    rw [hd', hgv]

/-- A fitting map gives a family of lifts at which evaluation agrees on relations with the image
of their first evaluation. -/
public theorem relation_agreement_of_fittingMap
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (F : D.FittingMap) :
    ∃ z : D.S₁.B → D.X₂.B',
      (∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b) ∧
      (∀ x : RingHom.ker (presentationToB D),
        (presentationEval₂With D z) x.1 =
          ((D.X₂.kernelEquiv (D.mapN (relationEval₁ D x)) :
            RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B')) := by
  let z : D.S₁.B → D.X₂.B' := fun b ↦ F.toRingHom (lift₁ D b)
  have hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b := by
    intro b
    have h := DFunLike.congr_fun F.toB_comm (lift₁ D b)
    change D.X₂.toB (F.toRingHom (lift₁ D b)) =
      algebraMap D.S₁.B D.S₂.B (D.X₁.toB (lift₁ D b)) at h
    rwa [lift₁_spec] at h
  refine ⟨z, hz, ?_⟩
  have heval : presentationEval₂With D z =
      F.toRingHom.comp (presentationEval₁ D).toRingHom := by
    apply MvPolynomial.ringHom_ext'
    · ext a
      have h := DFunLike.congr_fun F.toA'_comm a
      simp only [presentationEval₂With, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply, MvPolynomial.algHom_C, presentationEval₁]
      change algebraMap D.S₂.A' D.X₂.B'
        (algebraMap D.S₁.A' D.S₂.A' a) =
        F.toRingHom (algebraMap D.S₁.A' D.X₁.B' a)
      exact h.symm
    · intro b
      simp [presentationEval₂With, presentationEval₁, z]
  intro x
  have h := DFunLike.congr_fun heval x.1
  change (presentationEval₂With D z) x.1 =
    F.toRingHom ((presentationEval₁ D) x.1) at h
  rw [h, ← relationEval₁_spec D x]
  exact F.kernel_comm (relationEval₁ D x)

end Stacks.Deformation
end
