module

public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap
public import StacksFrontier.RingTheory.BaseChangeAlongSurjection
public import StacksFrontier.RingTheory.MilnorPatching.ModuleCategory

/-!
# Base change of a free differential lift

Let `fR : R' → R` and `fS : S' → S` be surjections of commutative rings fitting into a
commuting square with `a : R' → S'` and `b : R → S`, and let `L` be a free differential lift of
a complex `P` of `R`-modules along `fR`. Base change along `a` carries `L` to a free
differential lift of `S ⊗[R] P` along `fS`: the lifted terms are `S' ⊗[R'] Lⁿ`, the lifted
differentials are `S' ⊗[R'] d`, and the reduction sends `s' ⊗ x` to `fS s' ⊗ L.reduction x`.

The substance is the kernel condition. The reduction of `L` presents `Pⁿ` as `R ⊗[R'] Lⁿ`, so
`S ⊗[R] Pⁿ` is `S ⊗[S'] (S' ⊗[R'] Lⁿ)`, and the base-changed reduction is the canonical map
`W → S ⊗[S'] W` for `W = S' ⊗[R'] Lⁿ`, whose kernel is `ker fS • W`.

## Main definitions

* `Deformation.Obstruction.FreeDifferentialLift.baseChange`: the base-changed free differential
  lift, a lift of `S ⊗[R] P` along `fS` with terms `S' ⊗[R'] Lⁿ`.

## Main results

* `Deformation.Obstruction.freeLiftBaseChangeReduction_tmul`: the base-changed reduction on a
  pure tensor is `s' ⊗ x ↦ fS s' ⊗ L.reduction x`.

## Implementation notes

No square-zero hypothesis is used, and the square is not assumed cartesian: surjectivity of the
two vertical maps and commutativity of the square already force the kernel condition, because
the comparison `S ⊗[S'] (S' ⊗[R'] Lⁿ) ≅ S ⊗[R] Pⁿ` is built from the two scalar towers alone.
In particular the identification `ker fS = (ker fR) · S'` is nowhere needed.

The four ring maps are taken as bare `RingHom`s and the algebra structures are introduced with
`letI` inside the declarations, matching `FreeDifferentialLift`, whose reduction is a
`fR`-semilinear map rather than a map of algebras. This also keeps the statement of the base
change free of instance arguments: the target complex is `CochainComplex.extendScalars b`
applied to `P`, which mentions only the ring map.
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

namespace Deformation.Obstruction

variable {R' R S' S : Type u} [CommRing R'] [CommRing R] [CommRing S'] [CommRing S]

/-- The reduction of a free differential lift, read as a linear map over `R'` for the
`R'`-module structure that the ring map induces on the target. -/
noncomputable def freeLiftReductionLinear (fR : R' →+* R)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift fR P) (n : ℤ) :
    letI : Module R' (P.X n) := Module.compHom _ fR
    L.X n →ₗ[R'] P.X n :=
  letI : Module R' (P.X n) := Module.compHom _ fR
  { toFun := L.reduction n
    map_add' := (L.reduction n).map_add
    map_smul' := fun r x => (L.reduction n).map_smulₛₗ r x }

/-- A free differential lift presents each term of the complex as the base change of the
lifted term: `Pⁿ = R ⊗[R'] Lⁿ`. This is the reduction being surjective with kernel
`(ker fR) · Lⁿ`. -/
noncomputable def freeLiftTermBaseChangeEquiv (fR : R' →+* R)
    (hfR : Function.Surjective fR)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift fR P) (n : ℤ) :
    letI : Algebra R' R := fR.toAlgebra
    (R ⊗[R'] L.X n) ≃ₗ[R] P.X n := by
  letI : Algebra R' R := fR.toAlgebra
  letI : Module R' (P.X n) := Module.compHom _ fR
  haveI : IsScalarTower R' R (P.X n) :=
    ⟨fun x y z => by change (fR x * y) • z = fR x • y • z; rw [mul_smul]⟩
  exact (IsBaseChange.of_surjective_of_ker_eq_ker_smul_top (A := R') (S := R) hfR
    (f := freeLiftReductionLinear fR L n) (L.reduction_surjective n) (L.reduction_ker n)).equiv

/-- The presentation `R ⊗[R'] Lⁿ ≃ Pⁿ` sends `1 ⊗ x` to `L.reduction n x`. -/
lemma freeLiftTermBaseChangeEquiv_one_tmul (fR : R' →+* R)
    (hfR : Function.Surjective fR)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift fR P) (n : ℤ)
    (x : L.X n) :
    letI : Algebra R' R := fR.toAlgebra
    freeLiftTermBaseChangeEquiv fR hfR L n ((1 : R) ⊗ₜ[R'] x) = L.reduction n x := by
  let : Algebra R' R := fR.toAlgebra
  let : Module R' (P.X n) := Module.compHom _ fR
  have : IsScalarTower R' R (P.X n) :=
    ⟨fun x y z => by change (fR x * y) • z = fR x • y • z; rw [mul_smul]⟩
  exact (IsBaseChange.equiv_tmul _ 1 x).trans (one_smul _ _)

/-- The comparison `S ⊗[S'] (S' ⊗[R'] Lⁿ) ≅ S ⊗[R] Pⁿ`, obtained by cancelling the two base
changes against the presentation of `Pⁿ` as `R ⊗[R'] Lⁿ`. -/
noncomputable def freeLiftBaseChangeComparison {fR : R' →+* R}
    (hfR : Function.Surjective fR) (fS : S' →+* S) (a : R' →+* S') (b : R →+* S)
    (hcomm : b.comp fR = fS.comp a)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift fR P) (n : ℤ) :
    letI : Algebra R' S' := a.toAlgebra
    letI : Algebra R S := b.toAlgebra
    letI : Algebra S' S := fS.toAlgebra
    (S ⊗[S'] (S' ⊗[R'] L.X n)) ≃ₗ[S] (S ⊗[R] P.X n) := by
  letI : Algebra R' S' := a.toAlgebra
  letI : Algebra R S := b.toAlgebra
  letI : Algebra S' S := fS.toAlgebra
  letI : Algebra R' R := fR.toAlgebra
  letI : Algebra R' S := (b.comp fR).toAlgebra
  haveI : IsScalarTower R' R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R' S' S :=
    IsScalarTower.of_algebraMap_eq fun x => RingHom.congr_fun hcomm x
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R' S' S S (L.X n)) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R' R S S (L.X n)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (freeLiftTermBaseChangeEquiv fR hfR L n)

/-- The comparison `S ⊗[S'] (S' ⊗[R'] Lⁿ) ≃ S ⊗[R] Pⁿ` sends `1 ⊗ (s' ⊗ x)` to
`fS s' ⊗ L.reduction n x`. -/
lemma freeLiftBaseChangeComparison_tmul {fR : R' →+* R}
    (hfR : Function.Surjective fR) (fS : S' →+* S) (a : R' →+* S') (b : R →+* S)
    (hcomm : b.comp fR = fS.comp a)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift fR P) (n : ℤ)
    (s' : S') (x : L.X n) :
    letI : Algebra R' S' := a.toAlgebra
    letI : Algebra R S := b.toAlgebra
    letI : Algebra S' S := fS.toAlgebra
    freeLiftBaseChangeComparison hfR fS a b hcomm L n ((1 : S) ⊗ₜ[S'] (s' ⊗ₜ[R'] x)) =
      fS s' ⊗ₜ[R] L.reduction n x := by
  let : Algebra R' S' := a.toAlgebra
  let : Algebra R S := b.toAlgebra
  let : Algebra S' S := fS.toAlgebra
  let : Algebra R' R := fR.toAlgebra
  let : Algebra R' S := (b.comp fR).toAlgebra
  have : IsScalarTower R' R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R' S' S :=
    IsScalarTower.of_algebraMap_eq fun x => RingHom.congr_fun hcomm x
  have h1 : (TensorProduct.AlgebraTensorModule.cancelBaseChange R' S' S S (L.X n))
      ((1 : S) ⊗ₜ[S'] (s' ⊗ₜ[R'] x)) = fS s' ⊗ₜ[R'] x := by
    show (s' • (1 : S)) ⊗ₜ[R'] x = fS s' ⊗ₜ[R'] x
    congr 1
    show fS s' * (1 : S) = fS s'
    rw [mul_one]
  show TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (freeLiftTermBaseChangeEquiv fR hfR L n)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R' R S S (L.X n)).symm
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R' S' S S (L.X n))
          ((1 : S) ⊗ₜ[S'] (s' ⊗ₜ[R'] x)))) = _
  rw [h1]
  show TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (freeLiftTermBaseChangeEquiv fR hfR L n)
      ((fS s' : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[R'] x)) = _
  rw [TensorProduct.AlgebraTensorModule.congr_tmul, freeLiftTermBaseChangeEquiv_one_tmul]
  rfl

/-- The base-changed reduction `S' ⊗[R'] Lⁿ → S ⊗[R] Pⁿ`, semilinear over `fS`. It is the
canonical map into `S ⊗[S'] (S' ⊗[R'] Lⁿ)` read through the comparison. -/
noncomputable def freeLiftBaseChangeReduction {fR : R' →+* R} (hfR : Function.Surjective fR)
    (fS : S' →+* S) (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift fR P) (n : ℤ) :
    letI : Algebra R' S' := a.toAlgebra
    letI : Algebra R S := b.toAlgebra
    (S' ⊗[R'] L.X n) →ₛₗ[fS] (S ⊗[R] P.X n) := by
  letI : Algebra R' S' := a.toAlgebra
  letI : Algebra R S := b.toAlgebra
  letI : Algebra S' S := fS.toAlgebra
  have hone : ∀ s : S, s • (1 : S) = s := fun s => by rw [smul_eq_mul, mul_one]
  have key : ∀ (s : S) (w : S' ⊗[R'] L.X n),
      (s ⊗ₜ[S'] w : S ⊗[S'] (S' ⊗[R'] L.X n)) = s • ((1 : S) ⊗ₜ[S'] w) := by
    intro s w
    rw [TensorProduct.smul_tmul', hone]
  refine { toFun := fun w => freeLiftBaseChangeComparison hfR fS a b hcomm L n
             ((1 : S) ⊗ₜ[S'] w)
           map_add' := ?_, map_smul' := ?_ }
  · intro w w'
    rw [TensorProduct.tmul_add, map_add]
  · intro s' w
    have h : ((1 : S) ⊗ₜ[S'] (s' • w) : S ⊗[S'] (S' ⊗[R'] L.X n)) =
        fS s' • ((1 : S) ⊗ₜ[S'] w) := by
      rw [← key, ← TensorProduct.smul_tmul]
      congr 1
      change fS s' * (1 : S) = fS s'
      rw [mul_one]
    rw [h, map_smul]

/-- The base-changed reduction on a pure tensor. -/
lemma freeLiftBaseChangeReduction_tmul {fR : R' →+* R} (hfR : Function.Surjective fR)
    (fS : S' →+* S) (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift fR P) (n : ℤ)
    (s' : S') (x : L.X n) :
    letI : Algebra R' S' := a.toAlgebra
    letI : Algebra R S := b.toAlgebra
    freeLiftBaseChangeReduction hfR fS a b hcomm L n (s' ⊗ₜ[R'] x) =
      fS s' ⊗ₜ[R] L.reduction n x :=
  freeLiftBaseChangeComparison_tmul hfR fS a b hcomm L n s' x

/-- The base-changed reduction intertwines the base-changed differentials. -/
lemma freeLiftBaseChangeReduction_d {fR : R' →+* R} (hfR : Function.Surjective fR)
    (fS : S' →+* S) (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift fR P) (i j : ℤ) :
    letI : Algebra R' S' := a.toAlgebra
    letI : Algebra R S := b.toAlgebra
    ∀ x : S' ⊗[R'] L.X i,
      freeLiftBaseChangeReduction hfR fS a b hcomm L j
          ((LinearMap.baseChange S' (L.d i j).hom) x) =
        ((ModuleCat.extendScalars b).map (P.d i j))
          (freeLiftBaseChangeReduction hfR fS a b hcomm L i x) := by
  let : Algebra R' S' := a.toAlgebra
  let : Algebra R S := b.toAlgebra
  intro x
  induction x with
  | tmul s' y =>
      rw [LinearMap.baseChange_tmul, freeLiftBaseChangeReduction_tmul,
        freeLiftBaseChangeReduction_tmul, L.reduction_d]
      rfl
  | add y z hy hz =>
      rw [map_add, map_add, hy, hz,
        map_add (freeLiftBaseChangeReduction hfR fS a b hcomm L i) y z]
      exact (((ModuleCat.extendScalars b).map (P.d i j)).hom.map_add _ _).symm

/-- **Base change of a free differential lift.** For a commuting square of ring maps whose two
vertical maps `fR : R' → R` and `fS : S' → S` are surjective, a free differential lift `L` of
`P` along `fR` base-changes to a free differential lift of `S ⊗[R] P` along `fS`, with terms
`S' ⊗[R'] Lⁿ` and reduction `s' ⊗ x ↦ fS s' ⊗ L.reduction x`. -/
noncomputable def FreeDifferentialLift.baseChange {fR : R' →+* R}
    (hfR : Function.Surjective fR) {fS : S' →+* S} (hfS : Function.Surjective fS)
    (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift fR P) :
    FreeDifferentialLift fS ((CochainComplex.extendScalars b).obj P) := by
  letI : Algebra R' S' := a.toAlgebra
  letI : Algebra R S := b.toAlgebra
  letI : Algebra S' S := fS.toAlgebra
  refine
    { X := fun n => ModuleCat.of S' (S' ⊗[R'] L.X n)
      free := fun n => ?_
      d := fun i j => ModuleCat.ofHom (LinearMap.baseChange S' (L.d i j).hom)
      shape := fun i j h => ?_
      reduction := fun n => freeLiftBaseChangeReduction hfR fS a b hcomm L n
      reduction_surjective := fun n => ?_
      reduction_ker := fun n => ?_
      reduction_d := fun i j x =>
        freeLiftBaseChangeReduction_d hfR fS a b hcomm L i j x }
  · have := L.free n
    exact Module.Free.of_basis
      (Algebra.TensorProduct.basis S' (Module.Free.chooseBasis R' (L.X n)))
  · rw [L.shape i j h]
    ext w
    simp
  · intro v
    obtain ⟨w, hw⟩ :=
      (TensorProduct.isBaseChange S' (S' ⊗[R'] L.X n) S).surjective_of_surjective_algebraMap
        hfS ((freeLiftBaseChangeComparison hfR fS a b hcomm L n).symm v)
    refine ⟨w, ?_⟩
    change freeLiftBaseChangeComparison hfR fS a b hcomm L n ((1 : S) ⊗ₜ[S'] w) = v
    rw [show ((1 : S) ⊗ₜ[S'] w) =
      (freeLiftBaseChangeComparison hfR fS a b hcomm L n).symm v from hw]
    exact (freeLiftBaseChangeComparison hfR fS a b hcomm L n).apply_symm_apply v
  · rw [← MilnorPatching.ker_tensorProductMk_of_surjective (M := S' ⊗[R'] L.X n) fS hfS]
    refine Submodule.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · have h0 : freeLiftBaseChangeComparison hfR fS a b hcomm L n
          ((1 : S) ⊗ₜ[S'] w) = 0 := hw
      exact (LinearEquiv.map_eq_zero_iff _).mp h0
    · have h0 : ((1 : S) ⊗ₜ[S'] w : S ⊗[S'] (S' ⊗[R'] L.X n)) = 0 := hw
      change freeLiftBaseChangeComparison hfR fS a b hcomm L n ((1 : S) ⊗ₜ[S'] w) = 0
      rw [h0, map_zero]

end Deformation.Obstruction

end
