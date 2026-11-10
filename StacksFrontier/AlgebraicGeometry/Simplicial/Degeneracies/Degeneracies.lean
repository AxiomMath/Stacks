module

public import StacksFrontier.AlgebraicGeometry.Simplicial.Degeneracies.DegreeTwo
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Skeleton
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration.CechNerve
public import StacksFrontier.Cotangent.CellAttachment
public import StacksFrontier.Cotangent.FiniteTypeCoskeletal
public import StacksFrontier.Cotangent.PolynomialResolution
public import StacksFrontier.Cotangent.Resolution
public import StacksFrontier.Cotangent.StandardResolution
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Degeneracies in the explicit polynomial resolution

For a polynomial presentation of `B` over `A`, the two degeneracies from `P₁ = A[uᵢ,xₜ]` to the
displayed degree-two algebra `P₂ = A[uᵢ,yₜ,zₜ,vᵣ,wₜₜ']` fix the old variables and send `xₜ` to
`yₜ` and `zₜ`, respectively. They lift the two degeneracies of the degree-one coskeleton and fit
into a polynomial simplicial resolution.

## Main definitions

* `Algebra.PolynomialPresentationWithKernelGenerators.Degeneracies.degeneracyZero` and
  `degeneracyOne` are the prescribed polynomial maps.
* `Algebra.PolynomialPresentationWithKernelGenerators.Degeneracies.ExplicitResolution` records a
  resolution with the prescribed first three degrees.

## Main results

* `Algebra.PolynomialPresentationWithKernelGenerators.Degeneracies.degeneracyZero_lifts` and
  `degeneracyOne_lifts` identify the two lifts to the degree-one coskeleton.
* `Algebra.PolynomialPresentationWithKernelGenerators.Degeneracies.degeneracyZero_unique` and
  `degeneracyOne_unique` express the polynomial uniqueness of maps with the specified generator
  values.
* `Algebra.PolynomialPresentationWithKernelGenerators.Degeneracies.explicitResolution`
  constructs a resolution with these first three degrees.

## Implementation notes

The polynomial algebras and `B` are universe-lifted into the common algebra category of the
degree-one and degree-two constructions. The two algebra maps are defined by polynomial
evaluation, so their values on all generators and their uniqueness are part of their
definitions. The resolution records the three displayed faces in degree two as well as the two
displayed degeneracies.

The resolution is built stagewise by attaching free polynomial generators in one degree at a time;
every stage is a polynomial algebra on an arbitrary index type.

## References

* [Stacks Project, Tag 09D4](https://stacks.math.columbia.edu/tag/09D4)
-/

@[expose] public section

open Algebra MvPolynomial CategoryTheory Opposite
open CommAlgCat (CellVariable CellBoundary cellValue cellMap cellMap_C cellMap_X cellMap_value
  cellMap_id cellMap_comp attachCells attachCellsι attachCellsι_app isEmpty_cellVariable
  isIso_attachCellsι_app cellDescApp cellDescApp_C cellDescApp_X cellDescApp_value cellDesc
  attachCellsι_cellDesc exists_cellBoundary_of_bijective over_bijective_of_isIso)
open scoped Simplicial

universe u v w x

namespace Algebra.PolynomialPresentationWithKernelGenerators.Degeneracies

variable (p : PolynomialPresentationWithKernelGenerators.{u, v, w, x})

/-- The first degeneracy fixes `uᵢ` and sends `xₜ` to `yₜ`. -/
@[stacks 09D4 "degeneracies"]
noncomputable def degeneracyZero :
    DegreeOne.P1 p →ₐ[p.A] DegreeTwo.P2 p :=
  MvPolynomial.aeval (Sum.elim
    (fun i => MvPolynomial.X (DegreeTwo.DegreeTwoVariable.base i))
    (fun t => MvPolynomial.X (DegreeTwo.DegreeTwoVariable.y t)))

/-- The second degeneracy fixes `uᵢ` and sends `xₜ` to `zₜ`. -/
@[stacks 09D4 "degeneracies"]
noncomputable def degeneracyOne :
    DegreeOne.P1 p →ₐ[p.A] DegreeTwo.P2 p :=
  MvPolynomial.aeval (Sum.elim
    (fun i => MvPolynomial.X (DegreeTwo.DegreeTwoVariable.base i))
    (fun t => MvPolynomial.X (DegreeTwo.DegreeTwoVariable.z t)))

/-- The first degeneracy is the unique algebra map with the displayed
values on the old and relation variables. -/
@[stacks 09D4 "degeneracies"]
theorem degeneracyZero_unique
    (f : DegreeOne.P1 p →ₐ[p.A] DegreeTwo.P2 p)
    (hu : ∀ i : p.variableIndex,
      f (MvPolynomial.X (Sum.inl i)) =
        MvPolynomial.X (DegreeTwo.DegreeTwoVariable.base i))
    (hx : ∀ t : p.relationIndex,
      f (MvPolynomial.X (Sum.inr t)) =
        MvPolynomial.X (DegreeTwo.DegreeTwoVariable.y t)) :
    f = degeneracyZero p := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i => simpa [degeneracyZero] using hu i
  | inr t => simpa [degeneracyZero] using hx t

/-- The second degeneracy is the unique algebra map with the displayed
values on the old and relation variables. -/
@[stacks 09D4 "degeneracies"]
theorem degeneracyOne_unique
    (f : DegreeOne.P1 p →ₐ[p.A] DegreeTwo.P2 p)
    (hu : ∀ i : p.variableIndex,
      f (MvPolynomial.X (Sum.inl i)) =
        MvPolynomial.X (DegreeTwo.DegreeTwoVariable.base i))
    (hx : ∀ t : p.relationIndex,
      f (MvPolynomial.X (Sum.inr t)) =
        MvPolynomial.X (DegreeTwo.DegreeTwoVariable.z t)) :
    f = degeneracyOne p := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i => simpa [degeneracyOne] using hu i
  | inr t => simpa [degeneracyOne] using hx t

/-- The first degeneracy in the common category universe. -/
noncomputable def degeneracyZeroLift :
    ULift.{max u v w x, max u w x} (DegreeOne.P1 p) →ₐ[p.A]
      ULift.{max u v w x, max u w x} (DegreeTwo.P2 p) :=
  (ULift.algEquiv (R := p.A)).symm.toAlgHom.comp
    ((degeneracyZero p).comp (ULift.algEquiv (R := p.A)).toAlgHom)

/-- The second degeneracy in the common category universe. -/
noncomputable def degeneracyOneLift :
    ULift.{max u v w x, max u w x} (DegreeOne.P1 p) →ₐ[p.A]
      ULift.{max u v w x, max u w x} (DegreeTwo.P2 p) :=
  (ULift.algEquiv (R := p.A)).symm.toAlgHom.comp
    ((degeneracyOne p).comp (ULift.algEquiv (R := p.A)).toAlgHom)

/-- The first degree-two face in the common category universe. -/
noncomputable def faceZeroLift :
    ULift.{max u v w x, max u w x} (DegreeTwo.P2 p) →ₐ[p.A]
      ULift.{max u v w x, max u w x} (DegreeOne.P1 p) :=
  (ULift.algEquiv (R := p.A)).symm.toAlgHom.comp
    ((DegreeTwo.faceZero p).comp (ULift.algEquiv (R := p.A)).toAlgHom)

/-- The middle degree-two face in the common category universe. -/
noncomputable def faceOneLift :
    ULift.{max u v w x, max u w x} (DegreeTwo.P2 p) →ₐ[p.A]
      ULift.{max u v w x, max u w x} (DegreeOne.P1 p) :=
  (ULift.algEquiv (R := p.A)).symm.toAlgHom.comp
    ((DegreeTwo.faceOne p).comp (ULift.algEquiv (R := p.A)).toAlgHom)

/-- The last degree-two face in the common category universe. -/
noncomputable def faceTwoLift :
    ULift.{max u v w x, max u w x} (DegreeTwo.P2 p) →ₐ[p.A]
      ULift.{max u v w x, max u w x} (DegreeOne.P1 p) :=
  (ULift.algEquiv (R := p.A)).symm.toAlgHom.comp
    ((DegreeTwo.faceTwo p).comp (ULift.algEquiv (R := p.A)).toAlgHom)

private lemma faceZero_comp_degeneracyZero :
    (DegreeTwo.faceZero p).comp (degeneracyZero p) =
      AlgHom.id p.A (DegreeOne.P1 p) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [DegreeTwo.faceZero, degeneracyZero]

private lemma faceOne_comp_degeneracyZero :
    (DegreeTwo.faceOne p).comp (degeneracyZero p) =
      AlgHom.id p.A (DegreeOne.P1 p) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [DegreeTwo.faceOne, degeneracyZero]

private lemma faceTwo_comp_degeneracyZero :
    (DegreeTwo.faceTwo p).comp (degeneracyZero p) =
      (DegreeOne.degeneracyZero p).comp
        (DegreeOne.faceOne p) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [DegreeTwo.faceTwo, degeneracyZero,
    DegreeOne.degeneracyZero, DegreeOne.faceOne]

private lemma faceZero_comp_degeneracyOne :
    (DegreeTwo.faceZero p).comp (degeneracyOne p) =
      (DegreeOne.degeneracyZero p).comp
        (DegreeOne.faceZero p) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [DegreeTwo.faceZero, degeneracyOne,
    DegreeOne.degeneracyZero, DegreeOne.faceZero]

private lemma faceOne_comp_degeneracyOne :
    (DegreeTwo.faceOne p).comp (degeneracyOne p) =
      AlgHom.id p.A (DegreeOne.P1 p) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [DegreeTwo.faceOne, degeneracyOne]

private lemma faceTwo_comp_degeneracyOne :
    (DegreeTwo.faceTwo p).comp (degeneracyOne p) =
      AlgHom.id p.A (DegreeOne.P1 p) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [DegreeTwo.faceTwo, degeneracyOne]

private lemma faceZero_comp_faceZero :
    (DegreeOne.faceZero p).comp (DegreeTwo.faceZero p) =
      (DegreeOne.faceZero p).comp (DegreeTwo.faceOne p) := by
  apply MvPolynomial.algHom_ext
  intro i
  exact (DegreeTwo.faces_matching p (MvPolynomial.X i)).1

private lemma faceOne_comp_faceZero :
    (DegreeOne.faceOne p).comp (DegreeTwo.faceZero p) =
      (DegreeOne.faceZero p).comp (DegreeTwo.faceTwo p) := by
  apply MvPolynomial.algHom_ext
  intro i
  exact (DegreeTwo.faces_matching p (MvPolynomial.X i)).2.1

private lemma faceOne_comp_faceOne :
    (DegreeOne.faceOne p).comp (DegreeTwo.faceOne p) =
      (DegreeOne.faceOne p).comp (DegreeTwo.faceTwo p) := by
  apply MvPolynomial.algHom_ext
  intro i
  exact (DegreeTwo.faces_matching p (MvPolynomial.X i)).2.2

/-- The two composites from degree zero to degree two agree, the remaining
degree-zero simplicial identity for the displayed degeneracies. -/
private lemma degeneracyZero_comp_degreeOneDegeneracy :
    (degeneracyZero p).comp (DegreeOne.degeneracyZero p) =
      (degeneracyOne p).comp (DegreeOne.degeneracyZero p) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [degeneracyZero, degeneracyOne,
    DegreeOne.degeneracyZero]

/-- Lifting a polynomial map `P1 → P2` to the common universe. -/
private noncomputable abbrev liftP (g : DegreeOne.P1 p →ₐ[p.A] DegreeTwo.P2 p) :
    ULift.{max u v w x, max u w x} (DegreeOne.P1 p) →ₐ[p.A]
      ULift.{max u v w x, max u w x} (DegreeTwo.P2 p) :=
  (ULift.algEquiv (R := p.A)).symm.toAlgHom.comp (g.comp (ULift.algEquiv (R := p.A)).toAlgHom)

private lemma coskFace_sigma_delta_eq_id (D : DegreeOne.DegreeOneCoskeleton p) {i : Fin 2}
    {j : Fin 3} (h : D.simplicial.σ i ≫ D.simplicial.δ j = 𝟙 _) :
    D.oneIso.inv ≫ D.simplicial.σ i ≫ D.simplicial.δ j ≫ D.oneIso.hom = 𝟙 _ := by
  rw [reassoc_of% h, Iso.inv_hom_id]

private lemma coskFace_sigmaZero_zero (D : DegreeOne.DegreeOneCoskeleton p) :
    D.oneIso.inv ≫ D.simplicial.σ (0 : Fin 2) ≫ D.simplicial.δ (0 : Fin 3) ≫
        D.oneIso.hom = 𝟙 _ :=
  coskFace_sigma_delta_eq_id p D (D.simplicial.δ_comp_σ_self (i := (0 : Fin 2)))

private lemma coskFace_sigmaZero_one (D : DegreeOne.DegreeOneCoskeleton p) :
    D.oneIso.inv ≫ D.simplicial.σ (0 : Fin 2) ≫ D.simplicial.δ (1 : Fin 3) ≫
        D.oneIso.hom = 𝟙 _ :=
  coskFace_sigma_delta_eq_id p D (D.simplicial.δ_comp_σ_succ (i := (0 : Fin 2)))

private lemma coskFace_sigmaZero_two (D : DegreeOne.DegreeOneCoskeleton p) :
    D.oneIso.inv ≫ D.simplicial.σ (0 : Fin 2) ≫ D.simplicial.δ (2 : Fin 3) ≫
        D.oneIso.hom =
      AlgCat.ofHom (DegreeOne.faceOneLift p) ≫
        AlgCat.ofHom (DegreeOne.degeneracyZeroLift p) := by
  have h : D.simplicial.σ (0 : Fin 2) ≫ D.simplicial.δ (2 : Fin 3) =
      D.simplicial.δ (1 : Fin 2) ≫ D.simplicial.σ (0 : Fin 1) := by
    simpa using D.simplicial.δ_comp_σ_of_gt (i := (1 : Fin 2)) (j := (0 : Fin 1))
      (by decide)
  rw [reassoc_of% h, ← D.faceOne_eq, ← D.degeneracyZero_eq]
  simp

private lemma coskFace_sigmaOne_zero (D : DegreeOne.DegreeOneCoskeleton p) :
    D.oneIso.inv ≫ D.simplicial.σ (1 : Fin 2) ≫ D.simplicial.δ (0 : Fin 3) ≫
        D.oneIso.hom =
      AlgCat.ofHom (DegreeOne.faceZeroLift p) ≫
        AlgCat.ofHom (DegreeOne.degeneracyZeroLift p) := by
  have h : D.simplicial.σ (1 : Fin 2) ≫ D.simplicial.δ (0 : Fin 3) =
      D.simplicial.δ (0 : Fin 2) ≫ D.simplicial.σ (0 : Fin 1) := by
    simpa using D.simplicial.δ_comp_σ_of_le (n := 0) (i := (0 : Fin 2))
      (j := (0 : Fin 1)) (by decide)
  rw [reassoc_of% h, ← D.faceZero_eq, ← D.degeneracyZero_eq]
  simp

private lemma coskFace_sigmaOne_one (D : DegreeOne.DegreeOneCoskeleton p) :
    D.oneIso.inv ≫ D.simplicial.σ (1 : Fin 2) ≫ D.simplicial.δ (1 : Fin 3) ≫
        D.oneIso.hom = 𝟙 _ :=
  coskFace_sigma_delta_eq_id p D (D.simplicial.δ_comp_σ_self (i := (1 : Fin 2)))

private lemma coskFace_sigmaOne_two (D : DegreeOne.DegreeOneCoskeleton p) :
    D.oneIso.inv ≫ D.simplicial.σ (1 : Fin 2) ≫ D.simplicial.δ (2 : Fin 3) ≫
        D.oneIso.hom = 𝟙 _ :=
  coskFace_sigma_delta_eq_id p D (D.simplicial.δ_comp_σ_succ (i := (1 : Fin 2)))

/-- A map `P1 → P2` lifts the `i`-th degeneracy of the one-coskeleton once its composites with the
three faces are the corresponding composites of the coskeleton. -/
private lemma lift_comp_degreeTwoToCoskeleton (g : DegreeOne.P1 p →ₐ[p.A] DegreeTwo.P2 p)
    (i : Fin 2)
    (h : let D := DegreeOne.degreeOneCoskeleton p
      ∀ q : ULift.{max u v w x, max u w x} (DegreeOne.P1 p),
      ((DegreeTwo.faceZero p).comp g) q.down =
          ULift.down ((D.oneIso.inv ≫ D.simplicial.σ i ≫ D.simplicial.δ (0 : Fin 3) ≫
            D.oneIso.hom) q) ∧
      ((DegreeTwo.faceOne p).comp g) q.down =
          ULift.down ((D.oneIso.inv ≫ D.simplicial.σ i ≫ D.simplicial.δ (1 : Fin 3) ≫
            D.oneIso.hom) q) ∧
      ((DegreeTwo.faceTwo p).comp g) q.down =
          ULift.down ((D.oneIso.inv ≫ D.simplicial.σ i ≫ D.simplicial.δ (2 : Fin 3) ≫
            D.oneIso.hom) q)) :
    AlgCat.ofHom (liftP p g) ≫ DegreeTwo.degreeTwoToCoskeleton p =
      (DegreeOne.degreeOneCoskeleton p).oneIso.inv ≫
        (DegreeOne.degreeOneCoskeleton p).simplicial.σ i := by
  let D := DegreeOne.degreeOneCoskeleton p
  ext q
  apply (DegreeTwo.matchingEquiv p).injective
  change DegreeTwo.matchingEquiv p (DegreeTwo.degreeTwoToCoskeleton p (ULift.up (g q.down))) =
    DegreeTwo.matchingEquiv p ((D.oneIso.inv ≫ D.simplicial.σ i) q)
  rw [DegreeTwo.matchingEquiv_degreeTwoToCoskeleton]
  apply Subtype.ext
  rw [DegreeTwo.matchingEquiv_faces]
  simp only [Prod.mk.injEq]
  exact h q

/-- The displayed first degeneracy lifts the first degeneracy of the
one-coskeleton. -/
@[stacks 09D4 "degeneracies"]
theorem degeneracyZero_lifts :
    AlgCat.ofHom (degeneracyZeroLift p) ≫
        DegreeTwo.degreeTwoToCoskeleton p =
        (DegreeOne.degreeOneCoskeleton p).oneIso.inv ≫
        (DegreeOne.degreeOneCoskeleton p).simplicial.σ (0 : Fin 2) := by
  refine lift_comp_degreeTwoToCoskeleton p (degeneracyZero p) 0 fun q => ?_
  rw [faceZero_comp_degeneracyZero, faceOne_comp_degeneracyZero,
    faceTwo_comp_degeneracyZero, coskFace_sigmaZero_zero,
    coskFace_sigmaZero_one, coskFace_sigmaZero_two]
  simp [DegreeOne.faceOneLift, DegreeOne.degeneracyZeroLift]

/-- The displayed second degeneracy lifts the second degeneracy of the
one-coskeleton. -/
@[stacks 09D4 "degeneracies"]
theorem degeneracyOne_lifts :
    AlgCat.ofHom (degeneracyOneLift p) ≫
        DegreeTwo.degreeTwoToCoskeleton p =
      (DegreeOne.degreeOneCoskeleton p).oneIso.inv ≫
        (DegreeOne.degreeOneCoskeleton p).simplicial.σ (1 : Fin 2) := by
  refine lift_comp_degreeTwoToCoskeleton p (degeneracyOne p) 1 fun q => ?_
  rw [faceZero_comp_degeneracyOne, faceOne_comp_degeneracyOne,
    faceTwo_comp_degeneracyOne, coskFace_sigmaOne_zero,
    coskFace_sigmaOne_one, coskFace_sigmaOne_two]
  simp [DegreeOne.faceZeroLift, DegreeOne.degeneracyZeroLift]

/-- The target algebra in the category of commutative algebras at the common
universe level. -/
noncomputable def commAlgB : CommAlgCat.{max u v w x} p.A := by
  letI : Algebra p.A p.B := p.algebraMap.toAlgebra
  exact CommAlgCat.of p.A (ULift.{max u v w x, v} p.B)

/-- Forget commutativity from a simplicial commutative algebra. -/
abbrev underlying
    (P : SimplicialObject (CommAlgCat.{max u v w x} p.A)) :
    SimplicialObject (AlgCat.{max u v w x} p.A) :=
  P ⋙ forget₂ (CommAlgCat.{max u v w x} p.A) (AlgCat.{max u v w x} p.A)

/-- A polynomial simplicial resolution with its first three degrees specified. -/
structure ExplicitResolution where
  simplicial : SimplicialObject (CommAlgCat.{max u v w x} p.A)
  augmentation : simplicial ⟶
    (SimplicialObject.const (CommAlgCat.{max u v w x} p.A)).obj (commAlgB p)
  isResolution :
    (letI : Algebra p.A p.B := p.algebraMap.toAlgebra
     CommAlgCat.IsResolution p.A
       (ULift.{max u v w x, v} p.B) simplicial augmentation)
  zeroIso : underlying p simplicial _⦋0⦌ ≅ DegreeOne.algP0 p
  oneIso : underlying p simplicial _⦋1⦌ ≅ DegreeOne.algP1 p
  twoIso : underlying p simplicial _⦋2⦌ ≅ DegreeTwo.algP2 p
  faceZeroOne_eq : oneIso.inv ≫ (underlying p simplicial).δ (0 : Fin 2) ≫ zeroIso.hom =
    AlgCat.ofHom (DegreeOne.faceZeroLift p)
  faceOneOne_eq : oneIso.inv ≫ (underlying p simplicial).δ (1 : Fin 2) ≫ zeroIso.hom =
    AlgCat.ofHom (DegreeOne.faceOneLift p)
  degeneracyZeroOne_eq : zeroIso.inv ≫ (underlying p simplicial).σ (0 : Fin 1) ≫ oneIso.hom =
    AlgCat.ofHom (DegreeOne.degeneracyZeroLift p)
  faceZeroTwo_eq : twoIso.inv ≫ (underlying p simplicial).δ (0 : Fin 3) ≫ oneIso.hom =
    AlgCat.ofHom (faceZeroLift p)
  faceOneTwo_eq : twoIso.inv ≫ (underlying p simplicial).δ (1 : Fin 3) ≫ oneIso.hom =
    AlgCat.ofHom (faceOneLift p)
  faceTwoTwo_eq : twoIso.inv ≫ (underlying p simplicial).δ (2 : Fin 3) ≫ oneIso.hom =
    AlgCat.ofHom (faceTwoLift p)
  degeneracyZeroTwo_eq : oneIso.inv ≫ (underlying p simplicial).σ (0 : Fin 2) ≫ twoIso.hom =
    AlgCat.ofHom (degeneracyZeroLift p)
  degeneracyOneTwo_eq : oneIso.inv ≫ (underlying p simplicial).σ (1 : Fin 2) ≫ twoIso.hom =
    AlgCat.ofHom (degeneracyOneLift p)
  augmentation_eq :
    (letI : Algebra p.A p.B := p.algebraMap.toAlgebra
     zeroIso.inv ≫ (Functor.whiskerRight augmentation
       (forget₂ (CommAlgCat.{max u v w x} p.A) (AlgCat.{max u v w x} p.A))).app
         (op ⦋0⦌) =
       AlgCat.ofHom (DegreeOne.augmentationZeroLift p))

section Cells

universe a b

variable {A : Type u} [CommRing A] {P : SimplicialObject (CommAlgCat.{max u v} A)}
  {d : ℕ} {I : Type (max u v)}

/-- The category of commutative `A`-algebras over a fixed `A`-algebra `B`, with the universe of
the ambient algebra category pinned. An abbreviation: it is reducibly the plain
`Over (CommAlgCat.of A B)`. -/
private abbrev overCommAlg (A : Type u) [CommRing A] (B : Type (max u v))
    [CommRing B] [Algebra A B] :=
  Over (show CommAlgCat.{max u v} A from CommAlgCat.of A B)


attribute [local instance] CommAlgCat.forgetReflectsIsomorphisms

private lemma polynomial_attachCells (b : CellBoundary P d I)
    (hP : ∀ n : ℕ, CommAlgCat.IsPolynomialAlgebra A (P.obj (op ⦋n⦌))) :
    ∀ n : ℕ, CommAlgCat.IsPolynomialAlgebra A
      ((attachCells b).obj (op ⦋n⦌)) := by
  intro n
  obtain ⟨J, ⟨e⟩⟩ := hP n
  let V := CellVariable d I ⦋n⦌
  exact ⟨V ⊕ J, ⟨(MvPolynomial.sumAlgEquiv A V J).trans
    (MvPolynomial.mapAlgEquiv V e)⟩⟩

/-- Attaching cells in degree `d` to `P` keeps a map out of `P` bijective in degrees below `d`. -/
private lemma bijective_cellDesc_app {Q : SimplicialObject (CommAlgCat.{max u v} A)}
    (b : CellBoundary P d I) (f : P ⟶ Q) (t : I → Q.obj (op ⦋d⦌))
    (h : ∀ (Δ : SimplexCategory) (α : Δ ⟶ ⦋d⦌)
      (hα : ¬ Function.Surjective α.toOrderHom) (i : I),
      f.app (op Δ) (b.val Δ α hα i) = Q.map α.op (t i))
    (k : ℕ) (hk : k < d) (hf : Function.Bijective (f.app (op ⦋k⦌))) :
    Function.Bijective ((cellDesc b f t h).app (op ⦋k⦌)) := by
  have hi : IsIso ((attachCellsι b).app (op ⦋k⦌)) := isIso_attachCellsι_app _ _ (by simpa using hk)
  have hj : Function.Bijective ((attachCellsι b).app (op ⦋k⦌)) :=
    (isIso_iff_bijective ((forget (CommAlgCat.{max u v} A)).map
      ((attachCellsι b).app (op ⦋k⦌)))).mp inferInstance
  apply (Function.Bijective.of_comp_iff _ hj).mp
  change Function.Bijective ((attachCellsι b ≫ cellDesc b f t h).app (op ⦋k⦌))
  rw [attachCellsι_cellDesc]
  exact hf

private lemma exists_polynomial_extension {Q : SimplicialObject (CommAlgCat.{max u v} A)}
    (f : P ⟶ Q) (n : ℕ)
    (hf : ∀ k, k ≤ n → Function.Bijective (f.app (op ⦋k⦌)))
    (hP : ∀ n : ℕ, CommAlgCat.IsPolynomialAlgebra A (P.obj (op ⦋n⦌))) :
    ∃ (P' : SimplicialObject (CommAlgCat.{max u v} A)) (i : P ⟶ P') (q : P' ⟶ Q),
      i ≫ q = f ∧
      (∀ n : ℕ, CommAlgCat.IsPolynomialAlgebra A (P'.obj (op ⦋n⦌))) ∧
      (∀ k, k ≤ n → IsIso (i.app (op ⦋k⦌))) ∧
      Function.Surjective (q.app (op ⦋n + 1⦌)) := by
  classical
  obtain ⟨b, hb⟩ := exists_cellBoundary_of_bijective f n hf
    (_root_.id : Q.obj (op ⦋n + 1⦌) → Q.obj (op ⦋n + 1⦌))
  let q := cellDesc b f _root_.id hb
  refine ⟨attachCells b, attachCellsι b, q, attachCellsι_cellDesc b f _ hb,
    polynomial_attachCells b hP,
    fun j hj => isIso_attachCellsι_app b _ (by simpa using hj), ?_⟩
  intro t
  refine ⟨MvPolynomial.X (t, ⟨𝟙 _, Function.surjective_id⟩), ?_⟩
  change cellDescApp b f _root_.id (op ⦋n + 1⦌) _ = t
  rw [cellDescApp_X]
  simp

private def liftedBaseEquivalence (A : Type u) [CommRing A] :
    CommAlgCat.{max u v} A ≌ Under (CommRingCat.of (ULift.{v} A)) := by
  let F : CommAlgCat.{max u v} A ⥤ Under (CommRingCat.of (ULift.{v} A)) :=
    { obj := fun B => Under.mk (CommRingCat.ofHom
        ((_root_.Algebra.algebraMap A B).comp ULift.ringEquiv.toRingHom))
      map := fun f => Under.homMk (CommRingCat.ofHom f.hom.toRingHom) (by
        ext a
        exact f.hom.commutes a.down) }
  let G : Under (CommRingCat.of (ULift.{v} A)) ⥤ CommAlgCat.{max u v} A :=
    { obj := fun B => by
        letI : Algebra A B.right :=
          (B.hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        exact CommAlgCat.of A B.right
      map := fun {X Y} f => by
        letI : Algebra A X.right :=
          (X.hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        letI : Algebra A Y.right :=
          (Y.hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        exact CommAlgCat.ofHom
          { __ := f.right.hom
            commutes' := fun a => ConcreteCategory.congr_hom (Under.w f) (ULift.up a) } }
  refine CategoryTheory.Equivalence.mk F G ?_ ?_
  · refine NatIso.ofComponents (fun B => ?_) ?_
    · letI : Algebra A (F.obj B).right :=
        ((F.obj B).hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
      exact CommAlgCat.isoMk
        { toRingEquiv := RingEquiv.refl B
          commutes' := fun _ => rfl }
    · intro X Y f
      rfl
  · refine NatIso.ofComponents (fun B => Under.isoMk (Iso.refl _) ?_) ?_
    · ext a
      rfl
    · intro X Y f
      rfl

/-- The category `CommAlgCat.{max u v} A` has all limits. -/
local instance (priority := 2000) commAlgCatHasLimits :
    CategoryTheory.Limits.HasLimits (CommAlgCat.{max u v} A) :=
  CategoryTheory.Adjunction.has_limits_of_equivalence (liftedBaseEquivalence.{u, v} A).functor

private theorem commAlgCatSmallLimits :
    CategoryTheory.Limits.HasLimitsOfSize.{0, 0} (CommAlgCat.{max u v} A) := by
  let : CategoryTheory.Limits.HasLimits (CommAlgCat.{max u v} A) :=
    commAlgCatHasLimits (A := A)
  infer_instance

attribute [local instance 2100] commAlgCatSmallLimits

variable [CategoryTheory.Limits.HasLimits (CommAlgCat.{max u v} A)]

private alias isCoskeletal_comp := CommAlgCat.isCoskeletal_comp

omit [CategoryTheory.Limits.HasLimits (CommAlgCat.{max u v} A)] in
private lemma underlying_isCoskeletal {B : Type (max u v)} [CommRing B] [Algebra A B]
    (X : SimplicialObject (Over (CommAlgCat.of A B))) (n : ℕ)
    [X.IsCoskeletal (n + 1)] :
    SimplicialObject.IsCoskeletal
      (X ⋙ Over.forget _ ⋙ forget (CommAlgCat.{max u v} A)) (n + 1) := by
  have : CategoryTheory.Limits.PreservesLimitsOfSize.{0, 0} (forget (CommAlgCat.{max u v} A)) :=
    (CommAlgCat.adj.{u, v} A).rightAdjoint_preservesLimits
  have : SimplicialObject.IsCoskeletal (X ⋙ Over.forget (CommAlgCat.of A B)) (n + 1) :=
    isCoskeletal_comp X (n + 1) (Over.forget _)
  exact isCoskeletal_comp (X ⋙ Over.forget _) (n + 1) (forget (CommAlgCat.{max u v} A))

/-- The augmentation of a simplicial object over `B`, on underlying types. -/
private def underlyingAugmentation {A : Type u} [CommRing A]
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (X : SimplicialObject (Over (CommAlgCat.of A B))) :=
  Functor.whiskerRight (CommAlgCat.overAugmentation X) (forget (CommAlgCat.{max u v} A))

omit [CategoryTheory.Limits.HasLimits (CommAlgCat.{max u v} A)] in
private lemma exists_polynomial_extension_over {B : Type (max u v)} [CommRing B] [Algebra A B]
    (X Y : SimplicialObject (Over (CommAlgCat.of A B))) (f : X ⟶ Y) (n : ℕ)
    (hf : ∀ k, k ≤ n → Function.Bijective ((f.app (op ⦋k⦌)).left))
    (hX : ∀ k : ℕ, CommAlgCat.IsPolynomialAlgebra A ((X.obj (op ⦋k⦌)).left))
    :
    ∃ (X' : SimplicialObject (Over (CommAlgCat.of A B))) (i : X ⟶ X') (q : X' ⟶ Y),
      i ≫ q = f ∧
      (∀ k : ℕ, CommAlgCat.IsPolynomialAlgebra A ((X'.obj (op ⦋k⦌)).left)) ∧
      (∀ k, k ≤ n → IsIso (i.app (op ⦋k⦌))) ∧
      Function.Surjective ((q.app (op ⦋n + 1⦌)).left) := by
  obtain ⟨P', i, q, hfac, hP', hi, hq⟩ := exists_polynomial_extension
    (Functor.whiskerRight f (Over.forget _)) n hf hX
  let ε := q ≫ CommAlgCat.overAugmentation Y
  let X' := CommAlgCat.toOverAugmentation ε
  let q' : X' ⟶ Y :=
    { app := fun Δ => Over.homMk (q.app Δ) rfl
      naturality := fun Δ Δ' g => by
        apply Over.OverMorphism.ext
        exact q.naturality g }
  have hiw (Δ : SimplexCategoryᵒᵖ) : i.app Δ ≫ (X'.obj Δ).hom = (X.obj Δ).hom := by
    change i.app Δ ≫ q.app Δ ≫ (Y.obj Δ).hom = _
    rw [← Category.assoc, ← NatTrans.comp_app, hfac]
    exact Over.w (f.app Δ)
  let i' : X ⟶ X' :=
    { app := fun Δ => Over.homMk (i.app Δ) (hiw Δ)
      naturality := fun Δ Δ' g => by
        apply Over.OverMorphism.ext
        exact i.naturality g }
  refine ⟨X', i', q', ?_, hP', ?_, hq⟩
  · apply NatTrans.ext
    funext Δ
    apply Over.OverMorphism.ext
    exact congr_app hfac Δ
  · intro k hk
    have hm : IsIso ((Over.forget _).map (i'.app (op ⦋k⦌))) := hi k hk
    exact isIso_of_reflects_iso (i'.app (op ⦋k⦌)) (Over.forget _)

private alias cosk_isCoskeletal := CommAlgCat.cosk_isCoskeletal

omit [CategoryTheory.Limits.HasLimits (CommAlgCat.{max u v} A)] in
private lemma over_augmentation_naturality {B : Type (max u v)} [CommRing B] [Algebra A B]
    {X Y : SimplicialObject (Over (CommAlgCat.of A B))} (f : X ⟶ Y) :
    Functor.whiskerRight f (Over.forget _ ⋙ forget (CommAlgCat.{max u v} A)) ≫
      underlyingAugmentation Y = underlyingAugmentation X := by
  apply NatTrans.ext
  funext Δ
  exact congrArg ((forget (CommAlgCat.{max u v} A)).map) (Over.w (f.app Δ))

/-- A map `q : X ⟶ Y` to a coskeletal object that is bijective in low degrees and surjective in
degree `n + 1` induces a trivial Kan fibration `cosk (n + 1) X ⟶ Y` through which it factors. -/
private lemma exists_cosk_lift {B : Type (max u v)} [CommRing B] [Algebra A B]
    (X Y : SimplicialObject (Over (CommAlgCat.of A B))) (q : X ⟶ Y) (n : ℕ)
    [Y.IsCoskeletal (n + 1)]
    (hq : ∀ k, k ≤ n → Function.Bijective (q.app (op ⦋k⦌)).left)
    (hs : Function.Surjective (q.app (op ⦋n + 1⦌)).left) :
    ∃ f : (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) (n + 1)).obj X ⟶ Y,
      (SimplicialObject.coskAdj (C := overCommAlg.{u, v} A B) (n + 1)).unit.app X ≫ f = q ∧
      SSet.trivialKanFibrations
        (Functor.whiskerRight f (Over.forget _ ⋙ forget (CommAlgCat.{max u v} A))) := by
  let R := (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) (n + 1)).obj X
  let η := (SimplicialObject.coskAdj (C := overCommAlg.{u, v} A B) (n + 1)).unit.app X
  have hYη : IsIso ((SimplicialObject.coskAdj (C := overCommAlg.{u, v} A B) (n + 1)).unit.app Y) :=
    (SimplicialObject.isCoskeletal_iff_isIso Y _).mp inferInstance
  let f : R ⟶ Y := (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) (n + 1)).map q ≫
    inv ((SimplicialObject.coskAdj (C := overCommAlg.{u, v} A B) (n + 1)).unit.app Y)
  have hf : η ≫ f = q := by
    dsimp only [η, f]
    rw [← Category.assoc, ← NatTrans.naturality]
    simp
  have hb (k : ℕ) (hk : k ≤ n) : Function.Bijective (f.app (op ⦋k⦌)).left := by
    have hi : IsIso (η.app (op ⦋k⦌)) :=
      CommAlgCat.isIso_cosk_unit_app X (n + 1) ⦋k⦌ (by simpa using Nat.le_succ_of_le hk)
    have hη := over_bijective_of_isIso (η.app (op ⦋k⦌))
    apply (Function.Bijective.of_comp_iff _ hη).mp
    change Function.Bijective ((η.app (op ⦋k⦌) ≫ f.app (op ⦋k⦌)).left)
    rw [← NatTrans.comp_app, hf]
    exact hq k hk
  have hsurj : Function.Surjective (f.app (op ⦋n + 1⦌)).left := by
    apply Function.Surjective.of_comp (g := (η.app (op ⦋n + 1⦌)).left)
    change Function.Surjective ((η.app (op ⦋n + 1⦌) ≫ f.app (op ⦋n + 1⦌)).left)
    rw [← NatTrans.comp_app, hf]
    exact hs
  have hR : R.IsCoskeletal (n + 1) := cosk_isCoskeletal X _
  have hU := underlying_isCoskeletal Y n
  have hU' := underlying_isCoskeletal R n
  exact ⟨f, hf, SSet.trivialKanFibrations_of_coskeletal _ (n + 1)
    (fun k hk => hb k (by omega)) hsurj
    ((SimplicialObject.isCoskeletal_iff_isIso _ _).mp hU)
    ((SimplicialObject.isCoskeletal_iff_isIso _ _).mp hU')⟩

private lemma exists_next_stage {B : Type (max u v)} [CommRing B] [Algebra A B]
    (X : SimplicialObject (Over (CommAlgCat.of A B))) (n : ℕ)
    (hX : ∀ k : ℕ, CommAlgCat.IsPolynomialAlgebra A ((X.obj (op ⦋k⦌)).left))
    (hkan : SSet.trivialKanFibrations
      (underlyingAugmentation ((SimplicialObject.cosk (C := overCommAlg.{u, v} A B) n).obj X))) :
    ∃ (X' : SimplicialObject (Over (CommAlgCat.of A B)))
      (f : (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) (n + 1)).obj X' ⟶
        (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) n).obj X),
      (∀ k : ℕ, CommAlgCat.IsPolynomialAlgebra A ((X'.obj (op ⦋k⦌)).left)) ∧
      SSet.trivialKanFibrations
        (underlyingAugmentation
          ((SimplicialObject.cosk (C := overCommAlg.{u, v} A B) (n + 1)).obj X')) ∧
      SSet.trivialKanFibrations
        (Functor.whiskerRight f (Over.forget _ ⋙ forget (CommAlgCat.{max u v} A))) ∧
      (∀ k, k ≤ n → IsIso (f.app (op ⦋k⦌))) := by
  let R := (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) n).obj X
  have hR : R.IsCoskeletal n := cosk_isCoskeletal X n
  have hRn : IsIso ((SimplicialObject.coskAdj (C := overCommAlg.{u, v} A B) (n + 1)).unit.app R) :=
    (SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
      (C := Over (CommAlgCat.of A B)) (Nat.le_succ n)).2.2 R inferInstance
  have hRn' : R.IsCoskeletal (n + 1) :=
    (SimplicialObject.isCoskeletal_iff_isIso _ _).mpr hRn
  let η := (SimplicialObject.coskAdj (C := overCommAlg.{u, v} A B) n).unit.app X
  have hη (k : ℕ) (hk : k ≤ n) : IsIso (η.app (op ⦋k⦌)) :=
    CommAlgCat.isIso_cosk_unit_app X n ⦋k⦌ hk
  obtain ⟨X', i, q, hfac, hX', hi, hq⟩ :=
    exists_polynomial_extension_over X R η n
      (fun k hk => have := hη k hk; over_bijective_of_isIso _) hX
  have hqi (k : ℕ) (hk : k ≤ n) : IsIso (q.app (op ⦋k⦌)) := by
    have := hi k hk
    have := hη k hk
    exact IsIso.of_isIso_fac_left (congr_app hfac (op ⦋k⦌))
  obtain ⟨f, hf, hfk⟩ := exists_cosk_lift X' R q n
    (fun k hk => have := hqi k hk; over_bijective_of_isIso _) hq
  have hfiso (k : ℕ) (hk : k ≤ n) : IsIso (f.app (op ⦋k⦌)) := by
    have := hqi k hk
    have : IsIso (((SimplicialObject.coskAdj (C := overCommAlg.{u, v} A B) (n + 1)).unit.app
        X').app (op ⦋k⦌)) :=
      CommAlgCat.isIso_cosk_unit_app X' (n + 1) ⦋k⦌ (by simpa using Nat.le_succ_of_le hk)
    exact IsIso.of_isIso_fac_left (congr_app hf _)
  refine ⟨X', f, hX', ?_, hfk, hfiso⟩
  rw [← over_augmentation_naturality f]
  exact SSet.trivialKanFibrations_comp _ _ hfk hkan

private alias eventuallyConstantTo_of_isIso_succ :=
  CommAlgCat.eventuallyConstantTo_of_isIso_succ

omit [CategoryTheory.Limits.HasLimits (CommAlgCat.{max u v} A)] in
private lemma trivialKanFibrations_limit_augmentation {B : Type (max u v)}
    [CommRing B] [Algebra A B]
    (F : ℕᵒᵖ ⥤ SimplicialObject (Over (CommAlgCat.of A B)))
    (h₀ : SSet.trivialKanFibrations (underlyingAugmentation (F.obj (op 0))))
    (h : ∀ n : ℕ, SSet.trivialKanFibrations (Functor.whiskerRight
      (F.map (homOfLE (Nat.le_succ n)).op) (Over.forget _ ⋙ forget (CommAlgCat.{max u v} A)))) :
    SSet.trivialKanFibrations (underlyingAugmentation (CategoryTheory.Limits.limit F)) := by
  have : CategoryTheory.Limits.PreservesLimitsOfSize.{0, 0} (forget (CommAlgCat.{max u v} A)) :=
    (CommAlgCat.adj.{u, v} A).rightAdjoint_preservesLimits
  let G := (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
    (Over.forget (CommAlgCat.of A B) ⋙ forget (CommAlgCat.{max u v} A))
  have hlim := SSet.trivialKanFibrations_limit_π_zero (F ⋙ G) h
  have hπ : SSet.trivialKanFibrations (G.map (CategoryTheory.Limits.limit.π F (op 0))) := by
    rw [← preservesLimitIso_hom_π G F (op 0)]
    exact SSet.trivialKanFibrations_comp _ _
      (SSet.modelCategoryQuillen.I.rlp_of_isIso _) hlim
  rw [← over_augmentation_naturality (CategoryTheory.Limits.limit.π F (op 0))]
  exact SSet.trivialKanFibrations_comp _ _ hπ h₀

private lemma exists_polynomial_tower {B : Type (max u v)} [CommRing B] [Algebra A B]
    (r : ℕ) (X : SimplicialObject (Over (CommAlgCat.of A B)))
    (hX : ∀ k : ℕ, CommAlgCat.IsPolynomialAlgebra A ((X.obj (op ⦋k⦌)).left))
    (hkan : SSet.trivialKanFibrations
      (underlyingAugmentation ((SimplicialObject.cosk (C := overCommAlg.{u, v} A B) r).obj X))) :
    ∃ F : ℕᵒᵖ ⥤ SimplicialObject (Over (CommAlgCat.of A B)),
      F.obj (op 0) = (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) r).obj X ∧
      SSet.trivialKanFibrations (underlyingAugmentation (F.obj (op 0))) ∧
      (∀ n : ℕ, SSet.trivialKanFibrations (Functor.whiskerRight
        (F.map (homOfLE (Nat.le_succ n)).op) (Over.forget _ ⋙ forget (CommAlgCat.{max u v} A)))) ∧
      (∀ n k : ℕ, k ≤ r + n →
        IsIso ((F.map (homOfLE (Nat.le_succ n)).op).app (op ⦋k⦌))) ∧
      (∀ n k : ℕ, k ≤ r + n → CommAlgCat.IsPolynomialAlgebra A
        (((F.obj (op n)).obj (op ⦋k⦌)).left)) := by
  classical
  let S (n : ℕ) := {X : SimplicialObject (Over (CommAlgCat.of A B)) //
    (∀ k : ℕ, CommAlgCat.IsPolynomialAlgebra A ((X.obj (op ⦋k⦌)).left)) ∧
    SSet.trivialKanFibrations
      (underlyingAugmentation
        ((SimplicialObject.cosk (C := overCommAlg.{u, v} A B) (r + n)).obj X))}
  let s₀ : S 0 := ⟨X, hX, hkan⟩
  have hnext (n : ℕ) (s : S n) :
      ∃ (t : S (n + 1))
        (f : (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) (r + (n + 1))).obj t.val ⟶
          (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) (r + n)).obj s.val),
        SSet.trivialKanFibrations
          (Functor.whiskerRight f (Over.forget _ ⋙ forget (CommAlgCat.{max u v} A))) ∧
        (∀ k, k ≤ r + n → IsIso (f.app (op ⦋k⦌))) := by
    obtain ⟨X', f, hp, hk, hf, hi⟩ := exists_next_stage s.val (r + n) s.prop.1 s.prop.2
    exact ⟨⟨X', hp, hk⟩, f, hf, hi⟩
  choose next f hf hi using hnext
  let s : ∀ n, S n := Nat.rec s₀ (fun n sn => next n sn)
  let F := Functor.ofOpSequence
    (X := fun n => (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) (r + n)).obj (s n).val)
    (fun n => f n (s n))
  refine ⟨F, rfl, (s 0).prop.2, ?_, ?_, ?_⟩
  · intro n
    rw [show F.map (homOfLE (Nat.le_succ n)).op = f n (s n) from
      Functor.ofOpSequence_map_homOfLE_succ _ n]
    exact hf n (s n)
  · intro n k hk
    rw [show F.map (homOfLE (Nat.le_succ n)).op = f n (s n) from
      Functor.ofOpSequence_map_homOfLE_succ _ n]
    exact hi n (s n) k hk
  · intro n k hk
    obtain ⟨J, ⟨e⟩⟩ := (s n).prop.1 k
    have hu : IsIso (((SimplicialObject.coskAdj (C := overCommAlg.{u, v} A B)
        (r + n)).unit.app (s n).val).app (op ⦋k⦌)) :=
      CommAlgCat.isIso_cosk_unit_app (s n).val (r + n) ⦋k⦌ hk
    refine ⟨J, ⟨?_⟩⟩
    exact e.trans (CommAlgCat.algEquivOfIso ((Over.forget _).mapIso
      (@asIso _ _ _ _ (((SimplicialObject.coskAdj (C := overCommAlg.{u, v} A B)
        (r + n)).unit.app (s n).val).app (op ⦋k⦌)) hu)))

private lemma exists_resolution_preserving_coskeleton {B : Type (max u v)}
    [CommRing B] [Algebra A B]
    (r : ℕ) (X : SimplicialObject (Over (CommAlgCat.of A B)))
    (hX : ∀ k : ℕ, CommAlgCat.IsPolynomialAlgebra A ((X.obj (op ⦋k⦌)).left))
    (hkan : SSet.trivialKanFibrations
      (underlyingAugmentation ((SimplicialObject.cosk (C := overCommAlg.{u, v} A B) r).obj X))) :
    ∃ (R : SimplicialObject (Over (CommAlgCat.of A B)))
      (π : R ⟶ (SimplicialObject.cosk (C := overCommAlg.{u, v} A B) r).obj X),
      (∀ k : ℕ, CommAlgCat.IsPolynomialAlgebra A ((R.obj (op ⦋k⦌)).left)) ∧
      SSet.trivialKanFibrations (underlyingAugmentation R) ∧
      (∀ k, k ≤ r → IsIso (π.app (op ⦋k⦌))) := by
  obtain ⟨F, hF, h₀, hf, hi, hp⟩ := exists_polynomial_tower r X hX hkan
  let R := CategoryTheory.Limits.limit F
  let π := CategoryTheory.Limits.limit.π F (op 0) ≫ eqToHom hF
  have hπ (n k : ℕ) (hk : k ≤ r + n) :
      IsIso ((CategoryTheory.Limits.limit.π F (op n)).app (op ⦋k⦌)) := by
    let E := (evaluation SimplexCategoryᵒᵖ (Over (CommAlgCat.of A B))).obj (op ⦋k⦌)
    have hE : (F ⋙ E).IsEventuallyConstantTo (op n) :=
      eventuallyConstantTo_of_isIso_succ (F ⋙ E) n
        (fun j hj => hi j k (by omega))
    exact hE.isIso_π_of_isLimit
      (CategoryTheory.Limits.isLimitOfPreserves E (CategoryTheory.Limits.limit.isLimit F))
  refine ⟨R, π, ?_, trivialKanFibrations_limit_augmentation F h₀ hf, ?_⟩
  · intro k
    obtain ⟨J, ⟨e⟩⟩ := hp k k (by omega)
    have := hπ k k (by omega)
    exact ⟨J, ⟨e.trans (CommAlgCat.algEquivOfIso ((Over.forget _).mapIso
      (asIso ((CategoryTheory.Limits.limit.π F (op k)).app (op ⦋k⦌))))).symm⟩⟩
  · intro k hk
    have := hπ 0 k (by simpa using hk)
    dsimp [π]
    infer_instance

end Cells

private abbrev commRingOfCoskeletal {A : Type u} [CommRing A]
    (X : SimplicialObject (AlgCat.{v} A)) (n : ℕ) [X.IsCoskeletal n]
    (hc : ∀ (k : ℕ), k ≤ n → ∀ a b : X.obj (op ⦋k⦌), a * b = b * a)
    (Δ : SimplexCategoryᵒᵖ) : CommRing (X.obj Δ) := by
  refine { (inferInstance : Ring (X.obj Δ)) with mul_comm := ?_ }
  intro a b
  have : X.IsRightKanExtension
      (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X)) :=
    SimplicialObject.IsCoskeletal.isRightKanExtension
  let h := Functor.isPointwiseRightKanExtensionOfIsRightKanExtension X
    (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X)) Δ
  apply Limits.Concrete.isLimit_ext _ h
  intro j
  change (X.map j.hom).hom (a * b) = (X.map j.hom).hom (b * a)
  simp only [map_mul]
  exact hc j.right.unop.obj.len j.right.unop.property _ _

private lemma coskOne : (DegreeOne.degreeOneCoskeleton p).simplicial.IsCoskeletal 1 := by
  rw [(DegreeOne.degreeOneCoskeleton p).isCoskeleton]
  exact (SimplicialObject.isCoskeletal_iff_isIso _ 1).mpr
    ((SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
      (C := AlgCat.{max u v w x} p.A) (Nat.le_refl 1)).2.1 _)

private noncomputable abbrev commRingD (Δ : SimplexCategoryᵒᵖ) :
    CommRing ((DegreeOne.degreeOneCoskeleton p).simplicial.obj Δ) := by
  let D := DegreeOne.degreeOneCoskeleton p
  have := coskOne p
  apply commRingOfCoskeletal D.simplicial 1 ?_ Δ
  intro k hk a b
  interval_cases k
  · apply D.zeroIso.toAlgEquiv.injective
    simp only [map_mul, mul_comm]
  · apply D.oneIso.toAlgEquiv.injective
    simp only [map_mul, mul_comm]

attribute [local instance] commRingD

private noncomputable abbrev commD : SimplicialObject (CommAlgCat.{max u v w x} p.A) where
  obj Δ := CommAlgCat.of p.A ((DegreeOne.degreeOneCoskeleton p).simplicial.obj Δ)
  map f := CommAlgCat.ofHom ((DegreeOne.degreeOneCoskeleton p).simplicial.map f).hom
  map_id Δ := by
    ext a
    exact ConcreteCategory.congr_hom
      ((DegreeOne.degreeOneCoskeleton p).simplicial.map_id Δ) a
  map_comp f g := by
    ext a
    exact ConcreteCategory.congr_hom
      ((DegreeOne.degreeOneCoskeleton p).simplicial.map_comp f g) a

private noncomputable abbrev constantP0 : SimplicialObject (CommAlgCat.{max u v w x} p.A) :=
  (SimplicialObject.const _).obj
    (CommAlgCat.of p.A (ULift.{max u v w x, max u w} p.P0))

private noncomputable def constantToD : constantP0 p ⟶ commD p where
  app Δ := CommAlgCat.ofHom
    (((DegreeOne.degreeOneCoskeleton p).simplicial.map
      (SimplexCategory.const Δ.unop ⦋0⦌ 0).op).hom.comp
        (DegreeOne.degreeOneCoskeleton p).zeroIso.inv.hom)
  naturality Δ Δ' f := by
    ext a
    let D := DegreeOne.degreeOneCoskeleton p
    change (D.simplicial.map (SimplexCategory.const Δ'.unop ⦋0⦌ 0).op)
      (D.zeroIso.inv a) = (D.simplicial.map f)
        ((D.simplicial.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op) (D.zeroIso.inv a))
    change (D.simplicial.map (SimplexCategory.const Δ'.unop ⦋0⦌ 0).op)
      (D.zeroIso.inv a) = (D.simplicial.map
        (SimplexCategory.const Δ.unop ⦋0⦌ 0).op ≫ D.simplicial.map f) (D.zeroIso.inv a)
    rw [← Functor.map_comp]
    congr 2

private lemma constantToD_zero :
    (constantToD p).app (op ⦋0⦌) = CommAlgCat.ofHom
      (DegreeOne.degreeOneCoskeleton p).zeroIso.inv.hom := by
  ext a
  simp [constantToD]

private noncomputable def relationPoint (t : ULift.{max u v w x} p.relationIndex) :
    (commD p).obj (op ⦋1⦌) :=
  (DegreeOne.degreeOneCoskeleton p).oneIso.inv
    (ULift.up (MvPolynomial.X (Sum.inr t.down)))

private lemma exists_relationBoundary :
    ∃ b : CellBoundary.{u, max u v w x} (constantP0 p) 1 (ULift.{max u v w x} p.relationIndex),
      ∀ (Δ : SimplexCategory) (α : Δ ⟶ ⦋1⦌)
        (hα : ¬ Function.Surjective α.toOrderHom) (t : ULift.{max u v w x} p.relationIndex),
        (constantToD p).app (op Δ) (b.val Δ α hα t) =
          (commD p).map α.op (relationPoint p t) := by
  apply exists_cellBoundary_of_bijective.{u, max u v w x} (constantToD p) 0
  intro k hk
  obtain rfl : k = 0 := by omega
  rw [constantToD_zero]
  exact (DegreeOne.degreeOneCoskeleton p).zeroIso.symm.toAlgEquiv.bijective

private noncomputable abbrev relationBoundary := (exists_relationBoundary p).choose

private noncomputable abbrev relationModel := attachCells.{u, max u v w x} (relationBoundary p)

private noncomputable def relationToD : relationModel p ⟶ commD p :=
  cellDesc.{u, max u v w x} (relationBoundary p) (constantToD p) (relationPoint p)
    (exists_relationBoundary p).choose_spec

private lemma polynomial_constantP0 (n : ℕ) :
    CommAlgCat.IsPolynomialAlgebra p.A ((constantP0 p).obj (op ⦋n⦌)) :=
  ⟨ULift.{max u v w x} p.variableIndex,
    ⟨(MvPolynomial.renameEquiv p.A Equiv.ulift).trans ULift.algEquiv.symm⟩⟩

private lemma polynomial_relationModel (n : ℕ) :
    CommAlgCat.IsPolynomialAlgebra p.A ((relationModel p).obj (op ⦋n⦌)) :=
  polynomial_attachCells.{u, max u v w x} (relationBoundary p) (polynomial_constantP0 p) n

private lemma surjective_end_eq_id (n : ℕ) (α : ⦋n⦌ ⟶ ⦋n⦌)
    (h : Function.Surjective α.toOrderHom) : α = 𝟙 _ := by
  have : Epi α := SimplexCategory.epi_iff_surjective.mpr h
  exact SimplexCategory.eq_id_of_epi α

private noncomputable def relationOne : (relationModel p).obj (op ⦋1⦌) →ₐ[p.A]
    DegreeOne.P1 p :=
  ULift.algEquiv.toAlgHom.comp
    ((DegreeOne.degreeOneCoskeleton p).oneIso.hom.hom.comp
      ((relationToD p).app (op ⦋1⦌)).hom)

private lemma relationOne_C (a : ULift.{max u v w x, max u w} p.P0) :
    relationOne p (MvPolynomial.C a) = DegreeOne.degeneracyZero p a.down := by
  let D := DegreeOne.degreeOneCoskeleton p
  change ULift.down (D.oneIso.hom (cellDescApp (relationBoundary p)
    (constantToD p) (relationPoint p) (op ⦋1⦌) (MvPolynomial.C a))) = _
  rw [cellDescApp_C]
  have he : SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = SimplexCategory.σ (0 : Fin 1) :=
    Subsingleton.elim _ _
  change ULift.down ((D.zeroIso.inv ≫ D.simplicial.map
    (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op ≫ D.oneIso.hom) a) = _
  rw [he]
  change ULift.down ((D.zeroIso.inv ≫ D.simplicial.σ (0 : Fin 1) ≫ D.oneIso.hom) a) = _
  rw [D.degeneracyZero_eq]
  rfl

private lemma relationOne_X (t : ULift.{max u v w x} p.relationIndex) :
    relationOne p (MvPolynomial.X (t, ⟨𝟙 ⦋1⦌, Function.surjective_id⟩)) =
      MvPolynomial.X (Sum.inr t.down) := by
  change ULift.down ((DegreeOne.degreeOneCoskeleton p).oneIso.hom
    (cellDescApp (relationBoundary p) (constantToD p) (relationPoint p) (op ⦋1⦌)
      (MvPolynomial.X (t, ⟨𝟙 ⦋1⦌, Function.surjective_id⟩)))) = _
  rw [cellDescApp_X.{u, max u v w x}]
  simp [relationPoint, commD, AlgHom.id_apply]

private noncomputable def relationOneInv : DegreeOne.P1 p →ₐ[p.A]
    (relationModel p).obj (op ⦋1⦌) :=
  MvPolynomial.aeval (Sum.elim
    (fun i => MvPolynomial.C (ULift.up (MvPolynomial.X i)))
    (fun t => MvPolynomial.X (ULift.up t, ⟨𝟙 ⦋1⦌, Function.surjective_id⟩)))

private lemma relationOne_right_inv : (relationOne p).comp (relationOneInv p) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, relationOneInv, MvPolynomial.aeval_X]
  cases i with
  | inl i =>
      dsimp only [Sum.elim]
      rw [relationOne_C]
      simp [DegreeOne.degeneracyZero]
  | inr t =>
      dsimp only [Sum.elim]
      exact relationOne_X p (ULift.up t)

private lemma relationOneInv_degeneracy (a : p.P0) :
    relationOneInv p (DegreeOne.degeneracyZero p a) =
      MvPolynomial.C (ULift.up a) := by
  have he : (relationOneInv p).comp (DegreeOne.degeneracyZero p) =
      (IsScalarTower.toAlgHom p.A (ULift.{max u v w x, max u w} p.P0)
        (MvPolynomial (CellVariable 1 (ULift.{max u v w x} p.relationIndex) ⦋1⦌)
          (ULift.{max u v w x, max u w} p.P0))).comp
        ULift.algEquiv.symm.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, DegreeOne.degeneracyZero, MvPolynomial.aeval_X]
    simp only [relationOneInv, MvPolynomial.aeval_X]
    rfl
  exact DFunLike.congr_fun he a

private lemma relationOne_left_inv : (relationOneInv p).comp (relationOne p) = AlgHom.id _ _ := by
  apply AlgHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    change relationOneInv p (relationOne p (MvPolynomial.C a)) = MvPolynomial.C a
    rw [relationOne_C, relationOneInv_degeneracy]
    rfl
  · rintro ⟨t, α, hα⟩
    obtain rfl := surjective_end_eq_id 1 α hα
    change relationOneInv p (relationOne p (MvPolynomial.X _)) = MvPolynomial.X _
    rw [relationOne_X]
    simp only [relationOneInv, MvPolynomial.aeval_X]
    rfl

private noncomputable def relationOneEquiv :
    (relationModel p).obj (op ⦋1⦌) ≃ₐ[p.A] DegreeOne.P1 p :=
  AlgEquiv.ofAlgHom (relationOne p) (relationOneInv p)
    (relationOne_right_inv p) (relationOne_left_inv p)

private lemma relationToD_bijective (k : ℕ) (hk : k ≤ 1) :
    Function.Bijective ((relationToD p).app (op ⦋k⦌)) := by
  interval_cases k
  · refine bijective_cellDesc_app.{u, max u v w x} _ _ _ _ 0 (by decide) ?_
    rw [constantToD_zero]
    exact (DegreeOne.degreeOneCoskeleton p).zeroIso.symm.toAlgEquiv.bijective
  · have he := (relationOneEquiv p).bijective
    change Function.Bijective (ULift.down ∘
      (DegreeOne.degreeOneCoskeleton p).oneIso.hom ∘
      ((relationToD p).app (op ⦋1⦌))) at he
    exact (Function.Bijective.of_comp_iff'
      ((ULift.algEquiv (R := p.A)).bijective.comp
        (DegreeOne.degreeOneCoskeleton p).oneIso.toAlgEquiv.bijective) _).mp he

private abbrev ExtraIndex :=
  ULift.{max u v w x} (DegreeTwo.Rel p ⊕ (p.relationIndex × p.relationIndex))

private def extraVariable (i : ExtraIndex p) : DegreeTwo.DegreeTwoVariable p :=
  match i.down with
  | .inl r => .v r
  | .inr ts => .w ts.1 ts.2

private noncomputable def extraPoint (i : ExtraIndex p) : (commD p).obj (op ⦋2⦌) :=
  DegreeTwo.degreeTwoToCoskeleton p (ULift.up (MvPolynomial.X (extraVariable p i)))

private lemma exists_extraBoundary :
    ∃ b : CellBoundary.{u, max u v w x} (relationModel p) 2 (ExtraIndex p),
      ∀ (Δ : SimplexCategory) (α : Δ ⟶ ⦋2⦌)
        (hα : ¬ Function.Surjective α.toOrderHom) (i : ExtraIndex p),
        (relationToD p).app (op Δ) (b.val Δ α hα i) =
          (commD p).map α.op (extraPoint p i) :=
  exists_cellBoundary_of_bijective.{u, max u v w x} (relationToD p) 1
    (relationToD_bijective p) (extraPoint p)

private noncomputable abbrev extraBoundary := (exists_extraBoundary p).choose
private noncomputable abbrev polynomialModel := attachCells.{u, max u v w x} (extraBoundary p)

private noncomputable def polynomialToD : polynomialModel p ⟶ commD p :=
  cellDesc.{u, max u v w x} (extraBoundary p) (relationToD p) (extraPoint p)
    (exists_extraBoundary p).choose_spec

private lemma polynomial_polynomialModel (n : ℕ) :
    CommAlgCat.IsPolynomialAlgebra p.A ((polynomialModel p).obj (op ⦋n⦌)) :=
  polynomial_attachCells.{u, max u v w x} (extraBoundary p) (polynomial_relationModel p) n

private lemma surjective_sigma {n : ℕ} (i : Fin (n + 1)) :
    Function.Surjective (SimplexCategory.σ i).toOrderHom :=
  SimplexCategory.epi_iff_surjective.mp inferInstance

private lemma surjective_two_one (α : ⦋2⦌ ⟶ ⦋1⦌)
    (hα : Function.Surjective α.toOrderHom) :
    α = SimplexCategory.σ (0 : Fin 2) ∨ α = SimplexCategory.σ (1 : Fin 2) := by
  obtain ⟨i, rfl⟩ := SimplexCategory.toMk₁_surjective α
  fin_cases i <;> revert hα <;> decide

private noncomputable def relationTwo : (relationModel p).obj (op ⦋2⦌) →ₐ[p.A]
    DegreeTwo.P2 p := by
  classical
  exact MvPolynomial.aevalTower
    ((MvPolynomial.aeval (fun i => MvPolynomial.X
      (DegreeTwo.DegreeTwoVariable.base i))).comp ULift.algEquiv.toAlgHom)
    (fun t => if t.2.val = SimplexCategory.σ (0 : Fin 2) then
      MvPolynomial.X (.y t.1.down) else MvPolynomial.X (.z t.1.down))

private noncomputable def polynomialTwo : (polynomialModel p).obj (op ⦋2⦌) →ₐ[p.A]
    DegreeTwo.P2 p :=
  MvPolynomial.aevalTower (relationTwo p) (fun i => MvPolynomial.X (extraVariable p i.1))

private noncomputable def polynomialTwoInv : DegreeTwo.P2 p →ₐ[p.A]
    (polynomialModel p).obj (op ⦋2⦌) :=
  MvPolynomial.aeval fun
    | .base i => MvPolynomial.C (MvPolynomial.C (ULift.up (MvPolynomial.X i)))
    | .y t => MvPolynomial.C (MvPolynomial.X
        (ULift.up t, ⟨SimplexCategory.σ (0 : Fin 2), surjective_sigma 0⟩))
    | .z t => MvPolynomial.C (MvPolynomial.X
        (ULift.up t, ⟨SimplexCategory.σ (1 : Fin 2), surjective_sigma 1⟩))
    | .v r => MvPolynomial.X (ULift.up (Sum.inl r), ⟨𝟙 ⦋2⦌, Function.surjective_id⟩)
    | .w t t' => MvPolynomial.X (ULift.up (Sum.inr (t, t')), ⟨𝟙 ⦋2⦌, Function.surjective_id⟩)

private lemma polynomialTwo_right_inv :
    (polynomialTwo p).comp (polynomialTwoInv p) = AlgHom.id _ _ := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [polynomialTwoInv, polynomialTwo, relationTwo, extraVariable,
    show SimplexCategory.σ (1 : Fin 2) ≠ SimplexCategory.σ (0 : Fin 2) by decide]

private lemma polynomialTwoInv_base (a : p.P0) :
    polynomialTwoInv p (MvPolynomial.aeval
      (fun i => MvPolynomial.X (DegreeTwo.DegreeTwoVariable.base i)) a) =
      MvPolynomial.C (MvPolynomial.C (ULift.up a)) := by
  have he : (polynomialTwoInv p).comp (MvPolynomial.aeval
      (fun i => MvPolynomial.X (DegreeTwo.DegreeTwoVariable.base i))) =
      (IsScalarTower.toAlgHom p.A ((relationModel p).obj (op ⦋2⦌))
        (MvPolynomial (CellVariable 2 (ExtraIndex p) ⦋2⦌) ((relationModel p).obj (op ⦋2⦌)))).comp
        ((IsScalarTower.toAlgHom p.A (ULift.{max u v w x, max u w} p.P0)
          (MvPolynomial (CellVariable 1 (ULift.{max u v w x} p.relationIndex) ⦋2⦌)
            (ULift.{max u v w x, max u w} p.P0))).comp ULift.algEquiv.symm.toAlgHom) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, polynomialTwoInv]
    rfl
  exact DFunLike.congr_fun he a

private lemma polynomialTwo_left_inv :
    (polynomialTwoInv p).comp (polynomialTwo p) = AlgHom.id _ _ := by
  classical
  apply AlgHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · have he : ((polynomialTwoInv p).comp (relationTwo p)).toRingHom =
        (MvPolynomial.C : ((relationModel p).obj (op ⦋2⦌)) →+*
          (polynomialModel p).obj (op ⦋2⦌)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        change polynomialTwoInv p (relationTwo p (MvPolynomial.C a)) = _
        simp only [relationTwo, MvPolynomial.aevalTower_C, AlgHom.comp_apply]
        rw [polynomialTwoInv_base]
        rfl
      · rintro ⟨t, α, hα⟩
        rcases surjective_two_one α hα with rfl | rfl
        all_goals
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, relationTwo,
            MvPolynomial.aevalTower_X]
          simp [polynomialTwoInv,
            show SimplexCategory.σ (1 : Fin 2) ≠ SimplexCategory.σ (0 : Fin 2) by decide]
    intro a
    change polynomialTwoInv p (polynomialTwo p (MvPolynomial.C a)) = MvPolynomial.C a
    simp only [polynomialTwo, MvPolynomial.aevalTower_C]
    exact DFunLike.congr_fun he a
  · rintro ⟨i, α, hα⟩
    obtain rfl := surjective_end_eq_id 2 α hα
    change polynomialTwoInv p (polynomialTwo p (MvPolynomial.X _)) = MvPolynomial.X _
    simp only [polynomialTwo, MvPolynomial.aevalTower_X]
    rcases i with ⟨r | ⟨t, t'⟩⟩ <;> simp [extraVariable, polynomialTwoInv]

private noncomputable def polynomialTwoEquiv :
    (polynomialModel p).obj (op ⦋2⦌) ≃ₐ[p.A] DegreeTwo.P2 p :=
  AlgEquiv.ofAlgHom (polynomialTwo p) (polynomialTwoInv p)
    (polynomialTwo_right_inv p) (polynomialTwo_left_inv p)

private def commAlgForgetAlgFullyFaithful {A : Type u} [CommRing A] :
    (forget₂ (CommAlgCat.{v} A) (AlgCat.{v} A)).FullyFaithful where
  preimage f := CommAlgCat.ofHom f.hom

private lemma isCoskeletal_of_comp_fullyFaithful {C D : Type*} [Category C] [Category D]
    (X : SimplicialObject C) (n : ℕ) (G : C ⥤ D) [G.Full] [G.Faithful]
    [CategoryTheory.Limits.HasLimits D] [SimplicialObject.IsCoskeletal (X ⋙ G) n] :
    X.IsCoskeletal n := by
  have : (X ⋙ G).IsRightKanExtension
      (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ (X ⋙ G))) :=
    SimplicialObject.IsCoskeletal.isRightKanExtension
  constructor
  apply Functor.RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (E := Functor.RightExtension.mk X
      (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X)))
  intro Δ
  apply CategoryTheory.Limits.isLimitOfReflects G
  exact Limits.IsLimit.ofIsoLimit
    (Functor.isPointwiseRightKanExtensionOfIsRightKanExtension (X ⋙ G)
      (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ (X ⋙ G))) Δ)
    (Limits.Cone.ext (Iso.refl _) (by intro j; simp))

private lemma commD_isCoskeletal : (commD p).IsCoskeletal 1 := by
  let G := forget₂ (CommAlgCat.{max u v w x} p.A) (AlgCat.{max u v w x} p.A)
  have : G.Full := commAlgForgetAlgFullyFaithful.full
  have : G.Faithful := commAlgForgetAlgFullyFaithful.faithful
  have : SimplicialObject.IsCoskeletal ((commD p) ⋙ G) 1 := coskOne p
  exact isCoskeletal_of_comp_fullyFaithful (commD p) 1 G

private noncomputable def commDAugmentation : commD p ⟶
    (Functor.const _).obj (commAlgB p) where
  app Δ := by
    letI : Algebra p.A p.B := p.algebraMap.toAlgebra
    exact CommAlgCat.ofHom ((DegreeOne.degreeOneCoskeleton p).augmentation.app Δ).hom
  naturality Δ Δ' f := by
    apply CommAlgCat.hom_ext
    exact congrArg AlgCat.Hom.hom
      ((DegreeOne.degreeOneCoskeleton p).augmentation.naturality f)

private noncomputable abbrev commDOver : SimplicialObject (Over (commAlgB p)) :=
  CommAlgCat.toOverAugmentation (commDAugmentation p)

/-- The algebra category of the presentation has all limits. -/
local instance degeneraciesCommAlgCatHasLimits :
    Limits.HasLimits (CommAlgCat.{max u v w x} p.A) :=
  commAlgCatHasLimits.{u, max v w x}

private lemma commDOver_isCoskeletal : (commDOver p).IsCoskeletal 1 := by
  have := commD_isCoskeletal p
  have : (commD p).IsRightKanExtension
      (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ commD p)) :=
    SimplicialObject.IsCoskeletal.isRightKanExtension
  constructor
  apply Functor.RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (E := Functor.RightExtension.mk (commDOver p)
      (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ commDOver p)))
  intro Δ
  apply CategoryTheory.Limits.isLimitOfReflects (Over.forget (commAlgB p))
  exact Functor.isPointwiseRightKanExtensionOfIsRightKanExtension (commD p)
    (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ commD p)) Δ

private lemma polynomialToD_bijective (k : ℕ) (hk : k ≤ 1) :
    Function.Bijective ((polynomialToD p).app (op ⦋k⦌)) := by
  exact bijective_cellDesc_app.{u, max u v w x} _ _ _ _ k (by omega) (relationToD_bijective p k hk)

private noncomputable def polynomialZeroEquiv : (polynomialModel p).obj (op ⦋0⦌) ≃ₐ[p.A]
    ULift.{max u v w x, max u w} p.P0 :=
  AlgEquiv.ofBijective
    ((DegreeOne.degreeOneCoskeleton p).zeroIso.hom.hom.comp
      ((polynomialToD p).app (op ⦋0⦌)).hom)
    ((DegreeOne.degreeOneCoskeleton p).zeroIso.toAlgEquiv.bijective.comp
      (polynomialToD_bijective p 0 (by decide)))

private noncomputable def polynomialOneEquiv : (polynomialModel p).obj (op ⦋1⦌) ≃ₐ[p.A]
    ULift.{max u v w x, max u w x} (DegreeOne.P1 p) :=
  AlgEquiv.ofBijective
    ((DegreeOne.degreeOneCoskeleton p).oneIso.hom.hom.comp
      ((polynomialToD p).app (op ⦋1⦌)).hom)
    ((DegreeOne.degreeOneCoskeleton p).oneIso.toAlgEquiv.bijective.comp
      (polynomialToD_bijective p 1 (by decide)))

private lemma polynomialOneEquiv_C (z : (relationModel p).obj (op ⦋1⦌)) :
    polynomialOneEquiv p (MvPolynomial.C z) = ULift.up (relationOne p z) := by
  change (DegreeOne.degreeOneCoskeleton p).oneIso.hom
    (cellDescApp (extraBoundary p) (relationToD p) (extraPoint p) (op ⦋1⦌)
      (MvPolynomial.C z)) = _
  rw [cellDescApp_C]
  rfl

private lemma polynomialOneEquiv_symm (z : DegreeOne.P1 p) :
    (polynomialOneEquiv p).symm (ULift.up z) = MvPolynomial.C (relationOneInv p z) := by
  apply (polynomialOneEquiv p).injective
  rw [AlgEquiv.apply_symm_apply, polynomialOneEquiv_C]
  congr 1
  exact (DFunLike.congr_fun (relationOne_right_inv p) z).symm

private lemma polynomial_degeneracy_zero (z : DegreeOne.P1 p) :
    (polynomialModel p).σ (0 : Fin 2) (MvPolynomial.C (relationOneInv p z)) =
      polynomialTwoInv p (degeneracyZero p z) := by
  have he : ((polynomialModel p).σ (0 : Fin 2)).hom.comp
      ((IsScalarTower.toAlgHom p.A ((relationModel p).obj (op ⦋1⦌))
        ((polynomialModel p).obj (op ⦋1⦌))).comp (relationOneInv p)) =
      (polynomialTwoInv p).comp (degeneracyZero p) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [relationOneInv, polynomialTwoInv, degeneracyZero,
      SimplicialObject.σ, cellMap_C.{u, max u v w x}, cellMap_X.{u, max u v w x}, cellValue,
      surjective_sigma,
      constantP0]
  exact DFunLike.congr_fun he z

private lemma polynomial_degeneracy_one (z : DegreeOne.P1 p) :
    (polynomialModel p).σ (1 : Fin 2) (MvPolynomial.C (relationOneInv p z)) =
      polynomialTwoInv p (degeneracyOne p z) := by
  have he : ((polynomialModel p).σ (1 : Fin 2)).hom.comp
      ((IsScalarTower.toAlgHom p.A ((relationModel p).obj (op ⦋1⦌))
        ((polynomialModel p).obj (op ⦋1⦌))).comp (relationOneInv p)) =
      (polynomialTwoInv p).comp (degeneracyOne p) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [relationOneInv, polynomialTwoInv, degeneracyOne,
      SimplicialObject.σ, cellMap_C.{u, max u v w x}, cellMap_X.{u, max u v w x}, cellValue,
      surjective_sigma,
      constantP0]
  exact DFunLike.congr_fun he z

private lemma polynomialToD_one_inv (z : DegreeOne.P1 p) :
    (polynomialToD p).app (op ⦋1⦌) (MvPolynomial.C (relationOneInv p z)) =
      (DegreeOne.degreeOneCoskeleton p).oneIso.inv (ULift.up z) := by
  let D := DegreeOne.degreeOneCoskeleton p
  apply D.oneIso.toAlgEquiv.injective
  change polynomialOneEquiv p (MvPolynomial.C (relationOneInv p z)) =
    D.oneIso.hom (D.oneIso.inv (ULift.up z))
  rw [polynomialOneEquiv_C]
  have hz : relationOne p (relationOneInv p z) = z :=
    DFunLike.congr_fun (relationOne_right_inv p) z
  rw [hz]
  exact (ConcreteCategory.congr_hom D.oneIso.inv_hom_id (ULift.up z)).symm

/-- The cellular comparison sends the image of a lifted degeneracy to its image in the
coskeleton. -/
private lemma polynomialToD_degeneracy (i : Fin 2) (g : DegreeOne.P1 p →ₐ[p.A] DegreeTwo.P2 p)
    (hσ : ∀ z, (polynomialModel p).σ i (MvPolynomial.C (relationOneInv p z)) =
      polynomialTwoInv p (g z))
    (hl : AlgCat.ofHom (liftP p g) ≫ DegreeTwo.degreeTwoToCoskeleton p =
      (DegreeOne.degreeOneCoskeleton p).oneIso.inv ≫
        (DegreeOne.degreeOneCoskeleton p).simplicial.σ i)
    (z : DegreeOne.P1 p) :
    (polynomialToD p).app (op ⦋2⦌) (polynomialTwoInv p (g z)) =
      DegreeTwo.degreeTwoToCoskeleton p (ULift.up (g z)) := by
  have hn := ConcreteCategory.congr_hom ((polynomialToD p).naturality
    (SimplexCategory.σ i).op) (MvPolynomial.C (relationOneInv p z))
  change (polynomialToD p).app (op ⦋2⦌)
    ((polynomialModel p).σ i (MvPolynomial.C (relationOneInv p z))) =
      (DegreeOne.degreeOneCoskeleton p).simplicial.σ i
        ((polynomialToD p).app (op ⦋1⦌) (MvPolynomial.C (relationOneInv p z))) at hn
  rw [hσ, polynomialToD_one_inv] at hn
  exact hn.trans (ConcreteCategory.congr_hom hl (ULift.up z)).symm

private lemma polynomialToD_two (z : DegreeTwo.P2 p) :
    (polynomialToD p).app (op ⦋2⦌) (polynomialTwoInv p z) =
      DegreeTwo.degreeTwoToCoskeleton p (ULift.up z) := by
  have he : (((polynomialToD p).app (op ⦋2⦌)).hom.comp (polynomialTwoInv p)) =
      (DegreeTwo.degreeTwoToCoskeleton p).hom.comp ULift.algEquiv.symm.toAlgHom := by
    have h0 := polynomialToD_degeneracy p 0 _ (polynomial_degeneracy_zero p)
      (degeneracyZero_lifts p)
    have h1 := polynomialToD_degeneracy p 1 _ (polynomial_degeneracy_one p)
      (degeneracyOne_lifts p)
    apply MvPolynomial.algHom_ext
    intro i
    change (polynomialToD p).app (op ⦋2⦌) (polynomialTwoInv p (MvPolynomial.X i)) =
      DegreeTwo.degreeTwoToCoskeleton p (ULift.up (MvPolynomial.X i))
    cases i with
    | base i =>
        simpa only [degeneracyZero, MvPolynomial.aeval_X, Sum.elim_inl] using
          h0 (MvPolynomial.X (Sum.inl i))
    | y t =>
        simpa only [degeneracyZero, MvPolynomial.aeval_X, Sum.elim_inr] using
          h0 (MvPolynomial.X (Sum.inr t))
    | z t =>
        simpa only [degeneracyOne, MvPolynomial.aeval_X, Sum.elim_inr] using
          h1 (MvPolynomial.X (Sum.inr t))
    | v r =>
        simp [polynomialTwoInv, polynomialToD, cellDesc, cellDescApp_X.{u, max u v w x},
          extraPoint, extraVariable, commD]
    | w t t' =>
        simp [polynomialTwoInv, polynomialToD, cellDesc, cellDescApp_X.{u, max u v w x},
          extraPoint, extraVariable, commD]
  exact DFunLike.congr_fun he z

private lemma kan_cosk_of_map {A : Type u} [CommRing A]
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    [Limits.HasLimits (CommAlgCat.{max u v} A)]
    (X Y : SimplicialObject (Over (CommAlgCat.of A B))) (q : X ⟶ Y) (n : ℕ)
    [Y.IsCoskeletal (n + 1)]
    (hY : SSet.trivialKanFibrations (underlyingAugmentation.{u, v} Y))
    (hq : ∀ k, k ≤ n → Function.Bijective (q.app (op ⦋k⦌)).left)
    (hs : Function.Surjective (q.app (op ⦋n + 1⦌)).left) :
    SSet.trivialKanFibrations
      (underlyingAugmentation.{u, v}
        ((SimplicialObject.cosk (C := overCommAlg.{u, v} A B) (n + 1)).obj X)) := by
  obtain ⟨f, -, hfk⟩ := exists_cosk_lift X Y q n hq hs
  rw [← over_augmentation_naturality f]
  exact SSet.trivialKanFibrations_comp _ _ hfk hY

private noncomputable abbrev polynomialOver : SimplicialObject (Over (commAlgB p)) :=
  CommAlgCat.toOverAugmentation (polynomialToD p ≫ commDAugmentation p)

private noncomputable def polynomialToDOver : polynomialOver p ⟶ commDOver p where
  app Δ := Over.homMk ((polynomialToD p).app Δ) rfl
  naturality _ _ f := by
    apply Over.OverMorphism.ext
    exact (polynomialToD p).naturality f

private lemma polynomialOver_cosk_kan :
    (letI : Algebra p.A p.B := p.algebraMap.toAlgebra;
      SSet.trivialKanFibrations
        (underlyingAugmentation.{u, max v w x}
          ((SimplicialObject.cosk (C := Over (commAlgB p)) 2).obj (polynomialOver p)))) := by
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  have hD1 : (commDOver p).IsCoskeletal 1 := commDOver_isCoskeletal p
  have hD2 : (commDOver p).IsCoskeletal 2 :=
    (SimplicialObject.isCoskeletal_iff_isIso _ 2).mpr
      ((SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
        (C := Over (commAlgB p)) (by decide : 1 ≤ 2)).2.2 (commDOver p)
        ((SimplicialObject.isCoskeletal_iff_isIso _ 1).mp hD1))
  refine @kan_cosk_of_map.{u, max v w x} p.A _
    (ULift.{max u v w x, v} p.B) _ _ _ (polynomialOver p) (commDOver p)
    (polynomialToDOver p) 1 hD2 ?_ ?_ ?_
  · exact DegreeOne.coskeleton_trivialKanFibration p
  · exact polynomialToD_bijective p
  · intro a
    obtain ⟨⟨z⟩, hz⟩ := DegreeTwo.degreeTwoToCoskeleton_surjective p a
    exact ⟨polynomialTwoInv p z, (polynomialToD_two p z).trans hz⟩

private lemma exists_resolution_comparison :
    ∃ (R : SimplicialObject (Over (commAlgB p)))
      (π : R ⟶ (SimplicialObject.cosk (C := Over (commAlgB p)) 2).obj (polynomialOver p)),
      (∀ k : ℕ, CommAlgCat.IsPolynomialAlgebra p.A ((R.obj (op ⦋k⦌)).left)) ∧
      (letI : Algebra p.A p.B := p.algebraMap.toAlgebra;
        SSet.trivialKanFibrations (underlyingAugmentation.{u, max v w x} R)) ∧
      (∀ k, k ≤ 2 → IsIso (π.app (op ⦋k⦌))) := by
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  exact exists_resolution_preserving_coskeleton.{u, max v w x} 2 (polynomialOver p)
    (polynomial_polynomialModel p) (polynomialOver_cosk_kan p)

private lemma conjugate_map_of_comparison {J C : Type*} [Category J] [Category C]
    {X Y : J ⥤ C} (f : X ⟶ Y) {a b : J} (g : a ⟶ b) {A B : C}
    (e : X.obj a ≅ A) (e' : X.obj b ≅ B) (d : Y.obj a ≅ A) (d' : Y.obj b ≅ B)
    (he : e.hom = f.app a ≫ d.hom) (he' : e'.hom = f.app b ≫ d'.hom) :
    e.inv ≫ X.map g ≫ e'.hom = d.inv ≫ Y.map g ≫ d'.hom := by
  apply (cancel_epi e.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [he', he, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, f.naturality]
  simp only [Category.assoc]

/-- Two natural transformations to a common target that are invertible at `a` identify the two
values at `a`. -/
private noncomputable def comparisonIso {J C : Type*} [Category J] [Category C]
    {X Y Z : J ⥤ C} (f : X ⟶ Z) (g : Y ⟶ Z) (a : J)
    [IsIso (f.app a)] [IsIso (g.app a)] : X.obj a ≅ Y.obj a :=
  asIso (f.app a) ≪≫ (asIso (g.app a)).symm

private lemma comparisonIso_map {J C : Type*} [Category J] [Category C]
    {X Y Z : J ⥤ C} (f : X ⟶ Z) (g : Y ⟶ Z) {a b : J} (α : a ⟶ b)
    [IsIso (f.app a)] [IsIso (g.app a)] [IsIso (f.app b)] [IsIso (g.app b)] :
    (comparisonIso f g a).inv ≫ X.map α ≫ (comparisonIso f g b).hom = Y.map α := by
  apply (cancel_epi (comparisonIso f g a).hom).mp
  apply (cancel_mono (g.app b)).mp
  simp only [Iso.hom_inv_id_assoc]
  change (X.map α ≫ (f.app b ≫ inv (g.app b))) ≫ g.app b =
    ((f.app a ≫ inv (g.app a)) ≫ Y.map α) ≫ g.app b
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [g.naturality]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact f.naturality α

private noncomputable def polynomialZeroIso :
    underlying p (polynomialModel p) _⦋0⦌ ≅ DegreeOne.algP0 p :=
  (polynomialZeroEquiv p).toAlgebraIso

private noncomputable def polynomialOneIso :
    underlying p (polynomialModel p) _⦋1⦌ ≅ DegreeOne.algP1 p :=
  (polynomialOneEquiv p).toAlgebraIso

private noncomputable def polynomialTwoIso :
    underlying p (polynomialModel p) _⦋2⦌ ≅ DegreeTwo.algP2 p :=
  ((polynomialTwoEquiv p).trans ULift.algEquiv.symm).toAlgebraIso

private noncomputable abbrev polynomialComparison :
    underlying p (polynomialModel p) ⟶
      (DegreeOne.degreeOneCoskeleton p).simplicial :=
  Functor.whiskerRight (polynomialToD p)
    (forget₂ (CommAlgCat.{max u v w x} p.A) (AlgCat.{max u v w x} p.A))

private lemma polynomial_face_zero_one :
    (polynomialOneIso p).inv ≫ (underlying p (polynomialModel p)).δ (0 : Fin 2) ≫
      (polynomialZeroIso p).hom = AlgCat.ofHom (DegreeOne.faceZeroLift p) := by
  rw [← (DegreeOne.degreeOneCoskeleton p).faceZero_eq]
  exact conjugate_map_of_comparison (polynomialComparison p) (SimplexCategory.δ 0).op
    (polynomialOneIso p) (polynomialZeroIso p) _ _ rfl rfl

private lemma polynomial_face_one_one :
    (polynomialOneIso p).inv ≫ (underlying p (polynomialModel p)).δ (1 : Fin 2) ≫
      (polynomialZeroIso p).hom = AlgCat.ofHom (DegreeOne.faceOneLift p) := by
  rw [← (DegreeOne.degreeOneCoskeleton p).faceOne_eq]
  exact conjugate_map_of_comparison (polynomialComparison p) (SimplexCategory.δ 1).op
    (polynomialOneIso p) (polynomialZeroIso p) _ _ rfl rfl

private lemma polynomial_degeneracy_zero_one :
    (polynomialZeroIso p).inv ≫ (underlying p (polynomialModel p)).σ (0 : Fin 1) ≫
      (polynomialOneIso p).hom = AlgCat.ofHom (DegreeOne.degeneracyZeroLift p) := by
  rw [← (DegreeOne.degreeOneCoskeleton p).degeneracyZero_eq]
  exact conjugate_map_of_comparison (polynomialComparison p) (SimplexCategory.σ 0).op
    (polynomialZeroIso p) (polynomialOneIso p) _ _ rfl rfl

private lemma polynomial_degeneracy_two (i : Fin 2) (g : DegreeOne.P1 p →ₐ[p.A] DegreeTwo.P2 p)
    (hσ : ∀ z, (polynomialModel p).σ i (MvPolynomial.C (relationOneInv p z)) =
      polynomialTwoInv p (g z)) :
    (polynomialOneIso p).inv ≫ (underlying p (polynomialModel p)).σ i ≫
      (polynomialTwoIso p).hom = AlgCat.ofHom (liftP p g) := by
  apply AlgCat.hom_ext
  apply AlgHom.ext
  intro z
  change ULift.up (polynomialTwoEquiv p
    ((polynomialModel p).σ i ((polynomialOneEquiv p).symm z))) = ULift.up (g z.down)
  cases z with | up z =>
    rw [polynomialOneEquiv_symm, hσ]
    exact congrArg ULift.up (DFunLike.congr_fun (polynomialTwo_right_inv p) _)

private lemma polynomial_degeneracy_zero_two :
    (polynomialOneIso p).inv ≫ (underlying p (polynomialModel p)).σ (0 : Fin 2) ≫
      (polynomialTwoIso p).hom = AlgCat.ofHom (degeneracyZeroLift p) :=
  polynomial_degeneracy_two p 0 _ (polynomial_degeneracy_zero p)

private lemma polynomial_degeneracy_one_two :
    (polynomialOneIso p).inv ≫ (underlying p (polynomialModel p)).σ (1 : Fin 2) ≫
      (polynomialTwoIso p).hom = AlgCat.ofHom (degeneracyOneLift p) :=
  polynomial_degeneracy_two p 1 _ (polynomial_degeneracy_one p)

private lemma polynomial_faces_two (z : DegreeTwo.P2 p) :
    (polynomialOneEquiv p ((polynomialModel p).δ (0 : Fin 3) (polynomialTwoInv p z))).down =
        DegreeTwo.faceZero p z ∧
    (polynomialOneEquiv p ((polynomialModel p).δ (1 : Fin 3) (polynomialTwoInv p z))).down =
        DegreeTwo.faceOne p z ∧
    (polynomialOneEquiv p ((polynomialModel p).δ (2 : Fin 3) (polynomialTwoInv p z))).down =
        DegreeTwo.faceTwo p z := by
  have hn (i : Fin 3) :
      (polynomialOneEquiv p ((polynomialModel p).δ i (polynomialTwoInv p z))).down =
        DegreeTwo.coskeletonFace p i
          (DegreeTwo.degreeTwoToCoskeleton p (ULift.up z)) := by
    have h := ConcreteCategory.congr_hom
      ((polynomialToD p).naturality (SimplexCategory.δ i).op) (polynomialTwoInv p z)
    change (polynomialToD p).app (op ⦋1⦌)
      ((polynomialModel p).δ i (polynomialTwoInv p z)) =
        (commD p).δ i ((polynomialToD p).app (op ⦋2⦌) (polynomialTwoInv p z)) at h
    rw [polynomialToD_two] at h
    exact congrArg (fun a => ((DegreeOne.degreeOneCoskeleton p).oneIso.hom a).down) h
  have h := congrArg Subtype.val
    (DegreeTwo.matchingEquiv_degreeTwoToCoskeleton p z)
  rw [DegreeTwo.matchingEquiv_faces] at h
  exact ⟨(hn 0).trans (congrArg Prod.fst h),
    (hn 1).trans (congrArg (fun t => t.2.1) h),
    (hn 2).trans (congrArg (fun t => t.2.2) h)⟩

private lemma polynomial_face_zero_two :
    (polynomialTwoIso p).inv ≫ (underlying p (polynomialModel p)).δ (0 : Fin 3) ≫
      (polynomialOneIso p).hom = AlgCat.ofHom (faceZeroLift p) := by
  apply AlgCat.hom_ext
  apply AlgHom.ext
  intro z
  apply ULift.down_injective
  exact (polynomial_faces_two p z.down).1

private lemma polynomial_face_one_two :
    (polynomialTwoIso p).inv ≫ (underlying p (polynomialModel p)).δ (1 : Fin 3) ≫
      (polynomialOneIso p).hom = AlgCat.ofHom (faceOneLift p) := by
  apply AlgCat.hom_ext
  apply AlgHom.ext
  intro z
  apply ULift.down_injective
  exact (polynomial_faces_two p z.down).2.1

private lemma polynomial_face_two_two :
    (polynomialTwoIso p).inv ≫ (underlying p (polynomialModel p)).δ (2 : Fin 3) ≫
      (polynomialOneIso p).hom = AlgCat.ofHom (faceTwoLift p) := by
  apply AlgCat.hom_ext
  apply AlgHom.ext
  intro z
  apply ULift.down_injective
  exact (polynomial_faces_two p z.down).2.2

private lemma conjugate_map_trans {C : Type*} [Category C] {A B A' B' A'' B'' : C}
    (e : A ≅ A') (e' : B ≅ B') (d : A' ≅ A'') (d' : B' ≅ B'')
    (f : A ⟶ B) (g : A' ⟶ B') (h : e.inv ≫ f ≫ e'.hom = g) :
    (e ≪≫ d).inv ≫ f ≫ (e' ≪≫ d').hom = d.inv ≫ g ≫ d'.hom := by
  rw [← h]
  simp [Category.assoc]

/-- The displayed first three degrees extend to a polynomial simplicial
resolution of `B` over `A`. -/
@[stacks 09D4 "degeneracies"]
noncomputable def explicitResolution : ExplicitResolution p := Classical.choice (by
  classical
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  obtain ⟨R, π, hp, hk, hi⟩ := exists_resolution_comparison p
  let η := (SimplicialObject.coskAdj (C := Over (commAlgB p)) 2).unit.app (polynomialOver p)
  have hη (k : ℕ) (hk : k ≤ 2) : IsIso (η.app (op ⦋k⦌)) :=
    CommAlgCat.isIso_cosk_unit_app _ 2 ⦋k⦌ hk
  let e (k : ℕ) (hk : k ≤ 2) : R.obj (op ⦋k⦌) ≅ (polynomialOver p).obj (op ⦋k⦌) := by
    have := hi k hk
    have := hη k hk
    exact comparisonIso π η (op ⦋k⦌)
  let G := Over.forget (commAlgB p) ⋙
    forget₂ (CommAlgCat.{max u v w x} p.A) (AlgCat.{max u v w x} p.A)
  let E (k : ℕ) (hk : k ≤ 2) := G.mapIso (e k hk)
  have hE (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) (f : op ⦋a⦌ ⟶ op ⦋b⦌) :
      (E a ha).inv ≫ (R ⋙ G).map f ≫ (E b hb).hom =
        (underlying p (polynomialModel p)).map f := by
    have := hi a ha
    have := hi b hb
    have := hη a ha
    have := hη b hb
    change (E a ha).inv ≫ (R ⋙ G).map f ≫ (E b hb).hom =
      G.map ((polynomialOver p).map f)
    simpa [E, e, Functor.map_comp] using
      congrArg G.map (comparisonIso_map π η f)
  refine
    ⟨⟨R ⋙ Over.forget (commAlgB p),
      CommAlgCat.overAugmentation R,
      ⟨?_, hk⟩,
      E 0 (by decide) ≪≫ polynomialZeroIso p,
      E 1 (by decide) ≪≫ polynomialOneIso p,
      E 2 (by decide) ≪≫ polynomialTwoIso p,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro Δ
    exact hp Δ.unop.len
  · exact (conjugate_map_trans _ _ _ _ _ _
      (hE 1 0 (by decide) (by decide) (SimplexCategory.δ 0).op)).trans
        (polynomial_face_zero_one p)
  · exact (conjugate_map_trans _ _ _ _ _ _
      (hE 1 0 (by decide) (by decide) (SimplexCategory.δ 1).op)).trans
        (polynomial_face_one_one p)
  · exact (conjugate_map_trans _ _ _ _ _ _
      (hE 0 1 (by decide) (by decide) (SimplexCategory.σ 0).op)).trans
        (polynomial_degeneracy_zero_one p)
  · exact (conjugate_map_trans _ _ _ _ _ _
      (hE 2 1 (by decide) (by decide) (SimplexCategory.δ 0).op)).trans
        (polynomial_face_zero_two p)
  · exact (conjugate_map_trans _ _ _ _ _ _
      (hE 2 1 (by decide) (by decide) (SimplexCategory.δ 1).op)).trans
        (polynomial_face_one_two p)
  · exact (conjugate_map_trans _ _ _ _ _ _
      (hE 2 1 (by decide) (by decide) (SimplexCategory.δ 2).op)).trans
        (polynomial_face_two_two p)
  · exact (conjugate_map_trans _ _ _ _ _ _
      (hE 1 2 (by decide) (by decide) (SimplexCategory.σ 0).op)).trans
        (polynomial_degeneracy_zero_two p)
  · exact (conjugate_map_trans _ _ _ _ _ _
      (hE 1 2 (by decide) (by decide) (SimplexCategory.σ 1).op)).trans
        (polynomial_degeneracy_one_two p)
  · let D := DegreeOne.degreeOneCoskeleton p
    have hw := congrArg
      (fun f => (forget₂ (CommAlgCat.{max u v w x} p.A) (AlgCat.{max u v w x} p.A)).map f)
      (Over.w (e 0 (by decide)).inv)
    change (polynomialZeroIso p).inv ≫ (E 0 (by decide)).inv ≫
      (forget₂ (CommAlgCat.{max u v w x} p.A) (AlgCat.{max u v w x} p.A)).map
        (R.obj (op ⦋0⦌)).hom = _
    have hw' : (E 0 (by decide)).inv ≫
        (forget₂ (CommAlgCat.{max u v w x} p.A) (AlgCat.{max u v w x} p.A)).map
          (R.obj (op ⦋0⦌)).hom =
        (polynomialComparison p).app (op ⦋0⦌) ≫ D.augmentation.app (op ⦋0⦌) := by
      simp only [Functor.map_comp] at hw
      change (E 0 (by decide)).inv ≫
        (forget₂ (CommAlgCat.{max u v w x} p.A) (AlgCat.{max u v w x} p.A)).map
          (R.obj (op ⦋0⦌)).hom =
        (polynomialComparison p).app (op ⦋0⦌) ≫ D.augmentation.app (op ⦋0⦌) at hw
      exact hw
    have he : (polynomialZeroIso p).inv ≫ (polynomialComparison p).app (op ⦋0⦌) =
        D.zeroIso.inv := by
      apply (cancel_mono D.zeroIso.hom).mp
      change (polynomialZeroIso p).inv ≫ (polynomialZeroIso p).hom = _
      simp
    rw [← D.augmentation_eq]
    have hright : (polynomialZeroIso p).inv ≫
        ((polynomialComparison p).app (op ⦋0⦌) ≫ D.augmentation.app (op ⦋0⦌)) =
        D.zeroIso.inv ≫ D.augmentation.app (op ⦋0⦌) := by
      rw [← Category.assoc, he]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => (polynomialZeroIso p).inv ≫ f) hw').trans hright)
)


end Algebra.PolynomialPresentationWithKernelGenerators.Degeneracies

end
