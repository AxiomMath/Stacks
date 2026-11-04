module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamPerturbation
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BidegreeFiltration
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincareSpecial
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelTransition
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential.Splitting

/-!
# The splitting `d = d_rel + d_base` over the `p`-adic completion

Part of `StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential`, whose
module docstring explains the construction.  This file contains the completion of an additive map
over a finite sum (`Crystalline.PAdicCompletion.mapAddHom_sum`) and the `p`-adic completions of the
bidegree projections and of the relative and base differentials, with the completed splitting, the
completed square-zero identity and the completed projection identities.
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW uM

namespace Crystalline

/-! ### The completion of an additive map over a finite sum -/

namespace PAdicCompletion

/-- **The completion of a finite sum of additive maps is the sum of their completions**, by
`Crystalline.PAdicCompletion.mapAddHom_add` and induction on the index set. -/
theorem mapAddHom_sum (p : ℕ) (R : Type*) [CommRing R] (S : Type*) [CommRing S] {X : Type*}
    [AddCommGroup X] [Module R X] {Y : Type*} [AddCommGroup Y] [Module S Y] {iota : Type*}
    (s : Finset iota) (f : iota → (X →+ Y)) :
    mapAddHom p R S (∑ i ∈ s, f i) = ∑ i ∈ s, mapAddHom p R S (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa only [Finset.sum_empty] using mapAddHom_zero p R S
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, mapAddHom_add, ih]

end PAdicCompletion

namespace DividedPowerPolynomial

/-! ### The splitting over the `p`-adic completion -/

section Completed

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W] (p : ℕ)

/-- **The projection of `Ω̂ⁿ_{D'}` onto the forms with `i` coefficient differentials**, the
`p`-adic completion of `Crystalline.DividedPowerPolynomial.formsBidegreeProjection`. -/
def completedFormsBidegreeProjection (n i : ℕ) :
    completedPolynomialForms A B W p n →+ completedPolynomialForms A B W p n :=
  PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (formsBidegreeProjection A B W n i).toAddMonoidHom

/-- The completed projection, unfolded, with every argument explicit; see
`Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_eq` for why this is a
lemma. -/
theorem completedFormsBidegreeProjection_eq (n i : ℕ) :
    completedFormsBidegreeProjection A B W p n i =
      PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
        (setIndexedDividedPowerPolynomialAlgebra B W)
        (formsBidegreeProjection A B W n i).toAddMonoidHom :=
  rfl

/-- The completed projection extends the uncompleted one. -/
@[simp] theorem completedFormsBidegreeProjection_of (n i : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    completedFormsBidegreeProjection A B W p n i (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (formsBidegreeProjection A B W n i x) :=
  PAdicCompletion.mapAddHom_of p _ _ _ x

/-- **The relative part of the de Rham differential of `Ω̂^*_{D'}`**, the `p`-adic completion of
`Crystalline.DividedPowerPolynomial.formsRelDifferentialAux`.

It is produced as an additive map; its `B`-linearity
(`Crystalline.DividedPowerPolynomial.formsRelDifferentialAux_smul`) is recorded over the `p`-adic
completion `D` of `B` by
`Crystalline.DividedPowerPolynomial.completedFormsRelDifferentialₗ`, once the `D`-module
structure of `Ω̂ⁿ_{D'}` is installed. -/
def completedFormsRelDifferential (n : ℕ) :
    completedPolynomialForms A B W p n →+ completedPolynomialForms A B W p (n + 1) :=
  PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (formsRelDifferentialAux A B W n).toAddMonoidHom

/-- The completed relative differential, unfolded. -/
theorem completedFormsRelDifferential_eq (n : ℕ) :
    completedFormsRelDifferential A B W p n =
      PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
        (setIndexedDividedPowerPolynomialAlgebra B W)
        (formsRelDifferentialAux A B W n).toAddMonoidHom :=
  rfl

/-- The completed relative differential extends the uncompleted one. -/
@[simp] theorem completedFormsRelDifferential_of (n : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    completedFormsRelDifferential A B W p n (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (formsRelDifferentialAux A B W n x) :=
  PAdicCompletion.mapAddHom_of p _ _ _ x

/-- **The base part of the de Rham differential of `Ω̂^*_{D'}`**, the `p`-adic completion of
`Crystalline.DividedPowerPolynomial.formsBaseDifferential`. -/
def completedFormsBaseDifferential (n : ℕ) :
    completedPolynomialForms A B W p n →+ completedPolynomialForms A B W p (n + 1) :=
  PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (formsBaseDifferential A B W n).toAddMonoidHom

/-- The completed base differential, unfolded. -/
theorem completedFormsBaseDifferential_eq (n : ℕ) :
    completedFormsBaseDifferential A B W p n =
      PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
        (setIndexedDividedPowerPolynomialAlgebra B W)
        (formsBaseDifferential A B W n).toAddMonoidHom :=
  rfl

/-- The completed base differential extends the uncompleted one. -/
@[simp] theorem completedFormsBaseDifferential_of (n : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    completedFormsBaseDifferential A B W p n (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (formsBaseDifferential A B W n x) :=
  PAdicCompletion.mapAddHom_of p _ _ _ x

/-- **`d = d_rel + d_base` on `Ω̂^*_{D'}`**: the splitting of the de Rham differential survives the
`p`-adic completion, every map in it being the completion of its uncompleted counterpart. -/
theorem completedDividedPowerDeRham_eq_completedFormsRelDifferential_add (n : ℕ)
    (x : completedPolynomialForms A B W p n) :
    completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W) n x =
      completedFormsRelDifferential A B W p n x + completedFormsBaseDifferential A B W p n x := by
  have huncomp : dividedPowerDeRhamHom (A := A)
        (setIndexedDividedPowerPolynomialDividedPowers B W) n =
      (formsRelDifferentialAux A B W n).toAddMonoidHom +
        (formsBaseDifferential A B W n).toAddMonoidHom :=
      by
    refine AddMonoidHom.ext fun y ↦ ?_
    rw [dividedPowerDeRhamHom_apply, AddMonoidHom.add_apply, LinearMap.toAddMonoidHom_coe,
      LinearMap.toAddMonoidHom_coe]
    exact dividedPowerDeRham_eq_formsRelDifferential_add A B W n y
  have hcomp : completedDividedPowerDeRham p A
        (setIndexedDividedPowerPolynomialDividedPowers B W) n =
      completedFormsRelDifferential A B W p n + completedFormsBaseDifferential A B W p n := by
    rw [completedFormsRelDifferential_eq, completedFormsBaseDifferential_eq,
      completedDividedPowerDeRham_eq_mapAddHom, huncomp]
    exact PAdicCompletion.mapAddHom_add p (setIndexedDividedPowerPolynomialAlgebra B W)
      (setIndexedDividedPowerPolynomialAlgebra B W)
      (formsRelDifferentialAux A B W n).toAddMonoidHom
      (formsBaseDifferential A B W n).toAddMonoidHom
  exact DFunLike.congr_fun hcomp x

/-- **`d_rel² = 0` on `Ω̂^*_{D'}`.** -/
theorem completedFormsRelDifferential_comp_completedFormsRelDifferential (n : ℕ) :
    (completedFormsRelDifferential A B W p (n + 1)).comp
      (completedFormsRelDifferential A B W p n) = 0 :=
  PAdicCompletion.mapAddHom_comp_eq_zero p (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (formsRelDifferentialAux A B W n).toAddMonoidHom
    (formsRelDifferentialAux A B W (n + 1)).toAddMonoidHom _ _
    (completedFormsRelDifferential_eq A B W p n)
    (completedFormsRelDifferential_eq A B W p (n + 1))
    (AddMonoidHom.ext fun y ↦ formsRelDifferentialAux_formsRelDifferentialAux A B W n y)

/-- **`d_rel² = 0` on `Ω̂^*_{D'}`**, elementwise. -/
theorem completedFormsRelDifferential_completedFormsRelDifferential (n : ℕ)
    (x : completedPolynomialForms A B W p n) :
    completedFormsRelDifferential A B W p (n + 1)
      (completedFormsRelDifferential A B W p n x) = 0 :=
  DFunLike.congr_fun (completedFormsRelDifferential_comp_completedFormsRelDifferential
    A B W p n) x

/-- **The coefficient-degree projections of `Ω̂ⁿ_{D'}` sum to the identity.**  This is the
`hprojsum` hypothesis of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` at the
completed forms. -/
theorem completedFormsBidegreeProjection_sum (n : ℕ)
    (x : completedPolynomialForms A B W p n) :
    ∑ i ∈ Finset.range (n + 1), completedFormsBidegreeProjection A B W p n i x = x := by
  have huncomp : (∑ i ∈ Finset.range (n + 1),
        (formsBidegreeProjection A B W n i).toAddMonoidHom) =
      AddMonoidHom.id (dividedPowerPolynomialForms A B W n) := by
    refine AddMonoidHom.ext fun y ↦ ?_
    simpa only [AddMonoidHom.finset_sum_apply, LinearMap.toAddMonoidHom_coe,
      AddMonoidHom.id_apply] using formsBidegreeProjection_sum A B W n y
  have hcomp : (∑ i ∈ Finset.range (n + 1), completedFormsBidegreeProjection A B W p n i) =
      AddMonoidHom.id (completedPolynomialForms A B W p n) := by
    rw [show (∑ i ∈ Finset.range (n + 1), completedFormsBidegreeProjection A B W p n i) =
        PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
          (setIndexedDividedPowerPolynomialAlgebra B W)
          (∑ i ∈ Finset.range (n + 1),
            (formsBidegreeProjection A B W n i).toAddMonoidHom) from
      (PAdicCompletion.mapAddHom_sum p _ _ _ _).symm, huncomp,
      PAdicCompletion.mapAddHom_id]
  simpa only [AddMonoidHom.finset_sum_apply, AddMonoidHom.id_apply] using
    DFunLike.congr_fun hcomp x

/-- **The base part of the differential of `Ω̂^*_{D'}` strictly raises the coefficient degree.**
This is the `hprojbase` hypothesis of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` at the completed forms. -/
theorem completedFormsBidegreeProjection_completedFormsBaseDifferential_eq_zero (n : ℕ)
    {l i : ℕ} (hli : l ≤ i) (x : completedPolynomialForms A B W p n) :
    completedFormsBidegreeProjection A B W p (n + 1) l
      (completedFormsBaseDifferential A B W p n
        (completedFormsBidegreeProjection A B W p n i x)) = 0 := by
  have hzero : ((formsBidegreeProjection A B W (n + 1) l).toAddMonoidHom.comp
      ((formsBaseDifferential A B W n).toAddMonoidHom.comp
        (formsBidegreeProjection A B W n i).toAddMonoidHom)) = 0 :=
    AddMonoidHom.ext fun y ↦
      formsBidegreeProjection_formsBaseDifferential_eq_zero A B W n hli y
  have hinner : (completedFormsBaseDifferential A B W p n).comp
      (completedFormsBidegreeProjection A B W p n i) =
      PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
        (setIndexedDividedPowerPolynomialAlgebra B W)
        ((formsBaseDifferential A B W n).toAddMonoidHom.comp
          (formsBidegreeProjection A B W n i).toAddMonoidHom) :=
    (PAdicCompletion.mapAddHom_comp p (setIndexedDividedPowerPolynomialAlgebra B W)
      (setIndexedDividedPowerPolynomialAlgebra B W)
      (setIndexedDividedPowerPolynomialAlgebra B W) _ _).symm
  have hcomp := PAdicCompletion.mapAddHom_comp_eq_zero p
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    ((formsBaseDifferential A B W n).toAddMonoidHom.comp
      (formsBidegreeProjection A B W n i).toAddMonoidHom)
    (formsBidegreeProjection A B W (n + 1) l).toAddMonoidHom _ _ hinner
    (completedFormsBidegreeProjection_eq A B W p (n + 1) l) hzero
  exact DFunLike.congr_fun hcomp x

/-- **The completed relative homotopy `ĥ` preserves the coefficient degree**: it commutes with
every coefficient-degree projection of `Ω̂^*_{D'}`.  This is the `hprojhhat` hypothesis of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` at the completed forms. -/
theorem completedRelativeFormsHomotopy_completedFormsBidegreeProjection (n i : ℕ)
    (x : completedPolynomialForms A B W p (n + 1)) :
    completedRelativeFormsHomotopy A B W p n
        (completedFormsBidegreeProjection A B W p (n + 1) i x) =
      completedFormsBidegreeProjection A B W p n i
        (completedRelativeFormsHomotopy A B W p n x) := by
  have hcomp := PAdicCompletion.mapAddHom_comm_square p _ _
    (relativeFormsHomotopy A B W n).toAddMonoidHom
    (formsBidegreeProjection A B W (n + 1) i).toAddMonoidHom
    (formsBidegreeProjection A B W n i).toAddMonoidHom
    (relativeFormsHomotopy A B W n).toAddMonoidHom _ _ _ _
    (completedRelativeFormsHomotopy_eq A B W p n)
    (completedFormsBidegreeProjection_eq A B W p (n + 1) i)
    (completedFormsBidegreeProjection_eq A B W p n i)
    (completedRelativeFormsHomotopy_eq A B W p n)
    (AddMonoidHom.ext fun y ↦ (relativeFormsHomotopy_formsBidegreeProjection A B W n i y).symm)
  exact (DFunLike.congr_fun hcomp x).symm

end Completed

end DividedPowerPolynomial

end Crystalline

end
