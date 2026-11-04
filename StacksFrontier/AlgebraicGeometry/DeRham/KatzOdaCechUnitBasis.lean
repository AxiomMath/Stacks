module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechQuasiIso
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechCup

/-!
# The zeroth graded piece of `x̃` is a quasi-isomorphism when the classes form a basis

In the setting of `Stacks.KatzOda.Cech`, the map `⨁_i A[-n_i] ⟶ Tot(Č(U, Q))` sending the `i`-th
basis vector to the cocycle `x̄_i` (`Stacks.KatzOda.Cech.unitHom`) is a quasi-isomorphism as soon
as, in every degree `q`, the classes of the `x̄_i` with `n_i = q` form a basis of
`H^q(Tot(Č(U, Q)))` over `A`: its source has zero differentials, so on cohomology it is the map
`(v_i) ↦ ∑ v_i [x̄_i]`. For `Q = Ω^•_{X/Y}` this is how [Stacks, Tag 0FMP] enters the proof of
[Stacks, Tag 0FUM].

## Main results

* `Stacks.KatzOda.Cech.quasiIso_unitHom_of_bijective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.Hypercohomology (cocycleClass toMor)

universe u

namespace Stacks.KatzOda.Cech

variable {C : Type u} [Category.{u} C] [HasFiniteProducts C] {ι : Type u} [Fintype ι]
  [DecidableEq ι] {U : ι → C} {R A : CommRingCat.{u}} {gR : R ⟶ A} (D : ChartData (ι := ι) gR)
  {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ} (EP : FormsData U D D.ψ D.ψ_ρ P)
  {I : Type u} [Fintype I] [DecidableEq I] (n : I → ℕ) (x : ∀ i, TotX U P (n i))
  (hx : ∀ i, totDTo U P (n i) (n i + 1) rfl (x i) = 0)
  {Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} A) ℕ} (EQ : FormsData U D D.φ D.φ_ρ Q)

omit [DecidableEq I] in
include hx in
/-- The image under `unitHom` of a vector is a cocycle. -/
theorem d_unitMap (q : ℤ) (v : ∀ (_ : {i : I // (n i : ℤ) = q}), A) :
    ((cechTot U Q).d q (q + 1)).hom (unitMap D EP n x EQ q v) = 0 := by
  rw [cechTot_d_apply' U Q rfl]
  exact totDTo_unitMap D EP n x hx EQ q v

/-- The class in `H^q(Tot(Č(U, Q)))` of the image of `x̄_i`, for `n_i = q`. -/
def unitClass (q : ℤ) (i : {i : I // (n i : ℤ) = q}) : (cechTot U Q).homology q :=
  (cocycleClass q (toMor (unitMap D EP n x EQ q
    (Pi.single i (1 : A) : ∀ (_ : {i : I // (n i : ℤ) = q}), A)))
    (AlgebraicGeometry.DeRhamKatzOdaCech.toMor_comp_d_eq_zero _
      (d_unitMap D EP n x hx EQ q _))).hom 1

include hx in
/-- **The zeroth graded piece of `x̃` is a quasi-isomorphism** when, in every degree `q`, the
classes of the `x̄_i` with `n_i = q` form a basis of `H^q(Tot(Č(U, Q)))` over `A`. -/
theorem quasiIso_unitHom_of_bijective
    (hb : ∀ q : ℤ, Function.Bijective (fun v : ∀ (_ : {i : I // (n i : ℤ) = q}), A =>
      ∑ i, v i • unitClass D EP n x hx EQ q i)) :
    QuasiIso (unitHom D EP n x hx EQ) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let K := ShiftedSum.unitComplex A n
  have hd1 : K.d q (q + 1) = 0 := rfl
  have := K.isIso_iCycles q (q + 1) (CochainComplex.next ℤ q) hd1
  have := K.isIso_homologyπ (q - 1) q (CochainComplex.prev ℤ q) rfl
  have hcyc : (𝟙 (K.X q)) ≫ K.d q (q + 1) = 0 := by rw [Category.id_comp, hd1]
  have : IsIso (K.liftCycles (𝟙 (K.X q)) (q + 1) (CochainComplex.next ℤ q) hcyc) := by
    rw [← IsIso.inv_eq_of_inv_hom_id (K.liftCycles_i (𝟙 (K.X q)) (q + 1)
      (CochainComplex.next ℤ q) hcyc)]
    infer_instance
  have : IsIso (cocycleClass q (𝟙 (K.X q)) hcyc) := by
    unfold cocycleClass
    infer_instance
  have hcomp := Stacks.Cech.Hypercohomology.cocycleClass_comp_homologyMap
    (unitHom D EP n x hx EQ) q (𝟙 (K.X q)) hcyc
  have key : ∀ v : K.X q, (HomologicalComplex.homologyMap (unitHom D EP n x hx EQ) q).hom
      ((cocycleClass q (𝟙 (K.X q)) hcyc).hom v) = ∑ i, v i • unitClass D EP n x hx EQ q i := by
    intro v
    refine (ConcreteCategory.congr_hom hcomp v).trans ?_
    have hv : v = ∑ i, v i • (Pi.single i (1 : A) : ∀ (_ : {i : I // (n i : ℤ) = q}), A) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    exact Stacks.Cech.Hypercohomology.cocycleClass_apply_eq q _ _ _
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso
    (cocycleClass q (𝟙 (K.X q)) hcyc))).1 ((congrArg Function.Bijective (funext key)).mpr (hb q))

end Stacks.KatzOda.Cech

end
