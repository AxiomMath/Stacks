module

public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.PolyChart
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.SegreCharts
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# The standard chart ring of the Segre product

Stacks Tag 01WD still owes one isomorphism: `AlgebraicGeometry.Proj` of the Segre product
identified with the product of two projective spaces; see
`Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegre_of_projSegreIso`.  Its proof is a
chart-by-chart argument over the loci `D₊(x_i y_j)`, which cover by
`Stacks.AlgebraicGeometry.SegreCharts.iSup_basicOpen_genSub_eq_top` and are the spectra of the
degree-zero homogeneous localisations of the Segre product at the generators.  This file computes
those rings, which is the second step of that argument.

## What is proved, and the route

* `Stacks.AlgebraicGeometry.SegreChartRing.segreChartIso`: the degree-zero homogeneous
  localisation of the Segre product at the generator `x_i y_j` is the polynomial ring on the
  remaining `x` indices together with the remaining `y` indices.  The chart variables are the
  ratios `x_k / x_i` and `y_l / y_j`, realised inside the Segre product as `(x_k y_j)/(x_i y_j)`
  and `(x_i y_l)/(x_i y_j)` — `Stacks.AlgebraicGeometry.SegreChartRing.genSubQuot`.

* `Stacks.AlgebraicGeometry.SegreChartRing.segreChartTensorIso` restates it as a tensor product
  over `R` of two polynomial rings, through `MvPolynomial.tensorEquivSum`.  Combined with
  `Stacks.AlgebraicGeometry.PolyChart.chartIso`, which identifies each standard chart ring of a
  projective space with such a polynomial ring, this is the comparison of the Segre chart with
  the product of the two corresponding charts.

* The route is the one of
  `StacksFrontier/AlgebraicGeometry/SegreEmbedding/PolyChart.lean`.
  `Stacks.AlgebraicGeometry.SegreChartRing.dehomAmbient` substitutes `1` for `x_i` and for `y_j`;
  restricted to the Segre product it is
  `Stacks.AlgebraicGeometry.SegreChartRing.segreDehom`, which sends the generator to `1`, hence
  to a unit, so it extends over the localization and gives
  `Stacks.AlgebraicGeometry.SegreChartRing.fromAwayS`.
  `Stacks.AlgebraicGeometry.SegreChartRing.toAwayS` goes the other way.

* The one new ingredient over the polynomial case is
  `Stacks.AlgebraicGeometry.SegreChartRing.shiftHom_of_mem_grading`: on the degree-`n` component,
  the substitution `x_k ↦ x_k y_j`, `y_l ↦ x_i y_l` is multiplication by the `n`-th power of the
  generator.  This is where the two weights of the Segre grading are both used, and it is exactly
  what the weighted scaling identity
  `Stacks.AlgebraicGeometry.PolyChart.eval₂_mul_pow_weight_of_isWeightedHomogeneous` is for: the
  substitution multiplies each variable by `y_j ^ (weightLeft v) * x_i ^ (weightRight v)`, so
  applying that identity once for each weight produces `y_j ^ n * x_i ^ n`, which is the `n`-th
  power of `x_i y_j`.

* `Stacks.AlgebraicGeometry.SegreChartRing.val_toAwayS_segreDehom` is then the analogue of the
  polynomial case: for `a` in the degree-`n` component the image of its dehomogenisation is the
  fraction `a / (x_i y_j) ^ n`.  The total degree of such an `a` is `n + n`, which is
  `Stacks.AlgebraicGeometry.SegreChartRing.isHomogeneous_of_mem_gradePiece`, and that is the
  exponent the unweighted scaling identity contributes.

## Implementation notes

The grading of the Segre product, `Stacks.RingTheory.SegreProduct.gradingGradedAlgebra`, is a
definition rather than an instance, so it is taken here as an ordinary instance **binder**; a
local instance introduced in a *statement* does not survive into its proof.

The comparison is stated as a tensor product of two **polynomial** rings rather than of the two
chart rings, because `HomogeneousLocalization` carries an algebra structure only over the
degree-zero part of the grading and so no tensor product over `R` of two chart rings is available
without inventing one.  The identification of each factor with a chart ring is
`Stacks.AlgebraicGeometry.PolyChart.chartIso`, kept separate for the same reason.

`Stacks.RingTheory.SegreProduct.segre` is a subalgebra, so every computation is done in the
ambient polynomial ring and transferred once, as in
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegrePresentation.lean`.

## What is not done

Nothing here is geometric.  No morphism between `AlgebraicGeometry.Proj` of the Segre product and
a product of projective spaces is constructed, in either direction, and no `Spec` or scheme
appears.  Specifically, still owed for Tag 01WD:

* the comparison of the affine chart of the product of the two projective spaces with `Spec` of
  the tensor product computed here, for which `AlgebraicGeometry.pullbackSpecIso` and
  `AlgebraicGeometry.Proj.awayι` are the tools;
* the compatibility of these comparisons on the overlaps
  `D₊(x_i y_j) ∩ D₊(x_k y_l) = D₊(x_i y_j x_k y_l)`, for which
  `AlgebraicGeometry.Proj.basicOpen_mul` is the set-level statement and
  `AlgebraicGeometry.Proj.pullbackAwayιIso` the scheme-level tool;
* the gluing itself, in both directions, and that the two composites are the identity.
-/
@[expose] public section

open MvPolynomial Stacks.RingTheory.SegreProduct Stacks.AlgebraicGeometry.SegreCharts
open Stacks.AlgebraicGeometry.PolyChart

namespace Stacks.AlgebraicGeometry.SegreChartRing

universe v u

variable (R : Type u) [CommRing R] (X Y : Type v) [DecidableEq X] [DecidableEq Y]
  (i : X) (j : Y)

/-! ### Bidegree and total degree -/

omit [DecidableEq X] [DecidableEq Y] in
/-- A polynomial of bidegree `(n, n)` is homogeneous of total degree `n + n`. -/
public theorem isHomogeneous_of_mem_gradePiece {n : ℕ} {p : MvPolynomial (X ⊕ Y) R}
    (hp : p ∈ gradePiece R X Y n) : p.IsHomogeneous (n + n) := by
  intro γ hγ
  have hsplit : Finsupp.weight (1 : (X ⊕ Y) → ℕ) γ =
      Finsupp.weight (weightLeft X Y) γ + Finsupp.weight (weightRight X Y) γ := by
    rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.weight_apply,
      Finsupp.sum, Finsupp.sum, Finsupp.sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    cases v <;> simp [weightLeft, weightRight]
  rw [hsplit, hp.1 hγ, hp.2 hγ]

/-! ### Dehomogenisation at a generator -/

/-- Dehomogenisation of the ambient polynomial ring at the pair `(i, j)`: substitute `1` for
`x_i` and for `y_j`, and the corresponding chart variable for every other variable. -/
public noncomputable def dehomAmbient :
    MvPolynomial (X ⊕ Y) R →+* MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun k => if h : k = i then 1 else MvPolynomial.X (Sum.inl ⟨k, h⟩))
      (fun l => if h : l = j then 1 else MvPolynomial.X (Sum.inr ⟨l, h⟩)))

/-- Dehomogenisation fixes the constants. -/
@[simp] public theorem dehomAmbient_C (r : R) :
    dehomAmbient R X Y i j (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [dehomAmbient]

/-- Dehomogenisation at `(i, j)` sends `x_i` to `1`. -/
@[simp] public theorem dehomAmbient_X_inl_self :
    dehomAmbient R X Y i j (MvPolynomial.X (Sum.inl i)) = 1 := by
  simp [dehomAmbient]

/-- Dehomogenisation at `(i, j)` sends `y_j` to `1`. -/
@[simp] public theorem dehomAmbient_X_inr_self :
    dehomAmbient R X Y i j (MvPolynomial.X (Sum.inr j)) = 1 := by
  simp [dehomAmbient]

/-- Dehomogenisation at `(i, j)` sends `x_k`, for `k ≠ i`, to the chart variable indexed by `k`. -/
public theorem dehomAmbient_X_inl_of_ne {k : X} (h : k ≠ i) :
    dehomAmbient R X Y i j (MvPolynomial.X (Sum.inl k)) =
      MvPolynomial.X (Sum.inl ⟨k, h⟩) := by
  simp [dehomAmbient, h]

/-- Dehomogenisation at `(i, j)` sends `y_l`, for `l ≠ j`, to the chart variable indexed by `l`. -/
public theorem dehomAmbient_X_inr_of_ne {l : Y} (h : l ≠ j) :
    dehomAmbient R X Y i j (MvPolynomial.X (Sum.inr l)) =
      MvPolynomial.X (Sum.inr ⟨l, h⟩) := by
  simp [dehomAmbient, h]

/-- Dehomogenisation, restricted to the Segre product. -/
public noncomputable def segreDehom :
    segre R X Y →+* MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R :=
  (dehomAmbient R X Y i j).comp (segre R X Y).val.toRingHom

/-- `segreDehom` is `dehomAmbient` applied to the underlying polynomial. -/
public theorem segreDehom_apply (a : segre R X Y) :
    segreDehom R X Y i j a = dehomAmbient R X Y i j (a : MvPolynomial (X ⊕ Y) R) := rfl

/-- Dehomogenisation at `(i, j)` sends the generator `x_i y_j` to `1`. -/
@[simp] public theorem segreDehom_genSub :
    segreDehom R X Y i j (genSub R X Y (i, j)) = 1 := by
  rw [segreDehom_apply]
  show dehomAmbient R X Y i j (gen R X Y (i, j)) = 1
  rw [gen_eq, map_mul, dehomAmbient_X_inl_self, dehomAmbient_X_inr_self, one_mul]

/-- The dehomogenisation of the generator `x_i y_j` is a unit. -/
public theorem isUnit_segreDehom_genSub :
    IsUnit (segreDehom R X Y i j (genSub R X Y (i, j))) := by
  rw [segreDehom_genSub]
  exact isUnit_one

/-! ### Multiplying the two variable groups by the generator's complementary variable -/

/-- The ring homomorphism `x_k ↦ x_k y_j`, `y_l ↦ x_i y_l` into the Segre product. -/
public noncomputable def shiftHom : MvPolynomial (X ⊕ Y) R →+* segre R X Y :=
  MvPolynomial.eval₂Hom (algebraMap R (segre R X Y))
    (Sum.elim (fun k => genSub R X Y (k, j)) (fun l => genSub R X Y (i, l)))

/-- A constant of the Segre product is the constant polynomial in the ambient ring. -/
private theorem coe_algebraMap_segre_aux {S : Type u} [CommRing S] {P Q : Type v} (r : S) :
    ((algebraMap S (segre S P Q) r : segre S P Q) : MvPolynomial (P ⊕ Q) S) =
      MvPolynomial.C r := by
  rw [← MvPolynomial.algebraMap_eq]
  rfl

omit [DecidableEq X] [DecidableEq Y] in
/-- In the ambient polynomial ring, `shiftHom` is the substitution `x_k ↦ x_k y_j`,
`y_l ↦ x_i y_l`. -/
public theorem val_comp_shiftHom :
    (segre R X Y).val.toRingHom.comp (shiftHom R X Y i j) =
      MvPolynomial.eval₂Hom MvPolynomial.C
        (Sum.elim (fun k => gen R X Y (k, j)) (fun l => gen R X Y (i, l))) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · simp only [RingHom.comp_apply, shiftHom, MvPolynomial.eval₂Hom_C]
    exact coe_algebraMap_segre_aux r
  · cases v <;> simp [shiftHom, genSub]

omit [DecidableEq X] [DecidableEq Y] in
/-- **The key algebraic identity.**  On the degree-`n` piece, multiplying the `x` variables by
`y_j` and the `y` variables by `x_i` is multiplication by the `n`-th power of the generator
`x_i y_j`.  Both weights are used: `y_j` appears once for each `x` variable and `x_i` once for
each `y` variable, so the two weighted scaling identities give `y_j ^ n` and `x_i ^ n`. -/
public theorem shiftHom_of_mem_grading {n : ℕ} (a : segre R X Y) (ha : a ∈ grading R X Y n) :
    shiftHom R X Y i j (a : MvPolynomial (X ⊕ Y) R) = a * genSub R X Y (i, j) ^ n := by
  have hp : (a : MvPolynomial (X ⊕ Y) R) ∈ gradePiece R X Y n := ha
  refine Subtype.ext ?_
  have hval := DFunLike.congr_fun (val_comp_shiftHom R X Y i j) (a : MvPolynomial (X ⊕ Y) R)
  rw [RingHom.comp_apply] at hval
  have hcoe : ((shiftHom R X Y i j (a : MvPolynomial (X ⊕ Y) R) : segre R X Y) :
      MvPolynomial (X ⊕ Y) R) =
      MvPolynomial.eval₂ MvPolynomial.C
        (Sum.elim (fun k => gen R X Y (k, j)) (fun l => gen R X Y (i, l)))
        (a : MvPolynomial (X ⊕ Y) R) := by
    rw [← MvPolynomial.coe_eval₂Hom]
    exact hval
  have hfun : (Sum.elim (fun k => gen R X Y (k, j)) (fun l => gen R X Y (i, l)) :
      X ⊕ Y → MvPolynomial (X ⊕ Y) R) =
      fun v => MvPolynomial.X (Sum.inr j) ^ weightLeft X Y v *
        (MvPolynomial.X (Sum.inl i) ^ weightRight X Y v * MvPolynomial.X v) := by
    funext v
    cases v with
    | inl k => simp [gen_eq, weightLeft, weightRight, mul_comm]
    | inr l => simp [gen_eq, weightLeft, weightRight]
  rw [hcoe, hfun,
    eval₂_mul_pow_weight_of_isWeightedHomogeneous _ _ _ (weightLeft X Y) hp.1,
    eval₂_mul_pow_weight_of_isWeightedHomogeneous _ _ _ (weightRight X Y) hp.2,
    MvPolynomial.eval₂_eta]
  show _ = (a : MvPolynomial (X ⊕ Y) R) * (gen R X Y (i, j)) ^ n
  rw [gen_eq, mul_pow]
  ring

/-! ### The chart ring of the Segre product -/

section Away

variable [GradedAlgebra (Stacks.RingTheory.SegreProduct.grading R X Y)]

omit [DecidableEq X] [DecidableEq Y]
  [GradedAlgebra (Stacks.RingTheory.SegreProduct.grading R X Y)] in
/-- The constants lie in the degree-zero part of the Segre product. -/
public theorem algebraMap_mem_grading_zero (r : R) :
    algebraMap R (segre R X Y) r ∈ grading R X Y 0 := by
  rw [mem_grading, coe_algebraMap_segre_aux]
  exact ⟨MvPolynomial.isWeightedHomogeneous_C _ _, MvPolynomial.isWeightedHomogeneous_C _ _⟩

/-- The constants, as a ring homomorphism into the degree-zero part of the Segre product. -/
public noncomputable def constHomSegre :
    R →+* (Stacks.RingTheory.SegreProduct.grading R X Y 0) where
  toFun r := ⟨algebraMap R (segre R X Y) r, algebraMap_mem_grading_zero R X Y r⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/-- The fraction `(x_k y_l) / (x_i y_j)` in the chart ring. -/
public noncomputable def genSubQuot (p : X × Y) :
    HomogeneousLocalization.Away
      (Stacks.RingTheory.SegreProduct.grading R X Y) (genSub R X Y (i, j)) :=
  HomogeneousLocalization.Away.mk _ (genSub_mem_grading_one R X Y (i, j)) 1 (genSub R X Y p)
    (by simpa using genSub_mem_grading_one R X Y p)

/-- The comparison homomorphism from the polynomial ring on the chart variables to the chart
ring of the Segre product. -/
public noncomputable def toAwayS :
    MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R →+*
      HomogeneousLocalization.Away
        (Stacks.RingTheory.SegreProduct.grading R X Y) (genSub R X Y (i, j)) :=
  MvPolynomial.eval₂Hom
    ((HomogeneousLocalization.fromZeroRingHom _ _).comp (constHomSegre R X Y))
    (Sum.elim (fun k => genSubQuot R X Y i j (k.1, j))
      (fun l => genSubQuot R X Y i j (i, l.1)))

/-- The comparison homomorphism back, through the localization of the Segre product. -/
public noncomputable def fromAwayS :
    HomogeneousLocalization.Away
        (Stacks.RingTheory.SegreProduct.grading R X Y) (genSub R X Y (i, j)) →+*
      MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R :=
  (Localization.awayLift (segreDehom R X Y i j) (genSub R X Y (i, j))
      (isUnit_segreDehom_genSub R X Y i j)).comp
    (algebraMap (HomogeneousLocalization.Away
      (Stacks.RingTheory.SegreProduct.grading R X Y) (genSub R X Y (i, j)))
      (Localization.Away (genSub R X Y (i, j))))

end Away

/-! ### The two composites -/

/-- `1 / (x_i y_j)`, in the localization of the Segre product at the generator. -/
public noncomputable def invGen :
    Localization.Away (genSub R X Y (i, j)) :=
  IsLocalization.Away.invSelf (genSub R X Y (i, j))

omit [DecidableEq X] [DecidableEq Y] in
/-- `invGen` is the fraction `1 / (x_i y_j)`. -/
public theorem invGen_eq_mk' :
    invGen R X Y i j = IsLocalization.mk' _ 1
      (⟨genSub R X Y (i, j), Submonoid.mem_powers _⟩ :
        Submonoid.powers (genSub R X Y (i, j))) := rfl

omit [DecidableEq X] [DecidableEq Y] in
/-- The generator `x_i y_j` times `invGen` is `1` in the localization. -/
public theorem algebraMap_genSub_mul_invGen :
    algebraMap (segre R X Y) (Localization.Away (genSub R X Y (i, j))) (genSub R X Y (i, j)) *
      invGen R X Y i j = 1 :=
  IsLocalization.Away.mul_invSelf _

section Away2

variable [GradedAlgebra (Stacks.RingTheory.SegreProduct.grading R X Y)]

omit [DecidableEq X] [DecidableEq Y] in
/-- In the localization, `genSubQuot p` is `invGen` times the image of the generator at `p`. -/
public theorem val_genSubQuot (p : X × Y) :
    (genSubQuot R X Y i j p).val = invGen R X Y i j *
      algebraMap (segre R X Y) (Localization.Away (genSub R X Y (i, j))) (genSub R X Y p) := by
  rw [genSubQuot, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply,
    invGen_eq_mk', mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  exact Subtype.ext (pow_one _)

omit [DecidableEq X] [DecidableEq Y] in
/-- `toAwayS` sends a constant to its image in the localization. -/
public theorem val_toAwayS_C (r : R) :
    (toAwayS R X Y i j (MvPolynomial.C r)).val =
      algebraMap (segre R X Y) (Localization.Away (genSub R X Y (i, j)))
        (algebraMap R (segre R X Y) r) := by
  rw [toAwayS, MvPolynomial.eval₂Hom_C]
  exact Localization.mk_one_eq_algebraMap _

/-- The ambient evaluation sending each variable to its ratio with the generator. -/
public noncomputable def evalInvGen :
    MvPolynomial (X ⊕ Y) R →+* Localization.Away (genSub R X Y (i, j)) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (segre R X Y) (Localization.Away (genSub R X Y (i, j)))).comp
      (algebraMap R (segre R X Y)))
    (fun v => invGen R X Y i j *
      algebraMap (segre R X Y) (Localization.Away (genSub R X Y (i, j)))
        (Sum.elim (fun k => genSub R X Y (k, j)) (fun l => genSub R X Y (i, l)) v))

/-- Dehomogenising at `(i, j)` and then mapping into the chart ring agrees, in the localization,
with dividing each variable by the generator. -/
public theorem comp_toAwayS_dehomAmbient_eq :
    (algebraMap (HomogeneousLocalization.Away
        (Stacks.RingTheory.SegreProduct.grading R X Y) (genSub R X Y (i, j)))
      (Localization.Away (genSub R X Y (i, j)))).comp
        ((toAwayS R X Y i j).comp (dehomAmbient R X Y i j)) = evalInvGen R X Y i j := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · simp only [RingHom.comp_apply, dehomAmbient_C, evalInvGen, MvPolynomial.eval₂Hom_C,
      HomogeneousLocalization.algebraMap_apply]
    exact val_toAwayS_C R X Y i j r
  · simp only [RingHom.comp_apply, evalInvGen, MvPolynomial.eval₂Hom_X',
      HomogeneousLocalization.algebraMap_apply]
    cases v with
    | inl k =>
      by_cases h : k = i
      · subst h
        rw [dehomAmbient_X_inl_self, map_one, HomogeneousLocalization.val_one, Sum.elim_inl,
          mul_comm]
        exact (algebraMap_genSub_mul_invGen R X Y k j).symm
      · rw [dehomAmbient_X_inl_of_ne R X Y i j h, toAwayS, MvPolynomial.eval₂Hom_X',
          Sum.elim_inl, Sum.elim_inl]
        exact val_genSubQuot R X Y i j (k, j)
    | inr l =>
      by_cases h : l = j
      · subst h
        rw [dehomAmbient_X_inr_self, map_one, HomogeneousLocalization.val_one, Sum.elim_inr,
          mul_comm]
        exact (algebraMap_genSub_mul_invGen R X Y i l).symm
      · rw [dehomAmbient_X_inr_of_ne R X Y i j h, toAwayS, MvPolynomial.eval₂Hom_X',
          Sum.elim_inr, Sum.elim_inr]
        exact val_genSubQuot R X Y i j (i, l)

omit [DecidableEq X] [DecidableEq Y]
  [GradedAlgebra (Stacks.RingTheory.SegreProduct.grading R X Y)] in
/-- Sending each variable to the image of its generator in the localization is `shiftHom`
followed by the localization map. -/
public theorem evalInvGen_base_eq :
    MvPolynomial.eval₂Hom
      ((algebraMap (segre R X Y) (Localization.Away (genSub R X Y (i, j)))).comp
        (algebraMap R (segre R X Y)))
      (fun v => algebraMap (segre R X Y) (Localization.Away (genSub R X Y (i, j)))
        (Sum.elim (fun k => genSub R X Y (k, j)) (fun l => genSub R X Y (i, l)) v)) =
      (algebraMap (segre R X Y)
        (Localization.Away (genSub R X Y (i, j)))).comp (shiftHom R X Y i j) := by
  refine MvPolynomial.ringHom_ext (fun _ => ?_) (fun _ => ?_) <;> simp [shiftHom]

/-- **The chart ring of the Segre product receives every homogeneous fraction.**  For `a` in the
degree-`n` component, the image of its dehomogenisation is the fraction `a / (x_i y_j) ^ n`. -/
public theorem val_toAwayS_segreDehom {n : ℕ} (a : segre R X Y) (ha : a ∈ grading R X Y n) :
    (toAwayS R X Y i j (segreDehom R X Y i j a)).val =
      Localization.mk a (⟨genSub R X Y (i, j) ^ n, n, rfl⟩ :
        Submonoid.powers (genSub R X Y (i, j))) := by
  have h := DFunLike.congr_fun (comp_toAwayS_dehomAmbient_eq R X Y i j)
    (a : MvPolynomial (X ⊕ Y) R)
  rw [RingHom.comp_apply, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply] at h
  have hbase := DFunLike.congr_fun (evalInvGen_base_eq R X Y i j) (a : MvPolynomial (X ⊕ Y) R)
  rw [RingHom.comp_apply, shiftHom_of_mem_grading R X Y i j a ha] at hbase
  have hp : (a : MvPolynomial (X ⊕ Y) R) ∈ gradePiece R X Y n := ha
  have hhom : (a : MvPolynomial (X ⊕ Y) R).IsHomogeneous (n + n) :=
    isHomogeneous_of_mem_gradePiece R X Y hp
  rw [segreDehom_apply, h, evalInvGen, MvPolynomial.coe_eval₂Hom,
    eval₂_mul_left_of_isHomogeneous _ _ _ hhom,
    ← MvPolynomial.coe_eval₂Hom, hbase, map_mul, map_pow,
    Localization.mk_eq_mk'_apply, IsLocalization.eq_mk'_iff_mul_eq]
  have hcoe : ((⟨genSub R X Y (i, j) ^ n, n, rfl⟩ :
      Submonoid.powers (genSub R X Y (i, j))) : segre R X Y) =
      genSub R X Y (i, j) ^ n := rfl
  rw [hcoe, map_pow]
  have hunit : invGen R X Y i j ^ (n + n) *
      algebraMap (segre R X Y) (Localization.Away (genSub R X Y (i, j)))
        (genSub R X Y (i, j)) ^ (n + n) = 1 := by
    rw [← mul_pow, mul_comm, algebraMap_genSub_mul_invGen, one_pow]
  linear_combination
    algebraMap (segre R X Y) (Localization.Away (genSub R X Y (i, j))) a * hunit

end Away2

/-! ### The chart ring is a polynomial ring -/

omit [DecidableEq X] [DecidableEq Y] in
/-- A constant of the Segre product is the constant polynomial in the ambient ring. -/
public theorem coe_algebraMap_segre (r : R) :
    ((algebraMap R (segre R X Y) r : segre R X Y) : MvPolynomial (X ⊕ Y) R) =
      MvPolynomial.C r :=
  coe_algebraMap_segre_aux r

/-- Dehomogenisation at `(i, j)` sends the generator `x_k y_j` to the chart variable `k`. -/
public theorem segreDehom_genSub_inl (k : {k : X // k ≠ i}) :
    segreDehom R X Y i j (genSub R X Y (k.1, j)) = MvPolynomial.X (Sum.inl k) := by
  rw [segreDehom_apply]
  show dehomAmbient R X Y i j (gen R X Y (k.1, j)) = _
  rw [gen_eq, map_mul, dehomAmbient_X_inl_of_ne R X Y i j k.2, dehomAmbient_X_inr_self, mul_one]

/-- Dehomogenisation at `(i, j)` sends the generator `x_i y_l` to the chart variable `l`. -/
public theorem segreDehom_genSub_inr (l : {l : Y // l ≠ j}) :
    segreDehom R X Y i j (genSub R X Y (i, l.1)) = MvPolynomial.X (Sum.inr l) := by
  rw [segreDehom_apply]
  show dehomAmbient R X Y i j (gen R X Y (i, l.1)) = _
  rw [gen_eq, map_mul, dehomAmbient_X_inl_self, dehomAmbient_X_inr_of_ne R X Y i j l.2, one_mul]

/-- The lift of `segreDehom` to the localization sends `a / (x_i y_j) ^ n` to the
dehomogenisation of `a`. -/
public theorem awayLift_segreDehom_mk (a : segre R X Y) (n : ℕ) :
    Localization.awayLift (segreDehom R X Y i j) (genSub R X Y (i, j))
        (isUnit_segreDehom_genSub R X Y i j)
        (Localization.mk a (⟨genSub R X Y (i, j) ^ n, n, rfl⟩ :
          Submonoid.powers (genSub R X Y (i, j)))) = segreDehom R X Y i j a := by
  rw [Localization.awayLift_mk (segreDehom R X Y i j) (genSub R X Y (i, j)) a 1
    (by rw [segreDehom_genSub, mul_one]) n, one_pow, mul_one]

section Away3

variable [GradedAlgebra (Stacks.RingTheory.SegreProduct.grading R X Y)]

/-- The chart ring maps onto the polynomial ring on the chart variables, with the comparison
homomorphism as a section. -/
public theorem fromAwayS_comp_toAwayS :
    (fromAwayS R X Y i j).comp (toAwayS R X Y i j) =
      RingHom.id (MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · simp only [RingHom.comp_apply, RingHom.id_apply, fromAwayS,
      HomogeneousLocalization.algebraMap_apply, val_toAwayS_C]
    rw [IsLocalization.Away.lift_eq, segreDehom_apply, coe_algebraMap_segre, dehomAmbient_C]
  · simp only [RingHom.comp_apply, RingHom.id_apply, fromAwayS,
      HomogeneousLocalization.algebraMap_apply, toAwayS, MvPolynomial.eval₂Hom_X']
    cases v with
    | inl k =>
      rw [Sum.elim_inl, genSubQuot, HomogeneousLocalization.Away.val_mk,
        awayLift_segreDehom_mk R X Y i j (genSub R X Y (k.1, j)) 1, segreDehom_genSub_inl]
    | inr l =>
      rw [Sum.elim_inr, genSubQuot, HomogeneousLocalization.Away.val_mk,
        awayLift_segreDehom_mk R X Y i j (genSub R X Y (i, l.1)) 1, segreDehom_genSub_inr]

/-- Every element of the chart ring is the image of its own dehomogenisation. -/
public theorem toAwayS_fromAwayS
    (z : HomogeneousLocalization.Away
      (Stacks.RingTheory.SegreProduct.grading R X Y) (genSub R X Y (i, j))) :
    toAwayS R X Y i j (fromAwayS R X Y i j z) = z := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (genSub_mem_grading_one R X Y (i, j)) z
  have ha' : a ∈ Stacks.RingTheory.SegreProduct.grading R X Y n := by simpa using ha
  have hfrom : fromAwayS R X Y i j
      (HomogeneousLocalization.Away.mk _ (genSub_mem_grading_one R X Y (i, j)) n a ha) =
      segreDehom R X Y i j a := by
    simp only [fromAwayS, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk]
    exact awayLift_segreDehom_mk R X Y i j a n
  rw [hfrom]
  apply HomogeneousLocalization.val_injective
  rw [val_toAwayS_segreDehom R X Y i j a ha', HomogeneousLocalization.Away.val_mk]

/-- **The standard chart ring of the Segre product.**  The degree-zero homogeneous localisation of
the Segre product at the generator `x_i y_j` is the polynomial ring on the remaining `x` indices
together with the remaining `y` indices: the chart variables are the ratios `x_k / x_i` and
`y_l / y_j`, realised as `(x_k y_j) / (x_i y_j)` and `(x_i y_l) / (x_i y_j)`. -/
public noncomputable def segreChartIso :
    HomogeneousLocalization.Away
        (Stacks.RingTheory.SegreProduct.grading R X Y) (genSub R X Y (i, j)) ≃+*
      MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R where
  toFun := fromAwayS R X Y i j
  invFun := toAwayS R X Y i j
  left_inv := toAwayS_fromAwayS R X Y i j
  right_inv p := DFunLike.congr_fun (fromAwayS_comp_toAwayS R X Y i j) p
  map_mul' x y := map_mul _ x y
  map_add' x y := map_add _ x y

/-- `segreChartIso` is `fromAwayS`. -/
@[simp] public theorem segreChartIso_apply
    (z : HomogeneousLocalization.Away
      (Stacks.RingTheory.SegreProduct.grading R X Y) (genSub R X Y (i, j))) :
    segreChartIso R X Y i j z = fromAwayS R X Y i j z := rfl

/-- The inverse of `segreChartIso` is `toAwayS`. -/
@[simp] public theorem segreChartIso_symm_apply
    (p : MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R) :
    (segreChartIso R X Y i j).symm p = toAwayS R X Y i j p := rfl

/-- **The chart ring of the Segre product is the tensor product of the two chart rings.**  The
degree-zero homogeneous localisation of the Segre product at `x_i y_j` is the tensor product over
`R` of the polynomial ring on the remaining `x` indices with the polynomial ring on the remaining
`y` indices.  By `Stacks.AlgebraicGeometry.PolyChart.chartIso` those two factors are the standard
chart rings of the two projective spaces, so this is the comparison the chart-by-chart
identification of `Proj` of the Segre product with a product of projective spaces needs. -/
public noncomputable def segreChartTensorIso :
    HomogeneousLocalization.Away
        (Stacks.RingTheory.SegreProduct.grading R X Y) (genSub R X Y (i, j)) ≃+*
      TensorProduct R (MvPolynomial {k : X // k ≠ i} R) (MvPolynomial {l : Y // l ≠ j} R) :=
  (segreChartIso R X Y i j).trans
    (MvPolynomial.tensorEquivSum R {k : X // k ≠ i} {l : Y // l ≠ j} R).symm.toRingEquiv

end Away3

end Stacks.AlgebraicGeometry.SegreChartRing

end
