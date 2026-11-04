module

public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.SegreChartRing
public import StacksFrontier.AlgebraicGeometry.SegreProjection.Substitution

/-!
# The Segre chart ring, as the tensor product of the two chart rings it receives

`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegreChartRing.lean` proves that the degree-zero
homogeneous localisation of the Segre product at the generator `x_i y_j` is the tensor product
over `R` of two polynomial rings,
`Stacks.AlgebraicGeometry.SegreChartRing.segreChartTensorIso`.  What that file does *not* say is
which pair of ring homomorphisms into the Segre chart ring the tensor-product structure belongs
to, and without that the isomorphism says nothing about the two Segre projections.  This file
supplies the missing identification: the two structure maps are the maps of degree-zero
localisations induced by the two substitutions, which are exactly the maps
`Stacks.AlgebraicGeometry.SegreGlue.ι_projLeftGlued` and its mirror image exhibit as the
projections on the chart `D₊(x_i y_j)`.

## Main definitions

* `Stacks.AlgebraicGeometry.SegreChartProduct.awayCongr`: an equality of elements of a graded ring
  transports its degree-zero homogeneous localisation.

* `Stacks.AlgebraicGeometry.SegreChartProduct.chartMapLeft` and
  `Stacks.AlgebraicGeometry.SegreChartProduct.chartMapRight`: the two chart maps
  `R[x]_{(x_i)} → S_{(x_i y_j)}` and `R[y]_{(y_j)} → S_{(x_i y_j)}`, i.e.
  `HomogeneousLocalization.Away.map` of the two substitutions, read at `genSub R X Y (i, j)`.

## Main results

* `Stacks.AlgebraicGeometry.SegreChartProduct.segreDehom_substLeft`: the ring-theoretic heart.
  Dehomogenising at `(i, j)` after substituting `x_k ↦ x_k y_j` is renaming into the left summand
  after dehomogenising at `i`.  **No homogeneity hypothesis is needed**: both sides are ring
  homomorphisms out of `MvPolynomial X R` and agree on the constants and the variables, because
  `dehomAmbient` sends `y_j` to `1`.  The mirror image is
  `Stacks.AlgebraicGeometry.SegreChartProduct.segreDehom_substRight`.

* `Stacks.AlgebraicGeometry.SegreChartProduct.fromAwayS_chartMapLeft`: consequently the chart
  isomorphism `Stacks.AlgebraicGeometry.SegreChartRing.segreChartIso` carries the left chart map
  to the renaming `MvPolynomial.rename Sum.inl`, i.e. the square

  ```
  R[x]_{(x_i)} ---chartMapLeft---> S_{(x_i y_j)}
      |                                 |
   chartIso                        segreChartIso
      v                                 v
  R[x_k/x_i] ---rename Sum.inl---> R[x_k/x_i, y_l/y_j]
  ```

  commutes.  The mirror image is
  `Stacks.AlgebraicGeometry.SegreChartProduct.fromAwayS_chartMapRight`.

* `Stacks.AlgebraicGeometry.SegreChartProduct.segreChartTensorIso_symm_tmul`: **the statement Tag
  01WD needs.**  The inverse of `Stacks.AlgebraicGeometry.SegreChartRing.segreChartTensorIso`
  carries the pure tensor `a ⊗ b` to the product of the images of `a` and `b` under the two chart
  maps.  Since the pure tensors span, this says that
  `Stacks.AlgebraicGeometry.SegreChartRing.segreChartTensorIso` *is* the isomorphism induced by
  the two chart maps.

## Implementation notes

Both gradings are definitions rather than instances in this development, so they are taken as
instance binders, as everywhere else in the Segre files.

The tensor-product statement is phrased on pure tensors rather than as an equality with
`Algebra.TensorProduct.lift`, because the Segre chart ring
`HomogeneousLocalization.Away (grading R X Y) (genSub R X Y (i, j))` carries an algebra structure
only over the degree-zero part of the Segre grading, so no `Algebra R` instance is available to
state a lift against.  The pure-tensor form determines the map, and is the form the geometric
comparison with `AlgebraicGeometry.pullbackSpecIso` will consume.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open MvPolynomial TensorProduct
open Stacks.RingTheory.SegreProduct Stacks.RingTheory.SegreProjection
open Stacks.AlgebraicGeometry.SegreCharts Stacks.AlgebraicGeometry.SegreChartRing
open Stacks.AlgebraicGeometry.PolyChart Stacks.AlgebraicGeometry.SegreProjection

namespace Stacks.AlgebraicGeometry.SegreChartProduct

universe w u v

/-! ### Transporting a homogeneous localisation along an equality of elements -/

section AwayCongr

variable {A : Type u} [CommRing A] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Transport of a degree-zero homogeneous localisation along an equality of elements.**  An
equality `f = g` in a graded ring induces a ring isomorphism between the degree-zero homogeneous
localisations away from `f` and away from `g`. -/
public def awayCongr {f g : A} (h : f = g) :
    HomogeneousLocalization.Away 𝒜 f ≃+* HomogeneousLocalization.Away 𝒜 g :=
  h ▸ RingEquiv.refl _

/-- `awayCongr` sends the fraction `x / f ^ n` to the fraction `x / g ^ n`. -/
public theorem awayCongr_mk {f g : A} (h : f = g) {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • d)) :
    awayCongr 𝒜 h (HomogeneousLocalization.Away.mk 𝒜 hf n x hx) =
      HomogeneousLocalization.Away.mk 𝒜 (h ▸ hf) n x hx := by
  subst h
  rfl

end AwayCongr

/-! ### Dehomogenisation after substitution -/

section Dehom

variable (R : Type u) [CommRing R] (X Y : Type v) [DecidableEq X] [DecidableEq Y]
  (i : X) (j : Y)

/-- **Dehomogenisation after the left substitution.**  Substituting `x_k ↦ x_k y_j` into the Segre
product and then dehomogenising at `(i, j)` is the same as dehomogenising at `i` and renaming into
the left summand: both send `x_k` to `1` when `k = i` and to the chart variable otherwise, because
dehomogenisation sends `y_j` to `1`.

No homogeneity hypothesis is needed; the two sides are compared as ring homomorphisms on the
constants and the variables. -/
public theorem segreDehom_substLeft (p : MvPolynomial X R) :
    segreDehom R X Y i j (substLeft R X Y j p) =
      MvPolynomial.rename Sum.inl (dehom R i p) := by
  have h : (segreDehom R X Y i j).comp (substLeft R X Y j).toRingHom =
      ((MvPolynomial.rename (Sum.inl : {k : X // k ≠ i} → _) :
          MvPolynomial {k : X // k ≠ i} R →ₐ[R]
            MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R).toRingHom).comp
        (dehom R i) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp [segreDehom_apply, dehom_C]
    · by_cases hk : k = i
      · subst hk
        simp [segreDehom_apply, dehom_X_self, substLeft_X, gen_eq]
      · simp [segreDehom_apply, dehom_X_of_ne R i hk, substLeft_X, gen_eq,
          dehomAmbient_X_inl_of_ne R X Y i j hk]
  exact DFunLike.congr_fun h p

/-- The mirror image of
`Stacks.AlgebraicGeometry.SegreChartProduct.segreDehom_substLeft`. -/
public theorem segreDehom_substRight (q : MvPolynomial Y R) :
    segreDehom R X Y i j (substRight R X Y i q) =
      MvPolynomial.rename Sum.inr (dehom R j q) := by
  have h : (segreDehom R X Y i j).comp (substRight R X Y i).toRingHom =
      ((MvPolynomial.rename (Sum.inr : {l : Y // l ≠ j} → _) :
          MvPolynomial {l : Y // l ≠ j} R →ₐ[R]
            MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R).toRingHom).comp
        (dehom R j) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun l => ?_)
    · simp [segreDehom_apply, dehom_C]
    · by_cases hl : l = j
      · subst hl
        simp [segreDehom_apply, dehom_X_self, substRight_X, gen_eq]
      · simp [segreDehom_apply, dehom_X_of_ne R j hl, substRight_X, gen_eq,
          dehomAmbient_X_inr_of_ne R X Y i j hl]
  exact DFunLike.congr_fun h q

end Dehom

/-! ### The two chart maps -/

section ChartMaps

variable (R : Type u) [CommRing R] (X Y : Type v) (i : X) (j : Y)
  [GradedAlgebra (grading R X Y)]

/-- `fromAway` sends the fraction `p / x_i ^ n` to the dehomogenisation of `p`. -/
private theorem fromAway_mk {ι : Type v} [DecidableEq ι] (i : ι) (n : ℕ) (p : MvPolynomial ι R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι R (n • 1))
    [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)] :
    fromAway R i (HomogeneousLocalization.Away.mk _ (X_mem_one R i) n p hp) = dehom R i p := by
  simp only [fromAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  exact awayLift_dehom_mk R i p n

/-- `fromAwayS` sends the fraction `a / (x_i y_j) ^ n` to the Segre dehomogenisation of `a`. -/
private theorem fromAwayS_mk [DecidableEq X] [DecidableEq Y] (n : ℕ) (a : segre R X Y)
    (ha : a ∈ grading R X Y (n • 1)) :
    fromAwayS R X Y i j (HomogeneousLocalization.Away.mk (grading R X Y)
      (genSub_mem_grading_one R X Y (i, j)) n a ha) = segreDehom R X Y i j a := by
  simp only [fromAwayS, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  exact awayLift_segreDehom_mk R X Y i j _ n

section Left

variable [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)]

/-- **The left chart map.**  The map `R[x]_{(x_i)} → S_{(x_i y_j)}` of degree-zero homogeneous
localisations induced by the substitution `x_k ↦ x_k y_j`.  This is the map that
`Stacks.AlgebraicGeometry.SegreGlue.ι_projLeftGlued` exhibits as the Segre projection to the
first factor on the chart `D₊(x_i y_j)`, transported to the generator `genSub R X Y (i, j)`. -/
public def chartMapLeft :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule X R) (MvPolynomial.X i) →+*
      HomogeneousLocalization.Away (grading R X Y) (genSub R X Y (i, j)) :=
  (awayCongr (grading R X Y) (substLeftGraded_X R X Y j i)).toRingHom.comp
    (HomogeneousLocalization.Away.map (substLeftGraded R X Y j) (MvPolynomial.X i))

/-- The left chart map sends the fraction `p / x_i ^ n` to the fraction
`substLeft R X Y j p / (x_i y_j) ^ n`. -/
public theorem chartMapLeft_mk (n : ℕ) (p : MvPolynomial X R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule X R (n • 1)) :
    chartMapLeft R X Y i j
        (HomogeneousLocalization.Away.mk _ (X_mem_one R i) n p hp) =
      HomogeneousLocalization.Away.mk (grading R X Y) (genSub_mem_grading_one R X Y (i, j)) n
        (substLeft R X Y j p) ((substLeftGraded R X Y j).map_mem hp) := by
  rw [chartMapLeft, RingHom.comp_apply, HomogeneousLocalization.Away.map_mk,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, awayCongr_mk]
  rfl

section Dehomogenise

variable [DecidableEq X] [DecidableEq Y]

/-- **The left chart map, read through the two chart isomorphisms.**  Under
`Stacks.AlgebraicGeometry.PolyChart.chartIso` and
`Stacks.AlgebraicGeometry.SegreChartRing.segreChartIso`, the left chart map is the renaming of the
chart variables into the left summand. -/
public theorem fromAwayS_chartMapLeft
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule X R)
      (MvPolynomial.X i)) :
    fromAwayS R X Y i j (chartMapLeft R X Y i j z) =
      MvPolynomial.rename Sum.inl (fromAway R i z) := by
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (X_mem_one R i) z
  rw [chartMapLeft_mk, fromAway_mk]
  exact (fromAwayS_mk R X Y i j n _ _).trans (segreDehom_substLeft R X Y i j p)

end Dehomogenise

end Left

section Right

variable [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)]

/-- **The right chart map**, the mirror image of
`Stacks.AlgebraicGeometry.SegreChartProduct.chartMapLeft`. -/
public def chartMapRight :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule Y R) (MvPolynomial.X j) →+*
      HomogeneousLocalization.Away (grading R X Y) (genSub R X Y (i, j)) :=
  (awayCongr (grading R X Y) (substRightGraded_X R X Y i j)).toRingHom.comp
    (HomogeneousLocalization.Away.map (substRightGraded R X Y i) (MvPolynomial.X j))

/-- The right chart map sends the fraction `q / y_j ^ n` to the fraction
`substRight R X Y i q / (x_i y_j) ^ n`. -/
public theorem chartMapRight_mk (n : ℕ) (q : MvPolynomial Y R)
    (hq : q ∈ MvPolynomial.homogeneousSubmodule Y R (n • 1)) :
    chartMapRight R X Y i j
        (HomogeneousLocalization.Away.mk _ (X_mem_one R j) n q hq) =
      HomogeneousLocalization.Away.mk (grading R X Y) (genSub_mem_grading_one R X Y (i, j)) n
        (substRight R X Y i q) ((substRightGraded R X Y i).map_mem hq) := by
  rw [chartMapRight, RingHom.comp_apply, HomogeneousLocalization.Away.map_mk,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, awayCongr_mk]
  rfl

section Dehomogenise

variable [DecidableEq X] [DecidableEq Y]

/-- The mirror image of
`Stacks.AlgebraicGeometry.SegreChartProduct.fromAwayS_chartMapLeft`. -/
public theorem fromAwayS_chartMapRight
    (w : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule Y R)
      (MvPolynomial.X j)) :
    fromAwayS R X Y i j (chartMapRight R X Y i j w) =
      MvPolynomial.rename Sum.inr (fromAway R j w) := by
  obtain ⟨n, q, hq, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (X_mem_one R j) w
  rw [chartMapRight_mk, fromAway_mk]
  exact (fromAwayS_mk R X Y i j n _ _).trans (segreDehom_substRight R X Y i j q)

end Dehomogenise

end Right

end ChartMaps

/-! ### The renaming maps, read through `MvPolynomial.tensorEquivSum` -/

section TensorEquivSum

variable (R : Type u) [CommRing R] (X Y : Type v) (i : X) (j : Y)

/-- `MvPolynomial.tensorEquivSum` carries `a ⊗ 1` to the renaming of `a` into the left summand. -/
public theorem tensorEquivSum_tmul_one (a : MvPolynomial {k : X // k ≠ i} R) :
    MvPolynomial.tensorEquivSum R {k : X // k ≠ i} {l : Y // l ≠ j} R
        (a ⊗ₜ[R] (1 : MvPolynomial {l : Y // l ≠ j} R)) =
      MvPolynomial.rename Sum.inl a := by
  have h : (MvPolynomial.tensorEquivSum R {k : X // k ≠ i} {l : Y // l ≠ j} R).toAlgHom.comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R)
          (B := MvPolynomial {l : Y // l ≠ j} R)) =
      (MvPolynomial.rename (Sum.inl : {k : X // k ≠ i} → _) :
        MvPolynomial {k : X // k ≠ i} R →ₐ[R]
          MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R) := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp [MvPolynomial.tensorEquivSum_X_tmul_one]
  exact DFunLike.congr_fun h a

/-- `MvPolynomial.tensorEquivSum` carries `1 ⊗ b` to the renaming of `b` into the right
summand. -/
public theorem tensorEquivSum_one_tmul (b : MvPolynomial {l : Y // l ≠ j} R) :
    MvPolynomial.tensorEquivSum R {k : X // k ≠ i} {l : Y // l ≠ j} R
        ((1 : MvPolynomial {k : X // k ≠ i} R) ⊗ₜ[R] b) =
      MvPolynomial.rename Sum.inr b := by
  have h : ((MvPolynomial.tensorEquivSum R {k : X // k ≠ i} {l : Y // l ≠ j}
          R).toAlgHom.restrictScalars R).comp
        (Algebra.TensorProduct.includeRight (R := R)
          (A := MvPolynomial {k : X // k ≠ i} R)) =
      (MvPolynomial.rename (Sum.inr : {l : Y // l ≠ j} → _) :
        MvPolynomial {l : Y // l ≠ j} R →ₐ[R]
          MvPolynomial ({k : X // k ≠ i} ⊕ {l : Y // l ≠ j}) R) := by
    refine MvPolynomial.algHom_ext fun l => ?_
    simp [MvPolynomial.tensorEquivSum_one_tmul_X]
  exact DFunLike.congr_fun h b

end TensorEquivSum

/-! ### The Segre chart ring is the tensor product of the two chart rings -/

section Tensor

variable (R : Type u) [CommRing R] (X Y : Type v) [DecidableEq X] [DecidableEq Y]
  (i : X) (j : Y) [GradedAlgebra (grading R X Y)]
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)]
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)]

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)] in
/-- The left chart map, read through `segreChartTensorIso`: it is the inclusion of the left
tensor factor. -/
public theorem segreChartTensorIso_chartMapLeft
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule X R)
      (MvPolynomial.X i)) :
    segreChartTensorIso R X Y i j (chartMapLeft R X Y i j z) =
      (fromAway R i z) ⊗ₜ[R] (1 : MvPolynomial {l : Y // l ≠ j} R) := by
  rw [segreChartTensorIso, RingEquiv.trans_apply, segreChartIso_apply,
    fromAwayS_chartMapLeft, ← tensorEquivSum_tmul_one R X Y i j (fromAway R i z)]
  exact (MvPolynomial.tensorEquivSum R {k : X // k ≠ i} {l : Y // l ≠ j} R).symm_apply_apply _

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)] in
/-- The right chart map, read through `segreChartTensorIso`: it is the inclusion of the right
tensor factor. -/
public theorem segreChartTensorIso_chartMapRight
    (w : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule Y R)
      (MvPolynomial.X j)) :
    segreChartTensorIso R X Y i j (chartMapRight R X Y i j w) =
      (1 : MvPolynomial {k : X // k ≠ i} R) ⊗ₜ[R] (fromAway R j w) := by
  rw [segreChartTensorIso, RingEquiv.trans_apply, segreChartIso_apply,
    fromAwayS_chartMapRight, ← tensorEquivSum_one_tmul R X Y i j (fromAway R j w)]
  exact (MvPolynomial.tensorEquivSum R {k : X // k ≠ i} {l : Y // l ≠ j} R).symm_apply_apply _

/-- **The tensor-product structure on the Segre chart ring is the one carried by the two chart
maps.**  The inverse of `Stacks.AlgebraicGeometry.SegreChartRing.segreChartTensorIso` sends the
pure tensor `a ⊗ b` to the product of the images of `a` and `b` under the two chart maps.  Since
the pure tensors span the tensor product and both sides are additive, this determines the
isomorphism, so it says that the Segre chart ring `S_{(x_i y_j)}` *is* the tensor product of
`R[x]_{(x_i)}` and `R[y]_{(y_j)}` with the two substitution-induced maps as its structure maps. -/
public theorem segreChartTensorIso_symm_tmul (a : MvPolynomial {k : X // k ≠ i} R)
    (b : MvPolynomial {l : Y // l ≠ j} R) :
    (segreChartTensorIso R X Y i j).symm (a ⊗ₜ[R] b) =
      chartMapLeft R X Y i j ((chartIso R i).symm a) *
        chartMapRight R X Y i j ((chartIso R j).symm b) := by
  rw [RingEquiv.symm_apply_eq, map_mul, segreChartTensorIso_chartMapLeft,
    segreChartTensorIso_chartMapRight, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    chartIso_symm_apply, chartIso_symm_apply,
    show fromAway R i (toAway R i a) = a from
      DFunLike.congr_fun (fromAway_comp_toAway R i) a,
    show fromAway R j (toAway R j b) = b from
      DFunLike.congr_fun (fromAway_comp_toAway R j) b]

end Tensor

end Stacks.AlgebraicGeometry.SegreChartProduct

end
