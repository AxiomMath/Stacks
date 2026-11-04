module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomialFiberTestRing
public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomialTwistLocalization
public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomialVertexIdeal
public import StacksFrontier.RingTheory.Polynomial.QuotientXPow

/-!
# The fibre of the first twist at the vertex

Let `S = k[x, y, z]` be graded by the weights `1`, `2`, `3`, let `S₍z₎` be the degree-zero
localization at `z` and let `𝔪 = (u, v, w)` be its vertex ideal. The degree-zero localization
`S(1)₍z₎` of the first twist is spanned by `x` and `y²/z`, and this file shows that these two
generators stay independent modulo `𝔪`: the fibre `κ(𝔪) ⊗ S(1)₍z₎` is two-dimensional. Since the
third twist has a one-dimensional fibre, the multiplication map `S(1)₍z₎ ⊗ S(2)₍z₎ → S(3)₍z₎`
cannot be an isomorphism.

## Main results

* `Stacks.WeightedPolynomialSituation.finrank_firstTwistLocalization_fiber`: the fibre of the first
  localized twist at the vertex ideal has dimension two over the residue field.

## Implementation notes

The fibre is represented by its canonical scalar-extension model `κ(𝔪) ⊗_{S₍z₎} S(1)₍z₎` rather
than as a quotient, which is the form the dimension count of Tag 01ML consumes directly.

Independence of the two generators is detected by a test map into the square
`k[X]/(X³) × k[X]/(X³)`: its two components are the evaluations `x ↦ X, y ↦ 0, z ↦ 1` and
`x ↦ 0, y ↦ X, z ↦ 1`, which send the generator pair to `(X, 0)` and `(0, X²)`. The two
evaluations kill `u`, `v` and `w`, hence agree on `S₍z₎` (every element of `S₍z₎` is a constant
modulo `𝔪`, and the two maps agree on constants); that common value is what makes the pair of
evaluations `S₍z₎`-linear on the first twist, so it descends to the fibre.

The truncated polynomial ring and the vanishing and nonvanishing of its powers of `X` come from
`Polynomial.QuotientXPow`.

## References

* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
-/

@[expose] public noncomputable section

namespace Stacks.WeightedPolynomialSituation

open Stacks.WeightedPolynomial
open scoped TensorProduct

private def evalFirst (E : WeightedPolynomialSituation) :
    E.S →ₐ[E.k] Polynomial.QuotientXPow E.k 3 :=
  MvPolynomial.aeval ![Polynomial.QuotientXPow.gen E.k 3, 0, 1]

private def evalSecond (E : WeightedPolynomialSituation) :
    E.S →ₐ[E.k] Polynomial.QuotientXPow E.k 3 :=
  MvPolynomial.aeval ![0, Polynomial.QuotientXPow.gen E.k 3, 1]

private noncomputable def evalFirstLocalization (E : WeightedPolynomialSituation) :
    E.ordinaryLocalization →+* Polynomial.QuotientXPow E.k 3 :=
  Localization.awayLift (evalFirst E).toRingHom E.z
    (isUnit_iff_exists_inv.mpr ⟨1, by simp [evalFirst]⟩)

private noncomputable def evalSecondLocalization (E : WeightedPolynomialSituation) :
    E.ordinaryLocalization →+* Polynomial.QuotientXPow E.k 3 :=
  Localization.awayLift (evalSecond E).toRingHom E.z
    (isUnit_iff_exists_inv.mpr ⟨1, by simp [evalSecond]⟩)

private lemma evalFirst_x (E : WeightedPolynomialSituation) :
    evalFirst E E.x = Polynomial.QuotientXPow.gen E.k 3 := by
  simp [evalFirst, WeightedPolynomialSituation.x, MvPolynomial.aeval_X]

private lemma evalFirst_y (E : WeightedPolynomialSituation) : evalFirst E E.y = 0 := by
  simp [evalFirst, WeightedPolynomialSituation.y, MvPolynomial.aeval_X]

private lemma evalSecond_x (E : WeightedPolynomialSituation) : evalSecond E E.x = 0 := by
  simp [evalSecond, WeightedPolynomialSituation.x, MvPolynomial.aeval_X]

private lemma evalSecond_y (E : WeightedPolynomialSituation) :
    evalSecond E E.y = Polynomial.QuotientXPow.gen E.k 3 := by
  simp [evalSecond, WeightedPolynomialSituation.y, MvPolynomial.aeval_X]

private noncomputable def firstGen (E : WeightedPolynomialSituation) :
    E.firstTwistLocalization :=
  ⟨Localization.mk E.x (1 : Submonoid.powers E.z), by
    rw [firstTwistLocalization_eq_span]
    exact Submodule.subset_span (by simp)⟩

private noncomputable def secondGen (E : WeightedPolynomialSituation) :
    E.firstTwistLocalization :=
  ⟨Localization.mk (E.y ^ 2) ⟨E.z, Submonoid.mem_powers E.z⟩, by
    rw [firstTwistLocalization_eq_span]
    exact Submodule.subset_span (by simp)⟩

private def homogeneousLocalizationVal (E : WeightedPolynomialSituation) :
    E.R →+* E.ordinaryLocalization where
  toFun := HomogeneousLocalization.val
  map_zero' := HomogeneousLocalization.val_zero
  map_one' := HomogeneousLocalization.val_one
  map_add' := HomogeneousLocalization.val_add
  map_mul' := HomogeneousLocalization.val_mul

private noncomputable def evalFirstOnR (E : WeightedPolynomialSituation) :
    E.R →+* Polynomial.QuotientXPow E.k 3 :=
  (evalFirstLocalization E).comp (homogeneousLocalizationVal E)

private noncomputable def evalSecondOnR (E : WeightedPolynomialSituation) :
    E.R →+* Polynomial.QuotientXPow E.k 3 :=
  (evalSecondLocalization E).comp (homogeneousLocalizationVal E)

private lemma evalFirstOnR_algebraMap (E : WeightedPolynomialSituation) (a : E.k) :
    evalFirstOnR E (algebraMap E.k E.R a) =
      algebraMap E.k (Polynomial.QuotientXPow E.k 3) a := by
  change evalFirstLocalization E (algebraMap E.k E.ordinaryLocalization a) = _
  rw [IsScalarTower.algebraMap_apply E.k E.S E.ordinaryLocalization a]
  simp [evalFirstLocalization, evalFirst]

private lemma evalSecondOnR_algebraMap (E : WeightedPolynomialSituation) (a : E.k) :
    evalSecondOnR E (algebraMap E.k E.R a) =
      algebraMap E.k (Polynomial.QuotientXPow E.k 3) a := by
  change evalSecondLocalization E (algebraMap E.k E.ordinaryLocalization a) = _
  rw [IsScalarTower.algebraMap_apply E.k E.S E.ordinaryLocalization a]
  simp [evalSecondLocalization, evalSecond]

private lemma evalFirstLocalization_mk (E : WeightedPolynomialSituation)
    (p : E.S) (n : ℕ) :
    evalFirstLocalization E
      (Localization.mk p ⟨E.z ^ n,
        Submonoid.pow_mem _ (Submonoid.mem_powers E.z) n⟩) = evalFirst E p := by
  simpa [evalFirstLocalization, evalFirst] using
    (Localization.awayLift_mk (evalFirst E).toRingHom E.z p 1
      (by simp [evalFirst]) n)

private lemma evalSecondLocalization_mk (E : WeightedPolynomialSituation)
    (p : E.S) (n : ℕ) :
    evalSecondLocalization E
      (Localization.mk p ⟨E.z ^ n,
        Submonoid.pow_mem _ (Submonoid.mem_powers E.z) n⟩) = evalSecond E p := by
  simpa [evalSecondLocalization, evalSecond] using
    (Localization.awayLift_mk (evalSecond E).toRingHom E.z p 1
      (by simp [evalSecond]) n)

private lemma evalFirstLocalization_mk_any (E : WeightedPolynomialSituation)
    (p : E.S) (s : Submonoid.powers E.z) :
    evalFirstLocalization E (Localization.mk p s) = evalFirst E p := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 E.z).mp s.2
  have hs : s = ⟨E.z ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) n⟩ :=
    Subtype.ext hn.symm
  rw [hs]
  exact evalFirstLocalization_mk E p n

private lemma evalSecondLocalization_mk_any (E : WeightedPolynomialSituation)
    (p : E.S) (s : Submonoid.powers E.z) :
    evalSecondLocalization E (Localization.mk p s) = evalSecond E p := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 E.z).mp s.2
  have hs : s = ⟨E.z ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) n⟩ :=
    Subtype.ext hn.symm
  rw [hs]
  exact evalSecondLocalization_mk E p n

private lemma evalFirst_firstGen (E : WeightedPolynomialSituation) :
    evalFirstLocalization E (firstGen E : E.ordinaryLocalization) =
      Polynomial.QuotientXPow.gen E.k 3 := by
  change evalFirstLocalization E (Localization.mk E.x (1 : Submonoid.powers E.z)) = _
  rw [evalFirstLocalization_mk_any, evalFirst_x]

private lemma evalSecond_firstGen (E : WeightedPolynomialSituation) :
    evalSecondLocalization E (firstGen E : E.ordinaryLocalization) = 0 := by
  change evalSecondLocalization E (Localization.mk E.x (1 : Submonoid.powers E.z)) = 0
  rw [evalSecondLocalization_mk_any, evalSecond_x]

private lemma evalFirst_secondGen (E : WeightedPolynomialSituation) :
    evalFirstLocalization E (secondGen E : E.ordinaryLocalization) = 0 := by
  change evalFirstLocalization E
    (Localization.mk (E.y ^ 2) ⟨E.z, Submonoid.mem_powers E.z⟩) = 0
  rw [evalFirstLocalization_mk_any, map_pow, evalFirst_y]
  simp

private lemma evalSecond_secondGen (E : WeightedPolynomialSituation) :
    evalSecondLocalization E (secondGen E : E.ordinaryLocalization) =
      (Polynomial.QuotientXPow.gen E.k 3) ^ 2 := by
  change evalSecondLocalization E
    (Localization.mk (E.y ^ 2) ⟨E.z, Submonoid.mem_powers E.z⟩) = _
  rw [evalSecondLocalization_mk_any, map_pow, evalSecond_y]

private lemma span_firstGen_secondGen (E : WeightedPolynomialSituation) :
    Submodule.span E.R {firstGen E, secondGen E} = ⊤ := by
  apply Submodule.map_injective_of_injective
    (Submodule.injective_subtype E.firstTwistLocalization)
  rw [Submodule.map_span, Submodule.map_subtype_top]
  simp only [Set.image_insert_eq, Set.image_singleton]
  conv_rhs =>
    rw [firstTwistLocalization_eq_span E]
  rfl

private lemma evalFirstOnR_u (E : WeightedPolynomialSituation) :
    evalFirstOnR E E.u = 0 := by
  change evalFirstLocalization E (HomogeneousLocalization.val E.u) = 0
  rw [val_u, evalFirstLocalization_mk_any, map_pow, evalFirst_x,
    Polynomial.QuotientXPow.gen_pow_self]

private lemma evalFirstOnR_v (E : WeightedPolynomialSituation) :
    evalFirstOnR E E.v = 0 := by
  change evalFirstLocalization E (HomogeneousLocalization.val E.v) = 0
  rw [val_v, evalFirstLocalization_mk_any, map_mul, evalFirst_x, evalFirst_y]
  simp

private lemma evalFirstOnR_w (E : WeightedPolynomialSituation) :
    evalFirstOnR E E.w = 0 := by
  change evalFirstLocalization E (HomogeneousLocalization.val E.w) = 0
  rw [val_w, evalFirstLocalization_mk_any, map_pow, evalFirst_y]
  simp

private lemma evalSecondOnR_u (E : WeightedPolynomialSituation) :
    evalSecondOnR E E.u = 0 := by
  change evalSecondLocalization E (HomogeneousLocalization.val E.u) = 0
  rw [val_u, evalSecondLocalization_mk_any, map_pow, evalSecond_x]
  simp

private lemma evalSecondOnR_v (E : WeightedPolynomialSituation) :
    evalSecondOnR E E.v = 0 := by
  change evalSecondLocalization E (HomogeneousLocalization.val E.v) = 0
  rw [val_v, evalSecondLocalization_mk_any, map_mul, evalSecond_x, evalSecond_y]
  simp

private lemma evalSecondOnR_w (E : WeightedPolynomialSituation) :
    evalSecondOnR E E.w = 0 := by
  change evalSecondLocalization E (HomogeneousLocalization.val E.w) = 0
  rw [val_w, evalSecondLocalization_mk_any, map_pow, evalSecond_y,
    Polynomial.QuotientXPow.gen_pow_self]

private lemma evalFirstOnR_vertexIdeal (E : WeightedPolynomialSituation) :
    E.vertexIdeal ≤ RingHom.ker (evalFirstOnR E) := by
  rw [WeightedPolynomialSituation.vertexIdeal]
  apply Ideal.span_le.mpr
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl
  · exact evalFirstOnR_u E
  · exact evalFirstOnR_v E
  · exact evalFirstOnR_w E

private lemma evalSecondOnR_vertexIdeal (E : WeightedPolynomialSituation) :
    E.vertexIdeal ≤ RingHom.ker (evalSecondOnR E) := by
  rw [WeightedPolynomialSituation.vertexIdeal]
  apply Ideal.span_le.mpr
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl
  · exact evalSecondOnR_u E
  · exact evalSecondOnR_v E
  · exact evalSecondOnR_w E

private lemma evalFirstOnR_eq_evalSecondOnR (E : WeightedPolynomialSituation) :
    evalFirstOnR E = evalSecondOnR E := by
  have hsurj := (bijective_algebraMap_vertexIdeal_quotient E).2
  apply RingHom.ext
  intro r
  obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk E.vertexIdeal r)
  have hmem : r - algebraMap E.k E.R a ∈ E.vertexIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change algebraMap E.R (E.R ⧸ E.vertexIdeal) r -
      algebraMap E.R (E.R ⧸ E.vertexIdeal) (algebraMap E.k E.R a) = 0
    rw [← IsScalarTower.algebraMap_apply E.k E.R (E.R ⧸ E.vertexIdeal) a, ha]
    simp
  have hfirst' : evalFirstOnR E r = evalFirstOnR E (algebraMap E.k E.R a) := by
    have h := evalFirstOnR_vertexIdeal E hmem
    rw [RingHom.mem_ker] at h
    exact sub_eq_zero.mp (by simpa only [map_sub] using h)
  have hsecond' : evalSecondOnR E r = evalSecondOnR E (algebraMap E.k E.R a) := by
    have h := evalSecondOnR_vertexIdeal E hmem
    rw [RingHom.mem_ker] at h
    exact sub_eq_zero.mp (by simpa only [map_sub] using h)
  rw [hfirst', hsecond', evalFirstOnR_algebraMap, evalSecondOnR_algebraMap]

private def evalDiagonal (E : WeightedPolynomialSituation) :
    E.R →+* FiberTestRing E where
  toFun r := (evalFirstOnR E r, evalFirstOnR E r)
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intros; simp
  map_mul' := by intros; simp

private noncomputable def evalPairOnTwist (E : WeightedPolynomialSituation) :
    letI : Module E.R (FiberTestRing E) := Module.compHom _ (evalDiagonal E)
    E.firstTwistLocalization →ₗ[E.R] FiberTestRing E := by
  letI : Module E.R (FiberTestRing E) := Module.compHom _ (evalDiagonal E)
  exact {
    toFun := fun m => (evalFirstLocalization E (m : E.ordinaryLocalization),
      evalSecondLocalization E (m : E.ordinaryLocalization))
    map_add' := by simp
    map_smul' := by
      intro r m
      change (evalFirstLocalization E
          (homogeneousLocalizationVal E r * (m : E.ordinaryLocalization)),
        evalSecondLocalization E
          (homogeneousLocalizationVal E r * (m : E.ordinaryLocalization))) = _
      rw [map_mul, map_mul]
      change (evalFirstOnR E r * evalFirstLocalization E (m : E.ordinaryLocalization),
        evalSecondOnR E r * evalSecondLocalization E (m : E.ordinaryLocalization)) = _
      change _ = (evalFirstOnR E r * evalFirstLocalization E (m : E.ordinaryLocalization),
        evalFirstOnR E r * evalSecondLocalization E (m : E.ordinaryLocalization))
      rw [← evalFirstOnR_eq_evalSecondOnR E]
      }

private lemma evalFirstOnR_eq_scalar (E : WeightedPolynomialSituation) (r : E.R) :
    ∃ a : E.k,
      evalFirstOnR E r = algebraMap E.k (Polynomial.QuotientXPow E.k 3) a ∧
      Ideal.Quotient.mk E.vertexIdeal r = algebraMap E.k (E.R ⧸ E.vertexIdeal) a := by
  obtain ⟨a, ha⟩ := (bijective_algebraMap_vertexIdeal_quotient E).2
    (Ideal.Quotient.mk E.vertexIdeal r)
  have hmem : r - algebraMap E.k E.R a ∈ E.vertexIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change algebraMap E.R (E.R ⧸ E.vertexIdeal) r -
      algebraMap E.R (E.R ⧸ E.vertexIdeal) (algebraMap E.k E.R a) = 0
    rw [← IsScalarTower.algebraMap_apply E.k E.R (E.R ⧸ E.vertexIdeal) a, ha]
    simp
  have hval : evalFirstOnR E r = evalFirstOnR E (algebraMap E.k E.R a) := by
    have h := evalFirstOnR_vertexIdeal E hmem
    rw [RingHom.mem_ker] at h
    exact sub_eq_zero.mp (by simpa only [map_sub] using h)
  exact ⟨a, by rw [hval, evalFirstOnR_algebraMap], ha.symm⟩

private lemma evalFirstOnR_isUnit_of_notMem (E : WeightedPolynomialSituation)
    {r : E.R} (hr : r ∉ E.vertexIdeal) : IsUnit (evalFirstOnR E r) := by
  obtain ⟨a, hval, hq⟩ := evalFirstOnR_eq_scalar E r
  have ha : a ≠ 0 := by
    intro ha
    apply hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [hq, ha]
    simp
  rw [hval]
  exact IsUnit.map (algebraMap E.k (Polynomial.QuotientXPow E.k 3))
    (isUnit_iff_ne_zero.mpr ha)

private noncomputable def residueEvalFirst (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] :
    E.vertexIdeal.ResidueField →+* Polynomial.QuotientXPow E.k 3 :=
  Ideal.ResidueField.lift E.vertexIdeal (evalFirstOnR E)
    (evalFirstOnR_vertexIdeal E) (fun _ hr => evalFirstOnR_isUnit_of_notMem E hr)

private lemma residueEvalFirst_algebraMap (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] (r : E.R) :
    residueEvalFirst E (algebraMap E.R E.vertexIdeal.ResidueField r) = evalFirstOnR E r :=
  Ideal.ResidueField.lift_algebraMap (I := E.vertexIdeal)
    (f := evalFirstOnR E) (evalFirstOnR_vertexIdeal E) _ r

private noncomputable def residueEvalDiagonal (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] :
    E.vertexIdeal.ResidueField →+* FiberTestRing E where
  toFun a := (residueEvalFirst E a, residueEvalFirst E a)
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intros; simp
  map_mul' := by intros; simp

private lemma residueEvalDiagonal_algebraMap (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] (r : E.R) :
    residueEvalDiagonal E (algebraMap E.R E.vertexIdeal.ResidueField r) = evalDiagonal E r := by
  ext <;> simp [residueEvalDiagonal, residueEvalFirst_algebraMap, evalDiagonal]

/-- The test ring as an algebra over the residue field at the vertex. -/
@[instance_reducible]
private noncomputable def fiberTestAlgebraOfResidueField (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] : Algebra E.vertexIdeal.ResidueField (FiberTestRing E) :=
  (residueEvalDiagonal E).toAlgebra

/-- The test ring as an algebra over the degree-zero localization. -/
@[instance_reducible]
private noncomputable def fiberTestAlgebra (E : WeightedPolynomialSituation) :
    Algebra E.R (FiberTestRing E) :=
  (evalDiagonal E).toAlgebra

private lemma isScalarTower_fiberTest (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] :
    letI := fiberTestAlgebraOfResidueField E
    letI := fiberTestAlgebra E
    IsScalarTower E.R E.vertexIdeal.ResidueField (FiberTestRing E) := by
  let := fiberTestAlgebraOfResidueField E
  let := fiberTestAlgebra E
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext r
  · exact congrArg Prod.fst (residueEvalDiagonal_algebraMap E r).symm
  · exact congrArg Prod.snd (residueEvalDiagonal_algebraMap E r).symm

private lemma smulCommClass_fiberTest (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] :
    letI := fiberTestAlgebraOfResidueField E
    letI := fiberTestAlgebra E
    SMulCommClass E.R E.vertexIdeal.ResidueField (FiberTestRing E) := by
  let := fiberTestAlgebraOfResidueField E
  let := fiberTestAlgebra E
  exact ⟨fun r a p => by
    simp only [Algebra.smul_def]
    ring⟩

private noncomputable def fiberTestLift (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] :
    letI := fiberTestAlgebraOfResidueField E
    letI := fiberTestAlgebra E
    E.vertexIdeal.ResidueField →ₗ[E.vertexIdeal.ResidueField]
      E.firstTwistLocalization →ₗ[E.R] FiberTestRing E := by
  letI := fiberTestAlgebraOfResidueField E
  letI := fiberTestAlgebra E
  letI := smulCommClass_fiberTest E
  letI : IsScalarTower E.vertexIdeal.ResidueField E.vertexIdeal.ResidueField
      (E.firstTwistLocalization →ₗ[E.R] FiberTestRing E) :=
    ⟨fun a b f => LinearMap.ext fun m =>
      Prod.ext (congrArg Prod.fst (smul_assoc a b (f m)))
        (congrArg Prod.snd (smul_assoc a b (f m)))⟩
  exact {
    toFun := fun a => a • evalPairOnTwist E
    map_add' := by
      intro a b
      apply LinearMap.ext
      intro m
      simp only [LinearMap.smul_apply, LinearMap.add_apply, add_smul]
    map_smul' := by
      intro a b
      apply LinearMap.ext
      intro m
      simp only [LinearMap.smul_apply, smul_assoc]
      simp only [RingHom.id_apply] }

private noncomputable def evalPairTensor (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] :
    letI := fiberTestAlgebraOfResidueField E
    letI := fiberTestAlgebra E
    letI := isScalarTower_fiberTest E
    E.vertexIdeal.ResidueField ⊗[E.R] E.firstTwistLocalization →ₗ[E.vertexIdeal.ResidueField]
      FiberTestRing E := by
  letI := fiberTestAlgebraOfResidueField E
  letI := fiberTestAlgebra E
  letI := isScalarTower_fiberTest E
  letI := smulCommClass_fiberTest E
  exact TensorProduct.AlgebraTensorModule.lift (fiberTestLift E)

private lemma evalPairOnTwist_firstGen (E : WeightedPolynomialSituation) :
    evalPairOnTwist E (firstGen E) = (Polynomial.QuotientXPow.gen E.k 3, 0) :=
  Prod.ext (evalFirst_firstGen E) (evalSecond_firstGen E)

private lemma evalPairOnTwist_secondGen (E : WeightedPolynomialSituation) :
    evalPairOnTwist E (secondGen E) = (0, (Polynomial.QuotientXPow.gen E.k 3) ^ 2) :=
  Prod.ext (evalFirst_secondGen E) (evalSecond_secondGen E)

private lemma evalPairTensor_tmul_one (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] (m : E.firstTwistLocalization) :
    evalPairTensor E (1 ⊗ₜ[E.R] m) = evalPairOnTwist E m := by
  simp [evalPairTensor, fiberTestLift]

private lemma residueEvalFirst_mul_gen_ne_zero (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] {a : E.vertexIdeal.ResidueField} (ha : a ≠ 0) :
    residueEvalFirst E a * Polynomial.QuotientXPow.gen E.k 3 ≠ 0 := by
  have hu : IsUnit (residueEvalFirst E a) :=
    IsUnit.map (residueEvalFirst E) (isUnit_iff_ne_zero.mpr ha)
  intro hz
  have hz' : Polynomial.QuotientXPow.gen E.k 3 * residueEvalFirst E a =
      0 * residueEvalFirst E a := by
    simpa [mul_comm] using hz
  exact Polynomial.QuotientXPow.gen_pow_ne_zero E.k 3 (by norm_num : 1 < 3)
    (by simpa using hu.mul_left_injective hz')

private lemma residueEvalDiagonal_smul_fst (E : WeightedPolynomialSituation)
    [E.vertexIdeal.IsMaximal] (a : E.vertexIdeal.ResidueField) (q : FiberTestRing E) :
    letI := fiberTestAlgebraOfResidueField E
    (a • q).1 = residueEvalFirst E a * q.1 := by
  let := fiberTestAlgebraOfResidueField E
  simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, residueEvalDiagonal]

/-- The fiber of the first twist at the vertex ideal has dimension two. -/
public theorem finrank_firstTwistLocalization_fiber
    (E : WeightedPolynomialSituation) :
    letI : E.vertexIdeal.IsMaximal := vertexIdeal_isMaximal E
    Module.finrank E.vertexIdeal.ResidueField
      (E.vertexIdeal.ResidueField ⊗[E.R] E.firstTwistLocalization) = 2 := by
  let : E.vertexIdeal.IsMaximal := vertexIdeal_isMaximal E
  let := fiberTestAlgebraOfResidueField E
  let K := E.vertexIdeal.ResidueField
  let v : Fin 2 → K ⊗[E.R] E.firstTwistLocalization := ![
    (1 : K) ⊗ₜ[E.R] firstGen E,
    (1 : K) ⊗ₜ[E.R] secondGen E]
  let out : Fin 2 → FiberTestRing E := ![(Polynomial.QuotientXPow.gen E.k 3, 0),
    (0, (Polynomial.QuotientXPow.gen E.k 3) ^ 2)]
  have hgen : Polynomial.QuotientXPow.gen E.k 3 ≠ 0 := by
    simpa using Polynomial.QuotientXPow.gen_pow_ne_zero E.k 3 (by norm_num : 1 < 3)
  have hgensq : (Polynomial.QuotientXPow.gen E.k 3) ^ 2 ≠ 0 :=
    Polynomial.QuotientXPow.gen_pow_ne_zero E.k 3 (by norm_num : 2 < 3)
  have hfirst_ne :
      ((Polynomial.QuotientXPow.gen E.k 3, (0 : Polynomial.QuotientXPow E.k 3)) :
        FiberTestRing E) ≠ (0 : FiberTestRing E) :=
    fun h => hgen (by simpa using congrArg Prod.fst h)
  have hout : LinearIndependent K out := by
    rw [LinearIndependent.pair_iff' hfirst_ne]
    intro a hEq
    by_cases ha : a = 0
    · subst a
      have hpair : (0 : FiberTestRing E) =
          (0, (Polynomial.QuotientXPow.gen E.k 3) ^ 2) := by
        simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hEq
      exact hgensq (by simpa using (congrArg Prod.snd hpair).symm)
    · have hfst := congrArg Prod.fst hEq
      exact residueEvalFirst_mul_gen_ne_zero E ha (by
        rw [residueEvalDiagonal_smul_fst E a
          (Polynomial.QuotientXPow.gen E.k 3, (0 : Polynomial.QuotientXPow E.k 3))] at hfst
        simpa using hfst)
  have hcomp : (evalPairTensor E) ∘ v = out := by
    funext i
    fin_cases i
    · change evalPairTensor E (1 ⊗ₜ[E.R] firstGen E) = (Polynomial.QuotientXPow.gen E.k 3, 0)
      rw [evalPairTensor_tmul_one, evalPairOnTwist_firstGen]
    · change evalPairTensor E (1 ⊗ₜ[E.R] secondGen E) =
        (0, (Polynomial.QuotientXPow.gen E.k 3) ^ 2)
      rw [evalPairTensor_tmul_one, evalPairOnTwist_secondGen]
  have hli : LinearIndependent K v :=
    LinearIndependent.of_comp (evalPairTensor E) (by rwa [hcomp])
  let s : Set E.firstTwistLocalization := {firstGen E, secondGen E}
  have hbase := Submodule.baseChange_span (R := E.R) (A := K)
    (M := E.firstTwistLocalization) s
  rw [span_firstGen_secondGen E, Submodule.baseChange_top] at hbase
  have hset : TensorProduct.mk E.R K E.firstTwistLocalization (1 : K) '' s = Set.range v := by
    simp [s, v, Fin.range_fin_succ]
  rw [hset] at hbase
  have hspan : Submodule.span K (Set.range v) = ⊤ := hbase.symm
  let b : Module.Basis (Fin 2) K (K ⊗[E.R] E.firstTwistLocalization) :=
    Module.Basis.mk hli hspan.ge
  simpa [b] using (Module.finrank_eq_card_basis b)

end Stacks.WeightedPolynomialSituation

end
