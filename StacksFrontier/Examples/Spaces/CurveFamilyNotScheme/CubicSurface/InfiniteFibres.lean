module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.Charts
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The fibres of the cubic surface over the affine line are infinite

For an infinite field `k`, every fibre of `Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` over
`A¹_k` is infinite. The non-representability argument of Stacks 0D5E uses this through the source's
parenthetical "the fibres of `X → A¹` are proper of dimension 1": an affine open cannot contain a
whole fibre.

The proof is a point count on the chart `k[t][x, y] ⧸ (1 + x³ + y³ - t x y)`. Fix a prime `s` of
`k[t]` and an algebraic closure `K` of the fraction field of `k[t] ⧸ s`. For every `a ∈ k` the
cubic `y³ - t a y + 1 + a³` has a root `b` in `K`, and `x ↦ a, y ↦ b` is a point of the chart with
values in `K` lying over `s`. Its kernel contains `x - a`, so distinct `a` give distinct points.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.infinite_setOf_cubicSurfaceToLine_eq`: every fibre of
  `Y ⟶ A¹_k` is infinite.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable (k : Type u) [Field k]

section Points

variable (s : Ideal (Polynomial k)) [s.IsPrime]

/-- An algebraic closure of the fraction field of `k[t] ⧸ s`. -/
abbrev fibreClosure : Type u := AlgebraicClosure (FractionRing (Polynomial k ⧸ s))

/-- The map `k[t] → K` to the algebraic closure of the residue field of `s`. -/
def fibreClosureMap : Polynomial k →+* fibreClosure k s :=
  (algebraMap (FractionRing (Polynomial k ⧸ s)) (fibreClosure k s)).comp
    ((algebraMap (Polynomial k ⧸ s) (FractionRing (Polynomial k ⧸ s))).comp
      (Ideal.Quotient.mk s))

/-- The kernel of `k[t] → K` is `s`. -/
theorem ker_fibreClosureMap : RingHom.ker (fibreClosureMap k s) = s := by
  ext a
  simp only [RingHom.mem_ker, fibreClosureMap, RingHom.coe_comp, Function.comp_apply]
  rw [map_eq_zero_iff _ (algebraMap (FractionRing (Polynomial k ⧸ s)) _).injective,
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The image of `a ∈ k` in `K`. -/
abbrev fibreConst (a : k) : fibreClosure k s := fibreClosureMap k s (Polynomial.C a)

/-- The monic cubic `y³ - t a y + 1 + a³` over `K`, whose roots are the `y`-coordinates of the
points of the chart with `x = a` over `s`. -/
def fibreCubic (a : k) : Polynomial (fibreClosure k s) :=
  Polynomial.X ^ 3 - Polynomial.C (fibreClosureMap k s Polynomial.X * fibreConst k s a) *
    Polynomial.X + Polynomial.C (1 + fibreConst k s a ^ 3)

/-- The cubic `y³ - t a y + 1 + a³` has degree three. -/
theorem natDegree_fibreCubic (a : k) : (fibreCubic k s a).natDegree = 3 := by
  unfold fibreCubic
  compute_degree!

/-- The cubic `y³ - t a y + 1 + a³` is not constant. -/
theorem degree_fibreCubic_ne_zero (a : k) : (fibreCubic k s a).degree ≠ 0 := by
  intro h
  have := Polynomial.natDegree_eq_of_degree_eq_some (n := 0) h
  rw [natDegree_fibreCubic] at this
  exact absurd this (by norm_num)

/-- A root of `y³ - t a y + 1 + a³` in `K`. -/
def fibreRoot (a : k) : fibreClosure k s :=
  (IsAlgClosed.exists_root (fibreCubic k s a) (degree_fibreCubic_ne_zero k s a)).choose

/-- `fibreRoot k s a` is a root of `y³ - t a y + 1 + a³`. -/
theorem isRoot_fibreRoot (a : k) : (fibreCubic k s a).IsRoot (fibreRoot k s a) :=
  (IsAlgClosed.exists_root (fibreCubic k s a) (degree_fibreCubic_ne_zero k s a)).choose_spec

/-- The point `(a, b)` of the chart, as a ring map `k[t][x, y] → K`. -/
def fibrePointPoly (a : k) : MvPolynomial (Fin 2) (Polynomial k) →+* fibreClosure k s :=
  eval₂Hom (fibreClosureMap k s) ![fibreConst k s a, fibreRoot k s a]

/-- The chart equation vanishes at `(a, b)`. -/
theorem fibrePointPoly_cubicChartEquation (a : k) :
    fibrePointPoly k s a (cubicChartEquation k) = 0 := by
  have h := isRoot_fibreRoot k s a
  simp only [fibreCubic, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at h
  simp only [fibrePointPoly, cubicChartEquation, coe_eval₂Hom, eval₂_add, eval₂_sub, eval₂_one,
    eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  linear_combination h

/-- The point `(a, b)` of the chart, as a ring map from the chart ring to `K`. -/
def fibrePoint (a : k) : CubicChartRing k →+* fibreClosure k s :=
  Ideal.Quotient.lift _ (fibrePointPoly k s a) fun z hz => by
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_mul, fibrePointPoly_cubicChartEquation, mul_zero]

/-- The prime of the chart ring at the point `(a, b)`. -/
def fibrePrime (a : k) : PrimeSpectrum (CubicChartRing k) :=
  ⟨RingHom.ker (fibrePoint k s a), RingHom.ker_isPrime _⟩

/-- The point `(a, b)` lies over `s`. -/
theorem comap_fibrePrime (a : k) :
    (fibrePrime k s a).asIdeal.comap (algebraMap (Polynomial k) (CubicChartRing k)) = s := by
  conv_rhs => rw [← ker_fibreClosureMap k s]
  rw [fibrePrime, RingHom.comap_ker]
  congr 1
  refine RingHom.ext fun c => ?_
  change fibrePoint k s a (algebraMap (Polynomial k) (CubicChartRing k) c) = _
  rw [← Ideal.Quotient.mk_algebraMap]
  simp [fibrePoint, fibrePointPoly, MvPolynomial.algebraMap_eq]

/-- Distinct `a` give distinct points. -/
theorem fibrePrime_injective [s.IsPrime] : Function.Injective (fibrePrime k s) := by
  intro a b hab
  have hmem : Ideal.Quotient.mk _ (X 0 - C (Polynomial.C a)) ∈ (fibrePrime k s a).asIdeal := by
    simp [fibrePrime, fibrePoint, fibrePointPoly]
  rw [hab] at hmem
  simp only [fibrePrime, RingHom.mem_ker, fibrePoint, Ideal.Quotient.lift_mk, fibrePointPoly,
    coe_eval₂Hom, eval₂_sub, eval₂_X, eval₂_C, Matrix.cons_val_zero, sub_eq_zero] at hmem
  have hinj : Function.Injective (fun c : k => fibreConst k s c) := by
    intro c d hcd
    have h1 : Polynomial.C c - Polynomial.C d ∈ RingHom.ker (fibreClosureMap k s) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hcd
    rw [ker_fibreClosureMap, ← map_sub] at h1
    by_contra hne
    have hu : IsUnit (Polynomial.C (c - d)) :=
      Polynomial.isUnit_C.2 (sub_ne_zero.2 hne).isUnit
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ h1 hu)
  exact hinj hmem.symm

end Points

/-- **Every fibre of the cubic surface over the affine line is infinite**, for an infinite field
`k`. -/
theorem infinite_setOf_cubicSurfaceToLine_eq [Infinite k] (s : affineLine k) :
    {z : cubicSurface k | cubicSurfaceToLine k z = s}.Infinite := by
  have : s.asIdeal.IsPrime := s.isPrime
  let pt : k → cubicSurface k := fun a => cubicChart k 0 (fibrePrime k s.asIdeal a)
  have hpt : Function.Injective pt :=
    (cubicChart k 0).isOpenEmbedding.injective.comp (fibrePrime_injective k s.asIdeal)
  refine Set.infinite_of_injective_forall_mem hpt fun a => ?_
  change (cubicChart k 0 ≫ cubicSurfaceToLine k) (fibrePrime k s.asIdeal a) = s
  rw [cubicChart_comp_cubicSurfaceToLine]
  exact PrimeSpectrum.ext (comap_fibrePrime k s.asIdeal a)

end Stacks.Examples.CurveFamilyNotScheme

end
