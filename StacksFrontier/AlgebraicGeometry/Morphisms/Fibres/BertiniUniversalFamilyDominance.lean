module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniUniversalFamilyChart

/-!
# The universal family of a Bertini situation is dominant

Under the hypotheses of a Bertini situation, the universal family `H_univ → 𝔸^r_k` is dominant.
Over a chart, the ring map of the universal family is injective as soon as the images of the
parameters in some fraction field of the chart ring of the universal divisor are algebraically
independent over `k`, and injectivity over one chart makes the universal family dominant.

## Main results

* `Stacks.Bertini.FamilyDivisors.universalDivisorChartMap_comp_map_reducedChartRingHom`: the map
  `A[xⱼ] → Ω` of the chart, precomposed with the reduction of the coefficients, is evaluation at
  the images of the parameters.
* `Stacks.Bertini.FamilyDivisors.injective_chartDivisorParameterMap`: the ring map of the
  universal family over a chart is injective, given the algebraic independence in some fraction
  field of the chart ring of the universal divisor.
* `Stacks.Bertini.FamilyDivisors.isDominant_of_injective_chartDivisorParameterMap`: injectivity
  on one chart makes the universal family dominant.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.isDominant_universalFamily`: under the hypotheses of
  the family, the universal family is dominant.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

namespace Stacks.Bertini.FamilyDivisors

variable {D : FamilyDivisors.{u, v}}

/-- Reducing the coefficients carries the ring map of the universal family over a chart to the
structural map of the chart ring of the universal divisor over the *reduced* chart ring. -/
theorem reducedChartDivisorReduction_chartDivisorParameterMap (c : D.Chart)
    (p : MvPolynomial D.basisIndex D.k) :
    reducedChartDivisorReduction c (D.chartDivisorParameterMap c (D.parameterBaseΓEquiv p)) =
      Ideal.Quotient.mk _ (MvPolynomial.map (reducedChartRingHom c.U) p) := by
  rw [D.chartDivisorParameterMap_parameterBaseΓEquiv c, reducedChartDivisorReduction_mk,
    MvPolynomial.map_map]
  rfl

/-- Composing the map `A[xⱼ] → Ω` of the chart of the universal divisor with the reduction of the
coefficients gives the evaluation `k[xⱼ] → Ω` at the images of the parameters. -/
theorem universalDivisorChartMap_comp_map_reducedChartRingHom (c : D.Chart) (Ω : Type u) [Field Ω]
    [Algebra D.k Ω] :
    letI := reducedChartAlgebra c.U
    ∀ [Algebra (reducedChartFractionRing c.U) Ω]
      [IsScalarTower D.k (reducedChartFractionRing c.U) Ω]
      [Algebra (reducedChartDivisorRing c) Ω],
      (∀ a : reducedChartRing c.U,
        algebraMap (reducedChartFractionRing c.U) Ω
            (algebraMap (reducedChartRing c.U) (reducedChartFractionRing c.U) a) =
          Algebra.universalDivisorChartMap (reducedChartRing c.U) Ω (reducedChartEquation c)
            (MvPolynomial.C a)) →
      ((Algebra.universalDivisorChartMap (reducedChartRing c.U) Ω
          (reducedChartEquation c)).comp (MvPolynomial.map (reducedChartRingHom c.U))) =
        (MvPolynomial.aeval (fun j : D.basisIndex =>
          Algebra.universalDivisorChartMap (reducedChartRing c.U) Ω (reducedChartEquation c)
            (MvPolynomial.X j)) : MvPolynomial D.basisIndex D.k →ₐ[D.k] Ω).toRingHom := by
  let := reducedChartAlgebra c.U
  intro _ _ _ hcompat
  have := isScalarTower_reducedChartFractionRing (D := D) c.U
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
  · change Algebra.universalDivisorChartMap (reducedChartRing c.U) Ω (reducedChartEquation c)
        (MvPolynomial.map (reducedChartRingHom c.U) (MvPolynomial.C a)) =
      MvPolynomial.aeval _ (MvPolynomial.C a)
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
    change Algebra.universalDivisorChartMap (reducedChartRing c.U) Ω (reducedChartEquation c)
      (MvPolynomial.C (algebraMap D.k (reducedChartRing c.U) a)) = _
    rw [← hcompat, ← IsScalarTower.algebraMap_apply D.k (reducedChartRing c.U)
        (reducedChartFractionRing c.U),
      ← IsScalarTower.algebraMap_apply D.k (reducedChartFractionRing c.U) Ω]
  · change Algebra.universalDivisorChartMap (reducedChartRing c.U) Ω (reducedChartEquation c)
        (MvPolynomial.map (reducedChartRingHom c.U) (MvPolynomial.X j)) =
      MvPolynomial.aeval _ (MvPolynomial.X j)
    rw [MvPolynomial.map_X, MvPolynomial.aeval_X]

/-- The ring map of the universal family over a chart is injective as soon as the images of the
parameters in some fraction field `Ω` of the chart ring of the universal divisor are
algebraically independent over `k`. -/
theorem injective_chartDivisorParameterMap (c : D.Chart) (Ω : Type u) [Field Ω] [Algebra D.k Ω] :
    letI := reducedChartAlgebra c.U
    ∀ [Algebra (reducedChartFractionRing c.U) Ω]
      [IsScalarTower D.k (reducedChartFractionRing c.U) Ω]
      [Algebra (reducedChartDivisorRing c) Ω],
      (∀ a : reducedChartRing c.U,
        algebraMap (reducedChartFractionRing c.U) Ω
            (algebraMap (reducedChartRing c.U) (reducedChartFractionRing c.U) a) =
          Algebra.universalDivisorChartMap (reducedChartRing c.U) Ω (reducedChartEquation c)
            (MvPolynomial.C a)) →
      (AlgebraicIndependent D.k fun j : D.basisIndex =>
        Algebra.universalDivisorChartMap (reducedChartRing c.U) Ω (reducedChartEquation c)
          (MvPolynomial.X j)) →
      Function.Injective (D.chartDivisorParameterMap c) := by
  let := reducedChartAlgebra c.U
  intro _ _ _ hcompat hind
  have := isScalarTower_reducedChartFractionRing (D := D) c.U
  have hhom := universalDivisorChartMap_comp_map_reducedChartRingHom c Ω hcompat
  rw [algebraicIndependent_iff_injective_aeval] at hind
  intro x y hxy
  obtain ⟨p, rfl⟩ := D.parameterBaseΓEquiv.surjective x
  obtain ⟨q, rfl⟩ := D.parameterBaseΓEquiv.surjective y
  have h1 := congrArg (reducedChartDivisorReduction c) hxy
  simp only [D.reducedChartDivisorReduction_chartDivisorParameterMap c] at h1
  exact congrArg _ (hind ((DFunLike.congr_fun hhom p).symm.trans
    ((congrArg (algebraMap (reducedChartDivisorRing c) Ω) h1).trans (DFunLike.congr_fun hhom q))))

/-- The part of `H_univ` over a chart, read as an open subscheme, has the same ring map to
`𝔸^r_k` as the chart does. -/
theorem appLE_comp_ι_appLE (c : D.Chart) :
    D.universalFamily.appLE ⊤ (D.chartDivisorOpen c.U) le_top ≫
        (D.chartDivisorOpen c.U).ι.appLE (D.chartDivisorOpen c.U) ⊤
          (Scheme.Opens.ι_preimage_self _).ge =
      ((D.chartDivisorOpen c.U).ι ≫ D.universalFamily).appTop :=
  (Scheme.Hom.appLE_comp_appLE (D.chartDivisorOpen c.U).ι D.universalFamily ⊤
      (D.chartDivisorOpen c.U) ⊤ le_top
      (Scheme.Opens.ι_preimage_self _).ge).trans (Scheme.Hom.appLE_eq_app _)

/-- If the ring map of the universal family over one chart is injective, the universal family
`H_univ → 𝔸^r_k` is dominant. -/
theorem isDominant_of_injective_chartDivisorParameterMap (c : D.Chart)
    (hinj : Function.Injective (D.chartDivisorParameterMap c)) :
    IsDominant D.universalFamily := by
  have h1 : Function.Injective
      (D.universalFamily.appLE ⊤ (D.chartDivisorOpen c.U) le_top) := fun x y hxy ↦
    hinj (show D.chartDivisorParameterMap c x = D.chartDivisorParameterMap c y from
      congrArg (D.chartSubschemeΓEquiv c.U c.triv) hxy)
  have : IsDominant ((D.chartDivisorOpen c.U).ι ≫ D.universalFamily) := by
    refine isDominant_of_of_appTop_injective ?_
    rw [← D.appLE_comp_ι_appLE c]
    intro x y hxy
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hxy
    exact h1 ((ConcreteCategory.bijective_of_isIso _).1 hxy)
  exact IsDominant.of_comp (D.chartDivisorOpen c.U).ι D.universalFamily

namespace Hypotheses

variable (h : D.Hypotheses)

include h

/-- Under the hypotheses of the family, the universal family `H_univ → 𝔸^r_k` is dominant. -/
@[stacks 0G4F "the dominance of the universal family over the parameter space"]
theorem isDominant_universalFamily : IsDominant D.universalFamily := by
  obtain ⟨c, m, b, b', hbb', hb'b, hrest⟩ := h.exists_chart_substitution
  let := reducedChartAlgebra c.U
  obtain ⟨g, w, hg, hw, hcodim⟩ := hrest
  have := h.isDomain_reducedChartRing c
  have := h.algebraFiniteType_reducedChartRing c
  have := isScalarTower_reducedChartFractionRing (D := D) c.U
  have := h.isDomain_reducedChartDivisorRing c b b' hbb' hb'b g w hg hw
  have hcomp : Function.Injective
      ((algebraMap (reducedChartDivisorRing c) (FractionRing (reducedChartDivisorRing c))).comp
        (algebraMap (reducedChartRing c.U) (reducedChartDivisorRing c))) :=
    (IsFractionRing.injective (reducedChartDivisorRing c)
      (FractionRing (reducedChartDivisorRing c))).comp
        (injective_algebraMap_reducedChartDivisorRing c b b' hbb' hb'b g w hg hw)
  let : Algebra (reducedChartFractionRing c.U) (FractionRing (reducedChartDivisorRing c)) :=
    (IsFractionRing.lift (g :=
      (algebraMap (reducedChartDivisorRing c) (FractionRing (reducedChartDivisorRing c))).comp
        (algebraMap (reducedChartRing c.U) (reducedChartDivisorRing c))) hcomp).toAlgebra
  have hlift : ∀ a : reducedChartRing c.U,
      algebraMap (reducedChartFractionRing c.U) (FractionRing (reducedChartDivisorRing c))
          (algebraMap (reducedChartRing c.U) (reducedChartFractionRing c.U) a) =
        algebraMap (reducedChartDivisorRing c) (FractionRing (reducedChartDivisorRing c))
          (algebraMap (reducedChartRing c.U) (reducedChartDivisorRing c) a) :=
    IsFractionRing.lift_algebraMap hcomp
  have : IsScalarTower D.k (reducedChartFractionRing c.U)
      (FractionRing (reducedChartDivisorRing c)) := by
    refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
    rw [IsScalarTower.algebraMap_apply D.k (reducedChartRing c.U)
        (reducedChartFractionRing c.U), hlift,
      ← IsScalarTower.algebraMap_apply D.k (reducedChartRing c.U) (reducedChartDivisorRing c),
      ← IsScalarTower.algebraMap_apply D.k (reducedChartDivisorRing c)
        (FractionRing (reducedChartDivisorRing c))]
  exact isDominant_of_injective_chartDivisorParameterMap c
    (injective_chartDivisorParameterMap c (FractionRing (reducedChartDivisorRing c)) hlift
      (h.algebraicIndependent_reducedChartDivisor c b b' hbb' hb'b
        (FractionRing (reducedChartDivisorRing c)) g w hg hw hcodim hlift))

end Hypotheses

end Stacks.Bertini.FamilyDivisors

end
