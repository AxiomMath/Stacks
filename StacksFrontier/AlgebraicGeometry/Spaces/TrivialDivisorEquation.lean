module

public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeOfCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.StalkTorsionOfSupportedComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme

/-!
# A trivialization of `𝒪_X(D)` gives a global equation of `D`

Let `D` be an effective Cartier divisor on an algebraic space `X`. If the invertible sheaf
`𝒪_X(D)` is trivial, then `D` is cut out by a single global regular function: there is
`g ∈ Γ(X, 𝒪_X)` such that on every affine étale chart `U` of `X` the points of `U` lying over `D`
are exactly the zero locus of `g|_U`.

## The argument

An isomorphism `e : 𝒪_X(D) ≅ 𝒪_X` carries the canonical section `1_D` to a section `g` of `𝒪_X`,
that is, to a global regular function. On an affine chart `U` the defining ideal of `D` is the
evaluation ideal of `(𝒪_X(D), 1_D)` (Stacks 0847), which `e` matches with the evaluation ideal
of `(𝒪_X, g)`; the linear functionals on the free rank-one module `𝒪_X(U)` are the
multiplications, so this ideal is the principal ideal `(g|_U)`. The points of `U` over `D` are
the zero locus of the defining ideal of `D` on `U`, which is the zero locus of `g|_U`.

## Main results

* `AlgebraicGeometry.Space.exists_globalFunctions_zeroLocus_of_isTrivial`: a trivialization of
  `𝒪_X(D)` gives a global equation of `D`.

## References

* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If the invertible sheaf `𝒪_X(D)` of an effective Cartier divisor `D` is trivial, then `D` is
cut out by one global regular function `g`: on every affine étale chart the points over `D`
are the zero locus of the restriction of `g`. -/
theorem exists_globalFunctions_zeroLocus_of_isTrivial (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D)
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (associatedInvertibleSheaf B S hS X D hD)) :
    ∃ g : globalFunctions B S hS X.1, ∀ c : SmallEtale B S hS X.1, IsAffine (chartScheme c) →
      chartPointsMap c ⁻¹' Set.range (pointsMap B S hS D.1.toFunctor D.1.ι) =
        (chartScheme c).zeroLocus (U := ⊤) {globalFunctionsChartRestriction B S hS X c g} := by
  obtain ⟨e⟩ := htriv
  let s : (SheafOfModules.unit (structureRingSheaf B S hS X)).sections :=
    SheafOfModules.sectionsMap e.hom (canonicalSection B S hS X D hD)
  refine ⟨s, fun c hc => ?_⟩
  rw [preimage_chartPointsMap_range_eq_zeroLocus_definingIdealAt B S hS X D c hc,
    definingIdealAt_eq_sectionEvaluationIdealAt_canonicalSection B S hS X D hD c hc,
    sectionEvaluationIdealAt_eq_of_iso B S hS X _ _ (canonicalSection B S hS X D hD) s e
      (fun _ => rfl) c,
    sectionEvaluationIdealAt_eq_span_singleton B S hS X _ s c
      (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op c))) LinearMap.id
      (fun x : ToType ((structureRingSheaf B S hS X).obj.obj (op c)) => mul_one x)]
  exact Scheme.zeroLocus_span (X := chartScheme c) _

end AlgebraicGeometry.Space

end
