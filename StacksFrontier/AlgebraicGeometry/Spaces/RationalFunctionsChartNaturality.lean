module

public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsEvaluation

/-!
# Evaluation of rational functions is natural in the chart

Let `X` be an algebraic space over a scheme `S`, let `m : W → X` be a morphism from a
representable presheaf which factors through every dense open subspace of `X`, and let
`g : W' → W` be a morphism of the site. Then `yoneda.map g ≫ m` also factors through every
dense open subspace, and the two evaluations of a rational function differ by restriction
along `g`: evaluating on `W'` is evaluating on `W` and pulling the resulting global section
back along `g`.

This is immediate from
`AlgebraicGeometry.Space.evalSiteRingHom_eq`, which computes the evaluation from *any*
factorization of the morphism through the domain of a representative: the factorization of
`yoneda.map g ≫ m` obtained by composing `g` with a factorization of `m` computes the one
evaluation from the other, and pulling the coordinate of an affine-line-valued point back is
`AlgebraicGeometry.Space.affineLineCoordinate_map`.

## Main results

* `AlgebraicGeometry.Space.evalSiteRingHom_naturality`: evaluation on a chart is natural in
  the chart.

## References

* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- Evaluation of a rational function on a chart depends only on the morphism to `X`, not on
the proof that it factors through the dense open subspaces. -/
theorem evalSiteRingHom_congr_mor {W : BigFppfOver B S hS} {m m' : yoneda.obj W ⟶ X}
    (h : m = m') (hm : FactorsThroughDenseOpens B S hS hX W m)
    (hm' : FactorsThroughDenseOpens B S hS hX W m') (x : rationalFunctions B S hS hX) :
    evalSiteRingHom B S hS hX hm x = evalSiteRingHom B S hS hX hm' x := by
  subst h; rfl

/-- Evaluation of rational functions on a chart meeting every dense open subspace is natural in
the chart: evaluating on `W'` along `yoneda.map g ≫ m` is evaluating on `W` along `m` followed
by pullback of global sections along `g`. -/
theorem evalSiteRingHom_naturality {W W' : BigFppfOver B S hS} {m : yoneda.obj W ⟶ X}
    (g : W' ⟶ W) (hm : FactorsThroughDenseOpens B S hS hX W m)
    (hm' : FactorsThroughDenseOpens B S hS hX W' (yoneda.map g ≫ m))
    (x : rationalFunctions B S hS hX) :
    evalSiteRingHom B S hS hX hm' x =
      ((BigFppfOver.toScheme B S hS).map g).appTop (evalSiteRingHom B S hS hX hm x) := by
  obtain ⟨f, rfl⟩ := RationalMap.exists_rep B S hS x
  obtain ⟨l, hl⟩ := denseOpenLift B S hS hX hm f.dense_open_domain
  rw [evalSiteRingHom_eq B S hS hX hm f l hl,
    evalSiteRingHom_eq B S hS hX hm' f (yoneda.map g ≫ l) (by rw [Category.assoc, hl]),
    Category.assoc, ← yonedaEquiv_naturality, affineLineCoordinate_map]
  rfl

end AlgebraicGeometry.Space

end
