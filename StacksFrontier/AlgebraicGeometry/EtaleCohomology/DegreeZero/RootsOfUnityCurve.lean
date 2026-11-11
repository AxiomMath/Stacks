module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DegreeZero.RootsOfUnity
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Degree-zero étale cohomology of roots of unity on a smooth projective curve

Let `X` be a smooth projective curve over an algebraically closed field `k` and let `n` be
invertible in `k`. Then pullback along the structure morphism identifies the roots of unity of
`k` with `H⁰_étale(X, μ_n)`.

This is the `q = 0` case of the computation of `H^q_étale(X, μ_n)` on a smooth projective curve
of genus `g`; the implementation notes say what the other cases rest on.

## Main results

* `AlgebraicGeometry.baseRootsToEtaleH0_bijective_of_isCurve` — the degree-zero identification
  in the setting of the source: `X` a smooth projective curve over an algebraically closed field
  and `n` invertible in `k`.

## Implementation notes

Only the `q = 0` clause is stated here. The source computes `H^q_étale(X, μ_n)` for every `q`;
all clauses together are
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus` (in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityCurvesFinal`). The other three
clauses rest on the following, all in the library.

* `q = 1`, `H¹_étale(X, μ_n) = Pic⁰(X)[n]`, needs `H¹_étale(X, 𝐆_m) = Pic(X)`, Stacks Tag 03P8,
  which is `Stacks.Kummer.etaleH1MultiplicativeAddEquivPicard`. It also needs `Pic⁰` and the
  degree map `Pic(X) → 𝐙`, and the surjectivity of multiplication by `n` on an abelian variety,
  Stacks Tag 03RP.
* `q = 2`, `H²_étale(X, μ_n) = 𝐙/n𝐙`, needs in addition the vanishing of `H^q_étale(X, 𝐆_m)`
  for `q ≥ 2` on a curve, Stacks Tag 03RM, which is
  `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve`.
* `q ≥ 3` needs the same vanishing.

The hypotheses of the source are all taken, as the standing situation of the tag, even though
the proof uses only integrality of `X` — which `AlgebraicGeometry.IsCurve` supplies through
`AlgebraicGeometry.IsVariety` — and positivity of `n`, which invertibility of `n` in the field
supplies. The hypothesis-minimal statement is the one this specializes,
`AlgebraicGeometry.baseRootsToEtaleH0_bijective_of_isIntegral`, which carries Stacks Tag 03RR.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 03RQ, the case `q = 0`.** Let `X` be a smooth projective curve over an
algebraically closed field `k` and let `n` be invertible in `k`. Pullback along the structure
morphism is a bijection from the `n`-th roots of unity of `k` onto `H⁰_étale(X, μ_n)`. -/
@[stacks 03RQ "the q = 0 clause, H^0_etale(X, mu_n) = mu_n(k); all clauses together are \
etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus"]
public theorem baseRootsToEtaleH0_bijective_of_isCurve
    (B : BigEtaleSite.{u}) (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (hX : B.Contains X) (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProjectiveVariety k f] (n : ℕ) (hn : IsUnit (n : k))
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) := by
  refine baseRootsToEtaleH0_bijective_of_isIntegral B k X hX f n (Nat.pos_of_ne_zero ?_)
  rintro rfl
  simp at hn

end AlgebraicGeometry

end
