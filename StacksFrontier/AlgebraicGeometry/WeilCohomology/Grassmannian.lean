module

public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Projective
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.SmoothProjectiveScheme

/-!
# The Grassmannian as a smooth projective scheme over a field

For a field `k` the Grassmannian `G(l, n)_k` of Constructions, Section 089R — the base change to
`Spec k` of `AlgebraicGeometry.Grassmannian.scheme l n`, which parametrizes rank-`n - l` quotients
of `𝒪^n` — is smooth of relative dimension `l(n - l)` and projective over `k`, so it is an object
of the category of smooth projective schemes over `k` on which the cohomology theories of
Section 45.14 are defined.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.grassmannian`: `G(l, n)_k` as an object of
  `SmoothProjectiveScheme k`.

## References

* [Stacks Project, Tag 089U](https://stacks.math.columbia.edu/tag/089U)
* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable (k : Type u) [Field k]

/-- **The Grassmannian `G(l, n)_k` as a smooth projective scheme over `k`.** -/
def grassmannian (l n : ℕ) : (SmoothProjectiveScheme k).FullSubcategory :=
  mk (Grassmannian.schemeOver.over l n (Spec (.of k))).hom inferInstance
    (Grassmannian.isProjective_schemeOver l n _)

/-- The underlying scheme of `grassmannian k l n` is `Grassmannian.schemeOverRing l n k`. -/
theorem grassmannian_toScheme (l n : ℕ) :
    (toScheme k).obj (grassmannian k l n) = Grassmannian.schemeOverRing l n (.of k) :=
  rfl

/-- The structure morphism of `G(l, n)_k` is smooth of relative dimension `l(n - l)`. -/
instance smoothOfRelativeDimension_grassmannian (l n : ℕ) :
    SmoothOfRelativeDimension (l * (n - l)) (grassmannian k l n).obj.hom :=
  Grassmannian.smoothOfRelativeDimension_schemeOver l n _

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
