module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HypersurfaceGeometry
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphCodimension

/-!
# The geometry of the Fermat quartic surface

Let `k` be a field and `X = V(x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴) ⊆ 𝐏³_k` the Fermat quartic. With no
hypothesis on the characteristic of `k`, `X` is projective and proper over `k`, nonempty (though
it may have no `k`-rational point, for instance over `ℚ`), and equidimensional of dimension two:
its structure morphism has relative dimension two in the sense of [Stacks, Tag 02NJ].

## Main results

* `AlgebraicGeometry.FermatQuartic.isProjective_toSpec`: `X ⟶ Spec k` is projective.
* `AlgebraicGeometry.FermatQuartic.isProper_toSpec_of_isProjective`: `X ⟶ Spec k` is proper.
* `AlgebraicGeometry.FermatQuartic.nonempty_fermatQuartic`: `X` is nonempty.
* `AlgebraicGeometry.FermatQuartic.relativeDimension_toSpec`: `X ⟶ Spec k` has relative
  dimension two.
* `AlgebraicGeometry.FermatQuartic.equidimensional_fermatQuartic` and
  `AlgebraicGeometry.FermatQuartic.topologicalKrullDim_fermatQuartic`: `X` is equidimensional of
  dimension two.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

namespace AlgebraicGeometry.FermatQuartic

variable (k : Type u) [Field k]

/-- **The Fermat quartic is projective over `k`**: a closed subscheme of `𝐏³_k`. -/
theorem isProjective_toSpec : IsProjective (toSpec k) :=
  Stacks.ProjectiveSpace.isProjective_comp_projToSpecCoeff k 3 (toProjectiveSpace k)

/-- **The Fermat quartic is proper over `k`**, being projective. (The instance is
`AlgebraicGeometry.FermatQuartic.isProper_toSpec`, in the file on its cohomology.) -/
theorem isProper_toSpec_of_isProjective : IsProper (toSpec k) :=
  (isProjective_toSpec k).isProper

/-- The Fermat quartic is locally of finite type over `k`. -/
instance locallyOfFiniteType_toSpec : LocallyOfFiniteType (toSpec k) :=
  inferInstanceAs (LocallyOfFiniteType (toProjectiveSpace k ≫ projToSpecCoeff k 3))

/-- The Fermat quartic is flat over `k`, as is every scheme over a field. -/
instance flat_toSpec : Flat (toSpec k) :=
  Stacks.ProjectiveSpace.flat_of_to_spec_field k _

/-- **The Fermat quartic is nonempty.** Its global functions form a one-dimensional `k`-vector
space; no `k`-rational point is needed (and over `ℚ` there is none). -/
instance nonempty_fermatQuartic : Nonempty (fermatQuartic k) :=
  Stacks.ProjectiveSpace.nonempty_subscheme_zeroScheme_degreeSection k 3 4 (by norm_num)
    (by norm_num) (fermatPolynomial k) (fermatPolynomial_ne_zero k)

/-- **The Fermat quartic has relative dimension two over `k`** ([Stacks, Tag 02NJ]): it is a
hypersurface in `𝐏³_k`. -/
theorem relativeDimension_toSpec : AlgebraicGeometry.RelativeDimension (toSpec k) 2 :=
  Stacks.ProjectiveSpace.relativeDimension_zeroScheme_degreeSection k 2 4 (fermatPolynomial k)
    (fermatPolynomial_ne_zero k)

/-- **The Fermat quartic is equidimensional.** -/
theorem equidimensional_fermatQuartic : TopologicalSpace.Equidimensional (fermatQuartic k) :=
  (equidimensional_and_topologicalKrullDim_of_relativeDimension k (toSpec k) 2
    (relativeDimension_toSpec k)).1

/-- **The Fermat quartic is a surface**: its dimension is two. -/
theorem topologicalKrullDim_fermatQuartic : topologicalKrullDim (fermatQuartic k) = (2 : ℕ) :=
  (equidimensional_and_topologicalKrullDim_of_relativeDimension k (toSpec k) 2
    (relativeDimension_toSpec k)).2

end AlgebraicGeometry.FermatQuartic

end
