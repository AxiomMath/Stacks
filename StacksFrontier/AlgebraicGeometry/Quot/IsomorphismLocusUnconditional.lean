module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFromQuotAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicSpaceSeparated

/-!
# The isomorphisms form an open subspace of `Mor_B(Y, X)` (Stacks 0DPP)

Let `B` be an algebraic space and `Y, X` algebraic spaces over `B` with `Y ⟶ B` flat, proper and
of finite presentation and `X ⟶ B` separated and of finite presentation, the standing data of
Stacks 0DPL, so that `Mor_B(Y, X)` is an algebraic space (Stacks 0D1C). Stacks 0DPP asserts that
if moreover `X ⟶ B` is proper, the subfunctor `Isom_B(Y, X) ⊆ Mor_B(Y, X)` of isomorphisms is an
open subspace.

The source's proof is the isomorphism locus of Stacks 05XD, which is
`AlgebraicGeometry.Space.isOpenSubspace_isomSubfunctor` given the algebraicity of
`Mor_B(Y, X)`. That algebraicity is reduced to the first clause of Stacks 09TU for structure
sheaves by `AlgebraicGeometry.Space.isOpenSubspace_isomSubfunctor_of_quotAlgebraic`, and the
first clause of Stacks 09TU for a module of finite type is
`AlgebraicGeometry.Space.QuotSituation.isAlgebraicSpace_quot_of_isFiniteTypeOnSite`; the structure
sheaf is of finite type by `AlgebraicGeometry.Space.isFiniteTypeOnSite_unit_structureRingSheaf`.

Here `Y ⟶ B` is `z : Z ⟶ Q` and `X ⟶ B` is `x : X ⟶ Q`.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_isomSubfunctor_of_isFinitePresentation`:
  for `z` flat, proper and of finite presentation and `x` proper and of finite presentation, the
  isomorphisms form an open subspace of `Mor_Q(Z, X)`.

## References

* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 0DPL](https://stacks.math.columbia.edu/tag/0DPL)
* [Stacks Project, Tag 05XD](https://stacks.math.columbia.edu/tag/05XD)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- Let `Q` be an algebraic space and `z : Z ⟶ Q`, `x : X ⟶ Q` morphisms of algebraic spaces over
`S` with `z` flat, proper and of finite presentation and `x` proper and of finite presentation (in
particular separated, as in the standing data of Stacks 0DPL). Then the subfunctor
`Isom_Q(Z, X) ⊆ Mor_Q(Z, X)` of isomorphisms is an open subspace. -/
@[stacks 0DPP "the subfunctor Isom_B(Y, X) of Mor_B(Y, X) of isomorphisms is an open subspace, \
for Y ⟶ B flat, proper and of finite presentation and X ⟶ B proper and of finite presentation"]
theorem isOpenSubspace_isomSubfunctor_of_isFinitePresentation
    (hx_fp : IsFinitePresentation B S hS x) (hx_proper : IsProper B S hS x)
    (hz_fp : IsFinitePresentation B S hS z) (hz_flat : IsFlat B S hS z)
    (hz_proper : IsProper B S hS z) :
    IsOpenSubspace B S hS (isomSubfunctor B S hS Z X Q z x hZ hX hQ) :=
  isOpenSubspace_isomSubfunctor_of_quotAlgebraic z x hZ hX hQ hx_fp hx_proper hz_fp hz_flat
    hz_proper

end AlgebraicGeometry.Space
