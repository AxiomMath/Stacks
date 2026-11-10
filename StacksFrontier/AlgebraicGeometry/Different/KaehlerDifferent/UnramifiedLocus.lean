module

public import StacksFrontier.AlgebraicGeometry.Different.KaehlerDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria

/-!
# The Kähler different cuts out the ramified locus

Let `f : Y ⟶ X` be a morphism of schemes which is locally of finite type, and let `R ⊆ Y` be the
closed subscheme cut out by the Kähler different of `f`, the zeroth Fitting ideal sheaf of
`Ω_{Y/X}`. Then the underlying set of `R` is exactly the set of points of `Y` at which `f` is not
unramified.

## Main results

* `Stacks.Discriminant.mem_range_kaehlerDifferent_subschemeι_iff_not_unramifiedAt`: a point of
  `Y` lies in `R` if and only if `f` is not unramified there.
* `Stacks.Discriminant.range_kaehlerDifferent_subschemeι`: **Stacks Project, Tag 0BVY** and
  **Stacks Project, Tag 0C3J**, the same statement as an equality of subsets of `Y`.

## Implementation notes

The closed subscheme `R` is named by the closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` of the ideal sheaf
`Stacks.Discriminant.kaehlerDifferent f`, and its underlying subset of `Y` is the support of that
ideal sheaf by `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`.

The source proves the lemma by citing its copy in the chapter on divisors, [Stacks, Tag 0C3J].
That copy is not a weaker statement but the very same one: the Kähler different of [Stacks,
Tag 0BVW] is *by definition* the zeroth Fitting ideal sheaf of `Ω_{Y/X}`, so
`Stacks.Discriminant.kaehlerDifferent f` and `AlgebraicGeometry.fittingIdeal
(AlgebraicGeometry.Scheme.Hom.relativeDifferentials f) 0` are the same ideal sheaf, and the two
tags name one theorem with one set of hypotheses. Both are therefore registered on
`Stacks.Discriminant.range_kaehlerDifferent_subschemeι` rather than on two copies of it.

The proof combines two inputs, which are available here directly. The support of the zeroth
Fitting ideal sheaf of the finite type quasi-coherent module `Ω_{Y/X}` is the support of the
module, [Stacks, Tag 0CYX] in the form `AlgebraicGeometry.fittingIdeal_zero_support_eq_supp`;
and the stalk of `Ω_{Y/X}` at a point vanishes exactly when `f` is unramified there, the
equivalence of parts (1) and (3) of [Stacks, Tag 02GF], which is
`AlgebraicGeometry.unramifiedAt_iff_subsingleton_relativeDifferentialStalk`. The stalk read by
`SheafOfModules.supp` and `Stacks.SmoothAtJacobian.relativeDifferentialStalk` is the same one: the
stalk of the abelian presheaf underlying the sheaf of relative differentials.

## References

* [Stacks Project, Tag 0BVY](https://stacks.math.columbia.edu/tag/0BVY)
* [Stacks Project, Tag 0C3J](https://stacks.math.columbia.edu/tag/0C3J)
* [Stacks Project, Tag 0BVW](https://stacks.math.columbia.edu/tag/0BVW)
* [Stacks Project, Tag 0CYX](https://stacks.math.columbia.edu/tag/0CYX)
* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Discriminant

/-- For a morphism of schemes `f : Y ⟶ X` locally of finite type, a point of `Y` lies in the
closed subscheme cut out by the Kähler different of `f` if and only if `f` is not unramified at
that point. -/
theorem mem_range_kaehlerDifferent_subschemeι_iff_not_unramifiedAt {Y X : Scheme.{u}}
    (f : Y ⟶ X) [LocallyOfFiniteType f] (y : Y) :
    y ∈ Set.range (kaehlerDifferent f).subschemeι ↔ ¬ UnramifiedAt f y := by
  change y ∈ Set.range (fittingIdeal (Scheme.Hom.relativeDifferentials f) 0).subschemeι ↔ _
  rw [Scheme.IdealSheafData.range_subschemeι,
    show ((fittingIdeal (Scheme.Hom.relativeDifferentials f) 0).support : Set Y) =
      SheafOfModules.supp (Scheme.Hom.relativeDifferentials f) from
      fittingIdeal_zero_support_eq_supp _]
  change y ∈ SheafOfModules.supp
      (show SheafOfModules.{u} Y.ringCatSheaf from Scheme.Hom.relativeDifferentials f) ↔ _
  rw [SheafOfModules.mem_supp_iff_nontrivial_stalk
      (F := show SheafOfModules.{u} Y.ringCatSheaf from Scheme.Hom.relativeDifferentials f),
    unramifiedAt_iff_subsingleton_relativeDifferentialStalk f y]
  exact not_subsingleton_iff_nontrivial.symm

/-- **Stacks Project, Tag 0BVY** and **Stacks Project, Tag 0C3J.** For a morphism of schemes
`f : Y ⟶ X` locally of finite type, the closed subscheme `R ⊆ Y` cut out by the Kähler different
of `f` — equivalently, by the zeroth Fitting ideal of `Ω_{Y/X}`, which is what the Kähler
different is — has as its underlying subset of `Y` exactly the set of points at which `f` is not
unramified. -/
@[stacks 0BVY, stacks 0C3J]
theorem range_kaehlerDifferent_subschemeι {Y X : Scheme.{u}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] :
    Set.range (kaehlerDifferent f).subschemeι = {y : Y | ¬ UnramifiedAt f y} :=
  Set.ext fun y => mem_range_kaehlerDifferent_subschemeι_iff_not_unramifiedAt f y

end Stacks.Discriminant

end
