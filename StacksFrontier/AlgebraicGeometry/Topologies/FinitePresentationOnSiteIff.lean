module

public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# Finite presentation on a site: the two renderings agree

Modules on Sites, Definition 03DL (7) calls a sheaf of modules `𝓕` on a ringed site
`(𝒞, 𝒪)` of finite presentation when every object `U` of `𝒞` has a covering `{Uᵢ ⟶ U}` such
that each restriction `𝓕|_{𝒞/Uᵢ}` has a finite global presentation.  The library states this as
`SheafOfModules.IsFinitePresentationOnSite`, with the finite global presentation of 03DE (7)
written through universal properties.  Mathlib's `SheafOfModules.IsFinitePresentation` asks
instead for a single family covering the final object on whose members `𝓕` has a finite
presentation by free modules, which is the form of the condition given by Modules on Sites,
Lemma 03DN.

This file shows that the two agree, in an arbitrary module universe.

## Main results

* `SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation`: the two agree.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory

universe u v m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{m}}
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{m}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- A sheaf of modules is of finite presentation on the site, every object being covered by
objects over which it has a finite global presentation, if and only if it is of finite
presentation in Mathlib's sense, a family covering the final object carrying finite presentations
by free modules. -/
theorem isFinitePresentationOnSite_iff_isFinitePresentation (M : SheafOfModules.{m} R) :
    M.IsFinitePresentationOnSite ↔ M.IsFinitePresentation :=
  ⟨isFinitePresentation_of_isFinitePresentationOnSite' M,
    fun _ => isFinitePresentationOnSite_of_isFinitePresentation M⟩

end SheafOfModules

end
