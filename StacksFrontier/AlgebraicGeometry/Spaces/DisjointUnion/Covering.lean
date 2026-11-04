module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable

/-!
# The summands of a disjoint union of algebraic spaces

Let `Z` be the disjoint union of a family `X i` of algebraic spaces over `S`, that is, the
coproduct of the `X i` formed in the sheaves of sets on the big fppf site of `S`, with
injections `j i : X i ⟶ Z`. The injections are open immersions (Stacks 0F15) forming an étale
covering of `Z` (`AlgebraicGeometry.FormalSpace.isEtaleCovering_of_isColimit_cofan`). This file
reads these facts off in the spelling of the category `AlgebraicSpaces B S hS`.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_cofanInj_of_isColimit`: the injections are open
  immersions.
* `AlgebraicGeometry.Space.isEtaleCovering_cofanInj_of_isColimit`: they form an étale covering.
* `AlgebraicGeometry.Space.isEtale_cofanInj_of_isColimit`: they are étale.
* `AlgebraicGeometry.Space.exists_pointsMap_cofanInj_eq_of_isColimit`: every point of `Z` comes
  from a summand.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {ι : Type u} {X : ι → AlgebraicSpaces B S hS} {Z : AlgebraicSpaces B S hS}
  {j : ∀ i, X i ⟶ Z}
  (hc : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Z)
    fun i => (algebraicSpacesToSheaf B S hS).map (j i)))

include hc

/-- The injections of a disjoint union of algebraic spaces are open immersions. -/
theorem isOpenImmersion_cofanInj_of_isColimit (i : ι) : IsOpenImmersion B S hS (j i).hom :=
  coproductIncl_isOpenImmersion B S hS _ _ _ hc i

/-- The injections of a disjoint union of algebraic spaces form an étale covering. -/
theorem isEtaleCovering_cofanInj_of_isColimit :
    IsEtaleCovering B S hS (fun i => (X i).1) (fun i => (j i).hom) :=
  FormalSpace.isEtaleCovering_of_isColimit_cofan (fun i => (X i).2) Z.2 _ hc

/-- The injections of a disjoint union of algebraic spaces are étale. -/
theorem isEtale_cofanInj_of_isColimit (i : ι) : IsEtale B S hS (j i).hom :=
  (isEtaleCovering_cofanInj_of_isColimit hc).etale i

/-- Every point of a disjoint union of algebraic spaces comes from one of the summands. -/
theorem exists_pointsMap_cofanInj_eq_of_isColimit (x : points B S hS Z.1) :
    ∃ i, ∃ y : points B S hS (X i).1, pointsMap B S hS _ (j i).hom y = x :=
  Set.mem_iUnion.1 ((isEtaleCovering_cofanInj_of_isColimit hc).jointly_surjective.symm ▸
    Set.mem_univ x)

end AlgebraicGeometry.Space

end
