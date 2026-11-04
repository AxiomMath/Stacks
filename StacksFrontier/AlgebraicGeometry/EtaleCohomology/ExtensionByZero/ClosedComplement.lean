module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero and a closed subscheme: the localization short complex

Let `X` be a scheme, let `i : Z ⟶ X` be a closed immersion and let `j : U ⟶ X` be an open
immersion whose image is the complement of the image of `i`.  For an abelian sheaf `F` on the
small étale site of `X` the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*` form a short
complex
`0 ⟶ j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F ⟶ 0`
on `X_étale`, and that short complex is short exact.

## Main definitions

* `Stacks.EtaleCohomology.openClosedShortComplex`: the short complex above, whose two maps are
  the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*`.

## Main results

* `Stacks.EtaleCohomology.openClosedShortComplex_shortExact`: the short complex is short exact.

## References

* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})

/-- The short complex `j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F` built from the counit of `j_! ⊣ j^{-1}` and
the unit of `i^{-1} ⊣ i_*`, for a closed subscheme `i : Z ⟶ X` and the open immersion `j : U ⟶ X`
of its complement. -/
@[stacks 095L "the canonical short complex"]
def openClosedShortComplex :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  ShortComplex.mk ((extensionByZeroAdj.{u, v} j).counit.app F)
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app F)
    (extensionByZero_counit_comp_inverseImage_unit i j hij F)

variable [IsClosedImmersion i]

/-- For a closed immersion `i : Z ⟶ X` and the open immersion `j : U ⟶ X` of its complement, the
short complex `0 ⟶ j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F ⟶ 0` is short exact. -/
@[stacks 095L "short exactness"]
theorem openClosedShortComplex_shortExact :
    (openClosedShortComplex.{u, v} i j hij F).ShortExact :=
  (shortExact_extensionByZero_etaleAbelianDirectImage.{u, v} i j hij F).choose_spec

end Stacks.EtaleCohomology

end
