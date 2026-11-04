module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSections
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsComparisonMap

/-!
# Meromorphic sections of a sheaf of modules

Let `O` be a sheaf of commutative rings on a topological space and let `K` be its sheaf of
total quotient rings. A sheaf of `O`-modules `F` extends by scalars along the canonical
morphism `O ⟶ K` to a sheaf of `K`-modules, the sheaf `K_X(F)` of meromorphic sections of `F`.
Its global sections are the *meromorphic sections* of `F`. Such a section is *regular* when
multiplication by it embeds `K` into `K_X(F)`.

## Main definitions

* `AlgebraicGeometry.meromorphicSectionSheaf`: the sheaf `K_X(F)` of meromorphic sections of a
  sheaf of modules `F`, obtained from `F` by extension of scalars along the canonical morphism
  to the sheaf of total quotient rings.
* `AlgebraicGeometry.MeromorphicSection`: a meromorphic section of `F`, that is, a global
  section of `K_X(F)`.
* `AlgebraicGeometry.IsRegularMeromorphicSection`: regularity of a meromorphic section.

## Implementation notes

The sheaf `K_X(F)` is defined as `F ⊗_{𝒪_X} K_X`, the extension of scalars of `F` along `O ⟶ K`,
constructed sectionwise and then sheafified. Only the sheaf of rings enters, so `O` is an arbitrary
sheaf of commutative rings on a space rather than a sheaf of local rings.

Module carriers may lie in any universe at least as large as the universe of the space and of its
rings; sheafification into such a universe is obtained from an equivalent small category of opens.

In the equal-universe case, `SheafOfModules.unitHomEquiv` gives the morphism `K ⟶ K_X(F)` induced
by a meromorphic section, and the section is regular when this morphism is a monomorphism
(`AlgebraicGeometry.IsRegularSection`), which is the injectivity in the source. Regularity is
defined for an arbitrary sheaf of modules, with no invertibility hypothesis.

## References

* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u z

namespace AlgebraicGeometry

variable {X : TopCat.{u}}

/-- The sheaf `K_X(F)` of meromorphic sections of `F`, obtained by extension of scalars from
`O` to its sheaf of total quotient rings. -/
@[stacks 01X4 "part (1)", ega "IV 20.1.3" "M_X(F)"]
noncomputable abbrev meromorphicSectionSheaf (O : TopCat.Sheaf CommRingCat.{u} X)
    (F : SheafOfModules.{max u z} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
      (J := Opens.grothendieckTopology X) O)) :
    SheafOfModules.{max u z} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
      (J := Opens.grothendieckTopology X) (totalQuotientSheaf (X := X) O)) := by
  letI : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u z} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u z} _ _
  letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u z} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u z} _
  exact (Stacks.Sheaves.ChangeOfRings.changeOfRings.{z, u, u}
    (Opens.grothendieckTopology X) (toTotalQuotientSheaf O)).obj F

/-- A meromorphic section of `F` is a global section of `K_X(F)`. -/
@[stacks 01X4 "part (2)", ega "IV 20.1.3" "M(X,F)"]
abbrev MeromorphicSection (O : TopCat.Sheaf CommRingCat.{u} X)
    (F : SheafOfModules.{max u z} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
      (J := Opens.grothendieckTopology X) O)) :=
  (meromorphicSectionSheaf O F).sections

/-- A meromorphic section is regular if its induced map from the total quotient sheaf
to the meromorphic section sheaf is injective. -/
@[stacks 02OX, ega "IV 20.1.8" "regular section defn"]
noncomputable abbrev IsRegularMeromorphicSection (O : TopCat.Sheaf CommRingCat.{u} X)
    (L : SheafOfModules.{u} (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
      (J := Opens.grothendieckTopology X) O))
    (s : MeromorphicSection O L) : Prop :=
  IsRegularSection (totalQuotientSheaf O).presheaf
    (Stacks.Sheaves.Differentials.ringSheaf (totalQuotientSheaf O)).property s

end AlgebraicGeometry
