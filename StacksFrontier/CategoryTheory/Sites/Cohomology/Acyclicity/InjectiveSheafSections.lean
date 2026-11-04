module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris

/-!
# An injective abelian sheaf has epimorphic restriction maps along monomorphisms

Let `(C, J)` be a locally `w`-small site on which abelian sheaves admit sheafification.  If `I`
is an injective abelian sheaf on `(C, J)` and `a : S ⟶ T` is a monomorphism of `C`, then the
restriction map on sections

`I(T) ⟶ I(S)`

is surjective: this is
`Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective`, which holds on
an arbitrary such site, the chaotic topology included.  The monomorphism `a` generates a
monomorphism `Z_S^# ⟶ Z_T^#` of free abelian sheaves, morphisms out of a free abelian sheaf on an
object are the sections over that object, and injectivity of `I` turns the monomorphism into a
surjection on `Hom(-, I)`.  This module records the same fact as epimorphy of the restriction
map in `AddCommGrpCat`.

## Main results

* `Stacks.Cohomology.InjectiveSections.epi_sections_map_of_injective` — **the restriction map of
  an injective abelian sheaf along a monomorphism of the site is an epimorphism.**

## References

* [Stacks Project, Tag 05NY](https://stacks.math.columbia.edu/tag/05NY)
* [Stacks Project, Tag 03AB](https://stacks.math.columbia.edu/tag/03AB)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Cohomology.InjectiveSections

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- **The restriction map of an injective abelian sheaf along a monomorphism of the site is an
epimorphism**, the categorical form of
`Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective`. -/
lemma epi_sections_map_of_injective (I : Sheaf J AddCommGrpCat.{w})
    [Injective I] {S T : C} (a : S ⟶ T) [Mono a] :
    Epi (I.obj.map a.op) :=
  (AddCommGrpCat.epi_iff_surjective _).2
    (Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective J I a)

end Stacks.Cohomology.InjectiveSections

end
