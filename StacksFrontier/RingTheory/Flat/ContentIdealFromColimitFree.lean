module

public import StacksFrontier.Algebra.Module.ContentIdeal
public import StacksFrontier.RingTheory.Flat.MittagLefflerEssFiniteType

/-!
# Content ideals from a filtered-colimit presentation by free modules

Let `A → B` be a local homomorphism of local rings which is essentially of finite type, with `A`
henselian, and let `N` be a finite `B`-module which is flat over `A`. Stacks 05U7 has two
assertions: that `N` is a filtered colimit of free `A`-modules whose transition maps are
injective modulo the maximal ideal, and that `N` is Mittag-Leffler over `A`. The second follows
from the first, which is
`Module.isMittagLeffler_of_flat_finite_essFiniteType_local`.

This file takes one further step, to the form in which the proof of Stacks 05U9 uses Stacks 05U7:
every element of `N` has a content ideal in `A`. The step is Stacks 0ASD, every element of a flat
Mittag-Leffler module has a content ideal.

## Main results

* `Module.exists_isContentIdeal_of_colimit_free_presentation`: every element of `N` has a
  content ideal in `A`.

## Implementation notes

Both assertions of Stacks 05U7 are unconditional here, so this step carries no hypothesis of
its own: the filtered-colimit assertion is
`exists_filteredColimit_free_with_injective_reduction` and the Mittag-Leffler assertion it
yields is `Module.isMittagLeffler_of_flat_finite_essFiniteType_local`.

Nothing here proves Stacks 05U7, so nothing here carries its tag.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 0ASD](https://stacks.math.columbia.edu/tag/0ASD)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v uM

namespace Module

/-- **Content ideals over a henselian local base, from Stacks 05U7.** Let `A → B` be a local
homomorphism of local rings which is essentially of finite type, with `A` henselian, and let `N`
be a finite `B`-module which is flat over `A`. Then every element of `N` has a content ideal
in `A`.

Stacks 05U7 gives that `N` is Mittag-Leffler over `A`
(`Module.isMittagLeffler_of_flat_finite_essFiniteType_local`), and an element of a flat
Mittag-Leffler module has a content ideal by Stacks 0ASD. -/
theorem exists_isContentIdeal_of_colimit_free_presentation
    {A : Type u} {B : Type v} {N : Type uM} [CommRing A] [CommRing B]
    [IsLocalRing B] [HenselianLocalRing A]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hB : Algebra.EssFiniteType A B)
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module.Finite B N] [Module.Flat A N]
    (x : N) :
    ∃ I : Ideal A, IsContentIdeal x I := by
  have hML : IsMittagLeffler.{u, max u uM, uM, max u uM, max u uM} A N :=
    isMittagLeffler_of_flat_finite_essFiniteType_local
      (A := A) (B := B) (N := N) hB
  exact exists_isContentIdeal_of_flat_isMittagLeffler hML x

end Module

end
