module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-torsors and torsors under a sheaf of groups

Let `(C, J)` be a site and let `G` be a sheaf of (possibly non-commutative) groups on it.
Stacks 03AH is the package of definitions on which the whole theory of first cohomology and
torsors rests: a *pseudo `G`-torsor* is a sheaf of sets with a left `G`-action which is
simply transitive on every object whose set of sections is nonempty; a *morphism* of
pseudo-torsors is a `G`-equivariant morphism of sheaves; a *`G`-torsor* is a pseudo-torsor
which is locally nonempty; and the *trivial `G`-torsor* is `G` acting on itself by left
translation, which is indeed locally nonempty because it has a global section.

All four notions, together with the verification that the trivial pseudo-torsor is a torsor,
are developed in `StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections`,
where they are the vocabulary of Stacks 03AI: a torsor is trivial exactly when it has a global
section. This file registers the tag against those declarations.

## Main definitions

* `PseudoTorsor`: a sheaf of sets with a sectionwise simply transitive `G`-action.
* `PseudoTorsor.Hom`: an equivariant morphism of pseudo-torsors.
* `PseudoTorsor.IsTorsor`: local nonemptiness of a pseudo-torsor.
* `trivialTorsor`: the sheaf of groups acting on itself by left translation.

## Main results

* `trivialTorsor_isTorsor`: the trivial pseudo-torsor is a torsor.

## Implementation notes

A covering family `{U_i → U}` is represented by the covering sieve it generates in the
Grothendieck topology, so "locally nonempty" reads as: for every object `U` there is a
covering sieve of `U` all of whose members have a section. A torsor is not a separate
structure but a pseudo-torsor satisfying `PseudoTorsor.IsTorsor`; consequently its morphisms
are exactly the morphisms `PseudoTorsor.Hom` of the underlying pseudo-torsors, which is what
the source's definition of a morphism of torsors asks for.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

@[expose] public section

add_to_stacks 03AH "pseudo-torsor" PseudoTorsor
add_to_stacks 03AH "morphism of pseudo-torsors" PseudoTorsor.Hom
add_to_stacks 03AH "torsor" PseudoTorsor.IsTorsor
add_to_stacks 03AH "trivial torsor" trivialTorsor
add_to_stacks 03AH "the trivial torsor is a torsor" trivialTorsor_isTorsor
