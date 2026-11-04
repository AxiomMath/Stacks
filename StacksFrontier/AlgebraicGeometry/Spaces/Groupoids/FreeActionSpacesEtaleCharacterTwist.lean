module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionSpacesEtaleOrbitQuotient
public import StacksFrontier.CategoryTheory.Sites.FreeQuotientCharacterTwist

/-!
# The rank one twist attached to a character of a free action on an algebraic space

Let `S` be a scheme, let `W` be an algebraic space over `S` carrying a free action of a group
`G` and let `U = W/G` be the quotient, an algebraic space by [Stacks 071S]. **Stacks 0727**
attaches to a character `χ : G → {+1, -1}` a sheaf of `ℤ`-modules `ℤ(χ)` on `U_étale` which is
locally free of rank one and satisfies

```
H⁰(W, F|_W)^χ = H⁰(U, F ⊗_ℤ ℤ(χ))
```

for every abelian sheaf `F` on `U_étale`. This file states that conclusion at those
hypotheses, on the spaces-étale site of the quotient.

It is `CategoryTheory.characterTwistOfQuotient` — the same conclusion at an arbitrary site —
instantiated through `AlgebraicGeometry.Space.actsFreelyOnObject_orbitQuotientAut` and
`AlgebraicGeometry.Space.isOrbitQuotient_orbitQuotientAut`, which are exactly its two
hypotheses discharged for the quotient of a free action: the action of `G` on `W` is free over
the objects of the spaces-étale site of `U`, and the quotient morphism `W ⟶ U` exhibits the
final object of that site as `W/G`.

## Main results

* `AlgebraicGeometry.Space.characterTwistOfOrbitQuotient`: **Stacks 0727** on the spaces-étale
  site of the quotient of a free action — the twist `ℤ(χ)`, the covering of the quotient by
  `W` on which it is the constant sheaf `ℤ`, and the identification of the `χ`-semi-invariant
  sections of an abelian sheaf over `W` with the global sections of its tensor product with
  the twist.

## Implementation notes

Freeness is `AlgebraicGeometry.Space.IsFreeOnNonemptyPoints`, as in [Stacks 071S]:
cancellativity on the points over the test objects whose underlying scheme is nonempty.
Asking for it over every test object would force `G` to be trivial.

Finiteness of the group, which the source assumes, is not needed and is not assumed. It enters
Stacks 0727 only through the geometry of the quotient — that `W/G` is an algebraic space with
étale quotient morphism, so that `W` is an object of the étale site of `W/G` — and
[Stacks 071S] together with `AlgebraicGeometry.Space.isEtale_toOrbitQuotient` supply that
without it. The statement below is therefore a generalization of the source.

All the sheafification hypotheses of `CategoryTheory.characterTwistOfQuotient` are satisfied
here rather than assumed: the spaces-étale site of an algebraic space is essentially small at
the universe of its schemes by [Stacks 03G0], and so is its localization at any object.
Existence of sheafification for presheaves of sets on the big fppf site is assumed, as it must
be for the quotient of [Stacks 071S] — a sheafification — to be formed at all.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G : Type u} [Group G]
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [∀ T, MulAction G (W.obj T)]
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hnat : IsNaturalAction B S hS G W) (hW : IsAlgebraicSpace B S hS W)
    (hfree : IsFreeOnNonemptyPoints B S hS G W)

/-- **Stacks 0727.** Let `W` be an algebraic space over a scheme `S` carrying a free action of
a group `G`, let `U = W/G` be the quotient of [Stacks 071S] and let `χ : G → ℤˣ` be a
character. Then there is a sheaf of `ℤ`-modules `ℤ(χ)` on the spaces-étale site of `U` which is
locally free of rank one — trivial over the covering of `U` by `W` — and satisfies

```
H⁰(W, F|_W)^χ = H⁰(U, F ⊗_ℤ ℤ(χ))
```

for every abelian sheaf `F` on that site.

This is `CategoryTheory.characterTwistOfQuotient` at the spaces-étale site of `U`: the action
of `G` on `W` is free there and the quotient morphism exhibits the final object as `W/G`. -/
@[stacks 0727]
def characterTwistOfOrbitQuotient (χ : G →* ℤˣ) :
    CharacterTwistOfQuotient (orbitQuotientEtaleSource hnat hW hfree)
      (orbitQuotientAut hnat hW hfree) χ
      (SpacesEtale.topology B S hS (orbitQuotientSpace hnat hW hfree))
      (SpacesEtale.final B S hS (orbitQuotientSpace hnat hW hfree)) :=
  CategoryTheory.characterTwistOfQuotient (actsFreelyOnObject_orbitQuotientAut hnat hW hfree)
    (isOrbitQuotient_orbitQuotientAut hnat hW hfree)
    (SpacesEtale.final_isTerminal B S hS (orbitQuotientSpace hnat hW hfree)) χ

end AlgebraicGeometry.Space

end
