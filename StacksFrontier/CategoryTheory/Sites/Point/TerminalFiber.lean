module

public import StacksFrontier.CategoryTheory.Sites.Point.Basic

/-!
# The fibre of a terminal sheaf at a point of a site

The stalk functor of a point of a site is left exact ([Stacks Project, Tag 00Y5] (3), which for
Mathlib's notion of a point is `CategoryTheory.GrothendieckTopology.Point.sheafFiber_leftExact`),
so it carries a terminal sheaf to a terminal object of `Type w` — that is, to a singleton.  This
file says so.

The statement is small and entirely formal, and it is recorded on its own because it is what makes
the germ of a *global* section computable.  A global section of a sheaf `F` on a site whose
underlying category has a terminal object `T` is a morphism `⊤ ⟶ F` of sheaves
(`CategoryTheory.Sheaf.terminalObjHomEquiv`), and its germ at a point is therefore the image of
the germ of the unique section of `⊤` over `T`.  When one has to compare that germ with the germ
produced by some *other* identification of the fibre — an arbitrary isomorphism of stalk functors,
say — there is no description of the identification on germs to appeal to; what saves the
computation is that the two candidate elements of the fibre of `⊤` are equal because that fibre is
a singleton.  That is the shape of the argument in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineCase.lean`, step (3) of
[Stacks Project, Tag 04I6].

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.isTerminalSheafFiberOfIsTerminal` — the fibre of a
  terminal sheaf is a terminal object of `Type w`.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.subsingleton_sheafFiber_of_isTerminal` and
  `CategoryTheory.GrothendieckTopology.Point.eq_of_isTerminal` — that fibre is a subsingleton, and
  any two of its elements are equal.

## References

* [Stacks Project, Tag 00Y5](https://stacks.math.columbia.edu/tag/00Y5)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : J.Point.{w})
  [LocallySmall.{w} C]

/-- **The fibre of a terminal sheaf at a point of a site is terminal.**  The stalk functor is left
exact by `CategoryTheory.GrothendieckTopology.Point.sheafFiber_leftExact`, which is
[Stacks Project, Tag 00Y5] (3), so in particular it preserves the terminal object. -/
noncomputable def Point.isTerminalSheafFiberOfIsTerminal {E : Sheaf J (Type w)}
    (hE : IsTerminal E) : IsTerminal (Φ.sheafFiber.obj E) :=
  haveI := Φ.sheafFiber_leftExact
  hE.isTerminalObj (Φ.sheafFiber (A := Type w)) E

/-- **The fibre of a terminal sheaf at a point of a site is a subsingleton.**  A terminal object
of `Type w` is isomorphic to `PUnit`. -/
theorem Point.subsingleton_sheafFiber_of_isTerminal {E : Sheaf J (Type w)}
    (hE : IsTerminal E) : Subsingleton (Φ.sheafFiber.obj E) :=
  ((Φ.isTerminalSheafFiberOfIsTerminal hE).uniqueUpToIso
    Types.isTerminalPUnit).toEquiv.subsingleton

/-- Any two elements of the fibre of a terminal sheaf are equal.  This is the form in which the
germ computation of step (3) of [Stacks Project, Tag 04I6] uses
`CategoryTheory.GrothendieckTopology.Point.subsingleton_sheafFiber_of_isTerminal`: it identifies
the value at the terminal sheaf of an arbitrary isomorphism of stalk functors with a germ chosen
by hand, no description of the isomorphism being available. -/
theorem Point.eq_of_isTerminal {E : Sheaf J (Type w)} (hE : IsTerminal E)
    (a b : Φ.sheafFiber.obj E) : a = b :=
  (Φ.subsingleton_sheafFiber_of_isTerminal hE).allEq a b

end CategoryTheory.GrothendieckTopology

end
