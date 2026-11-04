module

public import StacksFrontier.AlgebraicGeometry.Full.Basic

/-!
# What is left of Tag 0E8Q's `equivalence` label, stated exactly

[Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) asserts that
`AlgebraicGeometry.canonicalRestrictionFunctor` is an equivalence.  Fullness and faithfulness
are proved (`AlgebraicGeometry.full_canonicalRestrictionFunctor`,
`AlgebraicGeometry.faithful_canonicalRestrictionFunctor`), so the whole of the remaining content
is essential surjectivity, which is
[Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA) plus an induction on the number of
points.  This file reduces the label to one existence statement and supplies the construction of
an isomorphism in the category of gluing data, which is residue item (5) of Tag 0BPA *minus* its
one remaining obligation.

## Main results

* `AlgebraicGeometry.glueingDataIsoMk`: an isomorphism of gluing data is a pair of isomorphisms
  — one over the open complement, one over the family of local schemes — making the square with
  the two comparison morphisms commute.  A morphism of the iso-comma category is literally a
  morphism of the comma category, so this is `CategoryTheory.Comma.isoMk` followed by
  `CategoryTheory.ObjectProperty.isoMk` and nothing else.
* `AlgebraicGeometry.isoCanonicalRestrictionFunctorObjMk`: the same, with the source being the
  image of a scheme of finite presentation over `S`.  **This is residue item (5) of Tag 0BPA:
  the square to be checked is the one relating the given gluing datum's own comparison to
  `AlgebraicGeometry.canonicalRestrictionComparison`, and this declaration is the statement that
  nothing beyond that square is needed.**
* `AlgebraicGeometry.essSurj_canonicalRestrictionFunctor_of_exists_iso`: essential surjectivity
  from the existence of such an isomorphism for every gluing datum.
* `AlgebraicGeometry.isEquivalence_canonicalRestrictionFunctor_of_essSurj`: **the label, from
  essential surjectivity alone.**  Its binder list is that of Tag 0E8Q, verbatim and in the same
  order, with one extra hypothesis — `CategoryTheory.Functor.EssSurj` — so the `equivalence`
  label is one `Functor.EssSurj` away and no other hypothesis is needed.

## Why no tag

The `equivalence` label is the single
`(canonicalRestrictionFunctor s hs).IsEquivalence` assertion.  The theorem below carries an
extra hypothesis that Tag 0E8Q does not have, so it does not prove the label.  The point of
stating it is that it isolates what remains — the `example` at the end of this file is the
binder list of Tag 0E8Q with
`EssSurj` as the *only* addition, and it compiles.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

/-- **An isomorphism of gluing data is a pair of isomorphisms and a commuting square.**  The
objects of `AlgebraicGeometry.glueingData` are objects of a comma category satisfying a
property, and its morphisms are literally comma morphisms, so an isomorphism needs no more data
than `CategoryTheory.Comma.isoMk` does. -/
noncomputable def glueingDataIsoMk {P Q : glueingData s hs}
    (l : P.obj.left ≅ Q.obj.left) (r : P.obj.right ≅ Q.obj.right)
    (w : (restrictOpenToPuncturedLocals s hs).map l.hom ≫ Q.obj.hom =
      P.obj.hom ≫ (restrictLocalsToPuncturedLocals s hs).map r.hom) :
    P ≅ Q :=
  ObjectProperty.isoMk _ (Comma.isoMk l r w)

/-- **Residue item (5) of Tag 0BPA, reduced to its square.**  An isomorphism between the gluing
datum attached to a scheme of finite presentation over `S` by
`AlgebraicGeometry.canonicalRestrictionFunctor` and a given gluing datum is: an isomorphism of
the restrictions to the open complement, an isomorphism of the families of restrictions to the
local schemes, and the square saying that the two carry
`AlgebraicGeometry.canonicalRestrictionComparison` to the given datum's own comparison. -/
noncomputable def isoCanonicalRestrictionFunctorObjMk (X : FinitePresentationOver S)
    (G : glueingData s hs)
    (l : (restrictToComplementOfClosedPoints s hs).obj X ≅ G.obj.left)
    (r : (restrictToLocalSchemes s).obj X ≅ G.obj.right)
    (w : (restrictOpenToPuncturedLocals s hs).map l.hom ≫ G.obj.hom =
      (canonicalRestrictionComparison s hs).1.hom.app X ≫
        (restrictLocalsToPuncturedLocals s hs).map r.hom) :
    (canonicalRestrictionFunctor s hs).obj X ≅ G :=
  glueingDataIsoMk s hs l r w

/-- **Essential surjectivity of the canonical restriction functor, from the existence of a
model for every gluing datum.**  This is the whole of what Tag 0BPA and the induction on the
number of points have to supply. -/
theorem essSurj_canonicalRestrictionFunctor_of_exists_iso
    (h : ∀ G : glueingData s hs, ∃ X : FinitePresentationOver S,
      Nonempty ((canonicalRestrictionFunctor s hs).obj X ≅ G)) :
    (canonicalRestrictionFunctor s hs).EssSurj where
  mem_essImage G := h G

include hs in
/-- **Tag 0E8Q's `equivalence` label, from essential surjectivity alone.**  Fullness and
faithfulness are `AlgebraicGeometry.full_canonicalRestrictionFunctor` and
`AlgebraicGeometry.faithful_canonicalRestrictionFunctor`, under the hypotheses of Tag 0E8Q and no
others; so the residue of the label is exactly one `CategoryTheory.Functor.EssSurj`.

No tag attribute for 0E8Q's `equivalence` label is attached: the
label is the single `IsEquivalence` assertion, and this theorem carries a
hypothesis — `hes` — that the tag does not have. -/
theorem isEquivalence_canonicalRestrictionFunctor_of_essSurj (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι)
    (hes : (canonicalRestrictionFunctor s hs).EssSurj) :
    (canonicalRestrictionFunctor s hs).IsEquivalence where
  faithful := faithful_canonicalRestrictionFunctor s hs hqc
  full := full_canonicalRestrictionFunctor s hs hinj hqc
  essSurj := hes

/-! ### The residue

The example below is Tag 0E8Q's binder list verbatim and in the same order, with
`CategoryTheory.Functor.EssSurj` of the canonical restriction functor as the *only* addition,
concluding the label's single assertion.  So the two
constituents need no hypothesis beyond those of the tag, and once essential surjectivity is
proved under these binders the label follows with nothing added. -/
example {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
    (hs : ∀ i, s i ∈ closedPoints S) (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι)
    (hes : (canonicalRestrictionFunctor s hs).EssSurj) :
    (canonicalRestrictionFunctor s hs).IsEquivalence :=
  isEquivalence_canonicalRestrictionFunctor_of_essSurj s hs hinj hqc hes

end AlgebraicGeometry

end
