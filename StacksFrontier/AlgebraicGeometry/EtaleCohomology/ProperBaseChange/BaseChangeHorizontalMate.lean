module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition

/-!
# The étale base change comparison as a mate along the horizontal adjunctions

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. `Stacks.EtaleCohomology.etaleAbelianBaseChange` is built as
the mate, along the two **vertical** inverse-image/direct-image adjunctions `f^{-1} ⊣ f_*` and
`(f')^{-1} ⊣ (f')_*`, of the comparison of the two composite *inverse* images around the square.
This file rewrites it as the mate, along the two **horizontal** adjunctions `g^{-1} ⊣ g_*` and
`(g')^{-1} ⊣ (g')_*`, of the comparison of the two composite *direct* images around the square.

The two descriptions are both standard and neither is the other by definition. The second is the
one in which the identification of a finite direct image with its base change is proved for
sheaves of sets, `AlgebraicGeometry.smallEtaleBaseChangeNatTrans`, so putting the comparison of
the proper base change development into that shape is what makes the two comparable at all: once
both are the horizontal mate of a comparison of composite direct images, the remaining work is to
match the two comparisons of direct images, and direct image is restriction along a functor of
sites, with no left adjoint or sheafification in it.

Nothing geometric happens here. Both steps are formal consequences of the calculus of mates: a
square of four adjunctions has one mate operation taken vertically and one taken horizontally,
and `CategoryTheory.iterated_mateEquiv_conjugateEquiv` says that iterating the two returns the
conjugate of the transformation one started from; while the comparison of composite inverse
images is by construction the comparison of left adjoints attached to the comparison of composite
direct images, so its conjugate is the latter.

## Main results

* `Stacks.EtaleCohomology.conjugateEquiv_etaleAbelianInverseImageCompIso'_hom` and
  `Stacks.EtaleCohomology.conjugateEquiv_etaleAbelianInverseImageCompIso'_inv` — the conjugate,
  under the adjunctions, of the composition comparison for inverse images is the composition
  comparison for direct images.
* `Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso` — **the
  base change comparison is the horizontal mate of the comparison of the two composite direct
  images around the square.**

## Implementation notes

The common composite `X' ⟶ Y` around the square is carried as a named morphism `P` with the two
equations naming it, as in `Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv`: the two
direct-image composition comparisons then both land on `P_*` and compose without an intervening
`eqToIso`, and a consumer with a square presented by a pullback cone can take `P` to be whichever
of the two composites it already has.

The conjugate of a composite of two transformations of left adjoints is the composite of the
conjugates in the opposite order, `CategoryTheory.conjugateEquiv_comp`; the middle adjunction in
that factorization is the one for `P`, which is why the named composite is needed in the proof
and not only in the statement.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section CompIso

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)

/-- **The composition comparison for inverse images is the conjugate of the composition
comparison for direct images.** `Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'` is by
construction the comparison of left adjoints attached to
`Stacks.EtaleCohomology.etaleAbelianDirectImageCompIso'`, and this is that construction read
back: conjugation under the adjunctions carries the one to the other. -/
public theorem conjugateEquiv_etaleAbelianInverseImageCompIso'_hom :
    conjugateEquiv ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).comp
          (etaleAbelianInverseImageDirectImageAdj.{u, v} f))
        (etaleAbelianInverseImageDirectImageAdj.{u, v} fg)
        (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).hom =
      (etaleAbelianDirectImageCompIso'.{u, v} f g fg hfg).hom := by
  rw [etaleAbelianInverseImageCompIso', Iso.symm_hom]
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

/-- The inverse half of
`Stacks.EtaleCohomology.conjugateEquiv_etaleAbelianInverseImageCompIso'_hom`: conjugation in the
other direction carries the inverse of the comparison of inverse images to the inverse of the
comparison of direct images. -/
public theorem conjugateEquiv_etaleAbelianInverseImageCompIso'_inv :
    conjugateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} fg)
        ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).comp
          (etaleAbelianInverseImageDirectImageAdj.{u, v} f))
        (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).inv =
      (etaleAbelianDirectImageCompIso'.{u, v} f g fg hfg).inv := by
  rw [etaleAbelianInverseImageCompIso', Iso.symm_inv, Adjunction.leftAdjointCompIso]
  simp

end CompIso

/-- **The étale base change comparison is the mate, along the two horizontal adjunctions, of the
comparison of the two composite direct images around the square.** For a commutative square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
and a named morphism `P : X' ⟶ Y` presenting the common composite, the comparison
`g^{-1} f_* ⟶ (f')_* (g')^{-1}` of `Stacks.EtaleCohomology.etaleAbelianBaseChange` is the mate,
under `(g')^{-1} ⊣ (g')_*` and `g^{-1} ⊣ g_*`, of the isomorphism
`(g')_* f_* ≅ P_* ≅ (f')_* g_*`.

This is the shape in which the identification of a finite direct image with its base change is
available for sheaves of sets, as `AlgebraicGeometry.smallEtaleBaseChangeNatTrans`; the
comparison here is built instead as the vertical mate of the comparison of composite inverse
images, which is why the two needed to be matched.

The proof is `CategoryTheory.iterated_mateEquiv_conjugateEquiv`, that taking the mate of a square
of four adjunctions vertically and then horizontally gives the conjugate, together with the
identification of the conjugate of the inverse-image composition comparison with the
direct-image one. -/
public theorem etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hyp : g' ≫ f = f' ≫ g) (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g) :
    etaleAbelianBaseChange.{u, v} f g g' f' hyp =
      (mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} g')
          (etaleAbelianInverseImageDirectImageAdj.{u, v} g)).symm
        (TwoSquare.mk _ _ _ _
          ((etaleAbelianDirectImageCompIso'.{u, v} g' f P hP₁).hom ≫
            (etaleAbelianDirectImageCompIso'.{u, v} f' g P hP₂).inv)) := by
  rw [etaleAbelianBaseChange_eq_mateEquiv.{u, v} f g g' f' hyp P hP₁ hP₂]
  refine (Equiv.eq_symm_apply _).2 ?_
  refine (iterated_mateEquiv_conjugateEquiv
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g') _).trans ?_
  rw [← conjugateEquiv_comp (adj₂ := etaleAbelianInverseImageDirectImageAdj.{u, v} P),
    conjugateEquiv_etaleAbelianInverseImageCompIso'_hom,
    conjugateEquiv_etaleAbelianInverseImageCompIso'_inv]

end Stacks.EtaleCohomology

end
