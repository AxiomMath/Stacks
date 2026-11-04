module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardBaseChangeCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.CategoryTheory.Adjunction.MateOfUnitSquareTransport

/-!
# The canonical étale base-change comparison, reduced to one unit square

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  `AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison` is the canonical
base-change comparison `(f_*F)|_{Y'} ⟶ f'_*(F|_{X'})` of the square, and Stacks 03LX for the
ordinary direct image — hence, by
`AlgebraicGeometry.Space.isIso_moduleHigherPushforwardEtaleBaseChangeComparison`, the whole of
Stacks 071Z — read as a statement about the canonical map is the assertion that it is
invertible.

`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` is an isomorphism with exactly
those endpoints, obtained from the sheaf-of-sets base-change isomorphism of Stacks 03LR,
part (1) by transporting the module structures; what is not known about it is that it *is* the
canonical comparison.  This file reduces that identification — and so the invertibility of the
canonical comparison — to a single equation between two morphisms of `𝒪_Y`-modules, in which
only the **units** of the two étale adjunctions occur.

## Main results

* `AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison_eq_of_unitSquare`: **the
  reduction.**  If the unit square of the two étale adjunctions commutes — that is, if the unit
  of `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` along `g`, followed by the direct
  image along `g` of `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`, agrees with
  the direct image along `f` of the unit along `i`, followed by the comparison of the two
  composite direct images around the square — then the canonical comparison *is* that
  isomorphism.
* `AlgebraicGeometry.Space.isIso_moduleEtaleBaseChangeComparison_of_unitSquare`: hence the
  canonical comparison is invertible.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardSquareComparison`: the comparison
  `i_*f_* ⟶ f'_*g_*` of the two composite direct images around the square, which is the 2-cell
  whose mate `AlgebraicGeometry.Space.moduleBaseChangeMap` is.

## Implementation notes

*Why the units and not the counits.*  `AlgebraicGeometry.Space.moduleBaseChangeMap` is the mate
of the comparison of the two composite direct images across the two adjunctions of the
*horizontal*, étale morphisms, and `CategoryTheory.mateEquiv` builds that mate out of the unit
of one adjunction and the counit of the other.  Reading the mate backwards through the counit —
which is what `AlgebraicGeometry.Space.moduleBaseChangeMap_adjoint_split` does — would require a
computation of the counit of `AlgebraicGeometry.Space.modulePullbackAdjunction`, which this
development does not have.  `CategoryTheory.mateEquiv_symm_eq_of_unit` recognises a mate from
the square it makes with the two *units* instead, and the units are the computable ones.  So no
counit is needed here, and none is used.

*Why the transported spelling.*  The canonical comparison is stated with
`AlgebraicGeometry.Space.etaleModulePullback`, étale restriction, in the two horizontal slots,
whereas the mate is built from `AlgebraicGeometry.Space.modulePullback`; the two agree by
Stacks 03LW, `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, which is also how
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is obtained from
`AlgebraicGeometry.Space.modulePullbackAdjunction`.
`CategoryTheory.mateEquiv_symm_whisker_eq_of_unit` is the recognition criterion read through
exactly that transport, so the hypothesis below is stated with the étale units throughout and
the conjugation by Stacks 03LW is discharged once, abstractly.

*Why the reduction is a term and not a tactic proof.*  The two sides are composites of functors
between the module categories of four algebraic spaces, and a `rw` against the definition of
`AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison` produces a motive whose kernel check
runs out of its budget.  The statement of
`CategoryTheory.mateEquiv_symm_whisker_eq_of_unit` is definitionally the statement proved here,
so a single application with its arguments written out is accepted at once.  This is the same
factorization — abstract lemma over opaque functors, one instantiation — that
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleBaseChangeMate.lean` records as necessary in this
area.

*What is still owed.*  The unit square itself.  It is an equation between two morphisms
`f_*F ⟶ g_*f'_*(F|_{X'})` of `𝒪_Y`-modules, so it can be checked on sections; both sides are
built from the unit of étale restriction, the base-change isomorphism of Stacks 03LR, part (1)
and the comparison of direct images along a composite, and on sections each of those is a
reindexing of sections along a canonical projection.  No `@[stacks]` attribute moves here: the
tags of Stacks 03LX and Stacks 071Z stay where they were.

## References

* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **The comparison `i_*f_* ⟶ f'_*g_*` of the two composite direct images around a commutative
square** of algebraic spaces: both composites are the direct image along the common composite
`X' ⟶ Y` of the square, by the direct-image half of Stacks 03LU.

This is the 2-cell whose mate, across the two adjunctions of the horizontal morphisms,
`AlgebraicGeometry.Space.moduleBaseChangeMap` is. -/
def modulePushforwardSquareComparison (comm : i ≫ f = f' ≫ g) :
    modulePushforward B S hS i ⋙ modulePushforward B S hS f ⟶
      modulePushforward B S hS f' ⋙ modulePushforward B S hS g :=
  (modulePushforwardCompIso B S hS i f).hom ≫
    eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) comm) ≫
    (modulePushforwardCompIso B S hS f' g).inv

/-- **The canonical étale base-change comparison is the base-change isomorphism of Stacks 03LX,
as soon as the unit square commutes.**

The hypothesis is the square made by the units of the two étale adjunctions of Stacks 03LU: for
every `𝒪_X`-module `K`, the unit `f_*K ⟶ g_*((f_*K)|_{Y'})` along `g` followed by the direct
image along `g` of `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` agrees with the
direct image along `f` of the unit `K ⟶ i_*(K|_{X'})` along `i`, followed by the comparison of
the two composite direct images around the square.

Granting it, `CategoryTheory.mateEquiv_symm_whisker_eq_of_unit` identifies the mate
`AlgebraicGeometry.Space.moduleBaseChangeMap`, conjugated into the étale-restriction spelling by
Stacks 03LW, with that isomorphism — and that conjugated mate is
`AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison` by definition.

No counit of `AlgebraicGeometry.Space.modulePullbackAdjunction` enters, in the statement or in
the proof. -/
theorem moduleEtaleBaseChangeComparison_eq_of_unitSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    (hunit : ∀ K : Modules.{u, u} B S hS X.1 X.2,
      (etaleModulePullbackAdjunction B S hS g hg).unit.app
            ((modulePushforward B S hS f).obj K) ≫
          (modulePushforward B S hS g).map
            ((modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg).inv.app K) =
        (modulePushforward B S hS f).map
            ((etaleModulePullbackAdjunction B S hS i
              (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).unit.app K) ≫
          (modulePushforwardSquareComparison B S hS i f' f g sq.w).app
            ((etaleModulePullback B S hS i
              (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).obj K)) :
    moduleEtaleBaseChangeComparison B S hS i f' f g sq hg =
      (modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg).inv :=
  mateEquiv_symm_whisker_eq_of_unit (modulePullbackAdjunction B S hS i)
    (modulePullbackAdjunction B S hS g)
    (modulePullbackIsoEtaleModulePullback B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
    (modulePullbackIsoEtaleModulePullback B S hS g hg)
    (modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg).inv
    (modulePushforwardSquareComparison B S hS i f' f g sq.w) hunit

/-- **Stacks 03LX for the ordinary direct image, read as a statement about the canonical map,
reduced to the unit square.**  If the unit square of
`AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison_eq_of_unitSquare` commutes, then the
canonical base-change comparison of the ordinary direct images is an isomorphism.

With `AlgebraicGeometry.Space.isIso_moduleHigherPushforwardEtaleBaseChangeComparison` this is
the whole of Stacks 071Z for the canonical maps: nothing in positive degree is owed beyond the
unit square. -/
theorem isIso_moduleEtaleBaseChangeComparison_of_unitSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    (hunit : ∀ K : Modules.{u, u} B S hS X.1 X.2,
      (etaleModulePullbackAdjunction B S hS g hg).unit.app
            ((modulePushforward B S hS f).obj K) ≫
          (modulePushforward B S hS g).map
            ((modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg).inv.app K) =
        (modulePushforward B S hS f).map
            ((etaleModulePullbackAdjunction B S hS i
              (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).unit.app K) ≫
          (modulePushforwardSquareComparison B S hS i f' f g sq.w).app
            ((etaleModulePullback B S hS i
              (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).obj K)) :
    IsIso (moduleEtaleBaseChangeComparison B S hS i f' f g sq hg) := by
  rw [moduleEtaleBaseChangeComparison_eq_of_unitSquare B S hS i f' f g sq hg hunit]
  infer_instance

end AlgebraicGeometry.Space

end
