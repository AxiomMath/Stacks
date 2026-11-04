module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMate

/-!
# Pasting of degree-zero base change maps of squares of algebraic spaces

Let

```
X'' --h'--> X' --g'--> X
 |f''        |f'        |f
 v           v          v
Y'' --h-->  Y' --g-->  Y
```

be two commutative squares of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, sharing the vertical edge `f'`.  The degree-zero base change map of the outer rectangle,
`(h ≫ g)^*f_* ⟶ f''_*(h' ≫ g')^*`, is the composite of the base change maps of the two squares,
read through the comparisons `(h ≫ g)^* ≅ h^* ∘ g^*` and `(h' ≫ g')^* ≅ (h')^* ∘ (g')^*` of
**Stacks 03LU**:

`(h ≫ g)^*f_* ≅ h^*g^*f_* ⟶ h^*f'_*(g')^* ⟶ f''_*(h')^*(g')^* ≅ f''_*(h' ≫ g')^*`.

This is the degree-zero shape of **Stacks 0E47**.  The companion law for two squares stacked
along a horizontal edge, with the comparisons of the direct images along the composite vertical
legs, is the degree-zero shape of **Stacks 0E46**.

## Main results

* `AlgebraicGeometry.Space.abstractBaseChange_paste`: the pasting law for an abstract calculus
  of inverse images, direct images, adjunctions, composition comparisons and base change maps,
  from the associativity of the comparisons and the adjoint characterization of the base change
  maps.
* `AlgebraicGeometry.Space.moduleBaseChangeMap_paste`: **the pasting law** for the base change
  maps of `𝒪`-modules of two squares of algebraic spaces stacked along the base (the shape of
  Stacks 0E47).
* `AlgebraicGeometry.Space.moduleBaseChangeMap_comp`: the pasting law for two squares stacked
  along a horizontal edge, read through the comparisons of the direct images along the two
  composite vertical legs (the shape of Stacks 0E46).
* `AlgebraicGeometry.Space.moduleBaseChangeMap_congr`: the base change map is compatible with
  equalities of the two horizontal morphisms of its square.

## Implementation notes

The argument is the abstract pasting lemmas
`Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal` and
`Stacks.Cohomology.DerivedBaseChangePasting.baseChangeMate_horizontal`, fed with the associativity
coherence `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`, the compatibility of the
comparison with an equality of either of its two morphisms, and the adjoint characterization
`AlgebraicGeometry.Space.moduleBaseChangeMap_adjoint_split'`.

The pasting argument produces one object under several spellings: a composite of functors
applied to a module is written either as `(F ⋙ G).obj M` or as `G.obj (F.obj M)`, and a threefold
composite of morphisms of algebraic spaces is bracketed either way.  The spellings are
definitionally equal, but when the inverse image is `AlgebraicGeometry.Space.modulePullback` the
kernel identifies them by unfolding the inverse image and runs out of its budget.  So the
argument is carried out in `AlgebraicGeometry.Space.abstractBaseChange_paste` for *variable*
families, where the identification is immediate, and
`AlgebraicGeometry.Space.moduleBaseChangeMap_paste` is the single instantiation of it, whose
hypotheses are the library's lemmas verbatim.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.TwoSquare
open Stacks.Cohomology.DerivedBaseChangePasting (transportNatTrans squareComparison_horizontal
  baseChangeMate_horizontal comp₄_inv squareComparison_comp_symm twoSquare_paste_of_app
  mate_twoSquare_paste)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Abstract

/-! ### The pasting law for an abstract inverse-image calculus

The statements of this section are about an arbitrary family `P` of inverse images, `Q` of
direct images, adjunctions `P f ⊣ Q f`, comparisons `P g ⋙ P f ≅ P (f ≫ g)` and base change maps
satisfying the adjoint characterization.  They are instantiated below at the inverse and direct
images of `𝒪`-modules on algebraic spaces.  Keeping the families as variables is what keeps the
kernel from unfolding `AlgebraicGeometry.Space.modulePullback` while it identifies the several
spellings of one object that the pasting argument produces. -/

variable
  (P : ∀ (X Y : AlgebraicSpaces B S hS), (X ⟶ Y) →
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2)
  (Q : ∀ (X Y : AlgebraicSpaces B S hS), (X ⟶ Y) →
    Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2)
  (adj : ∀ (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y), P X Y f ⊣ Q X Y f)
  (cmp : ∀ (X Y Z : AlgebraicSpaces B S hS) (f : X ⟶ Y) (g : Y ⟶ Z),
    P Y Z g ⋙ P X Y f ≅ P X Z (f ≫ g))
  (bc : ∀ (X Y X' Y' : AlgebraicSpaces B S hS) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X), g' ≫ f = f' ≫ g → (Q X Y f ⋙ P Y' Y g ⟶ P X' X g' ⋙ Q X' Y' f'))

/-- The comparison of an abstract inverse-image calculus is compatible with an equality of its
second morphism, the transports being written along the reversed equality. -/
theorem abstractCompIso_congr_right {V W Z : AlgebraicSpaces B S hS} (a : V ⟶ W)
    {k₁ k₂ : W ⟶ Z} (e : k₂ = k₁) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (P _ _ a).map ((transportNatTrans (congrArg (fun k : W ⟶ Z => P _ _ k) e).symm).app M) ≫
        (cmp _ _ _ a k₂).hom.app M =
      (cmp _ _ _ a k₁).hom.app M ≫
        (transportNatTrans (congrArg (fun k : W ⟶ Z => P _ _ (a ≫ k)) e).symm).app M := by
  subst e
  simp [transportNatTrans]

/-- The comparison of an abstract inverse-image calculus is compatible with an equality of its
first morphism, the transports being written along the reversed equality. -/
theorem abstractCompIso_congr_left {V W Z : AlgebraicSpaces B S hS} {k₁ k₂ : V ⟶ W}
    (e : k₂ = k₁) (a : W ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (transportNatTrans (congrArg (fun k : V ⟶ W => P _ _ k) e).symm).app ((P _ _ a).obj M) ≫
        (cmp _ _ _ k₂ a).hom.app M =
      (cmp _ _ _ k₁ a).hom.app M ≫
        (transportNatTrans (congrArg (fun k : V ⟶ W => P _ _ (k ≫ a)) e).symm).app M := by
  subst e
  simp [transportNatTrans]

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h : Y'' ⟶ Y') (f'' : X'' ⟶ Y'') (h' : X'' ⟶ X')

/-- **The pasting law for an abstract inverse-image calculus.**  If the comparisons are
associative and every base change map is characterized by its adjoint, then the base change map
of a rectangle stacked from two squares along the base is the composite of the base change maps
of the two squares, read through the comparisons for the two composite horizontal legs. -/
theorem abstractBaseChange_paste
    (hassoc : ∀ (W X Y Z : AlgebraicSpaces B S hS) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
      (M : Modules.{u, u} B S hS Z.1 Z.2),
      (P _ _ f).map ((cmp _ _ _ g h).hom.app M) ≫ (cmp _ _ _ f (g ≫ h)).hom.app M =
        (cmp _ _ _ f g).hom.app ((P _ _ h).obj M) ≫ (cmp _ _ _ (f ≫ g) h).hom.app M)
    (hbc : ∀ (X Y X' Y' : AlgebraicSpaces B S hS) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
      (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g) (K : Modules.{u, u} B S hS X.1 X.2),
      ((adj _ _ f').homEquiv _ _).symm ((bc _ _ _ _ f g f' g' comm).app K) =
        ((cmp _ _ _ f' g).hom.app ((Q _ _ f).obj K) ≫
            (transportNatTrans (congrArg (fun k : X' ⟶ Y => P _ _ k) comm).symm).app
              ((Q _ _ f).obj K) ≫
            (cmp _ _ _ g' f).inv.app ((Q _ _ f).obj K)) ≫
          (P _ _ g').map ((adj _ _ f).counit.app K))
    (comm₁ : g' ≫ f = f' ≫ g) (comm₂ : h' ≫ f' = f'' ≫ h) (w : (h' ≫ g') ≫ f = f'' ≫ (h ≫ g))
    (K : Modules.{u, u} B S hS X.1 X.2) :
    (bc _ _ _ _ f (h ≫ g) f'' (h' ≫ g') w).app K =
      (cmp _ _ _ h g).inv.app ((Q _ _ f).obj K) ≫
        (P _ _ h).map ((bc _ _ _ _ f g f' g' comm₁).app K) ≫
        (bc _ _ _ _ f' h f'' h' comm₂).app ((P _ _ g').obj K) ≫
        (Q _ _ f'').map ((cmp _ _ _ h' g').hom.app K) := by
  refine (baseChangeMate_horizontal (adj _ _ f) (adj _ _ f') (adj _ _ f'')
    (cmp _ _ _ h' g') (cmp _ _ _ h g)
    (fun M => (cmp _ _ _ f' g).hom.app M ≫
      (transportNatTrans (congrArg (fun k : X' ⟶ Y => P _ _ k) comm₁).symm).app M ≫
      (cmp _ _ _ g' f).inv.app M)
    (cmp _ _ _ f'' h).hom (transportNatTrans (congrArg (fun k : X'' ⟶ Y' => P _ _ k) comm₂).symm)
    (cmp _ _ _ h' f').inv
    (fun M => (cmp _ _ _ f'' (h ≫ g)).hom.app M ≫
      (transportNatTrans (congrArg (fun k : X'' ⟶ Y => P _ _ k) w).symm).app M ≫
      (cmp _ _ _ (h' ≫ g') f).inv.app M)
    (fun M => squareComparison_horizontal
      (cmp _ _ _ h g) (cmp _ _ _ h' g') (cmp _ _ _ f' g) (cmp _ _ _ g' f)
      (cmp _ _ _ f'' h) (cmp _ _ _ h' f') (cmp _ _ _ f'' (h ≫ g)) (cmp _ _ _ (h' ≫ g') f)
      (cmp _ _ _ (f'' ≫ h) g) (cmp _ _ _ h' (g' ≫ f)) (cmp _ _ _ h' (f' ≫ g))
      (cmp _ _ _ (h' ≫ f') g)
      (congrArg (fun k : X' ⟶ Y => P _ _ k) comm₁).symm
      (congrArg (fun k : X'' ⟶ Y' => P _ _ k) comm₂).symm
      (congrArg (fun k : X'' ⟶ Y => P _ _ k) w).symm
      (congrArg (fun k : X' ⟶ Y => P _ _ (h' ≫ k)) comm₁).symm
      (congrArg (fun k : X'' ⟶ Y' => P _ _ (k ≫ g)) comm₂).symm
      (fun M => (hassoc _ _ _ _ f'' h g M).symm)
      (fun M => (hassoc _ _ _ _ h' g' f M).symm)
      (fun M => (hassoc _ _ _ _ h' f' g M).symm)
      (fun M => abstractCompIso_congr_right P cmp h' comm₁ M)
      (fun M => abstractCompIso_congr_left P cmp comm₂ g M) M)
    K _ _ _ (hbc _ _ _ _ f g f' g' comm₁ K) (hbc _ _ _ _ f' h f'' h' comm₂ _)
    (hbc _ _ _ _ f (h ≫ g) f'' (h' ≫ g') w K)).symm.trans ?_
  simp only

/-- The comparison of an abstract inverse-image calculus is compatible with an equality of its
second morphism. -/
theorem abstractCompIso_congr_right' {V W Z : AlgebraicSpaces B S hS} (a : V ⟶ W)
    {k₁ k₂ : W ⟶ Z} (e : k₁ = k₂) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (P _ _ a).map ((transportNatTrans (congrArg (fun k : W ⟶ Z => P _ _ k) e)).app M) ≫
        (cmp _ _ _ a k₂).hom.app M =
      (cmp _ _ _ a k₁).hom.app M ≫
        (transportNatTrans (congrArg (fun k : W ⟶ Z => P _ _ (a ≫ k)) e)).app M :=
  abstractCompIso_congr_right P cmp a e.symm M

/-- The comparison of an abstract inverse-image calculus is compatible with an equality of its
first morphism. -/
theorem abstractCompIso_congr_left' {V W Z : AlgebraicSpaces B S hS} {k₁ k₂ : V ⟶ W}
    (e : k₁ = k₂) (a : W ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (transportNatTrans (congrArg (fun k : V ⟶ W => P _ _ k) e)).app ((P _ _ a).obj M) ≫
        (cmp _ _ _ k₂ a).hom.app M =
      (cmp _ _ _ k₁ a).hom.app M ≫
        (transportNatTrans (congrArg (fun k : V ⟶ W => P _ _ (k ≫ a)) e)).app M :=
  abstractCompIso_congr_left P cmp e.symm a M

/-- **An abstract base change map is compatible with an equality of the two horizontal
morphisms**, up to the transports of the inverse images along the two equalities. -/
theorem abstractBaseChange_congr {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (f' : X' ⟶ Y') {g₁ g₂ : Y' ⟶ Y} {g₁' g₂' : X' ⟶ X} (p : g₁ = g₂) (p' : g₁' = g₂')
    (w₁ : g₁' ≫ f = f' ≫ g₁) (w₂ : g₂' ≫ f = f' ≫ g₂) (K : Modules.{u, u} B S hS X.1 X.2) :
    (eqToIso (congrArg (fun k : Y' ⟶ Y => (P _ _ k).obj ((Q _ _ f).obj K)) p)).hom ≫
        (bc _ _ _ _ f g₂ f' g₂' w₂).app K =
      (bc _ _ _ _ f g₁ f' g₁' w₁).app K ≫
        (Q _ _ f').map (eqToIso (congrArg (fun k : X' ⟶ X => (P _ _ k).obj K) p')).hom := by
  subst p p'
  simp

section Vertical

variable {X X' Y Y' Z Z' : AlgebraicSpaces B S hS} (f₁ : X ⟶ Y) (g : Y' ⟶ Y) (f₁' : X' ⟶ Y')
    (g' : X' ⟶ X) (f₂ : Y ⟶ Z) (k : Z' ⟶ Z) (f₂' : Y' ⟶ Z')

/-- The component identity behind the vertical pasting of two squares of inverse images, for an
abstract inverse-image calculus with associative comparisons.  It is the horizontal identity of
`Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal` read on the transposed
diagram and inverted. -/
theorem abstractPullbackSquare_paste_app
    (hassoc : ∀ (W X Y Z : AlgebraicSpaces B S hS) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
      (M : Modules.{u, u} B S hS Z.1 Z.2),
      (P _ _ f).map ((cmp _ _ _ g h).hom.app M) ≫ (cmp _ _ _ f (g ≫ h)).hom.app M =
        (cmp _ _ _ f g).hom.app ((P _ _ h).obj M) ≫ (cmp _ _ _ (f ≫ g) h).hom.app M)
    (comm₁ : g' ≫ f₁ = f₁' ≫ g) (comm₂ : g ≫ f₂ = f₂' ≫ k)
    (w : g' ≫ (f₁ ≫ f₂) = (f₁' ≫ f₂') ≫ k) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (cmp _ _ _ (f₁' ≫ f₂') k).hom.app M ≫
        (transportNatTrans (congrArg (fun q : X' ⟶ Z => P _ _ q) w).symm).app M ≫
        (cmp _ _ _ g' (f₁ ≫ f₂)).inv.app M =
      (cmp _ _ _ f₁' f₂').inv.app ((P _ _ k).obj M) ≫
        (P _ _ f₁').map ((cmp _ _ _ f₂' k).hom.app M ≫
          (transportNatTrans (congrArg (fun q : Y' ⟶ Z => P _ _ q) comm₂).symm).app M ≫
          (cmp _ _ _ g f₂).inv.app M) ≫
        ((cmp _ _ _ f₁' g).hom.app ((P _ _ f₂).obj M) ≫
          (transportNatTrans (congrArg (fun q : X' ⟶ Y => P _ _ q) comm₁).symm).app
            ((P _ _ f₂).obj M) ≫
          (cmp _ _ _ g' f₁).inv.app ((P _ _ f₂).obj M)) ≫
        (P _ _ g').map ((cmp _ _ _ f₁ f₂).hom.app M) :=
  (comp₄_inv
      ((P _ _ g').map ((cmp _ _ _ f₁ f₂).inv.app M))
      ((P _ _ g').map ((cmp _ _ _ f₁ f₂).hom.app M))
      ((P _ _ f₁').map ((cmp _ _ _ g f₂).hom.app M ≫
        (transportNatTrans (congrArg (fun q : Y' ⟶ Z => P _ _ q) comm₂)).app M ≫
        (cmp _ _ _ f₂' k).inv.app M))
      ((P _ _ f₁').map ((cmp _ _ _ f₂' k).hom.app M ≫
        (transportNatTrans (congrArg (fun q : Y' ⟶ Z => P _ _ q) comm₂).symm).app M ≫
        (cmp _ _ _ g f₂).inv.app M))
      (by simp [← Functor.map_comp])
      (squareComparison_comp_symm (cmp _ _ _ f₁' g) (cmp _ _ _ g' f₁)
        (congrArg (fun q : X' ⟶ Y => P _ _ q) comm₁).symm
        (congrArg (fun q : X' ⟶ Y => P _ _ q) comm₁) ((P _ _ f₂).obj M))
      (by
        rw [← Functor.map_comp, squareComparison_comp_symm (cmp _ _ _ f₂' k) (cmp _ _ _ g f₂)
          (congrArg (fun q : Y' ⟶ Z => P _ _ q) comm₂).symm
          (congrArg (fun q : Y' ⟶ Z => P _ _ q) comm₂) M]
        exact CategoryTheory.Functor.map_id _ _)
      (Iso.inv_hom_id_app (cmp _ _ _ f₁' f₂') ((P _ _ k).obj M))
      (squareComparison_comp_symm (cmp _ _ _ g' (f₁ ≫ f₂)) (cmp _ _ _ (f₁' ≫ f₂') k)
        (congrArg (fun q : X' ⟶ Z => P _ _ q) w)
        (congrArg (fun q : X' ⟶ Z => P _ _ q) w).symm M)
      (squareComparison_horizontal
        (cmp _ _ _ f₁ f₂) (cmp _ _ _ f₁' f₂') (cmp _ _ _ g f₂) (cmp _ _ _ f₂' k)
        (cmp _ _ _ g' f₁) (cmp _ _ _ f₁' g) (cmp _ _ _ g' (f₁ ≫ f₂)) (cmp _ _ _ (f₁' ≫ f₂') k)
        (cmp _ _ _ (g' ≫ f₁) f₂) (cmp _ _ _ f₁' (f₂' ≫ k)) (cmp _ _ _ f₁' (g ≫ f₂))
        (cmp _ _ _ (f₁' ≫ g) f₂)
        (congrArg (fun q : Y' ⟶ Z => P _ _ q) comm₂)
        (congrArg (fun q : X' ⟶ Y => P _ _ q) comm₁)
        (congrArg (fun q : X' ⟶ Z => P _ _ q) w)
        (congrArg (fun q : Y' ⟶ Z => P _ _ (f₁' ≫ q)) comm₂)
        (congrArg (fun q : X' ⟶ Y => P _ _ (q ≫ f₂)) comm₁)
        (fun M => (hassoc _ _ _ _ g' f₁ f₂ M).symm)
        (fun M => (hassoc _ _ _ _ f₁' f₂' k M).symm)
        (fun M => (hassoc _ _ _ _ f₁' g f₂ M).symm)
        (fun M => abstractCompIso_congr_right' P cmp f₁' comm₂ M)
        (fun M => abstractCompIso_congr_left' P cmp comm₁ f₂ M) M)).symm

variable (pcmp : ∀ (X Y Z : AlgebraicSpaces B S hS) (f : X ⟶ Y) (g : Y ⟶ Z),
    Q X Y f ⋙ Q Y Z g ≅ Q X Z (f ≫ g))

/-- **The vertical pasting law for an abstract inverse-image calculus.**  If the comparisons are
associative, their conjugates are the comparisons of the direct images, and every base change map
is the mate of the comparison of the inverse images around its square, then the base change map
of a rectangle stacked from two squares along a horizontal edge is the composite of the base
change maps of the two squares, read through the comparisons of the direct images along the two
composite vertical legs. -/
theorem abstractBaseChange_comp
    (hassoc : ∀ (W X Y Z : AlgebraicSpaces B S hS) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
      (M : Modules.{u, u} B S hS Z.1 Z.2),
      (P _ _ f).map ((cmp _ _ _ g h).hom.app M) ≫ (cmp _ _ _ f (g ≫ h)).hom.app M =
        (cmp _ _ _ f g).hom.app ((P _ _ h).obj M) ≫ (cmp _ _ _ (f ≫ g) h).hom.app M)
    (hmate : ∀ (X Y X' Y' : AlgebraicSpaces B S hS) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
      (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g),
      bc _ _ _ _ f g f' g' comm =
        mateEquiv (adj _ _ f) (adj _ _ f')
          (TwoSquare.mk (P _ _ g) (P _ _ f) (P _ _ f') (P _ _ g')
            ((cmp _ _ _ f' g).hom ≫
              transportNatTrans (congrArg (fun q : X' ⟶ Y => P _ _ q) comm).symm ≫
              (cmp _ _ _ g' f).inv)))
    (hconj : ∀ (X Y Z : AlgebraicSpaces B S hS) (f : X ⟶ Y) (g : Y ⟶ Z),
      conjugateEquiv (adj _ _ (f ≫ g)) ((adj _ _ g).comp (adj _ _ f)) (cmp _ _ _ f g).hom =
        (pcmp _ _ _ f g).inv)
    (hconj' : ∀ (X Y Z : AlgebraicSpaces B S hS) (f : X ⟶ Y) (g : Y ⟶ Z),
      conjugateEquiv ((adj _ _ g).comp (adj _ _ f)) (adj _ _ (f ≫ g)) (cmp _ _ _ f g).inv =
        (pcmp _ _ _ f g).hom)
    (comm₁ : g' ≫ f₁ = f₁' ≫ g) (comm₂ : g ≫ f₂ = f₂' ≫ k)
    (w : g' ≫ (f₁ ≫ f₂) = (f₁' ≫ f₂') ≫ k) (K : Modules.{u, u} B S hS X.1 X.2) :
    (bc _ _ _ _ (f₁ ≫ f₂) k (f₁' ≫ f₂') g' w).app K =
      (P _ _ k).map ((pcmp _ _ _ f₁ f₂).inv.app K) ≫
        (bc _ _ _ _ f₂ k f₂' g comm₂).app ((Q _ _ f₁).obj K) ≫
        (Q _ _ f₂').map ((bc _ _ _ _ f₁ g f₁' g' comm₁).app K) ≫
        (pcmp _ _ _ f₁' f₂').hom.app ((P _ _ g').obj K) := by
  have hSo := twoSquare_paste_of_app
    (cmp _ _ _ (f₁' ≫ f₂') k).hom
    (transportNatTrans (congrArg (fun q : X' ⟶ Z => P _ _ q) w).symm)
    (cmp _ _ _ g' (f₁ ≫ f₂)).inv
    (cmp _ _ _ f₂' k).hom
    (transportNatTrans (congrArg (fun q : Y' ⟶ Z => P _ _ q) comm₂).symm)
    (cmp _ _ _ g f₂).inv
    (cmp _ _ _ f₁' g).hom
    (transportNatTrans (congrArg (fun q : X' ⟶ Y => P _ _ q) comm₁).symm)
    (cmp _ _ _ g' f₁).inv
    (cmp _ _ _ f₁ f₂).hom (cmp _ _ _ f₁' f₂').inv
    _ (fun _ => rfl) _ (fun _ => rfl) _ (fun _ => rfl)
    (abstractPullbackSquare_paste_app P cmp f₁ g f₁' g' f₂ k f₂' hassoc comm₁ comm₂ w)
  have hpaste := mate_twoSquare_paste (adj _ _ f₂) (adj _ _ f₂') (adj _ _ f₁) (adj _ _ f₁')
    (adj _ _ (f₁ ≫ f₂)) (adj _ _ (f₁' ≫ f₂')) _ _ _ _ _ _ _ hSo
    (hconj _ _ _ f₁ f₂) (hconj' _ _ _ f₁' f₂')
  rw [← hmate (comm := w), ← hmate (comm := comm₂), ← hmate (comm := comm₁)] at hpaste
  have h := congr_app (congrArg TwoSquare.natTrans hpaste) K
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, TwoSquare.natTrans,
    TwoSquare.mk, Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc] at h
  exact h

end Vertical

end Abstract

section Paste

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h : Y'' ⟶ Y') (f'' : X'' ⟶ Y'') (h' : X'' ⟶ X')

/-- **The pasting law for the degree-zero base change maps of two squares stacked along the
base.**  For commutative squares `(f, g, f', g')` and `(f', h, f'', h')` sharing the vertical edge
`f'`, the base change map `(h ≫ g)^*f_* ⟶ f''_*(h' ≫ g')^*` of the outer rectangle is

`(h ≫ g)^*f_* ≅ h^*g^*f_* ⟶ h^*f'_*(g')^* ⟶ f''_*(h')^*(g')^* ≅ f''_*(h' ≫ g')^*`,

the composite of the base change maps of the two squares read through the comparisons of
Stacks 03LU for the two composite horizontal legs.  This is the degree-zero shape of
Stacks 0E47. -/
theorem moduleBaseChangeMap_paste (comm₁ : g' ≫ f = f' ≫ g) (comm₂ : h' ≫ f' = f'' ≫ h)
    (w : (h' ≫ g') ≫ f = f'' ≫ (h ≫ g)) (K : Modules.{u, u} B S hS X.1 X.2) :
    (moduleBaseChangeMap f (h ≫ g) f'' (h' ≫ g') w).app K =
      (modulePullbackCompIso B S hS h g).inv.app ((modulePushforward B S hS f).obj K) ≫
        (modulePullback B S hS h).map ((moduleBaseChangeMap f g f' g' comm₁).app K) ≫
        (moduleBaseChangeMap f' h f'' h' comm₂).app ((modulePullback B S hS g').obj K) ≫
        (modulePushforward B S hS f'').map ((modulePullbackCompIso B S hS h' g').hom.app K) :=
  abstractBaseChange_paste (@modulePullback B S hS) (@modulePushforward B S hS)
    (@modulePullbackAdjunction B S hS) (@modulePullbackCompIso B S hS)
    (@moduleBaseChangeMap B S hS) f g f' g' h f'' h'
    (@ModulePullbackCompIsoAssoc.hom_app B S hS (modulePullbackCompIsoAssoc B S hS))
    (@moduleBaseChangeMap_adjoint_split' B S hS) comm₁ comm₂ w K

end Paste

section Comp

variable {X X' Y Y' Z Z' : AlgebraicSpaces B S hS} (f₁ : X ⟶ Y) (g : Y' ⟶ Y) (f₁' : X' ⟶ Y')
    (g' : X' ⟶ X) (f₂ : Y ⟶ Z) (k : Z' ⟶ Z) (f₂' : Y' ⟶ Z')

/-- **The pasting law for the degree-zero base change maps of two squares stacked along a
horizontal edge.**  For commutative squares `(f₁, g, f₁', g')` and `(f₂, k, f₂', g)` sharing the
horizontal edge `g`, the base change map `k^*(f₁ ≫ f₂)_* ⟶ (f₁' ≫ f₂')_*(g')^*` of the outer
rectangle is

`k^*(f₁ ≫ f₂)_* ≅ k^*f₂_*f₁_* ⟶ f₂'_*g^*f₁_* ⟶ f₂'_*f₁'_*(g')^* ≅ (f₁' ≫ f₂')_*(g')^*`,

the composite of the base change maps of the two squares read through the comparisons of
Stacks 03LU for the direct images along the two composite vertical legs.  This is the
degree-zero shape of Stacks 0E46. -/
theorem moduleBaseChangeMap_comp (comm₁ : g' ≫ f₁ = f₁' ≫ g) (comm₂ : g ≫ f₂ = f₂' ≫ k)
    (w : g' ≫ (f₁ ≫ f₂) = (f₁' ≫ f₂') ≫ k) (K : Modules.{u, u} B S hS X.1 X.2) :
    (moduleBaseChangeMap (f₁ ≫ f₂) k (f₁' ≫ f₂') g' w).app K =
      (modulePullback B S hS k).map ((modulePushforwardCompIso B S hS f₁ f₂).inv.app K) ≫
        (moduleBaseChangeMap f₂ k f₂' g comm₂).app ((modulePushforward B S hS f₁).obj K) ≫
        (modulePushforward B S hS f₂').map ((moduleBaseChangeMap f₁ g f₁' g' comm₁).app K) ≫
        (modulePushforwardCompIso B S hS f₁' f₂').hom.app ((modulePullback B S hS g').obj K) :=
  abstractBaseChange_comp (@modulePullback B S hS) (@modulePushforward B S hS)
    (@modulePullbackAdjunction B S hS) (@modulePullbackCompIso B S hS)
    (@moduleBaseChangeMap B S hS) f₁ g f₁' g' f₂ k f₂' (@modulePushforwardCompIso B S hS)
    (@ModulePullbackCompIsoAssoc.hom_app B S hS (modulePullbackCompIsoAssoc B S hS))
    (fun _ _ _ _ f g f' g' comm => by
      rw [moduleBaseChangeMap_eq_mateEquiv, modulePullbackSquareComparison_inv_eq])
    (@conjugateEquiv_modulePullbackCompIso_hom B S hS)
    (@conjugateEquiv_modulePullbackCompIso_inv B S hS) comm₁ comm₂ w K

end Comp

section Transport

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')

/-- **The base change map is compatible with an equality of the two horizontal morphisms.**  For
`g₁ = g₂ : Y' ⟶ Y` and `g₁' = g₂' : X' ⟶ X`, the base change maps of the two squares agree up
to the transports of the inverse images along the two equalities. -/
theorem moduleBaseChangeMap_congr {g₁ g₂ : Y' ⟶ Y} {g₁' g₂' : X' ⟶ X} (p : g₁ = g₂)
    (p' : g₁' = g₂') (w₁ : g₁' ≫ f = f' ≫ g₁) (w₂ : g₂' ≫ f = f' ≫ g₂)
    (K : Modules.{u, u} B S hS X.1 X.2) :
    (eqToIso (congrArg (fun k : Y' ⟶ Y =>
          (modulePullback B S hS k).obj ((modulePushforward B S hS f).obj K)) p)).hom ≫
        (moduleBaseChangeMap f g₂ f' g₂' w₂).app K =
      (moduleBaseChangeMap f g₁ f' g₁' w₁).app K ≫
        (modulePushforward B S hS f').map
          (eqToIso (congrArg (fun k : X' ⟶ X => (modulePullback B S hS k).obj K) p')).hom :=
  abstractBaseChange_congr (@modulePullback B S hS) (@modulePushforward B S hS)
    (@moduleBaseChangeMap B S hS) f f' p p' w₁ w₂ K


end Transport

end AlgebraicGeometry.Space

end
