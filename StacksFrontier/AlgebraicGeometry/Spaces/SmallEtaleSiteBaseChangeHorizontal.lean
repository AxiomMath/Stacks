module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSiteInverseImageNamedCongr

/-!
# Horizontal pasting of the degree-zero base change map of algebraic spaces

Two commutative squares of algebraic spaces sharing a vertical edge paste to a commutative
rectangle:

```
        g''        g'
  X'' ———→ X' ———→ X
   | f''     | f'    | f
   v         v       v
  Y'' ———→ Y' ———→ Y
         h         g
```

The degree-zero base change map `AlgebraicGeometry.Space.siteBaseChangeMap` of the rectangle is
the composite of the two base change maps of the squares, read through the comparisons of
Stacks 03LU for the two composite horizontal inverse images.  This is Stacks 0E47 in degree zero
on the small étale site.

## Main results

* `AlgebraicGeometry.Space.siteInverseImageSquareComparison_horizontal`: the comparison of the
  two composite inverse images around the rectangle is the horizontal pasting of the
  comparisons of its two squares.
* `AlgebraicGeometry.Space.siteBaseChangeMap_horizontal`: Stacks 0E47 in degree zero.
* `Stacks.CategoryTheory.squareComparison_app_of_eq`: the abstract pasting law of
  `Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal`, restated so that
  the three square comparisons enter as transformations identified with their three factors by
  an equation of natural transformations.

The five lemmas named `sitePasting_*` are the hypotheses of `squareComparison_horizontal`.

## Implementation notes

The base change map is the mate, across the two vertical adjunctions, of the comparison of the
two composite inverse images
(`AlgebraicGeometry.Space.conjugateEquiv_siteInverseImageSquareComparison`, Stacks 03D8 at a
square), so the pasting law reduces to that for the comparisons, and that in turn to the
associativity pentagon of Stacks 03LU used three times and the compatibility of the comparison
with an equality of either of its morphisms.  Both reductions are
`Stacks.Cohomology.BaseChange.mate_horizontal` and `squareComparison_horizontal`, stated with
every functor a variable.

At these functors the kernel does not decide
`(x ≫ y ≫ z).app M ≡ x.app M ≫ y.app M ≫ z.app M`, while the same identification between natural
transformations is one delta step; hence `Stacks.CategoryTheory.squareComparison_app_of_eq`, and
the five hypotheses are stated in the idiom of `squareComparison_horizontal`, each in its own
declaration.  The three comparisons whose source is a threefold composite are taken at
`AlgebraicGeometry.Space.siteInverseImageComp'`, which carries the bracketing as a propositional
equality of morphisms.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.Cohomology.DerivedBaseChangePasting (transportNatTrans
  squareComparison_horizontal)

namespace Stacks.CategoryTheory

/-- The horizontal pasting of three square comparisons, with each square comparison an opaque
transformation `α`, `α₂`, `α₀` identified with its three factors by an equation of natural
transformations: `Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal`
read at an object. -/
theorem squareComparison_app_of_eq
    {X X' X'' Y Y' Y'' : Type*} [Category* X] [Category* X'] [Category* X'']
    [Category* Y] [Category* Y'] [Category* Y'']
    {H : X ⥤ X'} {H' : X' ⥤ X''} {Hc : X ⥤ X''}
    {F : X ⥤ Y} {F' : X' ⥤ Y'} {F'' : X'' ⥤ Y''}
    {G : Y ⥤ Y'} {G' : Y' ⥤ Y''} {Gc : Y ⥤ Y''}
    {P P₂ : X ⥤ Y'} {Q Q₂ : X' ⥤ Y''} {R R₂ : X ⥤ Y''}
    (nH : H ⋙ H' ≅ Hc) (nG : G ⋙ G' ≅ Gc)
    (a : H ⋙ F' ≅ P) (b : F ⋙ G ≅ P₂)
    (a' : H' ⋙ F'' ≅ Q) (b' : F' ⋙ G' ≅ Q₂)
    (a₀ : Hc ⋙ F'' ≅ R) (b₀ : F ⋙ Gc ≅ R₂)
    (esq : P = P₂) (esq' : Q = Q₂) (eouter : R = R₂)
    (α : H ⋙ F' ⟶ F ⋙ G) (α₂ : H' ⋙ F'' ⟶ F' ⋙ G') (α₀ : Hc ⋙ F'' ⟶ F ⋙ Gc)
    (hα : α = a.hom ≫ transportNatTrans esq ≫ b.inv)
    (hα₂ : α₂ = a'.hom ≫ transportNatTrans esq' ≫ b'.inv)
    (hα₀ : α₀ = a₀.hom ≫ transportNatTrans eouter ≫ b₀.inv)
    (M : X)
    (hsplit : F''.map (nH.inv.app M) ≫
        (a'.hom.app (H.obj M) ≫ (transportNatTrans esq').app (H.obj M) ≫
          b'.inv.app (H.obj M)) ≫
        G'.map (a.hom.app M ≫ (transportNatTrans esq).app M ≫ b.inv.app M) ≫
        nG.hom.app (F.obj M) =
      a₀.hom.app M ≫ (transportNatTrans eouter).app M ≫ b₀.inv.app M) :
    F''.map (nH.inv.app M) ≫ α₂.app (H.obj M) ≫ G'.map (α.app M) ≫
        nG.hom.app (F.obj M) =
      α₀.app M := by
  subst hα
  subst hα₂
  subst hα₀
  simpa only [NatTrans.comp_app] using hsplit

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- `AlgebraicGeometry.Space.siteInverseImageSquareComparison` is its own definition, as an
equation of natural transformations, with its two outer factors written as the `Iso.symm` of
the comparisons of Stacks 03LU. -/
theorem siteInverseImageSquareComparison_def (comm : g' ≫ f = f' ≫ g) :
    siteInverseImageSquareComparison f g f' g' comm =
      (siteInverseImageComp f' g).symm.hom ≫
        transportNatTrans (congrArg (fun k : X' ⟶ Y => siteInverseImage k) comm.symm) ≫
        (siteInverseImageComp g' f).symm.inv := rfl

/-- `AlgebraicGeometry.Space.siteBaseChangeMap` is its own definition, as an equation of
natural transformations. -/
theorem siteBaseChangeMap_def (comm : g' ≫ f = f' ≫ g) :
    siteBaseChangeMap f g f' g' comm =
      Stacks.Cohomology.BaseChange.mate (ringedAdjunction g) (ringedAdjunction g')
        (ringedDirectImage f) (ringedDirectImage f')
        (ringedDirectImageSquareIso f g f' g' comm) := rfl

end Square

section Horizontal

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (f'' : X'' ⟶ Y'') (g : Y' ⟶ Y) (g' : X' ⟶ X) (h : Y'' ⟶ Y') (g'' : X'' ⟶ X')

/-! ### The five hypotheses of the abstract pasting law, in its own idiom -/

/-- The pentagon of Stacks 03LU for the composite `f'' ≫ h ≫ g` along the bottom of the
rectangle. -/
theorem sitePasting_pentagon_bottom (M : SiteModules B S hS Y) :
    (siteInverseImageComp f'' h).symm.hom.app ((siteInverseImage g).obj M) ≫
        (siteInverseImageComp' (f'' ≫ h) g (f'' ≫ h ≫ g)
          (Category.assoc f'' h g).symm).symm.hom.app M =
      (siteInverseImage f'').map ((siteInverseImageComp h g).symm.hom.app M) ≫
        (siteInverseImageComp f'' (h ≫ g)).symm.hom.app M :=
  siteInverseImageComp_assoc_right_app f'' h g M

/-- The pentagon of Stacks 03LU for the composite `(g'' ≫ g') ≫ f` along the top of the
rectangle. -/
theorem sitePasting_pentagon_top (M : SiteModules B S hS Y) :
    (siteInverseImageComp g'' g').symm.hom.app ((siteInverseImage f).obj M) ≫
        (siteInverseImageComp (g'' ≫ g') f).symm.hom.app M =
      (siteInverseImage g'').map ((siteInverseImageComp g' f).symm.hom.app M) ≫
        (siteInverseImageComp' g'' (g' ≫ f) ((g'' ≫ g') ≫ f)
          (Category.assoc g'' g' f)).symm.hom.app M :=
  siteInverseImageComp_assoc_left_app g'' g' f M

/-- The pentagon of Stacks 03LU for the diagonal composite `g'' ≫ f' ≫ g` of the rectangle. -/
theorem sitePasting_pentagon_middle (M : SiteModules B S hS Y) :
    (siteInverseImageComp g'' f').symm.hom.app ((siteInverseImage g).obj M) ≫
        (siteInverseImageComp' (g'' ≫ f') g (g'' ≫ f' ≫ g)
          (Category.assoc g'' f' g).symm).symm.hom.app M =
      (siteInverseImage g'').map ((siteInverseImageComp f' g).symm.hom.app M) ≫
        (siteInverseImageComp' g'' (f' ≫ g) (g'' ≫ f' ≫ g) rfl).symm.hom.app M :=
  siteInverseImageComp_assoc_named_app g'' f' g (g'' ≫ f' ≫ g)
    (Category.assoc g'' f' g).symm rfl M

/-- The compatibility of the inverse-image comparison with the commutativity of the right-hand
square. -/
theorem sitePasting_congr_rightSquare (comm : g' ≫ f = f' ≫ g)
    (hW : g'' ≫ f' ≫ g = (g'' ≫ g') ≫ f) (M : SiteModules B S hS Y) :
    (siteInverseImage g'').map
          ((transportNatTrans
            (congrArg (fun k : X' ⟶ Y => siteInverseImage k) comm.symm)).app M) ≫
        (siteInverseImageComp' g'' (g' ≫ f) ((g'' ≫ g') ≫ f)
          (Category.assoc g'' g' f)).symm.hom.app M =
      (siteInverseImageComp' g'' (f' ≫ g) (g'' ≫ f' ≫ g) rfl).symm.hom.app M ≫
        (transportNatTrans
          (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) hW)).app M :=
  siteInverseImageComp'_congr_right g'' comm.symm (g'' ≫ f' ≫ g) rfl
    ((g'' ≫ g') ≫ f) (Category.assoc g'' g' f) hW M

/-- The compatibility of the inverse-image comparison with the commutativity of the left-hand
square. -/
theorem sitePasting_congr_leftSquare (comm' : g'' ≫ f' = f'' ≫ h)
    (hR : f'' ≫ h ≫ g = g'' ≫ f' ≫ g) (M : SiteModules B S hS Y) :
    (transportNatTrans
            (congrArg (fun k : X'' ⟶ Y' => siteInverseImage k) comm'.symm)).app
          ((siteInverseImage g).obj M) ≫
        (siteInverseImageComp' (g'' ≫ f') g (g'' ≫ f' ≫ g)
          (Category.assoc g'' f' g).symm).symm.hom.app M =
      (siteInverseImageComp' (f'' ≫ h) g (f'' ≫ h ≫ g)
          (Category.assoc f'' h g).symm).symm.hom.app M ≫
        (transportNatTrans
          (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) hR)).app M :=
  siteInverseImageComp'_congr_left comm'.symm g (f'' ≫ h ≫ g)
    (Category.assoc f'' h g).symm (g'' ≫ f' ≫ g) (Category.assoc g'' f' g).symm hR M

/-! ### The pasting -/

/-- The horizontal pasting of the three square comparisons of a rectangle, with every
comparison written out as its three factors. -/
theorem sitePasting_factors (comm : g' ≫ f = f' ≫ g) (comm' : g'' ≫ f' = f'' ≫ h)
    (hW : g'' ≫ f' ≫ g = (g'' ≫ g') ≫ f) (hR : f'' ≫ h ≫ g = g'' ≫ f' ≫ g)
    (M : SiteModules B S hS Y) :
    (siteInverseImage f'').map ((siteInverseImageComp h g).symm.inv.app M) ≫
        ((siteInverseImageComp f'' h).symm.hom.app ((siteInverseImage g).obj M) ≫
          (transportNatTrans
              (congrArg (fun k : X'' ⟶ Y' => siteInverseImage k) comm'.symm)).app
            ((siteInverseImage g).obj M) ≫
          (siteInverseImageComp g'' f').symm.inv.app ((siteInverseImage g).obj M)) ≫
        (siteInverseImage g'').map
          ((siteInverseImageComp f' g).symm.hom.app M ≫
            (transportNatTrans
              (congrArg (fun k : X' ⟶ Y => siteInverseImage k) comm.symm)).app M ≫
            (siteInverseImageComp g' f).symm.inv.app M) ≫
        (siteInverseImageComp g'' g').symm.hom.app ((siteInverseImage f).obj M) =
      (siteInverseImageComp f'' (h ≫ g)).symm.hom.app M ≫
        (transportNatTrans (congrArg (fun k : X'' ⟶ Y => siteInverseImage k)
          (comp_rectangle f f' f'' g g' h g'' comm comm').symm)).app M ≫
        (siteInverseImageComp (g'' ≫ g') f).symm.inv.app M :=
  squareComparison_horizontal
    (siteInverseImageComp h g).symm (siteInverseImageComp g'' g').symm
    (siteInverseImageComp f' g).symm (siteInverseImageComp g' f).symm
    (siteInverseImageComp f'' h).symm (siteInverseImageComp g'' f').symm
    (siteInverseImageComp f'' (h ≫ g)).symm (siteInverseImageComp (g'' ≫ g') f).symm
    (siteInverseImageComp' (f'' ≫ h) g (f'' ≫ h ≫ g) (Category.assoc f'' h g).symm).symm
    (siteInverseImageComp' g'' (g' ≫ f) ((g'' ≫ g') ≫ f) (Category.assoc g'' g' f)).symm
    (siteInverseImageComp' g'' (f' ≫ g) (g'' ≫ f' ≫ g) rfl).symm
    (siteInverseImageComp' (g'' ≫ f') g (g'' ≫ f' ≫ g) (Category.assoc g'' f' g).symm).symm
    (congrArg (fun k : X' ⟶ Y => siteInverseImage k) comm.symm)
    (congrArg (fun k : X'' ⟶ Y' => siteInverseImage k) comm'.symm)
    (congrArg (fun k : X'' ⟶ Y => siteInverseImage k)
      (comp_rectangle f f' f'' g g' h g'' comm comm').symm)
    (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) hW)
    (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) hR)
    (sitePasting_pentagon_bottom f'' g h) (sitePasting_pentagon_top f g' g'')
    (sitePasting_pentagon_middle f' g g'')
    (sitePasting_congr_rightSquare f f' g g' g'' comm hW)
    (sitePasting_congr_leftSquare f' f'' g h g'' comm' hR) M

/-- The comparison of the two composite inverse images around a rectangle is the horizontal
pasting of the comparisons of its two squares, read through the comparisons of Stacks 03LU. -/
theorem siteInverseImageSquareComparison_horizontal (comm : g' ≫ f = f' ≫ g)
    (comm' : g'' ≫ f' = f'' ≫ h) (M : SiteModules B S hS Y) :
    (siteInverseImage f'').map ((siteInverseImageComp h g).symm.inv.app M) ≫
        (siteInverseImageSquareComparison f' h f'' g'' comm').app
          ((siteInverseImage g).obj M) ≫
        (siteInverseImage g'').map
          ((siteInverseImageSquareComparison f g f' g' comm).app M) ≫
        (siteInverseImageComp g'' g').symm.hom.app ((siteInverseImage f).obj M) =
      (siteInverseImageSquareComparison f (h ≫ g) f'' (g'' ≫ g')
        (comp_rectangle f f' f'' g g' h g'' comm comm')).app M :=
  Stacks.CategoryTheory.squareComparison_app_of_eq
    (siteInverseImageComp h g).symm (siteInverseImageComp g'' g').symm
    (siteInverseImageComp f' g).symm (siteInverseImageComp g' f).symm
    (siteInverseImageComp f'' h).symm (siteInverseImageComp g'' f').symm
    (siteInverseImageComp f'' (h ≫ g)).symm (siteInverseImageComp (g'' ≫ g') f).symm
    (congrArg (fun k : X' ⟶ Y => siteInverseImage k) comm.symm)
    (congrArg (fun k : X'' ⟶ Y' => siteInverseImage k) comm'.symm)
    (congrArg (fun k : X'' ⟶ Y => siteInverseImage k)
      (comp_rectangle f f' f'' g g' h g'' comm comm').symm)
    _ _ _
    (siteInverseImageSquareComparison_def f g f' g' comm)
    (siteInverseImageSquareComparison_def f' h f'' g'' comm')
    (siteInverseImageSquareComparison_def f (h ≫ g) f'' (g'' ≫ g')
      (comp_rectangle f f' f'' g g' h g'' comm comm'))
    M
    (sitePasting_factors f f' f'' g g' h g'' comm comm'
      (by rw [Category.assoc, comm]) (by rw [← Category.assoc, ← comm', Category.assoc]) M)

/-! ### Stacks 0E47 in degree zero -/

/-- Stacks 0E47 in degree zero: for two commutative squares of algebraic spaces sharing a
vertical edge, the degree-zero base change map of the pasted rectangle is the composite of the
base change maps of the two squares, read through the comparisons of Stacks 03LU. -/
theorem siteBaseChangeMap_horizontal (comm : g' ≫ f = f' ≫ g) (comm' : g'' ≫ f' = f'' ≫ h)
    (K : SiteModules B S hS X) :
    (siteInverseImageComp h g).symm.inv.app ((ringedDirectImage f).obj K) ≫
        (siteInverseImage h).map ((siteBaseChangeMap f g f' g' comm).app K) ≫
        (siteBaseChangeMap f' h f'' g'' comm').app ((siteInverseImage g').obj K) ≫
        (ringedDirectImage f'').map ((siteInverseImageComp g'' g').symm.hom.app K) =
      (siteBaseChangeMap f (h ≫ g) f'' (g'' ≫ g')
        (comp_rectangle f f' f'' g g' h g'' comm comm')).app K := by
  rw [siteBaseChangeMap_def f g f' g' comm, siteBaseChangeMap_def f' h f'' g'' comm',
    siteBaseChangeMap_def f (h ≫ g) f'' (g'' ≫ g')
      (comp_rectangle f f' f'' g g' h g'' comm comm')]
  exact Stacks.Cohomology.BaseChange.mate_horizontal (ringedAdjunction f) (ringedAdjunction f')
    (ringedAdjunction f'') (ringedAdjunction g) (ringedAdjunction g') (ringedAdjunction h)
    (ringedAdjunction g'') (ringedAdjunction (h ≫ g)) (ringedAdjunction (g'' ≫ g'))
    _ _ _
    (siteInverseImageComp h g).symm (siteInverseImageComp g'' g').symm _ _ _
    (conjugateEquiv_siteInverseImageSquareComparison f g f' g' comm)
    (conjugateEquiv_siteInverseImageSquareComparison f' h f'' g'' comm')
    (conjugateEquiv_siteInverseImageSquareComparison f (h ≫ g) f'' (g'' ≫ g')
      (comp_rectangle f f' f'' g g' h g'' comm comm'))
    (siteInverseImageSquareComparison_horizontal f f' f'' g g' h g'' comm comm') K

end Horizontal

end AlgebraicGeometry.Space

end
