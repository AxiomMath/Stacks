module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSiteInverseImageAssoc
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.BaseChangeMateHorizontalPasting

/-!
# The degree-zero base change map of a square of algebraic spaces, and its two squares

The base change map of **Stacks 0736** for a square of algebraic spaces,
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeMap`, is built from the direct and inverse
images of `𝒪`-modules in the shapes `AlgebraicGeometry.Space.ringedDirectImage` and
`AlgebraicGeometry.Space.siteInverseImage`.  This file assembles, for an arbitrary commutative
square of algebraic spaces

```
  X' ——g'——→ X
   | f'       | f
   v          v
  Y' ——g———→ Y
```

the two comparisons that map is made of — of the two composite direct images and of the two
composite inverse images — proves that each is the mate of the other, which is **Stacks 03D8**
read at a square, and writes the degree-zero base change map down.

## Main definitions

* `AlgebraicGeometry.Space.SiteModules`: the category of `𝒪`-modules in the spelling the base
  change map consumes.
* `AlgebraicGeometry.Space.ringedDirectImageSquareIso`: the comparison
  `g'_* ⋙ f_* ≅ f'_* ⋙ g_*` of the two composite direct images around the square.
* `AlgebraicGeometry.Space.siteInverseImageSquareComparison`: the comparison
  `g^* ⋙ f'^* ⟶ f^* ⋙ g'^*` of the two composite inverse images around the square.
* `AlgebraicGeometry.Space.siteBaseChangeMap`: the degree-zero base change map
  `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` of the square — the mate, across the two adjunctions of
  **Stacks 03D7** for the horizontal morphisms, of the direct-image comparison.

## Main results

* `AlgebraicGeometry.Space.siteInverseImageComp_congr_left` and
  `AlgebraicGeometry.Space.siteInverseImageComp_congr_right`: compatibility of the
  inverse-image comparison of **Stacks 03LU** with an equality of either of its two morphisms.
* `AlgebraicGeometry.Space.conjugateEquiv_siteInverseImageComp_inv` and
  `AlgebraicGeometry.Space.conjugateEquiv_transportNatTrans_siteInverseImage`: the mates of the
  two remaining factors of a square comparison.
* `AlgebraicGeometry.Space.conjugateEquiv_siteInverseImageSquareComparison`: **the mate of the
  inverse-image square comparison is the direct-image square comparison.**  This is
  **Stacks 03D8** read at a square.
* `AlgebraicGeometry.Space.comp_rectangle`: two commutative squares sharing a vertical edge
  paste to a commutative rectangle.

## Implementation notes

Everything is stated at `AlgebraicGeometry.Space.SiteModules`, the spelling of the category of
`𝒪`-modules that `ringedDirectImage` and `siteInverseImage` are functors between on the nose,
rather than at `AlgebraicGeometry.Space.Modules` over the small étale ringed site.  The two are
definitionally equal, and stating a componentwise identity at the second spelling makes the
kernel decide that defeq inside the identity, which it does not finish.

## References

* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.Cohomology.DerivedBaseChangePasting (transportNatTrans)

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The category of `𝒪`-modules on an algebraic space, in the spelling the base change map of
**Stacks 0736** consumes:  sheaves of modules over the structure ring sheaf of the small étale
ringed topos.  It is definitionally `AlgebraicGeometry.Space.Modules` over the small étale
ringed site, and it is the spelling `AlgebraicGeometry.Space.ringedDirectImage` and
`AlgebraicGeometry.Space.siteInverseImage` are functors between on the nose. -/
abbrev SiteModules (Z : AlgebraicSpaces B S hS) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS Z).O)

variable {B S hS}

/-! ### Compatibility of the inverse-image comparison with an equality of morphisms -/

section Congr

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **Compatibility of the inverse-image comparison of Stacks 03LU with an equality of the
inner morphism.** -/
theorem siteInverseImageComp_congr_left {f f' : X ⟶ Y} (e : f = f') (g : Y ⟶ Z)
    (M : SiteModules B S hS Z) :
    (transportNatTrans (congrArg (fun k : X ⟶ Y => siteInverseImage k) e)).app
          ((siteInverseImage g).obj M) ≫ (siteInverseImageComp f' g).inv.app M =
      (siteInverseImageComp f g).inv.app M ≫
        (transportNatTrans
          (congrArg (fun k : X ⟶ Y => siteInverseImage (k ≫ g)) e)).app M := by
  subst e
  simp [transportNatTrans]

/-- **Compatibility of the inverse-image comparison of Stacks 03LU with an equality of the
outer morphism.** -/
theorem siteInverseImageComp_congr_right (f : X ⟶ Y) {g g' : Y ⟶ Z} (e : g = g')
    (M : SiteModules B S hS Z) :
    (siteInverseImage f).map
          ((transportNatTrans (congrArg (fun k : Y ⟶ Z => siteInverseImage k) e)).app M) ≫
        (siteInverseImageComp f g').inv.app M =
      (siteInverseImageComp f g).inv.app M ≫
        (transportNatTrans
          (congrArg (fun k : Y ⟶ Z => siteInverseImage (f ≫ k)) e)).app M := by
  subst e
  simp [transportNatTrans]

end Congr

/-! ### The two square comparisons and the base change map -/

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- The comparison `g'_* ⋙ f_* ≅ f'_* ⋙ g_*` of the two composite direct images around a
commutative square of algebraic spaces.  Both composites are compared with the direct image along
the common composite by `AlgebraicGeometry.Space.ringedDirectImageComp`. -/
def ringedDirectImageSquareIso (comm : g' ≫ f = f' ≫ g) :
    ringedDirectImage g' ⋙ ringedDirectImage f ≅ ringedDirectImage f' ⋙ ringedDirectImage g :=
  ringedDirectImageComp g' f ≪≫
    eqToIso (congrArg (fun k : X' ⟶ Y => ringedDirectImage k) comm) ≪≫
    (ringedDirectImageComp f' g).symm

/-- The comparison `g^* ⋙ f'^* ⟶ f^* ⋙ g'^*` of the two composite inverse images around a
commutative square of algebraic spaces.  Both composites are compared with the inverse image
along the common composite by `AlgebraicGeometry.Space.siteInverseImageComp`. -/
def siteInverseImageSquareComparison (comm : g' ≫ f = f' ≫ g) :
    siteInverseImage g ⋙ siteInverseImage f' ⟶ siteInverseImage f ⋙ siteInverseImage g' :=
  (siteInverseImageComp f' g).inv ≫
    transportNatTrans (congrArg (fun k : X' ⟶ Y => siteInverseImage k) comm.symm) ≫
    (siteInverseImageComp g' f).hom

/-- **The degree-zero base change map `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*`** of a commutative square of
algebraic spaces:  the mate, across the two adjunctions of **Stacks 03D7** for the two horizontal
morphisms, of the comparison of the two composite direct images. -/
def siteBaseChangeMap (comm : g' ≫ f = f' ≫ g) :
    ringedDirectImage f ⋙ siteInverseImage g ⟶ siteInverseImage g' ⋙ ringedDirectImage f' :=
  Stacks.Cohomology.BaseChange.mate (ringedAdjunction g) (ringedAdjunction g') (ringedDirectImage f)
    (ringedDirectImage f') (ringedDirectImageSquareIso f g f' g' comm)

/-- The mate of the backward direction of the inverse-image comparison of **Stacks 03LU** is
the backward direction of the direct-image comparison. -/
theorem conjugateEquiv_siteInverseImageComp_inv {V W Z : AlgebraicSpaces B S hS} (a : V ⟶ W)
    (b : W ⟶ Z) :
    conjugateEquiv (ringedAdjunction (a ≫ b)) ((ringedAdjunction b).comp (ringedAdjunction a))
        (siteInverseImageComp a b).inv =
      (ringedDirectImageComp a b).inv := by
  have h := congrArg Iso.inv (conjugateIsoEquiv_siteInverseImageComp a b)
  simp only [Iso.symm_inv, conjugateIsoEquiv_apply_hom, Iso.symm_hom] at h
  exact h

/-- The mate of the transport of the inverse image along an equality of morphisms is the
transport of the direct image along it. -/
theorem conjugateEquiv_transportNatTrans_siteInverseImage {V W : AlgebraicSpaces B S hS}
    {p q : V ⟶ W} (h : p = q) :
    conjugateEquiv (ringedAdjunction q) (ringedAdjunction p)
        (transportNatTrans (congrArg (fun k : V ⟶ W => siteInverseImage k) h)) =
      transportNatTrans (congrArg (fun k : V ⟶ W => ringedDirectImage k) h.symm) := by
  subst h
  rw [← eqToHom_eq_transportNatTrans, ← eqToHom_eq_transportNatTrans]
  simp only [eqToHom_refl]
  exact conjugateEquiv_id _

/-- **The mate of the inverse-image square comparison is the direct-image square
comparison.**  This is **Stacks 03D8** read at a commutative square:  both comparisons are
built from the comparisons of **Stacks 03LU** for the two composite legs, and those are mates
of one another by `AlgebraicGeometry.Space.conjugateEquiv_siteInverseImageComp_hom`. -/
theorem conjugateEquiv_siteInverseImageSquareComparison (comm : g' ≫ f = f' ≫ g) :
    conjugateEquiv ((ringedAdjunction f).comp (ringedAdjunction g'))
        ((ringedAdjunction g).comp (ringedAdjunction f'))
        (siteInverseImageSquareComparison f g f' g' comm) =
      (ringedDirectImageSquareIso f g f' g' comm).hom := by
  rw [siteInverseImageSquareComparison, ringedDirectImageSquareIso,
    ← conjugateEquiv_comp _ (ringedAdjunction (f' ≫ g)) _,
    ← conjugateEquiv_comp _ (ringedAdjunction (g' ≫ f)) _,
    conjugateEquiv_siteInverseImageComp_hom g' f,
    conjugateEquiv_transportNatTrans_siteInverseImage comm.symm,
    conjugateEquiv_siteInverseImageComp_inv f' g]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
  rw [eqToHom_eq_transportNatTrans]

end Square

/-! ### The commutativity of a pasted rectangle -/

section Horizontal

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (f'' : X'' ⟶ Y'') (g : Y' ⟶ Y) (g' : X' ⟶ X) (h : Y'' ⟶ Y') (g'' : X'' ⟶ X')

/-- **The outer rectangle of two horizontally composable commutative squares commutes.** -/
theorem comp_rectangle (comm : g' ≫ f = f' ≫ g) (comm' : g'' ≫ f' = f'' ≫ h) :
    (g'' ≫ g') ≫ f = f'' ≫ h ≫ g := by
  rw [Category.assoc, comm, ← Category.assoc, comm', Category.assoc]

end Horizontal

end AlgebraicGeometry.Space

end

