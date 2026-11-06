module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSiteInverseImageComp
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateTransportCocycle

/-!
# The associativity pentagon for the images that the base change map consumes

`AlgebraicGeometry.Space.ringedDirectImageComp` and
`AlgebraicGeometry.Space.siteInverseImageComp` are the comparisons `f_* ⋙ g_* ≅ (f ≫ g)_*` and
`(f ≫ g)^* ≅ g^* ⋙ f^*` of **Stacks 03LU** for the direct and inverse images of `𝒪`-modules in
the shape the base change map of **Stacks 0736** consumes.  This file proves their associativity
pentagons as equalities of *isomorphisms of functors*, which is the ingredient the horizontal
pasting law of **Stacks 0E47** asks of them.

## Main results

* `AlgebraicGeometry.Space.ringedDirectImageComp_assoc_iso`: the direct-image pentagon, as an
  equality of isomorphisms.
* `AlgebraicGeometry.Space.conjugateIsoEquiv_siteInverseImageComp`: the mate of the
  inverse-image comparison, read as an isomorphism, is the direct-image comparison.  This is
  `AlgebraicGeometry.Space.conjugateEquiv_siteInverseImageComp_hom` — **Stacks 03D8** in this
  vocabulary — with both directions assembled.
* `AlgebraicGeometry.Space.siteInverseImageComp_assoc`: **the inverse-image pentagon.**
* `AlgebraicGeometry.Space.siteInverseImageComp'_assoc`: the same pentagon for the
  named-composite comparison `AlgebraicGeometry.Space.siteInverseImageComp'`, which is the form
  the horizontal pasting law of **Stacks 0E47** needs.

## Implementation notes

*Why the direct-image pentagon is proved again here.*
`AlgebraicGeometry.Space.ringedDirectImageComp_assoc_app` is the same statement at a component.
Assembling it over all objects *at these functors* asks the kernel to decide the defeq between
the two spellings of the category of `𝒪`-modules — `AlgebraicGeometry.Space.Modules` over the
small étale ringed site, and sheaves of modules over the structure ring sheaf of the small
étale ringed topos — under the binder of `CategoryTheory.NatTrans.ext`, which times out.  So the
assembling is done where the functors are variables, in
`CategoryTheory.Functor.compConj_cocycle'`, and instantiated here in one application.

*Why the inverse-image pentagon is not proved directly.*  A comparison of left adjoints is
determined by its mate, and the mate of each of the four inverse-image comparisons is the
corresponding direct-image comparison by
`AlgebraicGeometry.Space.conjugateIsoEquiv_siteInverseImageComp`;  so the pentagon for the
inverse images is the pentagon for the direct images read through conjugation, which is
`Stacks.Mates.trans_assoc_of_conjugate`.  Nothing has to be recomputed with
`AlgebraicGeometry.Space.pushforwardModulesCompAt`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {T X Y Z : AlgebraicSpaces B S hS}

/-- **The associativity pentagon for the direct-image comparison of Stacks 03LU**, as an
equality of isomorphisms of functors.  It is
`AlgebraicGeometry.Space.ringedDirectImageComp_assoc_app` assembled over all objects, obtained
the same way that statement is:  by instantiating the conjugated cocycle law
`CategoryTheory.Functor.compConj_cocycle'` at
`AlgebraicGeometry.Space.pushforwardModulesCompAt` and its pentagon. -/
theorem ringedDirectImageComp_assoc_iso (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    isoWhiskerLeft (ringedDirectImage f) (ringedDirectImageComp g h) ≪≫
        ringedDirectImageComp f (g ≫ h) =
      (associator (ringedDirectImage f) (ringedDirectImage g) (ringedDirectImage h)).symm ≪≫
        isoWhiskerRight (ringedDirectImageComp f g) (ringedDirectImage h) ≪≫
        ringedDirectImageComp (f ≫ g) h := by
  rw [ringedDirectImageComp_def f g, ringedDirectImageComp_def (f ≫ g) h,
    ringedDirectImageComp_def g h, ringedDirectImageComp_def f (g ≫ h)]
  exact compConj_cocycle' (ringedDirectImageIso f) (ringedDirectImageIso g) (ringedDirectImageIso h)
    (ringedDirectImageIso (f ≫ g)) (ringedDirectImageIso (g ≫ h))
    (ringedDirectImageIso (f ≫ g ≫ h)) (pushforwardModulesCompAt B S hS f g)
    (pushforwardModulesCompAt B S hS g h) (pushforwardModulesCompAt B S hS (f ≫ g) h)
    (pushforwardModulesCompAt B S hS f (g ≫ h))
    (pushforwardModulesCompAt_assoc B S hS f g h)

/-- **Stacks 03D8 as an equality of isomorphisms.**  The mate of the inverse-image comparison
of **Stacks 03LU**, read through `CategoryTheory.conjugateIsoEquiv`, is the direct-image
comparison.  This is `AlgebraicGeometry.Space.conjugateEquiv_siteInverseImageComp_hom` with
both directions assembled. -/
theorem conjugateIsoEquiv_siteInverseImageComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (conjugateIsoEquiv (ringedAdjunction (f ≫ g)) ((ringedAdjunction g).comp (ringedAdjunction f))
        (siteInverseImageComp f g).symm).symm =
      ringedDirectImageComp f g :=
  Iso.ext (conjugateEquiv_siteInverseImageComp_hom f g)

/-- **The associativity pentagon for the inverse-image comparison of Stacks 03LU**, in the
vocabulary the base change map of **Stacks 0736** consumes.  For three composable morphisms of
algebraic spaces the two ways of comparing the threefold composite inverse image with the
inverse image along the threefold composite agree. -/
theorem siteInverseImageComp_assoc (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (isoWhiskerRight (siteInverseImageComp g h).symm (siteInverseImage f)).symm ≪≫
        associator (siteInverseImage h) (siteInverseImage g) (siteInverseImage f) ≪≫
        isoWhiskerLeft (siteInverseImage h) (siteInverseImageComp f g).symm ≪≫
        (siteInverseImageComp (f ≫ g) h).symm =
      (siteInverseImageComp f (g ≫ h)).symm := by
  refine Stacks.Mates.trans_assoc_of_conjugate (ringedAdjunction h) (ringedAdjunction g)
    (ringedAdjunction f) (ringedAdjunction (g ≫ h)) (ringedAdjunction (f ≫ g))
    (ringedAdjunction (f ≫ g ≫ h)) _ _ _ _ ?_
  rw [conjugateIsoEquiv_siteInverseImageComp g h, conjugateIsoEquiv_siteInverseImageComp f (g ≫ h),
    conjugateIsoEquiv_siteInverseImageComp f g,
    show (conjugateIsoEquiv (ringedAdjunction (f ≫ g ≫ h))
          ((ringedAdjunction h).comp (ringedAdjunction (f ≫ g)))
          (siteInverseImageComp (f ≫ g) h).symm).symm = ringedDirectImageComp (f ≫ g) h from
      conjugateIsoEquiv_siteInverseImageComp (f ≫ g) h]
  exact ringedDirectImageComp_assoc_iso f g h

/-- **The associativity pentagon for the named-composite inverse-image comparison.**  The same
pentagon as `AlgebraicGeometry.Space.siteInverseImageComp_assoc`, for
`AlgebraicGeometry.Space.siteInverseImageComp'`:  the three composites of the chain are carried
as named morphisms together with equations naming them, so that the two bracketings of the
threefold composite are one morphism `fgh` and no transport along
`CategoryTheory.Category.assoc` appears in the statement.

This is the form the horizontal pasting law of **Stacks 0E47** needs. -/
theorem siteInverseImageComp'_assoc (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (gh : X ⟶ Z) (hgh : gh = g ≫ h) (fg : T ⟶ Y) (hfg : fg = f ≫ g)
    (fgh : T ⟶ Z) (e₁ : fgh = fg ≫ h) (e₂ : fgh = f ≫ gh) :
    (isoWhiskerRight (siteInverseImageComp' g h gh hgh).symm (siteInverseImage f)).symm ≪≫
        associator (siteInverseImage h) (siteInverseImage g) (siteInverseImage f) ≪≫
        isoWhiskerLeft (siteInverseImage h) (siteInverseImageComp' f g fg hfg).symm ≪≫
        (siteInverseImageComp' fg h fgh e₁).symm =
      (siteInverseImageComp' f gh fgh e₂).symm := by
  subst hgh
  subst hfg
  subst e₁
  rw [siteInverseImageComp'_rfl, siteInverseImageComp'_rfl, siteInverseImageComp'_rfl,
    siteInverseImageComp'_def,
    show congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) e₂ = rfl from rfl]
  simp only [eqToIso_refl, Iso.refl_trans]
  exact siteInverseImageComp_assoc f g h

end AlgebraicGeometry.Space

end
