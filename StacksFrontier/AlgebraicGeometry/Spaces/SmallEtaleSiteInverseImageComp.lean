module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSiteDirectImageComp

/-!
# The composition comparison for the inverse image that the base change map consumes

The base change map of **Stacks 0736** for a square of algebraic spaces,
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeMap`, is the mate of the comparison of the
two composite direct images across the adjunctions of **Stacks 03D7** for the two horizontal
morphisms.  Reading that mate — which is what the pasting law for the map needs — asks for the
*inverse* image in the same vocabulary as the direct image
`AlgebraicGeometry.Space.ringedDirectImage`, namely
`Stacks.Sheaves.RingedToposModules.pullbackModules` of the morphism of small étale ringed topoi
of **Stacks 03G8**, together with its composition comparison.

This file supplies those.  The comparison is *defined* so as to be canonical in the sense of
**Stacks 03D8**: it is the uniqueness isomorphism of left adjoints between the inverse image
along the composite and the composite of the inverse images, the right adjoints being
identified by `AlgebraicGeometry.Space.ringedDirectImageComp`.  What pins it down is
`AlgebraicGeometry.Space.conjugateEquiv_siteInverseImageComp_hom`: its conjugate is the
comparison of direct images it was built from.

## Main definitions

* `AlgebraicGeometry.Space.siteInverseImage`: the inverse image of `𝒪`-modules in the shape the
  base change map consumes.
* `AlgebraicGeometry.Space.ringedAdjunction`: **Stacks 03D7** for it,
  `siteInverseImage f ⊣ ringedDirectImage f`.
* `AlgebraicGeometry.Space.siteInverseImageComp`: **Stacks 03LU for the inverse image**,
  `(f ≫ g)^* ≅ g^* ⋙ f^*`.
* `AlgebraicGeometry.Space.siteInverseImageComp'`: the same with the composite carried as a
  named morphism together with an equation naming it.

## Main results

* `AlgebraicGeometry.Space.conjugateEquiv_siteInverseImageComp_hom`: **Stacks 03D8 in this
  vocabulary** — the conjugate of the inverse-image comparison, across the two adjunctions, is
  the direct-image comparison `AlgebraicGeometry.Space.ringedDirectImageComp`.  This is what makes
  the inverse-image comparison the canonical one rather than some isomorphism with the right
  endpoints.
* `AlgebraicGeometry.Space.siteInverseImageComp_def` and
  `AlgebraicGeometry.Space.siteInverseImageComp'_def`: the two comparisons as rewrite rules, for
  the reason recorded in `SmallEtaleSiteDirectImageComp.lean` — a defeq between the two
  spellings of the category of `𝒪`-modules is not one the kernel finishes inside an equation
  between composites of morphisms, and rewriting with the definition first keeps it at the size
  of an isomorphism of functors.

## Implementation notes

*Why not `pullbackModulesCompIso`.*
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` is the same construction one level
down, for the inverse image `AlgebraicGeometry.RingedToposHom.pullbackModules` of a morphism of
ringed topoi and the comparison
`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso` of *its* direct images.  Neither
functor is the one the base change map is built from:  that one is
`Stacks.Sheaves.RingedToposModules.pullbackModules` of the morphism's
`toRingedToposModulesHom`, and the two agree only up to
`AlgebraicGeometry.RingedToposHom.pullbackModulesIso`.  Carrying the comparison across that
isomorphism is what `AlgebraicGeometry.Space.ringedDirectImageComp` does on the direct-image side;
on the inverse-image side nothing has to be carried, because the comparison can be *built* from
the direct-image one by uniqueness of left adjoints, which is how the source normalizes it
anyway.

*Why the composite is also carried as a named morphism.*  In the pasting argument the two
composite legs of a rectangle are morphisms of algebraic spaces written in two bracketings, and
transporting the comparison along `CategoryTheory.Category.assoc` at every use is what
`siteInverseImageComp'` avoids.  The transports surviving in it are of the form
`eqToIso (congrArg siteInverseImage e)` for an equality `e` of morphisms of algebraic spaces,
which are harmless:  the two functors are one function applied to two equal arguments.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.Sheaves.RingedToposModules (pushforwardModules
  pullbackAdjPushforwardModules)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inverse image of `𝒪`-modules along a morphism of algebraic spaces, in the shape the base
change map of **Stacks 0736** consumes: the inverse image of **Stacks 03D6**, part (2) of the
modules development, applied to the morphism of small étale ringed topoi of **Stacks 03G8**. -/
abbrev siteInverseImage {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :=
  pullbackModules (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom

/-- **Stacks 03D7** for the two images the base change map of **Stacks 0736** consumes: the
inverse image is left adjoint to the direct image. -/
def ringedAdjunction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    siteInverseImage f ⊣ ringedDirectImage f :=
  pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **Stacks 03LU, the inverse image of a composite**, for the inverse image the base change map
of **Stacks 0736** consumes:  `(f ≫ g)^* ≅ g^* ⋙ f^*`.

Both sides are left adjoint to `f_* ⋙ g_*` — the left-hand side by
`AlgebraicGeometry.Space.ringedDirectImageComp` transported across its adjunction, the right-hand
side because adjunctions compose — so they agree by uniqueness of left adjoints.  That this is
the canonical comparison, and not merely an isomorphism with the right endpoints, is
`AlgebraicGeometry.Space.conjugateEquiv_siteInverseImageComp_hom`. -/
def siteInverseImageComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    siteInverseImage (f ≫ g) ≅ siteInverseImage g ⋙ siteInverseImage f :=
  ((ringedAdjunction (f ≫ g)).ofNatIsoRight (ringedDirectImageComp f g).symm).leftAdjointUniq
    ((ringedAdjunction g).comp (ringedAdjunction f))

/-- `AlgebraicGeometry.Space.siteInverseImageComp` is its own definition, as a rewrite rule, for
the reason `AlgebraicGeometry.Space.ringedDirectImageComp_def` is. -/
theorem siteInverseImageComp_def (f : X ⟶ Y) (g : Y ⟶ Z) :
    siteInverseImageComp f g =
      ((ringedAdjunction (f ≫ g)).ofNatIsoRight (ringedDirectImageComp f g).symm).leftAdjointUniq
        ((ringedAdjunction g).comp (ringedAdjunction f)) := rfl

/-- **Stacks 03D8 for the two images the base change map of Stacks 0736 consumes.**  The
conjugate of the inverse-image comparison, across the adjunction of the composite and the
composite of the adjunctions, is the direct-image comparison of **Stacks 03LU**.

A natural transformation of left adjoints is determined by its conjugate, so this pins the
inverse-image comparison down:  it is the mate of
`AlgebraicGeometry.Space.ringedDirectImageComp` and of nothing else. -/
theorem conjugateEquiv_siteInverseImageComp_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((ringedAdjunction g).comp (ringedAdjunction f)) (ringedAdjunction (f ≫ g))
        (siteInverseImageComp f g).hom =
      (ringedDirectImageComp f g).hom :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

/-- The inverse-image comparison with the composite carried as a named morphism together with an
equation naming it.  This is the vocabulary the pasting argument uses. -/
def siteInverseImageComp' (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    siteInverseImage fg ≅ siteInverseImage g ⋙ siteInverseImage f :=
  eqToIso (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) hfg) ≪≫
    siteInverseImageComp f g

/-- `AlgebraicGeometry.Space.siteInverseImageComp'` is its own definition, as a rewrite rule. -/
theorem siteInverseImageComp'_def (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    siteInverseImageComp' f g fg hfg =
      eqToIso (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) hfg) ≪≫
        siteInverseImageComp f g := rfl

/-- With the composite taken to be `f ≫ g` itself, `AlgebraicGeometry.Space.siteInverseImageComp'`
is `AlgebraicGeometry.Space.siteInverseImageComp`. -/
@[simp]
theorem siteInverseImageComp'_rfl (f : X ⟶ Y) (g : Y ⟶ Z) :
    siteInverseImageComp' f g (f ≫ g) rfl = siteInverseImageComp f g := by
  rw [siteInverseImageComp'_def]
  simp

end AlgebraicGeometry.Space

end
