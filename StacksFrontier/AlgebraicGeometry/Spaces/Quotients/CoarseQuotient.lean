module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CategoricalQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.OrbitSeparation

/-!
# Coarse quotients of a pre-relation

A morphism `φ : U ⟶ X` of algebraic spaces over an algebraic space `B` is a *coarse quotient*
of a pre-relation `j : R ⟶ U ×_B U` when it is at once a categorical quotient of `j` and an
orbit space for it: it has the universal property among algebraic spaces over `B`, and on
points over an algebraically closed field it identifies exactly the pairs joined by an arrow
of `j`, surjectively.

When instead the base is the base scheme `S` itself and `R`, `U` and `X` are schemes, the
same two conditions — now with the universal property imposed in schemes over `S` — define a
*coarse quotient in schemes*.

The two conditions are imposed in two different slices. The universal property quantifies over
the test objects of the ambient category, so it is a statement about the slice of
`AlgebraicGeometry.AlgebraicSpaces` over `B`, respectively about the slice of schemes over
`S`; the orbit conditions speak about points of presheaves and are stated in the slice of
presheaves over the presheaf of `B`, respectively over the presheaf of `S`. The functor
carrying the one to the other is `AlgebraicGeometry.Space.overForgetSpace`, and
`AlgebraicGeometry.Space.presheafPreRelation` is the pre-relation of presheaves it produces
from a pre-relation of algebraic spaces; for schemes the corresponding translations are
`AlgebraicGeometry.Space.schemeAsSpace`, `AlgebraicGeometry.Space.schemeMapAsSpace` and
`AlgebraicGeometry.Space.schemePreRelation`.

## Main definitions

* `AlgebraicGeometry.Space.overForgetSpace`: the forgetful functor from algebraic spaces over
  `B` to presheaves over the presheaf of `B`.
* `AlgebraicGeometry.Space.presheafPreRelation`: a pre-relation of algebraic spaces over `B`,
  read as a pre-relation of presheaves over the presheaf of `B`.
* `AlgebraicGeometry.Space.IsCoarseQuotient`: **Stacks 04A2**, the coarse-quotient condition
  among algebraic spaces over `B`.
* `AlgebraicGeometry.Space.siteTerminal` and `AlgebraicGeometry.Space.schemeBase`: the base
  scheme over itself, as an object of the big fppf category over `S` and as the presheaf it
  represents, with `AlgebraicGeometry.Space.toSiteTerminal` the canonical morphism to the
  former.
* `AlgebraicGeometry.Space.siteAsSpace` and `AlgebraicGeometry.Space.siteMapAsSpace`: an
  object, respectively a morphism, of the big fppf category over `S`, read in the slice of
  presheaves over the presheaf of `S`.
* `AlgebraicGeometry.Space.schemeInSite` and `AlgebraicGeometry.Space.schemeAsSpace`: a
  scheme over `S` contained in the site, as an object of the big fppf category over `S` and
  as a presheaf over the presheaf of `S`; `AlgebraicGeometry.Space.schemeMapInSite` and
  `AlgebraicGeometry.Space.schemeMapAsSpace` do the same for a morphism.
* `AlgebraicGeometry.Space.schemePreRelation`: a pre-relation of schemes over `S`, read as a
  pre-relation of presheaves over the presheaf of `S`.
* `AlgebraicGeometry.Space.IsCoarseQuotientInSchemes`: **Stacks 04A2**, the coarse-quotient
  condition among schemes over the base scheme.

## Main results

* `AlgebraicGeometry.Space.presheafPreRelation_target` and
  `AlgebraicGeometry.Space.presheafPreRelation_source`: the two maps of the presheaf
  pre-relation are the images of the two maps of the original one.
* `AlgebraicGeometry.Space.schemePreRelation_target` and
  `AlgebraicGeometry.Space.schemePreRelation_source`: the same for a pre-relation of schemes.
* `AlgebraicGeometry.Space.comp_toSiteTerminal`: the canonical morphisms to the terminal
  object of the big fppf category over `S` are compatible with every morphism.

## Implementation notes

`overForgetSpace` is `CategoryTheory.Over.post` of the inclusion of the full subcategory of
algebraic spaces, so on objects it forgets the algebraicity of the total space and keeps the
structure morphism, and on morphisms it is the underlying morphism of presheaves.

`presheafPreRelation` is defined by its two legs rather than by transporting the original map
along a comparison isomorphism of products. Both descriptions agree: the product in either
slice is the fibre product over the base, and by **Stacks 02X2** the presheaf fibre product of
algebraic spaces is again their product in algebraic spaces, so the comparison
`overForgetSpace B |>.obj (U ⨯ U) ⟶ (overForgetSpace B).obj U ⨯ (overForgetSpace B).obj U` is
an isomorphism. Defining the two legs directly means no such isomorphism has to be inverted,
and the two equations characterizing the result are then the universal property of the
product.

The scheme-level condition is stated for schemes over `S` — the objects of
`CategoryTheory.Over S` that the categorical quotient in schemes of **Stacks 048J**, part
(3), speaks about — together with the hypothesis that each of `R`, `U` and `X` is contained
in the big fppf site, which is what makes them objects of the site and hence algebraic spaces
over `S`. The base algebraic space is then `S` itself: `siteTerminal` is the terminal object
of the site, so `schemeBase` is the terminal presheaf, which is the algebraic space the base
scheme is. `schemePreRelation` is again defined by its two legs, so no containment hypothesis
on the fibre product `U ×_S U` is needed; the orbit conditions of **Stacks 0493** use only
the target and the source of the pre-relation, which are exactly those two legs.

Both conditions are transparent abbreviations, so clients may use the two conjuncts directly.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 048J](https://stacks.math.columbia.edu/tag/048J)
* [Stacks Project, Tag 0493](https://stacks.math.columbia.edu/tag/0493)
* [Stacks Project, Tag 04A2](https://stacks.math.columbia.edu/tag/04A2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}

/-! ### An algebraic-space pre-relation read in the presheaf slice -/

/-- The forgetful functor from algebraic spaces over an algebraic space `B` to presheaves over
the presheaf of `B`: it forgets algebraicity of the total space and keeps the structure
morphism. -/
abbrev overForgetSpace (B : AlgebraicSpaces site S hS) : Over B ⥤ Over B.obj :=
  Over.post (ObjectProperty.ι _)

variable {B : AlgebraicSpaces site S hS}

/-- **Stacks 043C, part (1).** A pre-relation of algebraic spaces over `B`, read as a
pre-relation of presheaves over the presheaf of `B`: the morphism to the product whose two
legs are the images of the target and the source of the original pre-relation. -/
noncomputable def presheafPreRelation {R U : Over B} (j : PreRelation R U) :
    PreRelation ((overForgetSpace B).obj R) ((overForgetSpace B).obj U) :=
  prod.lift ((overForgetSpace B).map j.target) ((overForgetSpace B).map j.source)

/-- The target of the presheaf pre-relation is the image of the target of the original
pre-relation. -/
@[simp]
theorem presheafPreRelation_target {R U : Over B} (j : PreRelation R U) :
    (presheafPreRelation j).target = (overForgetSpace B).map j.target :=
  prod.lift_fst _ _

/-- The source of the presheaf pre-relation is the image of the source of the original
pre-relation. -/
@[simp]
theorem presheafPreRelation_source {R U : Over B} (j : PreRelation R U) :
    (presheafPreRelation j).source = (overForgetSpace B).map j.source :=
  prod.lift_snd _ _

/-! ### Coarse quotients -/

/-- **Stacks 04A2.** A morphism `φ : U ⟶ X` of algebraic spaces over `B` is a *coarse
quotient* of a pre-relation `j` when it is a categorical quotient of `j` and an orbit space
for it. -/
@[stacks 04A2 "algebraic spaces"]
noncomputable abbrev IsCoarseQuotient {R U X : Over B} (j : PreRelation R U) (φ : U ⟶ X) :
    Prop :=
  IsCategoricalQuotient j φ ∧
    IsOrbitSpace (presheafPreRelation j) ((overForgetSpace B).map φ).left

/-! ### A scheme pre-relation read in the presheaf slice -/

section Schemes

variable (site S hS)

/-- The terminal object of the big fppf category over `S`: the base scheme over itself. -/
abbrev siteTerminal : BigFppfOver site S hS := Over.mk (𝟙 (site.obj hS))

/-- The presheaf represented by the base scheme over itself. This is the algebraic space
that the base scheme is, and it is the base over which a pre-relation of schemes over `S`
is read. -/
abbrev schemeBase : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u :=
  yoneda.obj (siteTerminal site S hS)

variable {site S hS}

/-- The canonical morphism to the terminal object of the big fppf category over `S`. -/
abbrev toSiteTerminal (T : BigFppfOver site S hS) : T ⟶ siteTerminal site S hS :=
  Over.homMk T.hom

/-- Every morphism of the big fppf category over `S` commutes with the canonical morphisms
to the terminal object. -/
theorem comp_toSiteTerminal {T T' : BigFppfOver site S hS} (f : T ⟶ T') :
    f ≫ toSiteTerminal T' = toSiteTerminal T := by
  apply CategoryTheory.Over.OverMorphism.ext
  simp

/-- An object of the big fppf category over `S`, as a presheaf over the presheaf of `S`:
the presheaf it represents, with the image of its structure morphism. -/
abbrev siteAsSpace (T : BigFppfOver site S hS) : Over (schemeBase site S hS) :=
  Over.mk (yoneda.map (toSiteTerminal T))

/-- A morphism of the big fppf category over `S`, as a morphism of presheaves over the
presheaf of `S`. -/
abbrev siteMapAsSpace {T T' : BigFppfOver site S hS} (f : T ⟶ T') :
    siteAsSpace T ⟶ siteAsSpace T' :=
  Over.homMk (yoneda.map f) (by
    simp only [siteAsSpace, Over.mk_left, Over.mk_hom, ← Functor.map_comp, comp_toSiteTerminal])

variable (hS)

/-- A scheme over `S` whose underlying scheme is contained in the site, as an object of the
big fppf category over `S`. -/
abbrev schemeInSite {T : Over S} (hT : site.Contains T.left) : BigFppfOver site S hS :=
  siteObject site S hS hT T.hom

/-- A scheme over `S` contained in the site, as a presheaf over the presheaf of `S`. -/
abbrev schemeAsSpace {T : Over S} (hT : site.Contains T.left) : Over (schemeBase site S hS) :=
  siteAsSpace (schemeInSite hS hT)

/-- A morphism of schemes over `S` between schemes contained in the site, as a morphism of
the big fppf category over `S`. -/
abbrev schemeMapInSite {T T' : Over S} (hT : site.Contains T.left)
    (hT' : site.Contains T'.left) (f : T ⟶ T') : schemeInSite hS hT ⟶ schemeInSite hS hT' :=
  Over.homMk (ObjectProperty.homMk f.left) (by
    apply ObjectProperty.hom_ext
    simp)

/-- A morphism of schemes over `S` between schemes contained in the site, as a morphism of
presheaves over the presheaf of `S`. -/
abbrev schemeMapAsSpace {T T' : Over S} (hT : site.Contains T.left)
    (hT' : site.Contains T'.left) (f : T ⟶ T') : schemeAsSpace hS hT ⟶ schemeAsSpace hS hT' :=
  siteMapAsSpace (schemeMapInSite hS hT hT' f)

/-- **Stacks 022P, part (1), read in presheaves.** A pre-relation of schemes over `S`
between schemes contained in the site, read as a pre-relation of presheaves over the
presheaf of `S`: the morphism to the product whose two legs are the images of the target
and the source of the original pre-relation. -/
noncomputable def schemePreRelation {R U : Over S} (hR : site.Contains R.left)
    (hU : site.Contains U.left) (j : Stacks.Groupoids.PreRelation R U) :
    PreRelation (schemeAsSpace hS hR) (schemeAsSpace hS hU) :=
  prod.lift (schemeMapAsSpace hS hR hU j.target) (schemeMapAsSpace hS hR hU j.source)

/-- The target of the presheaf pre-relation is the image of the target of the original
pre-relation of schemes. -/
@[simp]
theorem schemePreRelation_target {R U : Over S} (hR : site.Contains R.left)
    (hU : site.Contains U.left) (j : Stacks.Groupoids.PreRelation R U) :
    (schemePreRelation hS hR hU j).target = schemeMapAsSpace hS hR hU j.target :=
  prod.lift_fst _ _

/-- The source of the presheaf pre-relation is the image of the source of the original
pre-relation of schemes. -/
@[simp]
theorem schemePreRelation_source {R U : Over S} (hR : site.Contains R.left)
    (hU : site.Contains U.left) (j : Stacks.Groupoids.PreRelation R U) :
    (schemePreRelation hS hR hU j).source = schemeMapAsSpace hS hR hU j.source :=
  prod.lift_snd _ _

/-! ### Coarse quotients in schemes -/

/-- **Stacks 04A2.** A morphism `φ : U ⟶ X` of schemes over the base scheme `S`, with `R`,
`U` and `X` contained in the big fppf site, is a *coarse quotient in schemes* of a
pre-relation `j` of schemes over `S` when it is a categorical quotient in schemes of `j`
and an orbit space for it. -/
@[stacks 04A2 "schemes"]
noncomputable abbrev IsCoarseQuotientInSchemes {R U X : Over S} (hR : site.Contains R.left)
    (hU : site.Contains U.left) (hX : site.Contains X.left)
    (j : Stacks.Groupoids.PreRelation R U) (φ : U ⟶ X) : Prop :=
  IsCategoricalQuotientInSchemes j φ ∧
    IsOrbitSpace (schemePreRelation hS hR hU j) (schemeMapAsSpace hS hU hX φ).left

end Schemes

end AlgebraicGeometry.Space

end
