module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable
public import StacksFrontier.Deformation.Groupoid.Internal

/-!
# A groupoid in algebraic spaces after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `Bs`
be an algebraic space over `S` for `B`, and let `G = (U, R, s, t, c)` be a groupoid in algebraic
spaces over `Bs` (Stacks 043W). Write `f` for the morphism of sites that the inclusion
determines. This file constructs the groupoid in algebraic spaces
`(f⁻¹U, f⁻¹R, f⁻¹s, f⁻¹t, f⁻¹c)` over `f⁻¹Bs` on the larger site.

The structure maps are the images of those of `G`, the inverse image being a functor. The
content is the pointwise groupoid condition: a section of `f⁻¹U` over a test object of the
*larger* site has no description in terms of sections of `U`, so the condition cannot be
transported section by section. It is transported instead by internalizing it. A groupoid in
algebraic spaces is a groupoid *object* of the category of algebraic spaces — identity and
inverse as morphisms, and the groupoid laws as equations on generalized elements — and a
groupoid object transports along any functor carrying its two cartesian squares to cartesian
squares. The inverse image does, being left exact.

## Main definitions

* `AlgebraicGeometry.groupoidIdentityHom` and `AlgebraicGeometry.groupoidInverseHom`: the
  identity and the inverse of a groupoid in algebraic spaces, as morphisms of presheaves.
* `AlgebraicGeometry.groupoidObject`: a groupoid in algebraic spaces read as a
  `Deformation.GroupoidObject` of the category of algebraic spaces over `S`.
* `AlgebraicGeometry.changeBigSiteGroupoidObject` and
  `AlgebraicGeometry.changeBigSiteGroupoidPresheafObject`: its transport along the inverse
  image, in algebraic spaces and in presheaves.
* `AlgebraicGeometry.changeBigSiteCompComparison`: the comparison from the chosen fibre product
  of the enlarged source and target maps to the image of the chosen fibre product of the
  original ones, which is what turns the transported composition into a composition on the
  object the structure of Stacks 043W asks for.
* `AlgebraicGeometry.changeBigSiteGroupoid`: **the groupoid in algebraic spaces over `f⁻¹Bs` on
  the larger site.**

## Main results

* `AlgebraicGeometry.isPullback_hom_map_fibreProduct_changeBigSite` and
  `AlgebraicGeometry.isPullback_map_fibreProduct_changeBigSite`: the chosen fibre
  product of two morphisms of algebraic spaces stays cartesian after enlarging the big fppf
  site.
* `AlgebraicGeometry.comp_hom_app_eq`: the composition of a groupoid in algebraic spaces,
  evaluated on a section of the chosen fibre product presented by its two projections.

## No Stacks tag is placed here

Nothing here is hypothetical: the functor used throughout is
`AlgebraicGeometry.changeBigSite`, the inverse image *as a functor on algebraic spaces*, which
carries no hypothesis — the descent predicate the quotient theorem consumes is discharged once
and for all by `AlgebraicGeometry.descentForQuotients`. So the earlier reason for withholding an
attribute, that every declaration stood on a hypothesis the source does not have, no longer
applies.

An attribute is still withheld, for a purely mathematical reason. Stacks 04WX asserts a
*canonical equivalence* `[f⁻¹U/f⁻¹R] ≌ f⁻¹[U/R]` of stacks in groupoids over the enlarged site.
This file delivers the first step of its proof — that `(f⁻¹U, f⁻¹R, f⁻¹s, f⁻¹t, f⁻¹c)` is a
groupoid in algebraic spaces over `f⁻¹Bs`, which is what makes the left-hand side meaningful —
and nothing of the equivalence. The covering set of 04WX is therefore not met here, and an
attribute on one step of it would claim the equivalence. Nor does the construction carry a tag of
its own:
Stacks 04W1 is about algebraic spaces, not about groupoids in them, and the transport of the
groupoid structure is a step inside 04WX's proof rather than a separate assertion of the source.

What still blocks 04WX is its right-hand side `f⁻¹[U/R]`, the pullback of the quotient stack
along the morphism of sites; see the `## Main results` note of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackChangeBigSite`.

## Implementation notes

The groupoid object of `G` has the chosen algebraic-space fibre products
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` as its objects of composable pairs and of
composable triples, so both cartesian squares are
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` and neither has to be produced. Its
seven laws are proved one test object at a time, from
`Deformation.PointwiseGroupoid.toSetData` applied to the chosen pointwise groupoid there; the
section of a fibre product that a law speaks about is read as a composable pair of arrows
through `AlgebraicGeometry.pullbackToComposable`, which `AlgebraicGeometry.comp_hom_app_eq`
packages.

The identity and the inverse are *not* chosen out of the existence statements
`Deformation.existsUnique_identity` and `Deformation.existsUnique_inverse`: they are defined
pointwise, by `Deformation.GroupoidInFunctors.identity` and `Deformation.inverseArrow`, and only
their naturality is taken from those statements.

Left exactness of the inverse image is reached in three steps, as the type of a term built from
`h : AlgebraicGeometry.IsContained` is correct only at default transparency and so no equation
may be rewritten inside one: the presheaf fibre product square is lifted to sheaves on the
smaller site by full faithfulness of `CategoryTheory.sheafToPresheaf`, pushed along the inverse
image by `AlgebraicGeometry.inclusionOver_preservesFiniteLimits_sheafPullback`, and brought back
to algebraic spaces on the larger site by full faithfulness of `CategoryTheory.ObjectProperty.ι`.
For the same reason every proof past that point is a term rather than a rewrite.

## References

* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The identity map of a groupoid in algebraic spaces, as a morphism of the underlying
presheaves: at every test object it sends a point of the object space to the identity arrow at
that point. -/
def groupoidIdentityHom (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.objects.obj ⟶ G.arrows.obj where
  app T := ConcreteCategory.ofHom (TypeCat.Fun.mk fun x =>
    G.toGroupoidInFunctors.identity T x)
  naturality := by
    intro T T' f
    obtain ⟨e, he, -⟩ :=
      Deformation.existsUnique_identity G.toGroupoidInFunctors
    ext x
    have h := NatTrans.naturality_apply e f x
    rwa [he T' _, he T x] at h

/-- The inverse map of a groupoid in algebraic spaces, as a morphism of the underlying
presheaves: at every test object it sends an arrow to its inverse in the evaluated
groupoid. -/
def groupoidInverseHom (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.arrows.obj ⟶ G.arrows.obj where
  app T := ConcreteCategory.ofHom (TypeCat.Fun.mk fun a =>
    Deformation.inverseArrow G.toGroupoidInFunctors T a)
  naturality := by
    intro T T' f
    obtain ⟨i, hi, -⟩ :=
      Deformation.existsUnique_inverse G.toGroupoidInFunctors
    ext a
    have h := NatTrans.naturality_apply i f a
    rwa [hi T' _, hi T a] at h

/-- The composition of a groupoid in algebraic spaces, evaluated on a section of the fibre
product of the source and target maps presented by its two projections. -/
theorem comp_hom_app_eq (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (κ : (pullback G.source.hom G.target.hom).obj T)
    (a b : G.arrows.obj.obj T)
    (ha : (pullback.fst G.source.hom G.target.hom).app T κ = a)
    (hb : (pullback.snd G.source.hom G.target.hom).app T κ = b)
    (hab : G.source.hom.app T a = G.target.hom.app T b) :
    G.comp.hom.app T κ = G.toGroupoidInFunctors.comp.app T ⟨(a, b), hab⟩ := by
  have h1 : ((pullbackToComposable G.source.hom G.target.hom).app T κ).1.1 = a := by
    rw [← ha]
    exact natTrans_app_congr
      (pullbackToComposable_comp_composableFst G.source.hom G.target.hom) T κ
  have h2 : ((pullbackToComposable G.source.hom G.target.hom).app T κ).1.2 = b := by
    rw [← hb]
    exact natTrans_app_congr
      (pullbackToComposable_comp_composableSnd G.source.hom G.target.hom) T κ
  have h3 : (pullbackToComposable G.source.hom G.target.hom).app T κ = ⟨(a, b), hab⟩ :=
    Subtype.ext (Prod.ext h1 h2)
  have h4 : (composableToPullback G.source.hom G.target.hom).app T
      ((pullbackToComposable G.source.hom G.target.hom).app T κ) = κ :=
    natTrans_app_congr
      (pullbackToComposable_comp_composableToPullback G.source.hom G.target.hom) T κ
  have h5 : G.toGroupoidInFunctors.comp.app T
      ((pullbackToComposable G.source.hom G.target.hom).app T κ) = G.comp.hom.app T κ := by
    conv_rhs => rw [← h4]
    rfl
  rw [← h5, h3]
  rfl

/-- **A groupoid in algebraic spaces is a groupoid object of the category of algebraic
spaces.** The identity and the inverse that the pointwise groupoid condition determines at each
test object assemble into morphisms of algebraic spaces, and the seven laws of a groupoid
object hold because they hold at every test object. -/
def groupoidObject (G : GroupoidInAlgebraicSpaces C S hS B) :
    Deformation.GroupoidObject (AlgebraicSpaces C S hS) where
  objects := G.objects
  arrows := G.arrows
  pairs := AlgebraicSpaces.fiberProduct C S hS G.source G.target
  triples := AlgebraicSpaces.fiberProduct C S hS
    (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
      AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows)
    (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
      AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows)
  source := G.source
  target := G.target
  identity := ObjectProperty.homMk (groupoidIdentityHom G)
  inverse := ObjectProperty.homMk (groupoidInverseHom G)
  fst := ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom)
  snd := ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom)
  isPullback_pairs := AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target
  comp := G.comp
  fst₃ := ObjectProperty.homMk (pullback.fst
    (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
      AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows).hom
    (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
      AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows).hom)
  snd₃ := ObjectProperty.homMk (pullback.snd
    (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
      AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows).hom
    (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
      AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows).hom)
  isPullback_triples := AlgebraicSpaces.isPullback_fiberProduct C S hS
    (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
      AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows)
    (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
      AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows)
  identity_source := by
    have hgoal : groupoidIdentityHom G ≫ G.source.hom = 𝟙 G.objects.obj := by
      ext T x
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.source_identity x
    exact ObjectProperty.hom_ext _ hgoal
  identity_target := by
    have hgoal : groupoidIdentityHom G ≫ G.target.hom = 𝟙 G.objects.obj := by
      ext T x
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.target_identity x
    exact ObjectProperty.hom_ext _ hgoal
  inverse_source := by
    have hgoal : groupoidInverseHom G ≫ G.source.hom = G.target.hom := by
      ext T a
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.source_inverse a
    exact ObjectProperty.hom_ext _ hgoal
  inverse_target := by
    have hgoal : groupoidInverseHom G ≫ G.target.hom = G.source.hom := by
      ext T a
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.target_inverse a
    exact ObjectProperty.hom_ext _ hgoal
  comp_source := by
    have hgoal : G.comp.hom ≫ G.source.hom =
        pullback.snd G.source.hom G.target.hom ≫ G.source.hom := by
      ext T κ
      change G.source.hom.app T (G.comp.hom.app T κ) =
        G.source.hom.app T ((pullback.snd G.source.hom G.target.hom).app T κ)
      rw [comp_hom_app_eq G T κ _ _ rfl rfl
        (natTrans_app_congr (pullback.condition (f := G.source.hom) (g := G.target.hom)) T κ)]
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.source_comp _
    exact ObjectProperty.hom_ext _ hgoal
  comp_target := by
    have hgoal : G.comp.hom ≫ G.target.hom =
        pullback.fst G.source.hom G.target.hom ≫ G.target.hom := by
      ext T κ
      change G.target.hom.app T (G.comp.hom.app T κ) =
        G.target.hom.app T ((pullback.fst G.source.hom G.target.hom).app T κ)
      rw [comp_hom_app_eq G T κ _ _ rfl rfl
        (natTrans_app_congr (pullback.condition (f := G.source.hom) (g := G.target.hom)) T κ)]
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.target_comp _
    exact ObjectProperty.hom_ext _ hgoal
  comp_identity_left := by
    intro X a k h₁ h₂
    have hgoal : k.hom ≫ G.comp.hom = a.hom := by
      ext T x
      have e₁ : (pullback.fst G.source.hom G.target.hom).app T (k.hom.app T x) =
          G.toGroupoidInFunctors.identity T (G.target.hom.app T (a.hom.app T x)) :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) h₁) T x
      have e₂ : (pullback.snd G.source.hom G.target.hom).app T (k.hom.app T x) =
          a.hom.app T x :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) h₂) T x
      change G.comp.hom.app T (k.hom.app T x) = a.hom.app T x
      rw [comp_hom_app_eq G T (k.hom.app T x) _ _ e₁ e₂
        ((G.toGroupoidInFunctors.pointwiseData T).toSetData.source_identity _)]
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.comp_identity_left _
    exact ObjectProperty.hom_ext _ hgoal
  comp_identity_right := by
    intro X a k h₁ h₂
    have hgoal : k.hom ≫ G.comp.hom = a.hom := by
      ext T x
      have e₁ : (pullback.fst G.source.hom G.target.hom).app T (k.hom.app T x) =
          a.hom.app T x :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) h₁) T x
      have e₂ : (pullback.snd G.source.hom G.target.hom).app T (k.hom.app T x) =
          G.toGroupoidInFunctors.identity T (G.source.hom.app T (a.hom.app T x)) :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) h₂) T x
      change G.comp.hom.app T (k.hom.app T x) = a.hom.app T x
      rw [comp_hom_app_eq G T (k.hom.app T x) _ _ e₁ e₂
        ((G.toGroupoidInFunctors.pointwiseData T).toSetData.target_identity _).symm]
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.comp_identity_right _
    exact ObjectProperty.hom_ext _ hgoal
  comp_inverse_left := by
    intro X a k h₁ h₂
    have hgoal : k.hom ≫ G.comp.hom = a.hom ≫ G.source.hom ≫ groupoidIdentityHom G := by
      ext T x
      have e₁ : (pullback.fst G.source.hom G.target.hom).app T (k.hom.app T x) =
          Deformation.inverseArrow G.toGroupoidInFunctors T (a.hom.app T x) :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) h₁) T x
      have e₂ : (pullback.snd G.source.hom G.target.hom).app T (k.hom.app T x) =
          a.hom.app T x :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) h₂) T x
      change G.comp.hom.app T (k.hom.app T x) =
        G.toGroupoidInFunctors.identity T (G.source.hom.app T (a.hom.app T x))
      rw [comp_hom_app_eq G T (k.hom.app T x) _ _ e₁ e₂
        ((G.toGroupoidInFunctors.pointwiseData T).toSetData.source_inverse _)]
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.comp_inverse_left _
    exact ObjectProperty.hom_ext _ hgoal
  comp_inverse_right := by
    intro X a k h₁ h₂
    have hgoal : k.hom ≫ G.comp.hom = a.hom ≫ G.target.hom ≫ groupoidIdentityHom G := by
      ext T x
      have e₁ : (pullback.fst G.source.hom G.target.hom).app T (k.hom.app T x) =
          a.hom.app T x :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) h₁) T x
      have e₂ : (pullback.snd G.source.hom G.target.hom).app T (k.hom.app T x) =
          Deformation.inverseArrow G.toGroupoidInFunctors T (a.hom.app T x) :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) h₂) T x
      change G.comp.hom.app T (k.hom.app T x) =
        G.toGroupoidInFunctors.identity T (G.target.hom.app T (a.hom.app T x))
      rw [comp_hom_app_eq G T (k.hom.app T x) _ _ e₁ e₂
        ((G.toGroupoidInFunctors.pointwiseData T).toSetData.target_inverse _).symm]
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.comp_inverse_right _
    exact ObjectProperty.hom_ext _ hgoal
  comp_assoc := by
    intro X k l m n hkl hm₁ hm₂ hn₁ hn₂
    have hgoal : m.hom ≫ G.comp.hom = n.hom ≫ G.comp.hom := by
      ext T x
      have hcond : ∀ κ : (pullback G.source.hom G.target.hom).obj T,
          G.source.hom.app T ((pullback.fst G.source.hom G.target.hom).app T κ) =
            G.target.hom.app T ((pullback.snd G.source.hom G.target.hom).app T κ) :=
        fun κ => natTrans_app_congr
          (pullback.condition (f := G.source.hom) (g := G.target.hom)) T κ
      have ekl : (pullback.snd G.source.hom G.target.hom).app T (k.hom.app T x) =
          (pullback.fst G.source.hom G.target.hom).app T (l.hom.app T x) :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) hkl) T x
      have em₁ : (pullback.fst G.source.hom G.target.hom).app T (m.hom.app T x) =
          G.comp.hom.app T (k.hom.app T x) :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) hm₁) T x
      have em₂ : (pullback.snd G.source.hom G.target.hom).app T (m.hom.app T x) =
          (pullback.snd G.source.hom G.target.hom).app T (l.hom.app T x) :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) hm₂) T x
      have en₁ : (pullback.fst G.source.hom G.target.hom).app T (n.hom.app T x) =
          (pullback.fst G.source.hom G.target.hom).app T (k.hom.app T x) :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) hn₁) T x
      have en₂ : (pullback.snd G.source.hom G.target.hom).app T (n.hom.app T x) =
          G.comp.hom.app T (l.hom.app T x) :=
        natTrans_app_congr (congrArg (fun φ => φ.hom) hn₂) T x
      have hbd : G.source.hom.app T
            ((pullback.snd G.source.hom G.target.hom).app T (k.hom.app T x)) =
          G.target.hom.app T
            ((pullback.snd G.source.hom G.target.hom).app T (l.hom.app T x)) := by
        rw [ekl]
        exact hcond (l.hom.app T x)
      have hk := comp_hom_app_eq G T (k.hom.app T x) _ _ rfl rfl (hcond (k.hom.app T x))
      have hl := comp_hom_app_eq G T (l.hom.app T x) _ _ ekl.symm rfl hbd
      change G.comp.hom.app T (m.hom.app T x) = G.comp.hom.app T (n.hom.app T x)
      rw [comp_hom_app_eq G T (m.hom.app T x) _ _ (em₁.trans hk) em₂
          (((G.toGroupoidInFunctors.pointwiseData T).toSetData.source_comp _).trans hbd),
        comp_hom_app_eq G T (n.hom.app T x) _ _ en₁ (en₂.trans hl)
          ((hcond (k.hom.app T x)).trans
            ((G.toGroupoidInFunctors.pointwiseData T).toSetData.target_comp
              ⟨((pullback.snd G.source.hom G.target.hom).app T (k.hom.app T x),
                (pullback.snd G.source.hom G.target.hom).app T (l.hom.app T x)), hbd⟩).symm)]
      exact (G.toGroupoidInFunctors.pointwiseData T).toSetData.comp_assoc _ _ _ _ hbd
    exact ObjectProperty.hom_ext _ hgoal

/-! ### Enlarging the big fppf site -/

section ChangeOfBigSite

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- The underlying presheaf square of the fibre product of two morphisms of algebraic spaces
stays cartesian after enlarging the big fppf site, the inverse image being left exact. -/
theorem isPullback_hom_map_fibreProduct_changeBigSite
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback
      ((changeBigSite B B' h S hS).map
        (ObjectProperty.homMk (pullback.fst f.hom g.hom) :
          AlgebraicSpaces.fiberProduct B S hS f g ⟶ X)).hom
      ((changeBigSite B B' h S hS).map
        (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
          AlgebraicSpaces.fiberProduct B S hS f g ⟶ Y)).hom
      ((changeBigSite B B' h S hS).map f).hom
      ((changeBigSite B B' h S hS).map g).hom := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : HasSheafify J (Type u) := hasSheafify_overTopology B S hS
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S hS'
  let : PreservesFiniteLimits (i.sheafPullback (Type u) J K) :=
    inclusionOver_preservesFiniteLimits_sheafPullback B B' h S hS
  let toSheaf : AlgebraicSpaces B S hS ⥤ Sheaf J (Type u) :=
    ObjectProperty.lift _ (ObjectProperty.ι _) fun X => X.property.isSheaf
  have hJ : IsPullback
      (toSheaf.map (ObjectProperty.homMk (pullback.fst f.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS f g ⟶ X))
      (toSheaf.map (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS f g ⟶ Y))
      (toSheaf.map f) (toSheaf.map g) :=
    IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u))
      (IsPullback.of_hasPullback f.hom g.hom)
  exact (hJ.map (i.sheafPullback (Type u) J K)).map (sheafToPresheaf K (Type u))

/-- The fibre product of two morphisms of algebraic spaces stays cartesian after enlarging the
big fppf site. -/
theorem isPullback_map_fibreProduct_changeBigSite
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback
      ((changeBigSite B B' h S hS).map
        (ObjectProperty.homMk (pullback.fst f.hom g.hom) :
          AlgebraicSpaces.fiberProduct B S hS f g ⟶ X))
      ((changeBigSite B B' h S hS).map
        (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
          AlgebraicSpaces.fiberProduct B S hS f g ⟶ Y))
      ((changeBigSite B B' h S hS).map f)
      ((changeBigSite B B' h S hS).map g) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _)
    (isPullback_hom_map_fibreProduct_changeBigSite B B' h S hS f g)

variable {Bs : AlgebraicSpaces B S hS}

/-- **The groupoid object of a groupoid in algebraic spaces after enlarging the big fppf
site.** -/
def changeBigSiteGroupoidObject (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    Deformation.GroupoidObject (AlgebraicSpaces B' S (largerContains h hS)) :=
  (groupoidObject G).mapOfIsPullback (changeBigSite B B' h S hS)
    (isPullback_map_fibreProduct_changeBigSite B B' h S hS G.source G.target)
    (isPullback_map_fibreProduct_changeBigSite B B' h S hS
      (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct B S hS G.source G.target ⟶ G.arrows)
      (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct B S hS G.source G.target ⟶ G.arrows))

/-- The comparison from the chosen fibre product of the enlarged source and target maps to the
image of the chosen fibre product of the original ones. -/
def changeBigSiteCompComparison (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    AlgebraicSpaces.fiberProduct B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).map G.source)
        ((changeBigSite B B' h S hS).map G.target) ⟶
      (changeBigSite B B' h S hS).obj
        (AlgebraicSpaces.fiberProduct B S hS G.source G.target) :=
  (isPullback_map_fibreProduct_changeBigSite B B' h S hS
      G.source G.target).lift
    (ObjectProperty.homMk (pullback.fst
      ((changeBigSite B B' h S hS).map G.source).hom
      ((changeBigSite B B' h S hS).map G.target).hom))
    (ObjectProperty.homMk (pullback.snd
      ((changeBigSite B B' h S hS).map G.source).hom
      ((changeBigSite B B' h S hS).map G.target).hom))
    (AlgebraicSpaces.isPullback_fiberProduct B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).map G.source)
      ((changeBigSite B B' h S hS).map G.target)).w

/-- The comparison is compatible with the first projection. -/
theorem changeBigSiteCompComparison_comp_fst (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    changeBigSiteCompComparison B B' h S hS G ≫
        (changeBigSite B B' h S hS).map
          (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
            AlgebraicSpaces.fiberProduct B S hS G.source G.target ⟶ G.arrows) =
      ObjectProperty.homMk (pullback.fst
        ((changeBigSite B B' h S hS).map G.source).hom
        ((changeBigSite B B' h S hS).map G.target).hom) :=
  IsPullback.lift_fst _ _ _ _

/-- The comparison is compatible with the second projection. -/
theorem changeBigSiteCompComparison_comp_snd (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    changeBigSiteCompComparison B B' h S hS G ≫
        (changeBigSite B B' h S hS).map
          (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
            AlgebraicSpaces.fiberProduct B S hS G.source G.target ⟶ G.arrows) =
      ObjectProperty.homMk (pullback.snd
        ((changeBigSite B B' h S hS).map G.source).hom
        ((changeBigSite B B' h S hS).map G.target).hom) :=
  IsPullback.lift_snd _ _ _ _

/-- **The groupoid object in presheaves of a groupoid in algebraic spaces after enlarging the
big fppf site.** -/
def changeBigSiteGroupoidPresheafObject (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    Deformation.GroupoidObject
      ((BigFppfOver B' S (largerContains h hS))ᵒᵖ ⥤ Type u) :=
  (changeBigSiteGroupoidObject B B' h S hS G).mapOfIsPullback (ObjectProperty.ι _)
    (isPullback_hom_map_fibreProduct_changeBigSite B B' h S hS
      G.source G.target)
    (isPullback_hom_map_fibreProduct_changeBigSite B B' h S hS
      (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct B S hS G.source G.target ⟶ G.arrows)
      (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct B S hS G.source G.target ⟶ G.arrows))

/-- The generalized element of the image of the object of composable pairs determined by a
composable pair of sections of the enlarged arrow space is the one the comparison produces. -/
theorem sectionPairHom_changeBigSiteGroupoidPresheafObject
    (G : GroupoidInAlgebraicSpaces B S hS Bs)
    (T : (BigFppfOver B' S (largerContains h hS))ᵒᵖ)
    (p : (Deformation.composableArrows
      ((changeBigSite B B' h S hS).obj G.objects).obj
      ((changeBigSite B B' h S hS).obj G.arrows).obj
      ((changeBigSite B B' h S hS).map G.source).hom
      ((changeBigSite B B' h S hS).map G.target).hom).obj T) :
    (changeBigSiteGroupoidPresheafObject B B' h S hS G).sectionPairHom T.unop p =
      yonedaEquiv.symm ((composableToPullback
        ((changeBigSite B B' h S hS).map G.source).hom
        ((changeBigSite B B' h S hS).map G.target).hom ≫
          (changeBigSiteCompComparison B B' h S hS G).hom).app T p) :=
  have hfst : (changeBigSiteCompComparison B B' h S hS G).hom ≫
      (changeBigSiteGroupoidPresheafObject B B' h S hS G).fst =
        pullback.fst ((changeBigSite B B' h S hS).map G.source).hom
          ((changeBigSite B B' h S hS).map G.target).hom :=
    congrArg (fun k => k.hom) (changeBigSiteCompComparison_comp_fst B B' h S hS G)
  have hsnd : (changeBigSiteCompComparison B B' h S hS G).hom ≫
      (changeBigSiteGroupoidPresheafObject B B' h S hS G).snd =
        pullback.snd ((changeBigSite B B' h S hS).map G.source).hom
          ((changeBigSite B B' h S hS).map G.target).hom :=
    congrArg (fun k => k.hom) (changeBigSiteCompComparison_comp_snd B B' h S hS G)
  Deformation.GroupoidObject.sectionPairHom_eq_of_comparison
    (changeBigSiteGroupoidPresheafObject B B' h S hS G) _ _ _
    ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) hfst).trans (composableToPullback_comp_pullbackFst _ _)))
    ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) hsnd).trans (composableToPullback_comp_pullbackSnd _ _)))
    T.unop p p rfl rfl

/-- **The groupoid in algebraic spaces obtained by enlarging the big fppf site.** The object
and arrow spaces, the two structure maps to the base and the source and target maps are the
images of those of the given groupoid; composition is its image read through the comparison of
the two chosen fibre products; and the pointwise groupoid condition comes from the groupoid
object of the given groupoid, transported along the inverse image, which is left exact. -/
def changeBigSiteGroupoid (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    GroupoidInAlgebraicSpaces B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj Bs) where
  objects := (changeBigSite B B' h S hS).obj G.objects
  arrows := (changeBigSite B B' h S hS).obj G.arrows
  objectsToBase := (changeBigSite B B' h S hS).map G.objectsToBase
  arrowsToBase := (changeBigSite B B' h S hS).map G.arrowsToBase
  source := (changeBigSite B B' h S hS).map G.source
  target := (changeBigSite B B' h S hS).map G.target
  source_over :=
    ((changeBigSite B B' h S hS).map_comp G.source G.objectsToBase).symm.trans
      (congrArg (changeBigSite B B' h S hS).map G.source_over)
  target_over :=
    ((changeBigSite B B' h S hS).map_comp G.target G.objectsToBase).symm.trans
      (congrArg (changeBigSite B B' h S hS).map G.target_over)
  comp := changeBigSiteCompComparison B B' h S hS G ≫
    (changeBigSite B B' h S hS).map G.comp
  comp_over :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => changeBigSiteCompComparison B B' h S hS G ≫ k)
        ((((changeBigSite B B' h S hS).map_comp G.comp G.arrowsToBase).symm.trans
          (congrArg (changeBigSite B B' h S hS).map G.comp_over)).trans
          ((changeBigSite B B' h S hS).map_comp _ _))).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ (changeBigSite B B' h S hS).map G.arrowsToBase)
            (changeBigSiteCompComparison_comp_fst B B' h S hS G))))
  pointwiseGroupoid := by
    intro T
    refine ⟨(changeBigSiteGroupoidPresheafObject B B' h S hS G).pointwiseGroupoid
      T.unop _ fun p => ?_⟩
    refine Eq.symm (Eq.trans (congrArg (fun k => yonedaEquiv
      (k ≫ (changeBigSiteGroupoidPresheafObject B B' h S hS G).comp))
      (sectionPairHom_changeBigSiteGroupoidPresheafObject B B' h S hS G T p)) ?_)
    exact (yonedaEquiv_comp _ _).trans
      (congrArg (fun z => (changeBigSiteGroupoidPresheafObject B B' h S hS G).comp.app
        (Opposite.op T.unop) z) (Equiv.apply_symm_apply yonedaEquiv _))

end ChangeOfBigSite

end AlgebraicGeometry

end
