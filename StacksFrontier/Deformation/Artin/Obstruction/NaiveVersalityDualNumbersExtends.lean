module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityDegreeZeroConverse
public import StacksFrontier.Deformation.Artin.Versality.DualNumbersIsomorphismClasses
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfPostInclusion

/-!
# A lift along a square-zero immersion, read as a deformation over an Artinian base

Let `x` be an object of a category `p` fibred in groupoids over the big fppf site of `S`, let
`x₀` be an object over `Spec k` carrying an arrow `r₀ : x₀ ⟶ x`, and let `M` be a module in
the site over the field `k`. There are two ways to say that an infinitesimal deformation of
`x₀` over `k[M]` extends to `x`.

The degree-`0` half of Stacks 07YM produces the statement in the *lift* language: a lift of
`x₀` along the square-zero immersion `Spec k ⟶ Spec k[M]` is an object of the fibre of
`CategoryTheory.Under.post` at the composite of the structure equality of `x₀` with
`Deformation.Artin.squareZeroArrow`, and the conclusion is that its structure arrow composes
with an arrow to `x` to give `r₀`. Condition (a) of the versality criterion of Stacks 06IU, on
the other hand, consumes the statement in the *deformation* language: an arrow `i : x₀ ⟶ z`
whose underlying morphism of schemes is the augmentation of the object
`Deformation.Artin.squareZeroArtinianObj` of `𝒞_Λ`, and the conclusion is that `i` composes
with an arrow to `x` to give `r₀`.

This file is the translation from the first to the second. It is the inverse of the
translation `Deformation.Artin.exists_extends_of_liftsAtResiduePoint` runs, which takes a lift
and reads it as a deformation in order to apply versality.

## Main results

* `Deformation.Artin.extendsDeformation_of_exists_extends` — the deformation-shaped lifting
  statement at `Deformation.Artin.squareZeroArtinianObj`, from the lift-shaped one, at the
  single instance `Deformation.Artin.surjective_mapIsomorphismClasses_of_extendsAtArtinianBase`
  uses it: the source of the arrow is `x₀` itself and the arrow to `x` is `r₀`.
* `Deformation.Artin.extendsAtArtinianBase_of_exists_extends` — the same, strengthened to the
  whole of `Deformation.Artin.ExtendsAtArtinianBase`, which is the hypothesis that condition
  (a) of Stacks 06IU asks for at the dual numbers. The strengthening is where `p` being fibred
  in groupoids enters: it makes an arbitrary arrow `y ⟶ x` lying over the point of `Spec A`
  differ from `r₀` by an isomorphism.

That the result really is what the two neighbours say is pinned by a machine check rather than
by inspection: the private `extendsAtArtinianBase_of_surjective_canonicalTangentMap` at the end
of the file feeds `Deformation.Artin.exists_extends_of_surjective_canonicalTangentMap`, the
degree-`0` conclusion of Stacks 07YM, into the second result, and the output is the hypothesis
of `Deformation.Artin.surjective_mapIsomorphismClasses_of_extendsAtArtinianBase`. If either
statement drifts, that check stops compiling.

## Implementation notes

The inversion rests on the fact that `CategoryTheory.Over.post` of the inclusion of the site
is injective on objects: `AlgebraicGeometry.BigFppfSite.inclusion` is the inclusion of a
strictly full subcategory of `AlgebraicGeometry.Scheme` cut out by a size bound, so it is
injective on objects and faithful, and a slice object is determined by its underlying object
together with its structure morphism. That is what turns the hypothesis
`Deformation.Artin.squareZeroOver_post_eq` supplies — an equality of objects over `S` — back
into an equality of objects of the site, which is what the fibre of
`CategoryTheory.Under.post` is indexed by. (The same lemma is proved privately in
`StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison`, which carries out
the corresponding translation for isomorphism classes.)

On arrows the inversion is
`Deformation.Artin.NaiveVersalityDualNumbersExtends.map_eq_of_schemeMap_eq`, the converse of
the public `Deformation.Artin.schemeMap_eq_of_isHomLift`: an arrow of the total category whose
underlying morphism of schemes is the one underlying an arrow `ν` of the site does lie over
`ν`, because an arrow of the site is determined by its underlying morphism of schemes. It is
stated with the two objects of the site as variables so that both identifications can be
eliminated by substitution, after which every `eqToHom` in sight is one of a reflexive
equality.

Nothing here is special to the dual numbers, so the module `M` is left arbitrary; the base
`x₀` and the restriction arrow `r₀` are taken as data rather than as the chosen pullback of
`x`, since the chosen pullback is one instance and no property of the choice is used.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 06IU](https://stacks.math.columbia.edu/tag/06IU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

namespace NaiveVersalityDualNumbersExtends

/-! ### Objects and arrows of the site, recovered from their images over `S` -/

-- Two facts about slice categories stood here as `private` re-declarations, in this file's
-- nested namespace, which is why they never collided with the copies in
-- `Deformation/Artin/Infinitesimal/DeformationSpaceComparison.lean`. Objects of a strictly
-- full subcategory are equal as soon as their underlying objects are: Mathlib's
-- `CategoryTheory.ObjectProperty.FullSubcategory.ext`, generated by the `@[ext]` on the
-- structure, whose second field is a proposition. The other, the structure map of a slice
-- equality, was used only by the lemma below and is now dead.

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- Objects of the big fppf site over `S` are determined by their images over `S`:
-- `AlgebraicGeometry.BigFppfOver.obj_injective_post_inclusion`, public in
-- `StacksFrontier.AlgebraicGeometry.Topologies.FppfPostInclusion` (closure 23). A `private`
-- re-declaration stood here, with the same `(B) (S) (hS) {Y Z} (h)` binder shape, so its two
-- uses are renames.

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

/-- **The converse of `Deformation.Artin.schemeMap_eq_of_isHomLift`.** An arrow of the total
category whose underlying morphism of schemes is the one underlying an arrow `ν` of the site
factors, through the given identifications of its source and target, as `ν`: an arrow of the
site is determined by its underlying morphism of schemes. -/
private theorem map_eq_of_schemeMap_eq {Y₀ Z₀ : BigFppfOver B S hS} (ν : Y₀ ⟶ Z₀)
    {y z : X} (φ : y ⟶ z) (hy₀ : p.obj y = Y₀) (hz₀ : p.obj z = Z₀)
    (h : schemeMap (p ⋙ Over.post B.inclusion)
        (congrArg (Over.post B.inclusion).obj hy₀)
        (congrArg (Over.post B.inclusion).obj hz₀) φ =
      (BigFppfOver.toScheme B S hS).map ν) :
    p.map φ ≫ eqToHom hz₀ = eqToHom hy₀ ≫ ν := by
  subst hy₀ hz₀
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
  calc B.inclusion.map (p.map φ).left
      = 𝟙 _ ≫ B.inclusion.map (p.map φ).left ≫ 𝟙 _ := by simp
    _ = (BigFppfOver.toScheme B S hS).map ν := h

/-- The morphism of schemes underlying an arrow that lies over an arrow `ν` of the site is the one
underlying `ν`. -/
private theorem schemeMap_eq_map_of_isHomLift {Y₀ Z₀ : BigFppfOver B S hS} (ν : Y₀ ⟶ Z₀)
    {y z : X} (φ : y ⟶ z) [p.IsHomLift ν φ] (hy₀ : p.obj y = Y₀) (hz₀ : p.obj z = Z₀) :
    schemeMap (p ⋙ Over.post B.inclusion) (congrArg (Over.post B.inclusion).obj hy₀)
        (congrArg (Over.post B.inclusion).obj hz₀) φ =
      (BigFppfOver.toScheme B S hS).map ν :=
  (schemeMap_eq_of_isHomLift B S hS p ν φ _ _ rfl rfl).trans
    ((Category.id_comp _).trans (Category.comp_id _))

end NaiveVersalityDualNumbersExtends

/-! ### The lifting statement, read over an Artinian base -/

section Extends

open NaiveVersalityDualNumbersExtends

variable (A k : Type u) [CommRing A] [Field k] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hAk : B.Contains (Spec (.of k)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) {x : X}
variable (R : Type u) [CommRing R] [Algebra R k] (iR : Spec (.of R) ⟶ S)
  (hiR : Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR =
    Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
  (M : SiteModule k B) [Module.Finite k M.obj]
variable {x₀ : X} (hx₀ : p.obj x₀ =
    algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk)
  (r₀ : x₀ ⟶ x)

/-- **The deformation-shaped lifting statement, from the lift-shaped one.** Suppose every lift
of `x₀` along the square-zero immersion `Spec k ⟶ Spec k[M]` extends to `x`, that is every
object of the fibre of `CategoryTheory.Under.post` over the composite of the structure equality
of `x₀` with `Deformation.Artin.squareZeroArrow` has its structure arrow factor `r₀`. Then
every arrow `i : x₀ ⟶ z` whose target lies over `Spec` of the object
`Deformation.Artin.squareZeroArtinianObj` of `𝒞_R` and whose underlying morphism of schemes is
the augmentation `Deformation.Artin.residuePointMorphism` of that object extends to `x` as
well: there is an arrow `z ⟶ x` composing with `i` to give `r₀`.

This is the hypothesis `Deformation.Artin.ExtendsAtArtinianBase` asks for, at the one instance
`Deformation.Artin.surjective_mapIsomorphismClasses_of_extendsAtArtinianBase` uses it — the
source of the arrow being `x₀` itself and the arrow to `x` being `r₀`.

The target `z` is matched with the site's square-zero object by
`Deformation.Artin.squareZeroOver_post_eq` together with the injectivity of
`CategoryTheory.Over.post` of the inclusion of the site on objects, and the arrow `i` is
matched with `Deformation.Artin.squareZeroArrow` by the converse of
`Deformation.Artin.schemeMap_eq_of_isHomLift`. The two matchings assemble into the equality of
objects of `CategoryTheory.Under` that the fibre condition is. -/
public theorem extendsDeformation_of_exists_extends
    (hextends : ∀ w : (Under.post p).Fiber (Under.mk (eqToHom hx₀ ≫
        squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk M)),
      ∃ b : w.1.right ⟶ x, w.1.hom ≫ b = r₀)
    (z : X) (hz : (p ⋙ Over.post B.inclusion).obj z = Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap R (squareZeroArtinianObj R k M.obj))) ≫ iR))
    (i : x₀ ⟶ z)
    (hi : schemeMap (p ⋙ Over.post B.inclusion)
        ((congrArg (Over.post B.inclusion).obj hx₀).trans
          (algebraOver_post_eq A k B S hS toS hAk R iR hiR)) hz i =
      Spec.map (CommRingCat.ofHom
        (residuePointMorphism (squareZeroArtinianObj R k M.obj)).hom.toRingHom)) :
    ∃ b : z ⟶ x, i ≫ b = r₀ := by
  have hright : p.obj z =
      squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) M :=
    BigFppfOver.obj_injective_post_inclusion B S hS
      (hz.trans (squareZeroOver_post_eq A k B S hS toS R iR hiR M).symm)
  have hfac : p.map i ≫ eqToHom hright = eqToHom hx₀ ≫
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk M :=
    map_eq_of_schemeMap_eq B S hS p _ i hx₀ hright (hi.trans rfl)
  exact hextends ⟨Under.mk i, StructuredArrow.obj_ext _ _ hright hfac⟩

variable (hA : B.Contains (Spec (.of A)))
  (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)

include hp in
/-- **Condition (a) of Stacks 06IU at a square-zero base, from the lift-shaped statement.**
Under the same hypothesis as `Deformation.Artin.extendsDeformation_of_exists_extends`, the
full lifting property `Deformation.Artin.ExtendsAtArtinianBase` holds at
`Deformation.Artin.squareZeroArtinianObj`: it is not only `r₀` itself that extends across a
lift over `k[M]`, but every arrow `a : y ⟶ x` out of every object `y` over `Spec k` whose
underlying morphism of schemes is that of `r₀`.

The extra generality costs one step. Since `p` is fibred in groupoids, `a` is strongly
cartesian over the arrow of the site that `r₀` lies over — the two lie over the same arrow
because an arrow of the site is determined by its underlying morphism of schemes, which is
what the residue hypothesis on `a` equates — so the universal property produces a vertical
`g : x₀ ⟶ y` with `g ≫ a = r₀`. A vertical arrow is strongly cartesian over an identity and
hence invertible, so `i` may be replaced by `g ≫ i`, to which
`Deformation.Artin.extendsDeformation_of_exists_extends` applies; cancelling `g` turns the
resulting factorization of `r₀` into one of `a`. -/
public theorem extendsAtArtinianBase_of_exists_extends
    (hextends : ∀ w : (Under.post p).Fiber (Under.mk (eqToHom hx₀ ≫
        squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk M)),
      ∃ b : w.1.right ⟶ x, w.1.hom ≫ b = r₀) :
    ExtendsAtArtinianBase (k := k) iR (p ⋙ Over.post B.inclusion)
      ((congrArg (Over.post B.inclusion).obj hx₀).trans
        (algebraOver_post_eq A k B S hS toS hAk R iR hiR))
      (Over.mk toS) (congrArg (Over.post B.inclusion).obj hx) r₀
      (squareZeroArtinianObj R k M.obj) := by
  intro y z hy hz i hi a ha
  have hx₀S : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap R (fieldArtinianObj R k))) ≫ iR) :=
    (congrArg (Over.post B.inclusion).obj hx₀).trans
      (algebraOver_post_eq A k B S hS toS hAk R iR hiR)
  have hxS : (p ⋙ Over.post B.inclusion).obj x = (Over.mk toS : Over S) :=
    congrArg (Over.post B.inclusion).obj hx
  have hysite : p.obj y =
      algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk :=
    BigFppfOver.obj_injective_post_inclusion B S hS
      (hy.trans (algebraOver_post_eq A k B S hS toS hAk R iR hiR).symm)
  -- The arrow of the site that `r₀` lies over.
  set ν := eqToHom hx₀.symm ≫ p.map r₀ ≫ eqToHom hx with hν
  have hr₀ : p.IsHomLift ν r₀ := IsHomLift.of_fac' p _ r₀ hx₀ hx (by simp [hν])
  have hr : schemeMap (p ⋙ Over.post B.inclusion) hx₀S hxS r₀ =
      (BigFppfOver.toScheme B S hS).map ν := schemeMap_eq_map_of_isHomLift B S hS p ν r₀ hx₀ hx
  -- The arrow `a` lies over it too, its underlying morphism of schemes being the same.
  have hid : Spec.map (CommRingCat.ofHom (residueMap (fieldArtinianObj R k))) =
      𝟙 ((Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap R (fieldArtinianObj R k))) ≫ iR) : Over S).left) := by
    change Spec.map (𝟙 (CommRingCat.of k)) = _
    exact Spec.map_id _
  have hone := congrArg
    (fun t => t ≫ schemeMap (p ⋙ Over.post B.inclusion) hy hxS a) hid.symm
  have ha' : schemeMap (p ⋙ Over.post B.inclusion) hy hxS a =
      (BigFppfOver.toScheme B S hS).map ν :=
    (((Category.id_comp
      (schemeMap (p ⋙ Over.post B.inclusion) hy hxS a)).symm).trans hone).trans (ha.trans hr)
  have hamap : p.map a ≫ eqToHom hx = eqToHom hysite ≫ ν :=
    map_eq_of_schemeMap_eq B S hS p _ a hysite hx ha'
  have halift : p.IsHomLift ν a := by
    refine IsHomLift.of_fac' p _ a hysite hx ?_
    rw [← Category.assoc, ← hamap]
    simp
  have := hp.isStronglyCartesian_homLift ν a
  -- The vertical comparison arrow `x₀ ⟶ y` carrying `r₀` to `a`, and its invertibility.
  obtain ⟨g, ⟨hgv, hgfac⟩, -⟩ :=
    Functor.IsStronglyCartesian.universal_property p ν a (𝟙 _) ν (Category.id_comp _).symm r₀
  have := hp.isStronglyCartesian_homLift (𝟙 (algebraOver k B S hS
    (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk)) g
  have : IsIso g := Functor.IsStronglyCartesian.isIso_of_base_isIso p
    (𝟙 (algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk)) g
  have hgm : schemeMap (p ⋙ Over.post B.inclusion) hx₀S hy g = 𝟙 _ :=
    (schemeMap_eq_map_of_isHomLift B S hS p _ g hx₀ hysite).trans
      ((BigFppfOver.toScheme B S hS).map_id _)
  have hi' : schemeMap (p ⋙ Over.post B.inclusion) hx₀S hz (g ≫ i) =
      Spec.map (CommRingCat.ofHom
        (residuePointMorphism (squareZeroArtinianObj R k M.obj)).hom.toRingHom) := by
    rw [schemeMap_comp (p ⋙ Over.post B.inclusion) hx₀S hy hz g i, hgm]
    exact (Category.id_comp _).trans hi
  obtain ⟨b, hb⟩ := extendsDeformation_of_exists_extends A k B S hS toS hAk p R iR hiR M hx₀ r₀
    hextends z hz (g ≫ i) hi'
  rw [Category.assoc, ← hgfac] at hb
  exact ⟨b, (cancel_epi g).mp hb⟩

end Extends

/-! ### The two shapes match -/

section MachineCheck

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable (R : Type u) [CommRing R] [Algebra R k] (iR : Spec (.of R) ⟶ S)
  (hiR : Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR =
    Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)

/-- That the bridge really joins the two ends is pinned by a machine check rather than by
inspection: the degree-`0` conclusion of Stacks 07YM,
`Deformation.Artin.exists_extends_of_surjective_canonicalTangentMap`, is fed into
`Deformation.Artin.extendsAtArtinianBase_of_exists_extends` with no massaging, and what comes
out is the hypothesis of
`Deformation.Artin.surjective_mapIsomorphismClasses_of_extendsAtArtinianBase`, which is
condition (a) of Stacks 06IU at the dual numbers of the residue field. If either statement
drifts, this stops compiling. -/
private theorem extendsAtArtinianBase_of_surjective_canonicalTangentMap
    (hsurj : Function.Surjective (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk
      baseMap baseFactorization)) :
    letI : p.IsFibered := hp.isFibered
    ExtendsAtArtinianBase (k := k) iR (p ⋙ Over.post B.inclusion)
      ((congrArg (Over.post B.inclusion).obj
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
              (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj
            ⟨x, hx⟩).2).trans (algebraOver_post_eq A k B S hS toS hAk R iR hiR))
      (Over.mk toS) (congrArg (Over.post B.inclusion).obj hx)
      ((Functor.chosenPullbacks p).map
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩)
      (squareZeroArtinianObj R k (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B).obj) :=
  have : p.IsFibered := hp.isFibered
  extendsAtArtinianBase_of_exists_extends A k B S hS toS hAk p R iR hiR
    (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
    (((Functor.chosenPullbacks p).pullbackFunctor
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).2
    ((Functor.chosenPullbacks p).map
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩)
    hA hx hp
    (exists_extends_of_surjective_canonicalTangentMap Λ A k B S hS toS hA hAk p x hx hp hRS hΩ
      hk hkk baseMap baseFactorization hsurj)

end MachineCheck

end Deformation.Artin

end
