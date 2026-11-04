module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceCover
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# Local essential surjectivity of a flat, locally finitely presented, surjective 1-morphism

Let `S` be a scheme contained in a big fppf site `B` and let `g : 𝒲 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S` which is representable by algebraic
spaces. A 1-morphism is *locally essentially surjective* when every object of a fibre of `𝒴`
becomes, after restriction to a covering sieve of the big fppf topology, isomorphic to the image
of an object of `𝒲`; that is the hypothesis the descent lemma **Stacks 045D** consumes and the
one Properties of Stacks, Lemma **04XD** has to produce.

This module proves that `g` is locally essentially surjective as soon as every algebraic space
representing its base change along a scheme-valued point of `𝒴` has surjective, flat and locally
finitely presented structural morphism — the hypothesis **Stacks 04XD** makes on `g`, written out
as in **Stacks 03YK**. It is the implication which
`StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceCover` records as missing, and the
proof is the source's own.

Fix `U` and an object `y` of the fibre of `𝒴` over `U`. The 2-Yoneda lemma (**Stacks 004B**)
turns `y` into a scheme-valued point of `𝒴` over `U`, so the hypothesis applies and supplies an
algebraic space `F` over `U` representing `𝒲 ×_𝒴 U` whose structural morphism is surjective, flat
and locally of finite presentation. Read over `S` along the forward functor of **Stacks 04SG**,
`F` has a surjective étale scheme atlas `a : h_T ⟶ Λ F` (**Stacks 025Y**); an atlas is flat and
locally of finite presentation, so the composite `h_T ⟶ Λ F ⟶ h_U` is surjective, flat and
locally of finite presentation, and by full faithfulness of Yoneda it is `h_m` for a morphism
`m : T ⟶ U` of the site whose underlying morphism of schemes has those three properties
(**Stacks 03MJ** at the identity charts, and clause (1) of **Stacks 03BX** for surjectivity).
The one-member family `m` therefore generates a covering sieve of `U`
(`AlgebraicGeometry.exists_mem_topology_of_family`). The section of `Λ F` named by the atlas
carries, by the construction of the lower-shriek extension of **Stacks 03I5**, exactly the
factorisation `m` together with a section of `F` over `(T, m)`; that section is named by an
object of `𝒲 ×_𝒴 U` lying over `(T, m)`, whose `𝒲`-component and comparison isomorphism are the
lift of `y` along `m`. Every arrow of the sieve factors through `m`, and `𝒲` is fibred in
groupoids, so the lift transports along the factorisation.

## Main results

* `AlgebraicGeometry.Stack.localEssSurj_of_exists_scheme_lift`: the site-level reduction — one
  flat, locally finitely presented, surjective scheme morphism through which the object lifts
  suffices.
* `AlgebraicGeometry.Stack.exists_scheme_lift_of_isSurjective_isFlat_isLocallyOfFinitePresentation`
  — the single flat, locally finitely presented, surjective scheme morphism along which an object
  of a fibre lifts. This is the shape Stacks 06XH consumes.
* `AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation`:
  the content, with the hypothesis of **Stacks 04XD** on `g`.
* `AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isSmooth`: the same with a surjective and
  smooth base change, smoothness implying flatness and local finite presentation.
* `AlgebraicGeometry.Stack.exists_atlas_localEssSurj`: the scheme presentation of an algebraic
  stack is locally essentially surjective.
* `AlgebraicGeometry.Stack.hasRelativeProperty_of_prop_representingMap_of_fppf` and
  `AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap_of_fppf`: Properties of
  Stacks, Lemma **04XD** with its own hypotheses on `g`.
* `AlgebraicGeometry.Stack.isRelativelySmooth_of_baseChange_of_fppf`: **Stacks 045D** at the
  smooth property with its local essential surjectivity hypothesis discharged.
* `AlgebraicGeometry.Stack.small_fiber_schemeFibredCategory`: the fibres of the category
  represented by a scheme over `S` are small.

## Implementation notes

`AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation` is
`AlgebraicGeometry.Stack.exists_scheme_lift_of_isSurjective_isFlat_isLocallyOfFinitePresentation`
followed by `AlgebraicGeometry.Stack.localEssSurj_of_exists_scheme_lift`. The single-morphism form
is stated separately because Stacks 06XH needs the morphism itself, which the covering sieve of the
conclusion does not expose: the sieve is existentially quantified, so no single arrow can be
selected from it.

The two Stacks 04XD statements below are the ones of
`StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceCover` with the local essential
surjectivity hypothesis replaced by the surjectivity, flatness and local finite presentation
which that module records as implying it.

`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap_of_fppf` is the only
declaration here carrying a `@[stacks]` attribute, and it carries `@[stacks 04XD]`. Lemma 04XD is
one biconditional sentence, so its covering set is a single declaration, and that iff is it: it
states the sentence whole, with Lemma 04XD's own hypotheses on `g`.
`AlgebraicGeometry.Stack.hasRelativeProperty_of_prop_representingMap_of_fppf` is its backward half
and states less than the sentence, so it gets no site; and the pair of
`StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceCover` stays untagged as well, since
those state the sentence with the weaker hypothesis of local essential surjectivity in place of
the three properties which imply it.

The three scheme-level properties are read off `yoneda.map m` rather than off the atlas and the
structural morphism separately: flatness and local finite presentation go through
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`, which needs the property of
schemes to be étale local on the source and on the target, and surjectivity through
`AlgebraicGeometry.Space.surjective_yonedaMap_iff_surjective_pointsMap` followed by
`AlgebraicGeometry.Space.presheaf_yoneda_map_iff`, since surjectivity of a morphism of algebraic
spaces is surjectivity on point sets and not an every-chart condition.

The covering sieve is produced from a family indexed by `PUnit` in the universe `u + 1` of the
underlying category of the site, which is the index universe
`AlgebraicGeometry.exists_mem_topology_of_family` is stated at. The one-element family comes from
the geometry — the scheme atlas of the representing algebraic space — and not from re-extracting
a family out of a covering sieve, whose index type is only bounded by the site's covering bound.

The scheme-valued point attached to an object of a fibre is the composite of the 2-Yoneda
essential preimage `CategoryTheory.Functor.TwoYoneda.liftFunctor` with
`CategoryTheory.Over.iteratedSliceBackward`, the identification of the big fppf site of `U` with
the slice of the big fppf site of `S` over `U`. Both halves of the lift are read off the chosen
lifts of that construction, which is why the base objects never have to be transported: the
comparison isomorphism of an object of the 2-fibre product is vertical, and the chosen arrow to
`y` lies over the structural morphism of the slice object, so their composite lies over that
morphism with no `CategoryTheory.eqToHom` appearing.

The universes are those of the two inputs. The main statements hold at
`CatFiberedInGroupoids.{u, v, u + 1, w}` with `v` and `w` free, and the three corollaries
instantiate them: Stacks 04XD at `v = u`, `w = u + 1`, Stacks 045D at the saturation
`v = max u v'`, `w = max (max (u + 1) w') v'` of Stacks 0302, and the presentation of an
algebraic stack at `v = u`, `w = u + 1` again.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The scheme-valued point of `𝒴` over `U` named by an object `y` of the fibre of `𝒴` over `U`:
the essential preimage of `y` under the evaluation functor of the 2-Yoneda lemma
(Stacks 004B), read on the big fppf site of `U` through the identification of that site with the
slice of the big fppf site of `S` over `U`. -/
noncomputable def fibrePoint
    (𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U) :
    BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj :=
  Over.iteratedSliceBackward U ⋙
    Functor.TwoYoneda.liftFunctor 𝒴.val.p 𝒴.isFiberedInGroupoids U y

/-- The scheme-valued point named by an object of the fibre over `U` is a functor over the big
fppf site of `U`, as the representability condition of Stacks 02ZW requires: the 2-Yoneda
essential preimage lies over the slice of the site over `U`, and
`CategoryTheory.Over.iteratedSliceBackward_forget` identifies that slice with the site of `U`
over the base. -/
theorem fibrePoint_comp
    (𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U) :
    fibrePoint B S hS 𝒴 U y ⋙ 𝒴.val.p = Over.map U.hom := by
  rw [fibrePoint, Functor.assoc, Functor.TwoYoneda.liftFunctor_w,
    Over.iteratedSliceBackward_forget]

/-- **An object of the 2-fibre product is a lift.** An object of `U ×_𝒴 𝒲` whose first component
is a slice object `W₀` of the big fppf site of `U` supplies an object `z` of `𝒲` and a morphism
from its image to `y` lying over the structural morphism of `W₀` read in the site over `S`.

The morphism is the comparison isomorphism of the object, which is vertical, followed by the
chosen 2-Yoneda arrow to `y`, which lies over that structural morphism. -/
theorem exists_lift_of_fst_obj
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (g : 𝒲 ⟶ 𝒴)
    (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U)
    {W₀ : BigFppfOver B U.left.1 U.left.2}
    (P : TwoFibreProductOver (Over.map U.hom) 𝒲.val.p 𝒴.val.p
      (fibrePoint B S hS 𝒴 U y) (CatFiberedInGroupoids.homFunctor g))
    (hP : (TwoFibreProductOver.fst (Over.map U.hom) 𝒲.val.p 𝒴.val.p
      (fibrePoint B S hS 𝒴 U y) (CatFiberedInGroupoids.homFunctor g)).obj P = W₀) :
    ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1),
      𝒴.val.p.IsHomLift
        (Over.homMk W₀.hom rfl : (Over.mk (W₀.hom ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ := by
  subst hP
  set c := Functor.TwoYoneda.chosenLift 𝒴.val.p 𝒴.isFiberedInGroupoids U y
    ((Over.iteratedSliceBackward U).obj P.x)
  refine ⟨P.y, P.iso.inv ≫ c.φ, ?_⟩
  have hinv : 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj P.x)) P.iso.inv := by
    rw [P.hx]
    exact @IsHomLift.lift_id_inv _ _ _ _ 𝒴.val.p _ _ _ P.iso P.vertical
  exact Functor.isHomLift_comp_of_isHomLift_id 𝒴.val.p P.iso.inv _ _ hinv
    c.isStronglyCartesian.toIsHomLift

/-- **One flat, locally finitely presented, surjective scheme morphism suffices.** A 1-morphism
`g : 𝒲 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S` is locally
essentially surjective as soon as every object `y` of every fibre of `𝒴` admits a single
morphism `m : T ⟶ U` of the underlying category of the site, flat, locally of finite
presentation and surjective on the underlying schemes, along which `y` lifts to `𝒲`.

The one-member family `m` generates a covering sieve by
`AlgebraicGeometry.mem_topology_of_family`, every arrow of that sieve factors through `m`, and
the lift transports along the factorisation because `𝒲` is fibred in groupoids. -/
theorem localEssSurj_of_exists_scheme_lift
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (g : 𝒲 ⟶ 𝒴)
    (H : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ (T : B.Schemes) (m : T ⟶ U.left),
        Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
          Surjective (B.inclusion.map m) ∧
          ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1),
            𝒴.val.p.IsHomLift
              (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ) :
    ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1),
            𝒴.val.p.IsHomLift k φ := by
  intro U y
  obtain ⟨T, m, hflat, hlfp, hsurj, z, φ, hφ⟩ := H U y
  obtain ⟨R, hR, hfac⟩ := exists_mem_topology_of_family B S hS (I := PUnit.{u + 2})
    (fun _ => T) (fun _ => m) (fun _ => hflat) (fun _ => hlfp)
    (fun x => ⟨PUnit.unit, hsurj.1 x⟩)
  refine ⟨R, hR, ?_⟩
  intro V k hk
  obtain ⟨_, b, hb⟩ := hfac hk
  have hw : CatFiberedInGroupoids.homFunctor g ⋙ 𝒴.val.p = 𝒲.val.p := g.hom.w
  have hzbase : 𝒲.val.p.obj z = Over.mk (m ≫ U.hom) := by
    rw [← hw]
    exact IsHomLift.domain_eq 𝒴.val.p
      (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ
  obtain ⟨z', ρ, hρ⟩ := 𝒲.isFiberedInGroupoids.exists_lift b z hzbase
  refine ⟨z', (CatFiberedInGroupoids.homFunctor g).map ρ ≫ φ, ?_⟩
  rw [← hb]
  have : 𝒴.val.p.IsHomLift b ((CatFiberedInGroupoids.homFunctor g).map ρ) :=
    PresheafOfCategories.isHomLift_map_of_comp hw b ρ hρ
  exact IsHomLift.comp 𝒴.val.p b
    (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U)
    ((CatFiberedInGroupoids.homFunctor g).map ρ) φ

/-- **A single flat, locally finitely presented, surjective scheme morphism lifting an object.**
Let `g : 𝒲 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of
`S` representable by algebraic spaces, and suppose that every algebraic space representing the
base change of `g` along a scheme-valued point of `𝒴` has surjective, flat and locally finitely
presented structural morphism, as in Stacks 03YK. Then every object `y` of every fibre of `𝒴`
admits a *single* morphism `m : T ⟶ U` of the underlying category of the site, flat, locally of
finite presentation and surjective on the underlying schemes, along which `y` lifts to `𝒲`.

This is the source's own construction: the base change of `g` along the scheme-valued point
named by `y` is represented by an algebraic space whose structural morphism has the three
properties, an étale scheme atlas of that space composes with the structural morphism to a
morphism of the site with the same three properties, and the section named by the atlas carries
the lift. It is the form Stacks 06XH needs, where a single arrow is required rather than a
covering sieve, and
`AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation` is
this statement followed by
`AlgebraicGeometry.Stack.localEssSurj_of_exists_scheme_lift`. -/
theorem exists_scheme_lift_of_isSurjective_isFlat_isLocallyOfFinitePresentation
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (g : 𝒲 ⟶ 𝒴)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h)) :
    ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ (T : B.Schemes) (m : T ⟶ U.left),
        Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
          Surjective (B.inclusion.map m) ∧
          ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1),
            𝒴.val.p.IsHomLift
              (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ := by
  intro U y
  obtain ⟨F, hF, e⟩ := hg U (fibrePoint B S hS 𝒴 U y) (fibrePoint_comp B S hS 𝒴 U y)
  obtain ⟨hsurj, hflat, hlfp⟩ :=
    hprop U (fibrePoint B S hS 𝒴 U y) (fibrePoint_comp B S hS 𝒴 U y) F hF e
  set X : AlgebraicSpaces B U.left.1 U.left.2 := ⟨F, hF⟩ with hX
  set G := (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj X with hG
  set I := spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom with hI
  obtain ⟨T, a, hasurj, haetale⟩ := G.property.exists_atlas
  have hae : Space.IsEtale B S hS a := (Space.isEtale_iff_presheaf_of_yoneda B S hS a).2 haetale
  -- The section of the lower-shriek extension named by the atlas; it carries a factorisation of
  -- the structure morphism of `T` through `U` and a section of `F` over that factorisation.
  set t := (I.hom.app X).app (op T) (yonedaEquiv a) with ht
  have hm : yonedaEquiv (a ≫ G.obj.hom) = Over.homMk t.1.1 t.2 := by
    rw [yonedaEquiv_comp]
    have hround : (I.inv.app X).app (op T) t = yonedaEquiv a :=
      ((I.app X).app (op T)).toEquiv.symm_apply_apply _
    rw [ht] at hround ⊢
    rw [← hround]
    exact spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS U.hom
      X (op T) _
  have hrw : yoneda.map (Over.homMk t.1.1 t.2 : T ⟶ U) = a ≫ G.obj.hom :=
    yonedaEquiv.injective (by rw [yonedaEquiv_yoneda_map, hm])
  have key : ∀ {P : MorphismProperty Scheme.{u}} (hP : IsEtaleLocalOnSourceAndTarget P),
      Space.HoldsOnEveryEtaleChart B S hS P (a ≫ G.obj.hom) →
        P ((BigFppfOver.toScheme B S hS).map (Over.homMk t.1.1 t.2 : T ⟶ U)) := fun hP h =>
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP _).1 (hrw ▸ h)
  refine ⟨T.left, t.1.1, ?_, ?_, ?_, ?_⟩
  · exact key Flat.isEtaleLocalOnSourceAndTarget
      (Space.isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS T) G.property
        (isAlgebraicSpace_yoneda B S hS U) a G.obj.hom
        (Space.isFlat_atlas B S hS G.property hae) hflat)
  · exact key LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
      (Space.isLocallyOfFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS T)
        G.property (isAlgebraicSpace_yoneda B S hS U) a G.obj.hom
        (Space.isLocallyOfFinitePresentation_atlas B S hS G.property hae) hlfp)
  · refine (Space.presheaf_yoneda_map_iff B S hS
      (inferInstance : MorphismProperty.IsStableUnderBaseChange
        (@Surjective.{u} : MorphismProperty Scheme.{u}))
      (Over.homMk t.1.1 t.2 : T ⟶ U)).1 ?_
    refine (Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS _).2 ?_
    rw [hrw]
    exact Space.isSurjective_comp B S hS
      ((Space.surjective_iff_surjective_pointsMap B S hS G.obj.left G.property T a).1 hasurj)
      hsurj
  · obtain ⟨P, hP, _⟩ := PresheafOfCategories.exists_sectionOfObj e.some
      (W := (Over.mk t.1.1 : BigFppfOver B U.left.1 U.left.2)) t.1.2
    exact exists_lift_of_fst_obj B S hS g U y P hP

/-- **A 1-morphism whose base change along every scheme-valued point is surjective, flat and
locally of finite presentation is locally essentially surjective.** Let `g : 𝒲 ⟶ 𝒴` be a
1-morphism of categories fibred in groupoids over the big fppf site of `S` representable by
algebraic spaces, and suppose that every algebraic space representing the base change of `g`
along a scheme-valued point of `𝒴` has surjective, flat and locally finitely presented
structural morphism, read as a morphism of algebraic spaces over `S` as in Stacks 03YK. Then
every object of a fibre of `𝒴` becomes, after restriction to a covering sieve of the big fppf
topology, isomorphic to the image of an object of `𝒲`.

This is the hypothesis Properties of Stacks, Lemma 04XD makes on `g`, and the conclusion the
descent lemma Stacks 045D consumes. -/
theorem localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (g : 𝒲 ⟶ 𝒴)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h)) :
    ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1),
            𝒴.val.p.IsHomLift k φ :=
  localEssSurj_of_exists_scheme_lift B S hS g
    (exists_scheme_lift_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS g hg hprop)

/-- **A 1-morphism whose base change along every scheme-valued point is surjective and smooth is
locally essentially surjective.** This is
`AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation` with
the flatness and local finite presentation of the structural morphism supplied by its smoothness,
which is Stacks 03ZF and Stacks 03ZG for morphisms of algebraic spaces. It is the form the
presentation clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` is written in. -/
theorem localEssSurj_of_isSurjective_isSmooth
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (g : 𝒲 ⟶ 𝒴)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h)) :
    ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1),
            𝒴.val.p.IsHomLift k φ := by
  refine localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS g hg
    (fun V yv hyv F hF he => ?_)
  obtain ⟨hs, hsm⟩ := hprop V yv hyv F hF he
  exact ⟨hs, Space.isFlat_of_isSmooth B S hS _ hsm,
    Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩

/-- **The scheme presentation of an algebraic stack is locally essentially surjective.** An
algebraic stack over `S` carries, by the fourth clause of Stacks 026O, a 1-morphism from the
category represented by a scheme `U` over `S` which is representable by algebraic spaces and
whose base change along every scheme-valued point of the stack has surjective and smooth
structural morphism. Every object of a fibre of the stack therefore becomes, after restriction to
a covering sieve of the big fppf topology, isomorphic to the image of an object of that
represented category. -/
theorem exists_atlas_localEssSurj (𝒳 : AlgebraicStacks.{u, t} B S hS) :
    ∃ (U : BigFppfOver B S hS) (f : schemeFibredCategory B S hS U ⟶ 𝒳.val),
      IsRepresentableByAlgebraicSpaces B S hS f.hom ∧
      ∀ (V : BigFppfOver B S hS) (y : 𝒳.val.val.p.Fiber V),
        ∃ R ∈ BigFppfOver.topology B S hS V,
          ∀ ⦃V' : BigFppfOver B S hS⦄ ⦃k : V' ⟶ V⦄, R.arrows k →
            ∃ (z : (schemeFibredCategory B S hS U).val.obj)
              (φ : (CatFiberedInGroupoids.homFunctor f).obj z ⟶ y.1),
              𝒳.val.val.p.IsHomLift k φ := by
  obtain ⟨_, _, _, U, f, hfrep, hfprop⟩ := 𝒳.property
  exact ⟨U, Bicategory.InducedBicategory.mkHom f, hfrep,
    localEssSurj_of_isSurjective_isSmooth B S hS
      (Bicategory.InducedBicategory.mkHom f) hfrep hfprop⟩

/-- **The fibres of the category represented by a scheme over `S` are small.** An object of the
fibre of `(Sch/S)/U` over `V` is an object of the slice whose underlying object is `V`, hence is
determined by its structure morphism, so the fibre injects into the morphisms `V ⟶ U` of the
site, which form a `u`-small type. This is not an instance: the total category of the slice lives
in `Type (u + 1)` and the smallness of the fibre is not visible to instance search. -/
theorem small_fiber_schemeFibredCategory (U V : BigFppfOver B S hS) :
    Small.{u} ((schemeFibredCategory B S hS U).val.p.Fiber V) := by
  refine small_of_injective (f := fun a => eqToHom a.2.symm ≫ a.1.hom) ?_
  rintro ⟨⟨a, r, ha⟩, rfl⟩ ⟨⟨b, r', hb⟩, hb2⟩ h
  obtain rfl : a = b := hb2.symm
  obtain ⟨⟨⟩⟩ := r
  obtain ⟨⟨⟩⟩ := r'
  simp only [eqToHom_refl] at h
  obtain rfl : ha = hb := h
  rfl

/-- **Properties of Stacks, Lemma 04XD, the backward implication.** Let `P` be a property of
morphisms of algebraic spaces over `S` stable under base change and local on the target for the
fppf precoverage, let `f : 𝒳 ⟶ 𝒴` be representable by algebraic spaces, and let `g : 𝒲 ⟶ 𝒴` be
representable by algebraic spaces with every algebraic space representing its base change along a
scheme-valued point of `𝒴` surjective, flat and locally of finite presentation. Fix a 2-fibre
product square over the cospan `(g, f)` whose apex and whose `𝒲` are representable by algebraic
spaces `V` and `W`. If the induced morphism `V ⟶ W` of representing presheaves has `P`, then `f`
has the relative property `P` of Stacks 03YK.

This is `AlgebraicGeometry.Stack.hasRelativeProperty_of_prop_representingMap_of_localEssSurj`
with its local essential surjectivity hypothesis discharged by
`AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation`. -/
theorem hasRelativeProperty_of_prop_representingMap_of_fppf
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (𝒳 𝒴 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hgr : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hg : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h))
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
    (eV : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      𝒲.val.p (presheafOfCategories (W ⋙ typeToCat)).p)
    (hprop : P (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) :
      (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ (⟨W, hW⟩ : AlgebraicSpaces B S hS))) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P f hf :=
  hasRelativeProperty_of_prop_representingMap_of_localEssSurj B S hS P 𝒳 𝒴 𝒲 f g hf
    (localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS g hgr hg)
    Q hQ V W hV hW eV eW hprop

/-- **Properties of Stacks, Lemma 04XD.** In the situation above, `f` has the relative property
`P` of Stacks 03YK exactly when the morphism `V ⟶ W` of representing presheaves induced by the
first projection of the square has `P` as a morphism of algebraic spaces over `S`.

The forward implication is Stacks 04XC and uses no hypothesis on `g`; the backward one is
`AlgebraicGeometry.Stack.hasRelativeProperty_of_prop_representingMap_of_fppf`. -/
@[stacks 04XD]
theorem hasRelativeProperty_iff_prop_representingMap_of_fppf
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} B S hS)]
    (𝒳 𝒴 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hgr : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hg : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h))
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
    (eV : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      𝒲.val.p (presheafOfCategories (W ⋙ typeToCat)).p) :
    HasRelativeProperty.{u, u, u + 1, max u t} B S hS P f hf ↔
      P (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) :
        (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ (⟨W, hW⟩ : AlgebraicSpaces B S hS)) :=
  have : P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.Topology.precoverage_le_precoverage_max .fppf B S hS)
  hasRelativeProperty_iff_prop_representingMap_of_localEssSurj B S hS P 𝒳 𝒴 𝒲 f g hf
    (localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS g hgr hg)
    Q hQ V W hV hW eV eW

/-- **Stacks 045D at the smooth property, with the descent hypothesis discharged.** A 1-morphism
representable by algebraic spaces is smooth as soon as one of its base changes is, along a
1-morphism `g : 𝒵 ⟶ 𝒴` which is representable by algebraic spaces and whose base change along
every scheme-valued point of `𝒴` is surjective, flat and locally of finite presentation.

This is `AlgebraicGeometry.Stack.isRelativelySmooth_of_baseChange` with its local essential
surjectivity hypothesis supplied by
`AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation`. -/
theorem isRelativelySmooth_of_baseChange_of_fppf
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (D : Bicategory.TwoCommSq g f) (hD : Bicategory.IsTwoFibreProduct D)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hgr : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hg : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒵.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h))
    (hP : IsRelativelySmooth B S hS D.fst) :
    IsRelativelySmooth B S hS f :=
  isRelativelySmooth_of_baseChange.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g D hD hf
    (localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS g hgr hg) hP

end AlgebraicGeometry.Stack

end
