module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Sorites
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
import all StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.AffineCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative limit preservation for representable transformations

A transformation `a : F ⟶ G` of presheaves on the big fppf site of `S` is *relatively limit
preserving* when, for every object `X` of the site and every section `y` of `G` over `X`, the
presheaf on `Over X` of lifts of `y` through `a` turns cofiltered inverse limits of affine
schemes into filtered colimits of sets.

When `a` is representable, that presheaf of lifts is itself representable: it is the presheaf
on `Over X` represented by the represented pullback of `a` along `y`, viewed as an object over
`X`. Relative limit preservation of `a` therefore reduces to the representable case, which is
the content of `AlgebraicGeometry.limitPreserving_yoneda_of_locallyOfFinitePresentation`.

This gives the representable case of Stacks 04AK in the vocabulary of Tag 049J, and with it the
whole implication (2) ⇒ (1) of Stacks 04AK; see the *What is and is not proved* section below.

## Main definitions

No new public definitions are introduced. There are four private auxiliary declarations, all of
them steps in identifying the presheaf of lifts with a representable presheaf: the two
statements `AlgebraicGeometry.repFiber_app_eq` and `AlgebraicGeometry.repFiber_lift_comm`, the
bijection `AlgebraicGeometry.repFiberEquiv` at a single object over `X`, and the resulting
isomorphism of presheaves `AlgebraicGeometry.repFiberIso`.

## Main results

* `AlgebraicGeometry.relativelyLimitPreserving_of_presheaf_locallyOfFinitePresentation`: a
  representable transformation of presheaves whose represented base changes are locally of
  finite presentation is relatively limit preserving, for index categories in the universe of
  the schemes.
* `AlgebraicGeometry.etale_le_locallyOfFinitePresentation`: étaleness of a morphism of schemes
  implies local finite presentation, as an inequality of morphism properties.
* `AlgebraicGeometry.relativelyLimitPreserving_comp_of_etale_chart`: the composite of an étale
  chart of the source with a morphism of algebraic spaces locally of finite presentation is
  relatively limit preserving.
* `AlgebraicGeometry.locallyOfFinitePresentation_of_relativelyLimitPreserving_yoneda_map`: the
  implication (2) ⇒ (1) of Stacks 01ZC for a morphism of the site — if the Yoneda image of a
  morphism of the site is relatively limit preserving, its underlying morphism of schemes is
  locally of finite presentation.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving`: a
  relatively limit-preserving transformation of algebraic spaces is locally of finite
  presentation. This is the implication (2) ⇒ (1) of Stacks 04AK;
  `AlgebraicGeometry.isLocallyOfFinitePresentation_of_relativelyLimitPreserving` is the same
  statement with its scheme-level input taken as the hypothesis `h01ZC`.

## Implementation notes

*What is and is not proved.* Stacks 04AK is the equivalence of (1) local finite presentation
and (2) relative limit preservation for a morphism of algebraic spaces. The implication
(2) ⇒ (1) is proved here, unconditionally; the implication (1) ⇒ (2) is not.

The scheme-level input of that implication is the implication (2) ⇒ (1) of Stacks 01ZC, read
for a morphism `h : U ⟶ V` of the site: that relative limit preservation of `yoneda.map h`
gives local finite presentation of the underlying morphism of schemes. It is proved here as
`AlgebraicGeometry.locallyOfFinitePresentation_of_relativelyLimitPreserving_yoneda_map`, and
*not* by appeal to the scheme-level characterisations of Stacks 01ZC in
`StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints`. Those are not applicable,
and the reason is the heart of the matter: relative limit preservation only ever tests inverse
systems internal to the size-bounded site `AlgebraicGeometry.BigFppfOver B S hS`, whereas
`AlgebraicGeometry.Scheme.IsLimitPreserving` and
`AlgebraicGeometry.Scheme.IsLimitPreservingOnAffineTransitions` — and equally the criterion of
Tag 0CM0 — quantify over systems of *arbitrary* schemes over the base, of which the site
contains only those below its cutoff. There is no map from the one quantifier to the other.

What bridges the gap is the surjective affine-limit criterion of Tag 0CM6,
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_affineLimit_surjective`, whose
hypothesis is itself restricted to systems internal to the site. It is there that the
set-theoretic caveat the source's proof of Stacks 04AK closes with is discharged: the systems
the proof needs are the spectra of the finitely presented subalgebras of a ring of functions on
a chart, and those lie below the cutoff because the cutoff is a strong prelimit, so only
algebras of cardinality bounded by that of the base ring are ever required.

The rest of the implication is as before: the two étale charts of a square are representable and
étale, hence representable and locally of finite presentation by
`AlgebraicGeometry.etale_le_locallyOfFinitePresentation`, hence relatively limit preserving by
the first result below; composing with the given transformation and cancelling the chart of the
target leaves the Yoneda image of the chart morphism relatively limit preserving, which is where
the scheme-level implication is applied. Because the hypothesis of that result is relative limit
preservation at index universes equal to the universe of the schemes, which the free-universe
form of Tag 049J specialises to, it is not weaker than the implication (2) ⇒ (1) of Stacks 04AK.
Note that Stacks 0468 itself — étaleness implies local finite presentation for a morphism of
algebraic *spaces* — is not what is used here and is proved separately, as
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isEtale`; only its scheme-level input
is needed below.

The implication (1) ⇒ (2) is *not* proved here, in any form. The source proves it by choosing a
presentation `X = U/R` and sheafifying, and the single binding constraint on the conclusion is
the index universe: Mathlib's inverse-limit API for schemes with affine transition maps is
stated for an index category `I : Type u` with `Category.{u} I`, where `u` is the universe of
the schemes, while Tag 049J as recorded in this repository quantifies over all index universes,
including ones strictly larger than that.

*Index universes.* All results here are at index universes equal to the universe of the
schemes, inherited from `AlgebraicGeometry.limitPreserving_yoneda_of_locallyOfFinitePresentation`.

*The identification of the presheaf of lifts.* Mathlib's relative representability API is
phrased internally to the site wherever possible, and that is what is used: the lift of a
section is produced by `CategoryTheory.Functor.relativelyRepresentable.lift`, which returns a
morphism of the site rather than of presheaves, and the two triangles and the uniqueness come
from `lift_fst`, `lift_snd` and `hom_ext`. The auxiliary statements are deliberately phrased for
a bare morphism of the site together with a commuting triangle, rather than for a morphism of
`Over X`, because the projection of an `Over.mk` is only definitionally the represented
pullback and a rewrite against the latter fails on the former.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 0468](https://stacks.math.columbia.edu/tag/0468)
* [Stacks Project, Tag 06BC](https://stacks.math.columbia.edu/tag/06BC)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Representable

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
  (ha : yoneda.relativelyRepresentable a)
  {X : BigFppfOver B S hS} (y : G.obj (Opposite.op X))

/-- A morphism of the site into the represented pullback of `a` along `y`, composed with the
first projection, is a lift of `y` through `a` over the triangle it commutes with. -/
private theorem repFiber_app_eq {c : BigFppfOver B S hS} {h : c ⟶ X}
    {g : c ⟶ ha.pullback (yonedaEquiv.symm y)}
    (hg : g ≫ ha.snd (yonedaEquiv.symm y) = h) :
    a.app (Opposite.op c) (yonedaEquiv (yoneda.map g ≫ ha.fst (yonedaEquiv.symm y))) =
      G.map h.op y := by
  rw [← yonedaEquiv_comp, Category.assoc, ha.w, ← Category.assoc, ← Functor.map_comp, hg,
    ← yonedaEquiv_naturality, Equiv.apply_symm_apply]

/-- A lift of `y` through `a` over a morphism `h` of the site gives a commuting square against
the defining square of the represented pullback of `a` along `y`. -/
private theorem repFiber_lift_comm {c : BigFppfOver B S hS} {h : c ⟶ X}
    {x : F.obj (Opposite.op c)} (hx : a.app (Opposite.op c) x = G.map h.op y) :
    yonedaEquiv.symm x ≫ a = yoneda.map h ≫ yonedaEquiv.symm y := by
  apply yonedaEquiv.injective
  rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, ← yonedaEquiv_naturality,
    Equiv.apply_symm_apply]

/-- At each object over `X`, the morphisms into the represented pullback of `a` along `y` are
exactly the lifts of `y` through `a`. -/
private noncomputable def repFiberEquiv (Y : (Over X)ᵒᵖ) :
    (yoneda.obj (Over.mk (ha.snd (yonedaEquiv.symm y)))).obj Y ≃
      (sectionFiber B S hS a X y).obj Y where
  toFun φ := ⟨_, repFiber_app_eq B S hS ha y (Over.w φ)⟩
  invFun x :=
    Over.homMk (ha.lift (yonedaEquiv.symm x.1) Y.unop.hom
      (repFiber_lift_comm B S hS y x.2)) (ha.lift_snd _ _ _)
  left_inv φ :=
    Over.OverMorphism.ext (ha.hom_ext
      ((ha.lift_fst _ _ _).trans (Equiv.symm_apply_apply _ _))
      ((ha.lift_snd _ _ _).trans (Over.w φ).symm))
  right_inv _x :=
    Subtype.ext ((congrArg yonedaEquiv (ha.lift_fst _ _ _)).trans
      (Equiv.apply_symm_apply _ _))

/-- The presheaf of lifts of `y` through a representable `a` is the presheaf on `Over X`
represented by the represented pullback of `a` along `y`. -/
private noncomputable def repFiberIso :
    yoneda.obj (Over.mk (ha.snd (yonedaEquiv.symm y))) ≅ sectionFiber B S hS a X y :=
  NatIso.ofComponents (fun Y => (repFiberEquiv B S hS ha y Y).toIso) (by
    intro Y Z g
    ext φ
    apply Subtype.ext
    change yonedaEquiv (yoneda.map (g.unop ≫ φ).left ≫ ha.fst (yonedaEquiv.symm y)) =
      F.map g.unop.left.op (yonedaEquiv (yoneda.map φ.left ≫ ha.fst (yonedaEquiv.symm y)))
    rw [yonedaEquiv_naturality, Over.comp_left, Functor.map_comp, Category.assoc])

end Representable

/-- A representable transformation of presheaves on the big fppf site whose represented base
changes are locally of finite presentation is relatively limit preserving, for index categories
in the universe of the schemes.

This is the representable case of Stacks 04AK, stated in the vocabulary of Tag 049J. The
presheaf of lifts of a section of the target is represented by the represented pullback, so
`AlgebraicGeometry.limitPreserving_yoneda_of_locallyOfFinitePresentation` applies to it. -/
theorem relativelyLimitPreserving_of_presheaf_locallyOfFinitePresentation
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    RelativelyLimitPreserving.{u, u, u, u} B S hS a := by
  intro X y
  exact limitPreserving_of_natIso (repFiberIso B S hS ha.rep y)
    (limitPreserving_yoneda_of_locallyOfFinitePresentation B S hS X
      (Over.mk (ha.rep.snd (yonedaEquiv.symm y))) (ha.property_snd (yonedaEquiv.symm y)))

/-- An étale morphism of schemes is locally of finite presentation. -/
theorem etale_le_locallyOfFinitePresentation :
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ≤
      @AlgebraicGeometry.LocallyOfFinitePresentation.{u} := fun _ _ g hg =>
  have : Etale g := hg
  inferInstance

/-- For a morphism of algebraic spaces, being locally of finite presentation is equivalent to the
represented base changes being so. -/
private theorem isLocallyOfFinitePresentation_iff_presheaf
    {U : BigFppfOver B S hS} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G) (f : yoneda.obj U ⟶ G) :
    Space.IsLocallyOfFinitePresentation B S hS f ↔
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  have := Stacks.Descent.isLocalAtTarget_fppfPrecoverage
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
  Space.holdsOnEveryEtaleChart_iff_relative B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_yoneda B S hS U) hG f
    (Space.relativelyRepresentable_of_isAlgebraicSpace B S hS hG f)

/-- A representable transformation whose represented base changes are étale has represented base
changes locally of finite presentation. -/
private theorem presheaf_locallyOfFinitePresentation_of_etale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a :=
  MorphismProperty.relative_monotone (MorphismProperty.monotone_inverseImage
    (BigFppfOver.toScheme B S hS) etale_le_locallyOfFinitePresentation) _ ha

/-- The composite of an étale chart of the source with a morphism of algebraic spaces over `S`
which is locally of finite presentation is relatively limit preserving, for index categories in
the universe of the schemes. -/
theorem relativelyLimitPreserving_comp_of_etale_chart
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {a : F ⟶ G} (ha : Space.IsLocallyOfFinitePresentation B S hS a)
    {U : BigFppfOver B S hS} (p : yoneda.obj U ⟶ F)
    (hp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p) :
    RelativelyLimitPreserving.{u, u, u, u} B S hS (p ≫ a) := by
  have hU := isAlgebraicSpace_yoneda B S hS U
  have hpChart := (isLocallyOfFinitePresentation_iff_presheaf B S hS hF p).mpr
    (presheaf_locallyOfFinitePresentation_of_etale B S hS hp)
  exact relativelyLimitPreserving_of_presheaf_locallyOfFinitePresentation B S hS
    ((isLocallyOfFinitePresentation_iff_presheaf B S hS hG (p ≫ a)).mp
      (Space.isLocallyOfFinitePresentation_comp B S hS hU hF hG p a hpChart ha))

/-- **Stacks 01ZC, the implication (2) ⇒ (1), for a morphism of the big fppf site.** If the
Yoneda image of a morphism `h` of the site is relatively limit preserving, then the underlying
morphism of schemes of `h` is locally of finite presentation.

The two presheaves `yoneda.obj U` and `yoneda.obj V` are algebraic spaces, so the surjective
affine-limit criterion of Tag 0CM6,
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_affineLimit_surjective`, applies to
`yoneda.map h`. Its hypothesis is exactly the surjectivity half of the affine-limit comparison
square, and that square is cartesian by the criterion of Tag 06BC in its unlifted form
`AlgebraicGeometry.relativelyLimitPreserving_iff_affineLimit_isPullback_ordinary`: at index
universes equal to the universe of the schemes no universe lift is needed, so the square's
vertices are the plain colimits of the sections and
`CategoryTheory.Limits.Types.exists_of_isPullback` reads off the surjectivity directly. Tag
0CM6 then gives local finite presentation of `yoneda.map h` as a morphism of algebraic spaces,
and for a represented morphism that is local finite presentation of the underlying morphism of
schemes, by the chart characterisation of Tag 03XP together with
`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`.

Crucially, the hypothesis of Tag 0CM6 quantifies only over inverse systems internal to the
size-bounded site, which is exactly what relative limit preservation provides; the unrestricted
scheme-level criterion of Tag 0CM0 is not applicable, since it tests systems of arbitrary
schemes over the base. The set-theoretic step — that the site contains the spectra of the
finitely presented subalgebras which the proof of Tag 0CM6 builds, because the site's cutoff is
a strong prelimit — is discharged inside Tag 0CM6. -/
@[ega "IV 17.3.2" "Remark 17.3.2(i)",
  ega "IV 8.14.2" "partial",
  sga "3 XI 3.2" "Representable case"]
theorem locallyOfFinitePresentation_of_relativelyLimitPreserving_yoneda_map
    {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hh : RelativelyLimitPreserving.{u, u, u, u} B S hS (yoneda.map h)) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h) := by
  have := Stacks.Descent.isLocalAtTarget_fppfPrecoverage
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
  have hU := isAlgebraicSpace_yoneda B S hS U
  have hV := isAlgebraicSpace_yoneda B S hS V
  have hspace : Space.IsLocallyOfFinitePresentation B S hS (yoneda.map h) :=
    Space.isLocallyOfFinitePresentation_of_affineLimit_surjective B S hS hU hV (yoneda.map h)
      fun I _ _ D c hc hAffine hAffineLimit x y hxy =>
        Types.exists_of_isPullback
          ((relativelyLimitPreserving_iff_affineLimit_isPullback_ordinary.{u, u, u, u}
            B S hS (yoneda.map h)).mp hh I D c hc hAffine hAffineLimit) x y hxy
  exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) h).mp
    ((isLocallyOfFinitePresentation_iff_presheaf B S hS hV (yoneda.map h)).mp hspace)

/-- **Stacks 04AK, the implication from relative limit preservation towards local finite
presentation, from an explicit scheme-level input.** A relatively limit-preserving
transformation of presheaves on the big fppf site of `S` is locally of finite presentation as a
morphism of algebraic spaces, given the hypothesis `h01ZC`.

In a commuting square of étale charts `a` of the source and `b` of the target over a morphism
`h` of the site, both charts are representable and étale, hence relatively limit preserving by
`AlgebraicGeometry.relativelyLimitPreserving_of_presheaf_locallyOfFinitePresentation`.
Composing `a` with the given transformation and cancelling `b` off the resulting composite
leaves the Yoneda image of `h` relatively limit preserving, and `h01ZC` turns that into local
finite presentation of the underlying scheme morphism of `h`, which is what the chart
characterisation of Tag 03XP asks for.

The hypothesis `h01ZC` is the implication (2) ⇒ (1) of Stacks 01ZC, read for a morphism of the
site. It is proved, as
`AlgebraicGeometry.locallyOfFinitePresentation_of_relativelyLimitPreserving_yoneda_map`, and
the unconditional statement, which carries `@[stacks 04AK]`, is
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving`. -/
theorem isLocallyOfFinitePresentation_of_relativelyLimitPreserving
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (h01ZC : ∀ {U V : BigFppfOver B S hS} (h : U ⟶ V),
      RelativelyLimitPreserving.{u, u, u, u} B S hS (yoneda.map h) →
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h))
    (hf : RelativelyLimitPreserving.{u, u, u, u} B S hS f) :
    Space.IsLocallyOfFinitePresentation B S hS f := by
  intro U V a b h ha hb hsq
  have haLP := relativelyLimitPreserving_of_presheaf_locallyOfFinitePresentation B S hS
    (presheaf_locallyOfFinitePresentation_of_etale B S hS ha)
  have hbLP := relativelyLimitPreserving_of_presheaf_locallyOfFinitePresentation B S hS
    (presheaf_locallyOfFinitePresentation_of_etale B S hS hb)
  have hcomp := relativelyLimitPreserving_comp.{u, u, u, u} B S hS a f haLP hf
  rw [← hsq] at hcomp
  exact h01ZC h (relativelyLimitPreserving_of_comp_of_right B S hS (yoneda.map h) b hcomp hbLP)

/-- **Stacks 04AK, the implication from relative limit preservation towards local finite
presentation.** A relatively limit-preserving transformation of presheaves on the big fppf site
of `S` is locally of finite presentation as a morphism of algebraic spaces.

This is `AlgebraicGeometry.isLocallyOfFinitePresentation_of_relativelyLimitPreserving` with its
scheme-level input discharged by
`AlgebraicGeometry.locallyOfFinitePresentation_of_relativelyLimitPreserving_yoneda_map` — the
implication (2) ⇒ (1) of Stacks 01ZC for a morphism of the site. -/
@[stacks 04AK "the implication from relatively limit preserving to locally of finite
presentation"]
theorem Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : RelativelyLimitPreserving.{u, u, u, u} B S hS f) :
    Space.IsLocallyOfFinitePresentation B S hS f :=
  _root_.AlgebraicGeometry.isLocallyOfFinitePresentation_of_relativelyLimitPreserving B S hS
    (fun h hh => locallyOfFinitePresentation_of_relativelyLimitPreserving_yoneda_map B S hS h hh)
    hf

end AlgebraicGeometry

end
