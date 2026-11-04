module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp

/-!
# Étale localization of the restriction to an algebraic space

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` and `q : 𝒴 ⥤ (Sch/S)_{fppf}` be categories fibred in groupoids
representable by algebraic spaces `F` and `G`, and let `f : 𝒳 ⥤ 𝒴` be a 1-morphism. Such an `f`
induces a morphism `F ⟶ G` of the representing presheaves. Reading a scheme chart of `F` as an
object of `𝒳` and applying `f` is compatible with postcomposing the chart with that morphism;
and when the morphism is étale, so is the functor `F_étale ⥤ 𝒳` of Stacks 073M with
postcomposition `F_étale ⥤ G_étale`.

## Main definitions

* `AlgebraicGeometry.Space.inducedSpaceMap`: the morphism `F ⟶ G` of representing presheaves
  induced by a 1-morphism `f : 𝒳 ⥤ 𝒴` over the site.
* `AlgebraicGeometry.Space.inducedSpacesHom`: the same, as a morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.inducedSpaceMap_app`: the element of `G` named by the image under
  `f` of the object of `𝒳` attached to an element of `F`.
* `AlgebraicGeometry.Space.schemeChartPostcompEq` and
  `AlgebraicGeometry.Space.schemeChartPostcompIso`: the functor reading a *scheme* chart of `F`
  as an object of `𝒳`, followed by `f`, agrees — up to a constructed isomorphism — with
  postcomposition of charts along the induced morphism `F ⟶ G` followed by the same functor for
  `G`. No étaleness is asked of the induced morphism, because postcomposition of scheme charts
  needs none; this is the compatibility that the comparison map of equation 075M carries as a
  hypothesis for a free morphism of algebraic spaces, and which the **induced** morphism
  satisfies.
* `AlgebraicGeometry.Space.isHomLift_schemeChartPostcompIso_hom_app`: the components of that
  constructed isomorphism are *vertical* — each lies over an identity of the big fppf site. This
  is the verticality hypothesis `hab` of
  `AlgebraicGeometry.Space.isHomLift_comparisonMorphism`, discharged at the induced morphism, and
  it is what makes the comparison map of equation 075M compatible with the structure sheaves.
* `AlgebraicGeometry.Space.restrictionFunctorPostcompEq` and
  `AlgebraicGeometry.Space.restrictionFunctorPostcompIso`: the same two statements for the small
  étale sites — the functor `F_étale ⥤ 𝒳` of Stacks 073M followed by `f` agrees, up to a
  constructed isomorphism, with postcomposition `F_étale ⥤ G_étale` along the induced étale
  morphism followed by the functor `G_étale ⥤ 𝒴` of Stacks 073M. Here the induced morphism must
  be étale, postcomposition on the small étale sites being defined only then.
* `AlgebraicGeometry.Space.isHomLift_restrictionFunctorPostcompIso_hom_app`: the components of
  that isomorphism are vertical.

## Implementation notes

The morphism `F ⟶ G` of Stacks 0GQA is *constructed* rather than hypothesised: an element of `F`
over `U` is an object of `𝒳` over `U`, its image under `f` is an object of `𝒴` over `U`, hence an
element of `G` over `U`. Only the verticality `f ⋙ q = p` of the 1-morphism enters, so the
construction needs neither the fibred-in-groupoids hypotheses nor the étale charts.

The comparison isomorphism is likewise constructed, from the unit of the chosen equivalence for
`𝒴` and a transport, and not obtained from an existence statement: in particular
`CategoryTheory.PresheafOfCategories.exists_vertical_iso_of_sections_eq` is *not* used, since the
isomorphism it provides comes from `CategoryTheory.Functor.FullyFaithful.preimage`, which is
`Classical.choice`.

The square of sites is the geometric input of Stacks 0GQA. Its promotion to the asserted
commutative diagram of *ringed* topoi, together with the lower half of that diagram (Stacks 073N
at the induced morphism), is `AlgebraicGeometry.Space.etaleLocalizationRingedSquares` in
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionEtaleLocalization.lean`, which carries the
Stacks 0GQA attribute; the declarations here carry none.

## References

* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)

/-- The functor `El F ⥤ El G` between the categories of elements attached to a 1-morphism
`f : 𝒳 ⥤ 𝒴` over the site and to chosen equivalences of `𝒳` and `𝒴` with those categories of
elements. It lies over the site because each of its three factors does. -/
noncomputable def inducedElementsFunctor
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) :
    (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (G ⋙ typeToCat)).obj :=
  eF.inv.functor ⋙ f ⋙ eG.hom.functor

/-- The functor of categories of elements induced by a 1-morphism is strictly over the site. -/
theorem inducedElementsFunctor_comp
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) :
    inducedElementsFunctor B S hS F G p q eF eG f ⋙
        (presheafOfCategories (G ⋙ typeToCat)).p =
      (presheafOfCategories (F ⋙ typeToCat)).p := by
  rw [inducedElementsFunctor, Functor.assoc, Functor.assoc, eG.hom.w, hf, eF.inv.w]

/-- **The morphism of algebraic spaces induced by a 1-morphism of categories fibred in
groupoids.** If `𝒳` and `𝒴` are representable by `F` and `G` through chosen equivalences over
the site, a 1-morphism `f : 𝒳 ⥤ 𝒴` induces a morphism `F ⟶ G` of the representing presheaves:
an element of `F` over `U` is an object of `𝒳` over `U`, whose image under `f` is an object of
`𝒴` over `U`, hence an element of `G` over `U`.

This is the morphism `f : F → G` of the statement of Stacks 0GQA. It is *constructed*, and only
the verticality `f ⋙ q = p` of the 1-morphism enters; neither the fibred-in-groupoids
hypotheses nor the étale charts are used. -/
noncomputable def inducedSpaceMap
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) : F ⟶ G :=
  PresheafOfCategories.natTransOfBasedFunctor
    (inducedElementsFunctor B S hS F G p q eF eG f)
    (inducedElementsFunctor_comp B S hS F G p q eF eG f hf)

/-- **The defining property of the induced morphism of algebraic spaces.** The object of the
category of elements of `G` attached to the image under the induced morphism of an element `x`
of `F` over `V` is the image under `f` of the object of `𝒳` attached to `x`, read in the
category of elements of `G` through the chosen equivalence.

Both sides lie over `V` and name the same element of `G`, and the fibres of the category of
elements are discrete, so they are equal. -/
theorem inducedSpaceMap_app
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (V : BigFppfOver B S hS) (x : F.obj (op V)) :
    (⟨V, Discrete.mk ((inducedSpaceMap B S hS F G p q eF eG f hf).app (op V) x)⟩ :
        (presheafOfCategories (G ⋙ typeToCat)).obj) =
      (inducedElementsFunctor B S hS F G p q eF eG f).obj ⟨V, Discrete.mk x⟩ :=
  PresheafOfCategories.obj_eq_of_elementOf_eq rfl
    (Functor.congr_obj (inducedElementsFunctor_comp B S hS F G p q eF eG f hf)
      (⟨V, Discrete.mk x⟩ : (presheafOfCategories (F ⋙ typeToCat)).obj))
    (PresheafOfCategories.elementOf_mk G V _)

/-! ### Compatibility of the functor of Stacks 073M with étale postcomposition -/

section Etale

variable {X Y : AlgebraicSpaces B S hS}

/-- The morphism of algebraic spaces induced by a 1-morphism of categories fibred in groupoids,
as a morphism of `AlgebraicGeometry.AlgebraicSpaces`: the morphism of presheaves
`AlgebraicGeometry.Space.inducedSpaceMap`, which is a morphism of algebraic spaces because the
subcategory of algebraic spaces is full. -/
noncomputable def inducedSpacesHom
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (X.1 ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) : X ⟶ Y :=
  ObjectProperty.homMk (inducedSpaceMap B S hS X.1 Y.1 p q eF eG f hf)

/-- The underlying morphism of presheaves of the induced morphism of algebraic spaces is the
induced morphism of presheaves. -/
@[simp] theorem inducedSpacesHom_hom
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (X.1 ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) :
    (inducedSpacesHom B S hS p q eF eG f hf).hom =
      inducedSpaceMap B S hS X.1 Y.1 p q eF eG f hf :=
  rfl

/-- **The square of scheme charts underlying Stacks 0GQA commutes in the category of
elements.** Reading a scheme chart of `X` as an element of `X`, hence as an object of `𝒳`, and
then pushing it into the category of elements of `Y` through `f` and the chosen equivalence,
gives the same object of the category of elements of `Y` as postcomposing the chart with the
induced morphism `X ⟶ Y`.

This is `AlgebraicGeometry.Space.restrictionFunctorPostcompEq` at *all* scheme charts, and it
carries no étaleness hypothesis: postcomposition with an arbitrary morphism of algebraic spaces
is a functor of scheme charts, `CategoryTheory.CostructuredArrow.map`, whereas postcomposition
on the *small étale* sites exists only for an étale morphism. The proof is the same one — both
1-morphisms lie over `CategoryTheory.CostructuredArrow.proj` and name the same element of `Y` at
every chart, namely the image of the chart under
`AlgebraicGeometry.Space.inducedSpaceMap`, which is what that morphism is defined to be, and the
fibres of a category of elements are discrete. -/
theorem schemeChartPostcompEq
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (X.1 ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) :
    PresheafOfCategories.costructuredArrowToElements X.1 ⋙
        inducedElementsFunctor B S hS X.1 Y.1 p q eF eG f =
      CostructuredArrow.map (inducedSpacesHom B S hS p q eF eG f hf).hom ⋙
        PresheafOfCategories.costructuredArrowToElements Y.1 :=
  PresheafOfCategories.eq_of_sections_eq (pT := CostructuredArrow.proj yoneda X.1) _ _
    (by
      rw [Functor.assoc, inducedElementsFunctor_comp B S hS X.1 Y.1 p q eF eG f hf,
        PresheafOfCategories.costructuredArrowToElements_comp])
    rfl (fun _ => rfl)

/-- **The scheme-chart square of Stacks 0GQA commutes up to a canonical isomorphism.** The
functor `CostructuredArrow yoneda X ⥤ 𝒳` reading a scheme chart of `X` as an object of `𝒳`,
followed by the 1-morphism `f`, is isomorphic to postcomposition of charts with the induced
morphism `X ⟶ Y` of algebraic spaces, followed by the same functor for `Y`.

This is `AlgebraicGeometry.Space.restrictionFunctorPostcompIso` with the small étale sites
replaced by all scheme charts, and therefore without its `IsEtale` hypothesis on the induced
morphism. It is the compatibility that the comparison map of equation 075M
(`AlgebraicGeometry.Space.restrictedDirectImageComparison`) carries as a hypothesis `ha` for a
*free* morphism of algebraic spaces: for the **induced** morphism that hypothesis is this
theorem, so a square of Stacks 073N stated at the induced morphism asks only for invertibility
of the comparison and for its structure-sheaf compatibility.

As there, the isomorphism is constructed, not chosen: it is the unit of the chosen equivalence
for `𝒴`, whiskered by the left-hand composite, followed by the transport along
`AlgebraicGeometry.Space.schemeChartPostcompEq`. -/
noncomputable def schemeChartPostcompIso
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (X.1 ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) :
    schemeChartFunctor B S hS X.1 p eF ⋙ f ≅
      CostructuredArrow.map (inducedSpacesHom B S hS p q eF eG f hf).hom ⋙
        schemeChartFunctor B S hS Y.1 q eG :=
  (Functor.rightUnitor (schemeChartFunctor B S hS X.1 p eF ⋙ f)).symm ≪≫
    Functor.isoWhiskerLeft (schemeChartFunctor B S hS X.1 p eF ⋙ f) eG.unitIso ≪≫
      eqToIso (congrArg (fun T : CostructuredArrow yoneda X.1 ⥤
          (presheafOfCategories (Y.1 ⋙ typeToCat)).obj => T ⋙ eG.inv.functor)
        (schemeChartPostcompEq B S hS p q eF eG f hf))

/-- A morphism lying over an identity still lies over it after transport along an equality of
its target. Stated with abstract objects: the composition of this development's categories
carries a category instance that `rw` and instance search do not see through, so the
`CategoryTheory.Functor.IsHomLift` instances for `eqToHom` cannot be applied in place. -/
theorem isHomLift_comp_eqToHom_of_isHomLift {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*}
    [Category 𝒟] (r : 𝒟 ⥤ 𝒞) {R : 𝒞} {a b b' : 𝒟} (φ : a ⟶ b) (h : b = b')
    (hφ : r.IsHomLift (𝟙 R) φ) : r.IsHomLift (𝟙 R) (φ ≫ eqToHom h) :=
  have := hφ
  inferInstance

/-- The component of the unit of an equivalence over the site, followed by the transport along an
equality of functors, lies over an identity. -/
private theorem isHomLift_unitIso_trans_eqToIso_hom_app {𝒞 : Type*} [Category 𝒞]
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (G ⋙ typeToCat)).p)
    {A B : 𝒞 ⥤ 𝒴} (h : A ⋙ eG.hom.functor ⋙ eG.inv.functor = B) (Z : 𝒞) :
    q.IsHomLift (𝟙 (q.obj (A.obj Z)))
      (((Functor.rightUnitor A).symm ≪≫ Functor.isoWhiskerLeft A eG.unitIso ≪≫
        eqToIso h).hom.app Z) := by
  subst h
  simpa using eG.isHomLift_unitIso_hom_app (A.obj Z)

/-- **The components of the scheme-chart isomorphism of Stacks 0GQA are vertical.** Each
component of `AlgebraicGeometry.Space.schemeChartPostcompIso` lies over an identity of the big
fppf site: it is an isomorphism of two objects of `𝒴` naming the *same* scheme chart, not merely
two charts with the same base.

This is the verticality hypothesis `hab` of
`AlgebraicGeometry.Space.isHomLift_comparisonMorphism`, discharged at the induced morphism of
algebraic spaces. It is what makes the morphism `AlgebraicGeometry.Space.comparisonChartHom`
of `𝒴` lie over the vertical morphism of schemes of its chart diagram, and hence what makes the
comparison map of equation 075M compatible with the structure sheaves.

Both factors are vertical for a reason of its own: the unit of the chosen equivalence for `𝒴` is
a 2-cell over the site, which is the field
`CategoryTheory.StacksRepresentableCFG.EquivalenceOver.unit_over`, and the transport along
`AlgebraicGeometry.Space.schemeChartPostcompEq` is an `eqToHom`, whose source and target have
equal images. -/
theorem isHomLift_schemeChartPostcompIso_hom_app
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (X.1 ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (Z : CostructuredArrow yoneda X.1) :
    q.IsHomLift (𝟙 (q.obj ((schemeChartFunctor B S hS X.1 p eF ⋙ f).obj Z)))
      ((schemeChartPostcompIso B S hS p q eF eG f hf).hom.app Z) := by
  exact isHomLift_unitIso_trans_eqToIso_hom_app B S hS Y.1 q eG
    (congrArg (fun T : CostructuredArrow yoneda X.1 ⥤
      (presheafOfCategories (Y.1 ⋙ typeToCat)).obj ↦ T ⋙ eG.inv.functor)
      (schemeChartPostcompEq B S hS p q eF eG f hf)) Z

/-- **The square of sites underlying Stacks 0GQA commutes in the category of elements.**
Reading an étale chart of `F` as an element of `F`, hence as an object of `𝒳`, and then pushing
it into the category of elements of `G` through `f` and the chosen equivalence, gives the same
object of the category of elements of `G` as postcomposing the chart with the induced morphism
`F ⟶ G`.

Both 1-morphisms lie over the structure functor of the small étale site of `F` and name the same
element of `G` at every chart — the image of the chart under the induced morphism, which is what
`AlgebraicGeometry.Space.inducedSpaceMap` is defined to be — and the fibres of a category of
elements are discrete, so the two are equal. -/
theorem restrictionFunctorPostcompEq
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (X.1 ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (hg : IsEtale B S hS (inducedSpacesHom B S hS p q eF eG f hf).hom) :
    SmallEtale.inclusion B S hS X.1 ⋙
        PresheafOfCategories.costructuredArrowToElements X.1 ⋙
          inducedElementsFunctor B S hS X.1 Y.1 p q eF eG f =
      smallEtalePostcomp B S hS (inducedSpacesHom B S hS p q eF eG f hf) hg ⋙
        SmallEtale.inclusion B S hS Y.1 ⋙
          PresheafOfCategories.costructuredArrowToElements Y.1 :=
  PresheafOfCategories.eq_of_sections_eq (pT := SmallEtale.toOver B S hS X.1) _ _
    (by
      rw [Functor.assoc, Functor.assoc,
        inducedElementsFunctor_comp B S hS X.1 Y.1 p q eF eG f hf,
        PresheafOfCategories.costructuredArrowToElements_comp])
    rfl (fun _ => rfl)

/-- **The square of sites underlying Stacks 0GQA commutes up to a canonical isomorphism.** The
functor `F_étale ⥤ 𝒳` of Stacks 073M followed by the 1-morphism `f` is isomorphic to
postcomposition `F_étale ⥤ G_étale` with the induced étale morphism followed by the functor
`G_étale ⥤ 𝒴` of Stacks 073M.

The isomorphism is constructed, not chosen: it is the unit of the chosen equivalence for `𝒴`,
whiskered by the left-hand composite, followed by the transport along
`AlgebraicGeometry.Space.restrictionFunctorPostcompEq`. -/
noncomputable def restrictionFunctorPostcompIso
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (X.1 ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (hg : IsEtale B S hS (inducedSpacesHom B S hS p q eF eG f hf).hom) :
    restrictionFunctor B S hS X.1 p eF ⋙ f ≅
      smallEtalePostcomp B S hS (inducedSpacesHom B S hS p q eF eG f hf) hg ⋙
        restrictionFunctor B S hS Y.1 q eG :=
  (Functor.rightUnitor (restrictionFunctor B S hS X.1 p eF ⋙ f)).symm ≪≫
    Functor.isoWhiskerLeft (restrictionFunctor B S hS X.1 p eF ⋙ f) eG.unitIso ≪≫
      eqToIso (congrArg (fun T : SmallEtale B S hS X.1 ⥤
          (presheafOfCategories (Y.1 ⋙ typeToCat)).obj => T ⋙ eG.inv.functor)
        (restrictionFunctorPostcompEq B S hS p q eF eG f hf hg))

/-- **The components of the étale-chart isomorphism of Stacks 0GQA are vertical.** Each
component of `AlgebraicGeometry.Space.restrictionFunctorPostcompIso` lies over an identity of the
big fppf site: it is the unit of the chosen equivalence for `𝒴`, a 2-cell over the site, followed
by a transport along an equality of objects.

This is what makes the comparison of the two inverse images of the upper square of Stacks 0GQA
compatible with the structure sheaves: the structure sheaf of `𝒴` takes a vertical morphism to
the identity of the ring of functions on the common underlying scheme. -/
theorem isHomLift_restrictionFunctorPostcompIso_hom_app
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (X.1 ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (hg : IsEtale B S hS (inducedSpacesHom B S hS p q eF eG f hf).hom)
    (U : SmallEtale B S hS X.1) :
    q.IsHomLift (𝟙 (q.obj ((restrictionFunctor B S hS X.1 p eF ⋙ f).obj U)))
      ((restrictionFunctorPostcompIso B S hS p q eF eG f hf hg).hom.app U) := by
  exact isHomLift_unitIso_trans_eqToIso_hom_app B S hS Y.1 q eG
    (congrArg (fun T : SmallEtale B S hS X.1 ⥤
      (presheafOfCategories (Y.1 ⋙ typeToCat)).obj ↦ T ⋙ eG.inv.functor)
      (restrictionFunctorPostcompEq B S hS p q eF eG f hf hg)) U

end Etale

end AlgebraicGeometry.Space

end
