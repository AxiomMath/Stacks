module

public import Mathlib.CategoryTheory.Abelian.Transfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentationFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationExistence

/-!
# A flat groupoid presentation of an algebraic stack

Let `𝒳` be an algebraic stack over a scheme `S` of a big fppf site. Section 94.16 of the source
presents `𝒳` by the groupoid in algebraic spaces `(U, R, s, t, c)` of Stacks 04T4 (4), built from
a presentation `𝒮_U ⟶ 𝒳` by a scheme and the self-intersection `R = 𝒮_U ×_𝒳 𝒮_U`; by Stacks 04T5
its source and target are smooth, hence flat, and the canonical 1-morphism `[U/R] ⟶ 𝒳` of
Stacks 04T4 (5) is an equivalence. This file packages that presentation in the form in which it
is used to compare quasi-coherent modules on `𝒳` with modules on the groupoid (Stacks 06WT): the
pointwise groupoid fibration of `(U, R, s, t, c)` — whose objects over `T` are the `T`-points of
`U` and whose vertical arrows are the `T`-points of `R` — maps fully faithfully to `𝒳`, over the
site, and every object of `𝒳` is reached from it locally in the fppf topology `𝒳` inherits.

## Main definitions

* `AlgebraicGeometry.Stack.FlatGroupoidPresentation`: a flat groupoid in algebraic spaces together
  with a fully faithful 1-morphism from its pointwise groupoid fibration to `𝒳` which is locally
  essentially surjective for the inherited fppf topology.
* `AlgebraicGeometry.Stack.flatGroupoidPresentation`: the flat groupoid presentation of an
  algebraic stack built from the groupoid of Stacks 04T4 (4) and the canonical 1-morphism of
  Stacks 04T4 (5).

## Main results

* `AlgebraicGeometry.Stack.nonempty_flatGroupoidPresentation`: every algebraic stack has a flat
  groupoid presentation.
* `AlgebraicGeometry.FibredSite.hasFiniteProducts_quasicoherentModules`: quasi-coherent modules on
  a category fibred in groupoids have finite products.
* `AlgebraicGeometry.FibredSite.abelianQuasicoherentModulesOfEquivalence`: quasi-coherent modules
  on a category fibred in groupoids form an abelian category as soon as they are equivalent to
  one.

## Implementation notes

The 1-morphism of the presentation is the canonical functor from the pointwise groupoid fibration
to the quotient stack, followed by the canonical 1-morphism `[U/R] ⟶ 𝒳` of Stacks 04T4 (5). The
first is fully faithful because the quotient prestack is a prestack, and the second is fully
faithful by Stacks 04T4 (6). Local essential surjectivity is Stacks 06XH (1) for the presenting
1-morphism `𝒮_U ⟶ 𝒳`, transported along the comparison of Stacks 04T4 (5) with that 1-morphism;
so none of the essential surjectivity of `[U/R] ⟶ 𝒳` is needed beyond what the local lift gives.

The covering condition is stated with the topology for which the structure sheaf of rings
`AlgebraicGeometry.FibredSite.ringStructureSheafCore` of `𝒳` at `.fppf` is a sheaf, namely
`AlgebraicGeometry.BigFppfOver.associatedTopology` at `.fppf`, and with an index type in the
universe of the morphisms of the site.

## References

* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w v w' m

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A flat groupoid presentation of an algebraic stack `𝒳`.** A groupoid `(U, R, s, t, c)` in
algebraic spaces over `S` whose source and target are flat, together with a 1-morphism `F` from
its pointwise groupoid fibration to `𝒳` over the big fppf site, which is fully faithful and is
locally essentially surjective: every object of `𝒳` receives a family of morphisms from objects in
the image of `F` generating a covering sieve of the fppf topology `𝒳` inherits from the site. -/
structure FlatGroupoidPresentation (𝒳 : AlgebraicStacks.{u, w} B S hS) where
  /-- The base algebraic space the groupoid lives over. -/
  A : AlgebraicSpaces B S hS
  /-- The groupoid in algebraic spaces. -/
  G : GroupoidInAlgebraicSpaces B S hS A
  /-- The source morphism `s : R ⟶ U` is flat. -/
  hs : Space.IsFlat B S hS G.source.hom
  /-- The target morphism `t : R ⟶ U` is flat. -/
  ht : Space.IsFlat B S hS G.target.hom
  /-- The 1-morphism from the pointwise groupoid fibration of the groupoid to `𝒳`. -/
  F : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj ⥤
    𝒳.val.val.obj
  /-- The 1-morphism lies over the big fppf site. -/
  hF : F ⋙ 𝒳.val.val.p =
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
  /-- The 1-morphism is full. -/
  full : F.Full
  /-- The 1-morphism is faithful. -/
  faithful : F.Faithful
  /-- Every object of `𝒳` is reached from the image of the 1-morphism locally in the inherited fppf
  topology. -/
  hloc : ∀ y : 𝒳.val.val.obj, ∃ (I : Type u)
    (x : I → (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj)
    (g : ∀ i, F.obj (x i) ⟶ y),
    Sieve.ofArrows _ g ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf y

namespace FlatGroupoidPresentation

open SelfIntersection

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {W : BigFppfOver B S hS}
  (f : schemeFibredCategory B S hS W ⟶ 𝒳.val)
  (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
  (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
    (Space.smoothMorphismProperty B S hS) f hf)
  (hsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS
    (Space.surjectiveMorphismProperty B S hS) f hf)
  {R : AlgebraicSpaces B S hS}
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS (schemeFibredCategory B S hS W) 𝒳.val f.hom).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- The algebraic space `yoneda.obj W` representing the presenting scheme `W`, as an object of
`AlgebraicSpaces B S hS`. -/
abbrev schemeSpace (W : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  AlgebraicGeometry.schemeSpace W

/-- The equivalence of the category `𝒮_W` represented by a scheme `W` with the fibred category of
the algebraic space `yoneda.obj W` (Stacks 025Z). -/
abbrev schemeEquivalence (W : BigFppfOver B S hS) :
    StacksRepresentableCFG.EquivalenceOver (schemeFibredCategory B S hS W).val.p
      (presheafOfCategories ((schemeSpace W).obj ⋙ typeToCat)).p :=
  PresheafOfCategories.sliceElementsEquivalenceOver W

/-- The presentation datum of Stacks 04T4 (4) and (5) attached to a presentation `f : 𝒮_W ⟶ 𝒳` by
a scheme and a representing space `R` of its self-intersection. -/
noncomputable abbrev selfIntersectionDatum :=
  selfIntersectionPresentation (schemeEquivalence W) eR 𝒳.property

/-- The 1-morphism from the pointwise groupoid fibration of the groupoid of Stacks 04T4 (4) to
`𝒳`: the canonical functor to the quotient stack followed by the canonical 1-morphism of
Stacks 04T4 (5). -/
noncomputable abbrev pointwiseFunctor :=
  pointwiseToQuotientStack (selfIntersectionDatum f eR).groupoid ⋙
    (selfIntersectionDatum f eR).canonicalMap.toFunctor

/-- The 1-morphism from the pointwise groupoid fibration to `𝒳` lies over the big fppf site. -/
theorem pointwiseFunctor_comp_p :
    pointwiseFunctor f eR ⋙ 𝒳.val.val.p =
      (presheafOfGroupoids (evaluationGroupoidFunctor
        (selfIntersectionDatum f eR).groupoid.toGroupoidInFunctors)).p := by
  rw [Functor.assoc, (selfIntersectionDatum f eR).canonicalMap.w]
  exact (isFibredOneMorphism_pointwiseToQuotientStack _).comp_eq

/-- The 1-morphism from the pointwise groupoid fibration to `𝒳` is fully faithful: the canonical
functor to the quotient stack is, and so is the canonical 1-morphism by Stacks 04T4 (6). -/
noncomputable def fullyFaithfulPointwiseFunctor : (pointwiseFunctor f eR).FullyFaithful :=
  Functor.FullyFaithful.comp
    (fullyFaithfulPointwiseToQuotientStack (selfIntersectionDatum f eR).groupoid)
    (nonempty_fullyFaithful_canonicalMap (schemeEquivalence W) eR 𝒳.property).some

include hsmooth hsurj in
/-- **Every object of `𝒳` is reached locally from the pointwise groupoid fibration.** Stacks
06XH (1) lifts it to `𝒮_W` along a single morphism generating a covering sieve of the inherited
fppf topology, and the comparison of Stacks 04T4 (5) identifies the image of the lift with the
image of a point of the pointwise groupoid fibration. -/
theorem exists_pointwiseFunctor_cover (y : 𝒳.val.val.obj) :
    ∃ (I : Type u)
      (x : I → (presheafOfGroupoids (evaluationGroupoidFunctor
        (selfIntersectionDatum f eR).groupoid.toGroupoidInFunctors)).obj)
      (g : ∀ i, (pointwiseFunctor f eR).obj (x i) ⟶ y),
      Sieve.ofArrows _ g ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf y := by
  obtain ⟨x, a, ha⟩ := exists_fppfLocalLift B S hS f hf
    (fun T z hz F hF hE => by
      have hsm := hsmooth T z hz F hF hE
      exact ⟨hsurj T z hz F hF hE, Space.isFlat_of_isSmooth B S hS _ hsm,
        Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩) y
  let P := selfIntersectionDatum f eR
  let e : (pointwiseFunctor f eR).obj
      ⟨(P.sourcePresentation.hom.functor.obj x).base,
        Discrete.as (P.sourcePresentation.hom.functor.obj x).fiber⟩ ≅
      (CatFiberedInGroupoids.homFunctor f).obj x :=
    eqToIso (congrArg P.canonicalMap.toFunctor.obj (P.sourcePresentation_pointwise x)) ≪≫
      P.extends_f.1.app x
  refine ⟨PUnit, fun _ => _, fun _ => e.hom ≫ a, ?_⟩
  refine GrothendieckTopology.superset_covering _ ?_ ha
  rintro Z h ⟨Z', k, -, ⟨⟩, rfl⟩
  refine ⟨_, k ≫ e.inv, e.hom ≫ a, ⟨PUnit.unit⟩, ?_⟩
  simp

/-- **The flat groupoid presentation attached to a presentation by a scheme.** The groupoid is
the groupoid `(U, R, s, t, c)` of Stacks 04T4 (4) with `U = W`, whose source and target are smooth
by Stacks 04T5 (1), hence flat (Stacks 03ZF); the 1-morphism is the canonical functor to the
quotient stack followed by the canonical 1-morphism of Stacks 04T4 (5). -/
noncomputable def ofScheme : FlatGroupoidPresentation 𝒳 where
  A := (selfIntersectionDatum f eR).base
  G := (selfIntersectionDatum f eR).groupoid
  hs := Space.isFlat_of_isSmooth B S hS _
    (isSmooth_selfIntersectionPresentation_source (F := f) (schemeEquivalence W) eR hf hsmooth
      𝒳.property)
  ht := Space.isFlat_of_isSmooth B S hS _
    (isSmooth_selfIntersectionPresentation_target (F := f) (schemeEquivalence W) eR hf hsmooth
      𝒳.property)
  F := pointwiseFunctor f eR
  hF := pointwiseFunctor_comp_p f eR
  full := (fullyFaithfulPointwiseFunctor f eR).full
  faithful := (fullyFaithfulPointwiseFunctor f eR).faithful
  hloc := exists_pointwiseFunctor_cover f hf hsmooth hsurj eR

include hsmooth hsurj in
/-- **The 1-morphism of `ofScheme` factors through the equivalence of Stacks 04T5 (2).** It is the
canonical functor to the quotient stack `[U/R]` followed by the forward 1-morphism of an
equivalence `[U/R] ⟶ 𝒳` over the big fppf site. -/
theorem exists_equivalenceOver_ofScheme_F :
    ∃ e : StacksRepresentableCFG.EquivalenceOver
        (quotientStack (ofScheme f hf hsmooth hsurj eR).G).p 𝒳.val.val.p,
      (ofScheme f hf hsmooth hsurj eR).F =
        pointwiseToQuotientStack (ofScheme f hf hsmooth hsurj eR).G ⋙ e.hom.functor := by
  obtain ⟨e, he⟩ := exists_equivalenceOver_canonicalMap_of_isSmooth (f := f)
    (schemeEquivalence W) eR 𝒳.property hsmooth hsurj
  exact ⟨e, by rw [he]; rfl⟩

end FlatGroupoidPresentation

open SelfIntersection in
/-- **The flat groupoid presentation of an algebraic stack.** It is
`AlgebraicGeometry.Stack.FlatGroupoidPresentation.ofScheme` at the presentation `𝒮_W ⟶ 𝒳` by a
scheme which the defining clause of Stacks 026O provides, with the representing space of its
self-intersection which Stacks 04T4 (1) provides: the groupoid is that of Stacks 04T4 (4) and the
1-morphism factors through the canonical 1-morphism of Stacks 04T4 (5). -/
noncomputable def flatGroupoidPresentation (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    FlatGroupoidPresentation 𝒳 :=
  let hP := 𝒳.property.choose_spec.2.2
  let W := hP.choose
  let f : schemeFibredCategory B S hS W ⟶ 𝒳.val :=
    Bicategory.InducedBicategory.mkHom hP.choose_spec.choose
  have hf : IsRepresentableByAlgebraicSpaces B S hS f.hom := hP.choose_spec.choose_spec.1
  have hR := isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
    (schemeFibredCategory B S hS W) 𝒳.val f.hom 𝒳.property
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  FlatGroupoidPresentation.ofScheme f hf
    (fun V y hy G hG he => (hP.choose_spec.choose_spec.2 V y hy G hG he).2)
    (fun V y hy G hG he => (hP.choose_spec.choose_spec.2 V y hy G hG he).1)
    (R := ⟨hR.choose, hR.choose_spec.1⟩) hR.choose_spec.2.some

/-- **Every algebraic stack has a flat groupoid presentation.** -/
theorem nonempty_flatGroupoidPresentation (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Nonempty (FlatGroupoidPresentation 𝒳) :=
  ⟨flatGroupoidPresentation 𝒳⟩

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w'} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **Quasi-coherent modules on a category fibred in groupoids have finite products.** Sheaves of
modules have finite products, and a finite product of quasi-coherent modules is quasi-coherent:
two quasi-coherent modules are globally presented on the members of a common covering. -/
instance hasFiniteProducts_quasicoherentModules :
    HasFiniteProducts (quasicoherentModules.{u, v, w', m} B S hS p hp) :=
  inferInstance

/-- **Quasi-coherent modules on a category fibred in groupoids form an abelian category as soon as
they are equivalent to one.** The preadditive structure is the canonical one of the full
subcategory of sheaves of modules; kernels, cokernels and the coimage-image comparison are
transported along the equivalence. -/
noncomputable abbrev abelianQuasicoherentModulesOfEquivalence
    {A : Type*} [Category* A] [Abelian A]
    (Φ : quasicoherentModules.{u, v, w', m} B S hS p hp ⥤ A) [Φ.IsEquivalence] :
    Abelian (quasicoherentModules.{u, v, w', m} B S hS p hp) :=
  abelianOfEquivalence Φ

end AlgebraicGeometry.FibredSite

end
