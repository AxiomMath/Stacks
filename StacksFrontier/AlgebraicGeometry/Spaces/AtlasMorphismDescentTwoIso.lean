module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAffineCover

/-!
# Descending a morphism along an étale atlas, with the gluing condition checked up to
2-isomorphism

Let `X`, `Y` be algebraic spaces over `S`, let `p : h_U ⟶ X` be a surjective étale atlas and let
`k : h_U ⟶ Y` be a morphism.  `AlgebraicGeometry.Space.existsUnique_hom_of_atlas_invariant`
descends `k` to a unique `X ⟶ Y` provided `k` is invariant under a kernel pair `s, t : R ⟶ U` of
the atlas, i.e. provided `h_s ≫ k = h_t ≫ k`.  This file weakens the condition that has to be
*checked* to: the two morphisms of algebraic spaces `h_R ⟶ Y` given by `h_s ≫ k` and `h_t ≫ k`
induce 2-isomorphic morphisms of small étale ringed topoi.

That weakening is [Stacks Project, Tag 04M6]
(`AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso`), which is proved
unconditionally: a morphism of algebraic spaces is determined by the morphism of small étale
ringed topoi it induces.  So nothing new is assumed, and no generality is lost.

## Main results

* `AlgebraicGeometry.Space.eq_of_twoIso_yoneda` — two morphisms from a *representable*
  algebraic space to an algebraic space whose morphisms of small étale ringed topoi are
  2-isomorphic are equal, stated for morphisms of the underlying presheaves.  This is Stacks
  04M6 at a representable source, read through the full inclusion of the algebraic spaces into
  the presheaves.
* `AlgebraicGeometry.Space.existsUnique_hom_of_atlas_twoIso` — the descent of `k` with the
  kernel-pair condition replaced by a 2-isomorphism of the induced morphisms of small étale
  ringed topoi.
* `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso` — the same replacement in
  `AlgebraicGeometry.Space.exists_hom_of_chartHoms`: a family of morphisms to `Y` given on the
  affine étale charts of a sheaf and compatible *up to 2-isomorphism* glues to a morphism out of
  that sheaf.

## Implementation notes

### What this is for: the step of Stacks 04KL that needs no morphism of kernel pairs

In the proof of [Stacks Project, Tag 04KL] a chart `V ⟶ Y` and a chart `U ⟶ X` are chosen
together with a section `s : h_U ⟶ g⁻¹h_V`, the recovery theorem for schemes
([Stacks Project, Tag 04I7]) turns `s` into a morphism of schemes `f_s : U ⟶ V`, and the
composite `k := h_{f_s} ≫ h_{V ⟶ Y}` has to be descended along `U ⟶ X`.  The source produces
the required invariance by constructing a *second* morphism of schemes
`f_{s × s} : U ×_X U ⟶ V ×_Y V`, applying the same recovery theorem to it, and reading the
invariance off the commutative square relating the two.

`existsUnique_hom_of_atlas_twoIso` makes that second application unnecessary.  Invariance is an
equality of two morphisms `h_{U ×_X U} ⟶ Y`, i.e. of two morphisms of algebraic spaces out of a
representable one, and Stacks 04M6 decides such an equality from a 2-isomorphism of the induced
morphisms of small étale ringed topoi.  What makes that 2-isomorphism the cheaper thing to
supply is that both composites `U ×_X U ⟶ U ⟶ X` agree — they are the two projections of a
kernel pair of `p`, composed with `p` — so the two morphisms of ringed topoi to be compared are
both expected to be 2-isomorphic to the one restriction of `(g, g^♯)` along that single
morphism.  Producing those two 2-isomorphisms is a *localization* of the given `(g, g^♯)`, not a
second application of a recovery theorem; the lemma below assumes them and proves nothing about
them.

This matters for how much of the scheme-level chain Stacks 04KL consumes, and the measurement is
recorded in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/ExistenceChain.lean`: the
target `V ×_Y V` of the eliminated application is in general neither affine nor quasi-compact,
even when `V` is affine, so it is precisely the application that no affine-target recovery
theorem can serve.

### Why the statement quantifies over kernel pairs

`AlgebraicGeometry.Space.existsUnique_hom_of_atlas_invariant` asks for invariance under *every*
represented kernel pair rather than under a supplied one, because an étale atlas is relatively
representable and so has one; the condition here is quantified the same way, so that a caller
which has a particular `U ×_X U` in hand need not produce the chosen pullback of the site.

### Why the conclusion is about `f.hom`

`AlgebraicGeometry.AlgebraicSpaces` is a full subcategory of the presheaves, so a morphism of
algebraic spaces *is* a morphism of the underlying presheaves; the `∃!` is therefore stated with
`p ≫ f.hom = k` and the uniqueness is uniqueness of a morphism of algebraic spaces, which is
what a caller descending a chart wants.

## References

* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04M6 at a representable source, read on the underlying presheaves.** Two morphisms
`k₁, k₂ : h_R ⟶ Y` from the presheaf represented by an object of the big fppf site to an
algebraic space over `S` whose induced morphisms of small étale ringed topoi are 2-isomorphic
are equal.

The representable presheaf is an algebraic space by [Stacks Project, Tag 025Z]
(`AlgebraicGeometry.isAlgebraicSpace_yoneda`), so `k₁` and `k₂` are morphisms of algebraic
spaces, and `AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso` identifies them
there; the full inclusion of the algebraic spaces into the presheaves then gives the equality
asserted. -/
theorem eq_of_twoIso_yoneda {Y : AlgebraicSpaces B S hS} {R : BigFppfOver B S hS}
    (k₁ k₂ : yoneda.obj R ⟶ Y.1)
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (ObjectProperty.homMk k₁ :
        (schemeSpace R : AlgebraicSpaces B S hS) ⟶ Y))
      (smallEtaleRingedToposHom B S hS (ObjectProperty.homMk k₂ :
        (schemeSpace R : AlgebraicSpaces B S hS) ⟶ Y))) :
    k₁ = k₂ := by
  have h := eq_of_smallEtaleRingedToposHom_twoIso B S hS
    (ObjectProperty.homMk k₁ :
      (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (ObjectProperty.homMk k₂) t
  exact congrArg CategoryTheory.InducedCategory.Hom.hom h

set_option synthInstance.maxHeartbeats 400000 in
/-- **A morphism out of a surjective étale atlas descends when its two restrictions to a kernel
pair induce 2-isomorphic morphisms of small étale ringed topoi.**

This is `AlgebraicGeometry.Space.existsUnique_hom_of_atlas_invariant` — the atlas is a
coequalizer of its kernel pair in sheaves, [Stacks Project, Tag 0262] part (3) — with the
invariance of `k` deduced from the 2-isomorphism by [Stacks Project, Tag 04M6], as
`AlgebraicGeometry.Space.eq_of_twoIso_yoneda`.  Nothing is assumed beyond that 2-isomorphism:
Stacks 04M6 is proved unconditionally, so this is strictly easier to apply than the invariance
form and no generality is lost.

In the proof of [Stacks Project, Tag 04KL] this is the step which removes the need to recover a
second morphism of schemes `U ×_X U ⟶ V ×_Y V`; see the module documentation. -/
theorem existsUnique_hom_of_atlas_twoIso {X Y : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X.1)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (k : yoneda.obj U ⟶ Y.1)
    (hcompat : ∀ (R : BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) p p →
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (ObjectProperty.homMk (yoneda.map s ≫ k) :
          (schemeSpace R : AlgebraicSpaces B S hS) ⟶ Y))
        (smallEtaleRingedToposHom B S hS (ObjectProperty.homMk (yoneda.map t ≫ k) :
          (schemeSpace R : AlgebraicSpaces B S hS) ⟶ Y)))) :
    ∃! f : X ⟶ Y, p ≫ f.hom = k := by
  obtain ⟨d, hd, hu⟩ := existsUnique_hom_of_atlas_invariant B S hS X.property.isSheaf
    Y.property.isSheaf p hsurj hetale k
    fun R s t hR => eq_of_twoIso_yoneda B S hS _ _ (hcompat R s t hR).some
  refine ⟨ObjectProperty.homMk d, hd, fun a ha => ?_⟩
  ext : 1
  simpa using hu a.hom ha

set_option synthInstance.maxHeartbeats 400000 in
/-- **A family of morphisms to an algebraic space `Y`, given on the affine étale charts of a
sheaf `F` and compatible up to 2-isomorphism, glues to a morphism `F ⟶ Y`.**

This is `AlgebraicGeometry.Space.exists_hom_of_chartHoms` with its compatibility hypothesis — an
equality `h_r ≫ k U b = k T (h_r ≫ b)` of two morphisms `h_T ⟶ Y` — replaced by a 2-isomorphism
of the morphisms of small étale ringed topoi the two induce.  The replacement is
`AlgebraicGeometry.Space.eq_of_twoIso_yoneda`, i.e. [Stacks Project, Tag 04M6], so nothing is
assumed and no generality is lost.

This is the form in which a recovery theorem supplies the data: what it produces over an affine
chart is a morphism of schemes *together with a 2-isomorphism*, and the compatibility of two such
morphisms is read off the 2-isomorphisms, never off an equality of morphisms of schemes. -/
theorem exists_hom_of_chartHoms_twoIso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y : AlgebraicSpaces B S hS}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (k : ∀ T : BigFppfOver B S hS, IsAffineOver B S hS T →
      ∀ b : yoneda.obj T ⟶ F, IsEtale B S hS b → (yoneda.obj T ⟶ Y.1))
    (hk : ∀ (T U : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
      (hU : IsAffineOver B S hS U) (r : T ⟶ U) (b : yoneda.obj U ⟶ F)
      (hb : IsEtale B S hS b) (hrb : IsEtale B S hS (yoneda.map r ≫ b)),
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS
          (ObjectProperty.homMk (yoneda.map r ≫ k U hU b hb) :
            (schemeSpace T : AlgebraicSpaces B S hS) ⟶ Y))
        (smallEtaleRingedToposHom B S hS
          (ObjectProperty.homMk (k T hT (yoneda.map r ≫ b) hrb) :
            (schemeSpace T : AlgebraicSpaces B S hS) ⟶ Y))))
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ F) (hb : IsEtale B S hS b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ l : F ⟶ Y.1, ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T) (r : T ⟶ U)
      (hrb : IsEtale B S hS (yoneda.map r ≫ b)),
      yoneda.map r ≫ b ≫ l = k T hT (yoneda.map r ≫ b) hrb :=
  exists_hom_of_chartHoms B S hS Y.property.isSheaf k
    (fun T U hT hU r c hc hrc =>
      eq_of_twoIso_yoneda B S hS _ _ (hk T U hT hU r c hc hrc).some)
    hF U b hb hsurj

end AlgebraicGeometry.Space

end
