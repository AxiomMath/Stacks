module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# Transporting an étale atlas to an enlarged big fppf site

A big fppf site contained in a larger one induces, after localizing at a scheme `S` of the
smaller site, an inverse-image functor on sheaves of sets. This file shows that an étale
presentation of an algebraic space over `S` transports along it: the inverse image of the
algebraic space receives a locally surjective morphism from the sheaf represented by the *same*
atlas, read in the larger site, whose kernel pair is the sheaf represented by the same relation
scheme, with the same two surjective étale projections. None of this uses a descent hypothesis.

The transport rests on left exactness of the inverse image on `Type u`-valued sheaves, which is
proved here as well. Stacks 00X5 gives left exactness for a continuous representably flat
functor, but only when the universe of the sheaves is the universe of the site; the localized
big fppf sites are `Type (u + 1)` categories whose sheaves of sets are valued in `Type u`. Both
sites are essentially small at `u`, so the situation transports to their small models, where the
two universes agree, and comes back by uniqueness of left adjoints.

What the transported presentation then buys is a reduction. Of the three fields of
`AlgebraicGeometry.IsAlgebraicSpace` for the inverse image, the sheaf condition is free and the
atlas is the transported presentation; so Stacks 03FP, part (2) follows from representability of
the diagonal of the inverse image and nothing else. That is strictly less than the effective
descent predicate along the covering sieves which the quotient route carries, and the
implication between the two is recorded here.

## Main results

* `AlgebraicGeometry.inclusionOver_preservesFiniteLimits_sheafPullback`: the inverse image along
  the localized inclusion is left exact on sheaves of sets valued in the universe of the schemes.
* `AlgebraicGeometry.exists_sheafPullback_atlas`: the étale presentation of an algebraic space
  over `S` transports to the inverse image, with no descent hypothesis.
* `AlgebraicGeometry.Space.presheaf_of_isLocallySurjective_of_kernelPair`: a locally surjective
  morphism from a representable presheaf which is relatively representable and has a
  representable kernel pair is relatively representable with every base-change stable,
  Zariski local, fppf descending property of its kernel pair.
* `AlgebraicGeometry.isAlgebraicSpace_sheafPullback_of_relativelyRepresentable_diag`: Stacks
  03FP, part (2) from representability of the diagonal of the inverse image alone, and
  `AlgebraicGeometry.relativelyRepresentable_diag_sheafPullback_of_descent`, which shows that
  hypothesis to be implied by the effective descent predicate of the quotient route.

## Implementation notes

Every term built from `h : IsContained (τ := .fppf) B B'` is type-correct only at default
transparency, because `AlgebraicGeometry.BigSite` is defined by cases on the topology; so no
equation is rewritten inside such a term. The two coherence identities needed to read the
transported kernel pair through the comparison isomorphism of Stacks 03FP, part (1) are proved
in `AlgebraicGeometry.isPullback_of_iso_comp_inv`, stated for an arbitrary category, and applied
with `exact`. The same discipline forces the finite-limit and binary-product instances of the
two localized sites to be supplied as explicit terms rather than synthesized.

Surjectivity of the transported atlas is obtained from Stacks 0262, part (3) rather than from a
direct computation: the atlas is the coequalizer of its kernel pair in sheaves of sets, hence an
epimorphism, and the inverse image is a left adjoint, so it preserves that coequalizer and with
it the epimorphism. Local surjectivity is then read off by
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`.

No declaration here carries a Stacks tag. The atlas transport and the left exactness are
unconditional but are not themselves clauses of a tag; the reduction of Stacks 03FP, part (2)
carries an undischarged hypothesis.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **The inverse image of an enlargement of big fppf sites is left exact on sheaves of sets
valued in the universe of the schemes.**

Left exactness of the inverse image along a continuous representably flat functor is Stacks
00X5, which the library has at `Type u` only for genuinely small sites
(`CategoryTheory.Functor.preservesFiniteLimits_sheafPullback`); the localized big fppf sites are
`Type (u + 1)` categories. Both are essentially small at `u`, so the situation transports to
their small models, where the universe of the sheaves agrees with the universe of the site, and
the conclusion comes back by uniqueness of left adjoints. -/
theorem inclusionOver_preservesFiniteLimits_sheafPullback (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S) :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
      inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
    PreservesFiniteLimits (i.sheafPullback (Type u) J K) := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K := inclusionOver_isContinuous (τ := .fppf) B B' h S hS
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : EssentiallySmall.{u} (Over (base (τ := .fppf) B S hS)) :=
    essentiallySmall_overTopologySite B S hS
  let : EssentiallySmall.{u} (Over (base (τ := .fppf) B' S hS')) :=
    essentiallySmall_overTopologySite B' S hS'
  let : PreservesFiniteLimits i :=
    inclusionOver_preservesFiniteLimits (τ := .fppf) B B' h S hS
  let : HasFiniteLimits (siteCategory (τ := .fppf) B) :=
    hasFiniteLimits_siteCategory (τ := .fppf) B
  let : HasFiniteLimits (Over (base (τ := .fppf) B S hS)) := inferInstance
  let : RepresentablyFlat i := flat_of_preservesFiniteLimits i
  let eC := equivSmallModel.{u} (Over (base (τ := .fppf) B S hS))
  let eC' := equivSmallModel.{u} (Over (base (τ := .fppf) B' S hS'))
  let J₀ := eC.inverse.inducedTopology J
  let K₀ := eC'.inverse.inducedTopology K
  let i₀ := eC.inverse ⋙ i ⋙ eC'.functor
  let : (i ⋙ eC'.functor).IsContinuous J K₀ := Functor.isContinuous_comp _ _ _ K _
  let : i₀.IsContinuous J₀ K₀ := Functor.isContinuous_comp _ _ _ J _
  let : ∀ W : (Over (base (τ := .fppf) B S hS))ᵒᵖ,
      HasLimitsOfShape (StructuredArrow W eC.inverse.op) (Type u) := by
    intro W
    let : EssentiallySmall.{u} (StructuredArrow W eC.inverse.op) := inferInstance
    exact hasLimitsOfShape_of_essentiallySmall _ _
  let : ∀ W : (SmallModel.{u} (Over (base (τ := .fppf) B' S hS')))ᵒᵖ,
      HasLimitsOfShape (StructuredArrow W eC'.functor.op) (Type u) := by
    intro W
    let : EssentiallySmall.{u} (StructuredArrow W eC'.functor.op) := inferInstance
    exact hasLimitsOfShape_of_essentiallySmall _ _
  exact Adjunction.preservesFiniteLimits_of_conjugate
    (V := eC.inverse.sheafPushforwardContinuous (Type u) J₀ J)
    (W := eC'.functor.sheafPushforwardContinuous (Type u) K K₀)
    (R := i.sheafPushforwardContinuous (Type u) J K)
    (P₀ := i₀.sheafPullback (Type u) J₀ K₀)
    (Functor.preservesFiniteLimits_sheafPullback i₀ J₀ K₀)
    (i₀.sheafAdjunctionContinuous (Type u) J₀ K₀)
    (i.sheafAdjunctionContinuous (Type u) J K)

/-- A Cartesian square whose two parallel legs are rewritten by the inverse of an isomorphism
stays Cartesian after the matching change of apex. This is `CategoryTheory.IsPullback.of_iso`
in the shape needed to pass from a square over `L(F)` to the same square read through a
comparison isomorphism of the two sources; it is stated separately so that the two coherence
proofs are discharged in a context where the terms carry no change-of-site data. -/
theorem isPullback_of_iso_comp_inv {C : Type*} [Category C] {P X Y Z P' X' Y' : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback fst snd f g)
    (eP : P ≅ P') (eX : X ≅ X') (eY : Y ≅ Y') {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'}
    (hfst : fst ≫ eX.hom = eP.hom ≫ fst') (hsnd : snd ≫ eY.hom = eP.hom ≫ snd') :
    IsPullback fst' snd' (eX.inv ≫ f) (eY.inv ≫ g) :=
  H.of_iso eP eX eY (Iso.refl Z) hfst hsnd (by simp) (by simp)

/-- **A given atlas of an algebraic space transports to an enlarged big fppf site.**

Let `q : h_U ⟶ F` be a surjective étale atlas of an algebraic space `F` over `S` on the smaller
big fppf site, with kernel pair `s, t : R ⇉ U`. Then the inverse image `f⁻¹F` of `F` on the larger
localized site receives a morphism from the sheaf represented by the same object `U`, read in the
larger site, which is surjective as a map of sheaves and whose kernel pair is the sheaf represented
by the same object `R`, with the same two projections; these are still surjective and étale,
being the same morphisms of schemes. `AlgebraicGeometry.exists_sheafPullback_atlas` is the case of
an atlas chosen by `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`; the present form lets a
client keep a property of its own atlas, such as quasi-compactness or affineness of `U`. -/
theorem sheafPullback_atlas (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
      inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
    ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U)
      (f : yoneda.obj (i.obj U) ⟶
        ((i.sheafPullback (Type u) J K).obj ⟨F, hF.isSheaf⟩).obj),
      Presheaf.IsLocallySurjective
          (BigFppfOver.topology B' S (largerContains h hS)) f ∧
        IsPullback (yoneda.map (i.map s)) (yoneda.map (i.map t)) f f ∧
        Surjective ((BigFppfOver.toScheme B' S (largerContains h hS)).map (i.map t)) ∧
        Etale ((BigFppfOver.toScheme B' S (largerContains h hS)).map (i.map t)) ∧
        IsPullback (yoneda.map s) (yoneda.map t) q q := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K := inclusionOver_isContinuous (τ := .fppf) B B' h S hS
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : HasSheafify J (Type u) := hasSheafify_overTopology B S hS
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S hS'
  let : J.Subcanonical := subcanonical_overTopology B S hS
  let : K.Subcanonical := subcanonical_overTopology B' S hS'
  let L := i.sheafPullback (Type u) J K
  let : PreservesFiniteLimits L :=
    inclusionOver_preservesFiniteLimits_sheafPullback B B' h S hS
  let : PreservesColimits L :=
    (i.sheafAdjunctionContinuous (Type u) J K).leftAdjoint_preservesColimits
  let R := hqe.rep.pullback q
  let s : R ⟶ U := hqe.rep.fst' q
  let t : R ⟶ U := hqe.rep.snd q
  have hR : IsPullback (yoneda.map s) (yoneda.map t) q q := hqe.rep.isPullback' q
  let A : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  let qS : J.yoneda.obj U ⟶ A := ⟨q⟩
  have hw : J.yoneda.map s ≫ qS = J.yoneda.map t ≫ qS := Sheaf.hom_ext hR.w
  obtain ⟨_, _, ⟨hcoeq⟩⟩ := Space.isCoequalizer_of_surjectiveEtale B S hS q s t hR hF hqs hqe
  have hRS : IsPullback (J.yoneda.map s) (J.yoneda.map t) qS qS :=
    IsPullback.of_map_of_faithful (F := sheafToPresheaf J (Type u)) hR
  let e := pullbackYonedaIso i J K
  let qS' : K.yoneda.obj (i.obj U) ⟶ L.obj A := (e.app U).inv ≫ L.map qS
  have hsq : IsPullback (K.yoneda.map (i.map s)) (K.yoneda.map (i.map t)) qS' qS' :=
    isPullback_of_iso_comp_inv (hRS.map L) (e.app R) (e.app U) (e.app U)
      (e.hom.naturality s) (e.hom.naturality t)
  have hepi : Epi (L.map qS) :=
    Cofork.IsColimit.epi (isColimitCoforkMapOfIsColimit L hw hcoeq)
  exact ⟨R, s, t, qS'.hom,
    (Sheaf.isLocallySurjective_iff_epi qS').mpr
      (inferInstanceAs (Epi ((e.app U).inv ≫ L.map qS))),
    hsq.map (sheafToPresheaf K (Type u)),
    hqs.property q (yoneda.map s) t hR, hqe.property q (yoneda.map s) t hR, hR⟩

/-- **The atlas of an algebraic space transports to an enlarged big fppf site.**

Let `F` be an algebraic space over `S` on the smaller big fppf site, with surjective étale
atlas `q : h_U ⟶ F` and kernel pair `s, t : R ⇉ U`. Then the inverse image `f⁻¹F` of `F` on the
larger localized site receives a morphism from the sheaf represented by the *same* object `U`,
now read in the larger site, which is surjective as a map of sheaves and whose kernel pair is
the sheaf represented by the same object `R`, with the same two projections. The two
projections are still surjective and étale, being the same morphisms of schemes.

This is the transport of the second and third pieces of an étale presentation along the
enlargement; it uses no descent hypothesis. The kernel pair transports because the inverse
image is left exact
(`AlgebraicGeometry.inclusionOver_preservesFiniteLimits_sheafPullback`) and carries the sheaf
represented by `U` to the sheaf represented by `U`
(`CategoryTheory.pullbackYonedaIso`); surjectivity transports because the atlas is an
effective epimorphism of sheaves (Stacks 0262, part (3)) and the inverse image, being a left
adjoint, preserves that colimit. -/
theorem exists_sheafPullback_atlas (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
      inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
    ∃ (U R : BigFppfOver B S hS) (s t : R ⟶ U)
      (f : yoneda.obj (i.obj U) ⟶
        ((i.sheafPullback (Type u) J K).obj ⟨F, hF.isSheaf⟩).obj),
      Presheaf.IsLocallySurjective
          (BigFppfOver.topology B' S (largerContains h hS)) f ∧
        IsPullback (yoneda.map (i.map s)) (yoneda.map (i.map t)) f f ∧
        Surjective ((BigFppfOver.toScheme B' S (largerContains h hS)).map (i.map t)) ∧
        Etale ((BigFppfOver.toScheme B' S (largerContains h hS)).map (i.map t)) := by
  obtain ⟨U, q, hqs, hqe⟩ := hF.exists_atlas
  obtain ⟨R, s, t, f, hls, hsq, hsurj, het, -⟩ := sheafPullback_atlas B B' h S hS F hF q hqs hqe
  exact ⟨U, R, s, t, f, hls, hsq, hsurj, het⟩

namespace Space

/-- **A locally surjective morphism from a representable presheaf with a representable kernel
pair is representable with every property its kernel pair has.**

Let `c : h_U ⟶ X` be a morphism of presheaves on the big fppf site of `S` out of a
representable presheaf which is locally surjective, relatively representable, and has a
kernel pair `s, t : R ⇉ U` by an object of the site. Let `P` be a property of morphisms of
schemes which is stable under base change, Zariski local on the target and satisfies fppf
descent. If the underlying morphism of schemes of `t` has `P`, then `c` is relatively
representable with `P`: *every* represented base change of `c` is a morphism of the site whose
underlying morphism of schemes has `P`.

This is the descent-free half of the atlas criterion. The covering sieve used at an object `a`
of the site is the sieve of arrows along which the given section of `X` lifts to `U`, which is
covering because `c` is locally surjective; over each of its arrows the base change of `c` is
the fibre product of `t` with the lift, by the kernel-pair square. Representability of the
descended morphism is the hypothesis `hrep` rather than an effective descent predicate, and the
property is then recovered on it by the unconditional
`AlgebraicGeometry.Space.presheaf_of_coveringSieve_of_descendsAlong`. -/
theorem presheaf_of_isLocallySurjective_of_kernelPair {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U R : BigFppfOver B S hS}
    {c : yoneda.obj U ⟶ X} {s t : R ⟶ U}
    (hc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c)
    (hrep : yoneda.relativelyRepresentable c)
    (hker : IsPullback (yoneda.map s) (yoneda.map t) c c)
    (hP : P ((BigFppfOver.toScheme B S hS).map t)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf c := by
  have _hri : MorphismProperty.RespectsIso (P.inverseImage (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ _).2 fun a g => ?_
  refine presheaf_of_coveringSieve_of_descendsAlong g
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ g) hrep)
    (T := Presheaf.imageSieve c (yonedaEquiv g)) (Presheaf.imageSieve_mem _ _ _) ?_
  rintro b p ⟨x, hx⟩
  have hfac : yoneda.map p ≫ g = yoneda.map x ≫ c := by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact hx.symm
  have hsq : IsPullback (Limits.pullback.fst t x) (Limits.pullback.snd t x) t x :=
    IsPullback.of_hasPullback t x
  have sq : IsPullback (yoneda.map (Limits.pullback.fst t x) ≫ yoneda.map s)
      (yoneda.map (Limits.pullback.snd t x)) c (yoneda.map p ≫ g) := by
    rw [hfac]
    exact (hsq.map yoneda).paste_horiz hker
  exact presheaf_pullback_snd_of_isPullback sq
    (MorphismProperty.of_isPullback (hsq.map (BigFppfOver.toScheme B S hS)) hP)

end Space

/-- **Stacks 03FP, part (2), reduced to one representability statement.**

Enlarging the big fppf site carries an algebraic space over `S` to an algebraic space over `S`
as soon as the diagonal of the inverse image is relatively representable, and with no other
hypothesis.

Of the three fields of `AlgebraicGeometry.IsAlgebraicSpace` the sheaf condition is free, the
diagonal is the hypothesis, and the atlas is supplied by transporting the atlas of `F`
(`AlgebraicGeometry.exists_sheafPullback_atlas`) and feeding it to
`AlgebraicGeometry.Space.presheaf_of_isLocallySurjective_of_kernelPair`, whose representability
input is the hypothesis read through
`CategoryTheory.Functor.relativelyRepresentable.of_diag`.

This replaces the effective descent predicate carried by
`AlgebraicGeometry.isAlgebraicSpace_sheafPullback_of_descent` — a statement quantified over
all morphisms of sheaves, all represented points and all covering sieves of the larger site —
by a single assertion about a single presheaf, which the descent predicate implies. It does
**not** carry `@[stacks 03FP]`: that assertion is undischarged, and gluing it needs effective
descent for the monomorphisms locally of finite type. -/
theorem isAlgebraicSpace_sheafPullback_of_relativelyRepresentable_diag (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
      inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
    yoneda.relativelyRepresentable
        (diag ((i.sheafPullback (Type u) J K).obj ⟨F, hF.isSheaf⟩).obj) →
      IsAlgebraicSpace B' S (largerContains h hS)
        ((i.sheafPullback (Type u) J K).obj ⟨F, hF.isSheaf⟩).obj := by
  intro hdiag
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K := inclusionOver_isContinuous (τ := .fppf) B B' h S hS
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : HasFiniteLimits (siteCategory (τ := .fppf) B') :=
    hasFiniteLimits_siteCategory (τ := .fppf) B'
  let : HasFiniteLimits (Over (base (τ := .fppf) B' S hS')) := inferInstance
  let : HasBinaryProducts (Over (base (τ := .fppf) B' S hS')) := inferInstance
  have _h₁ :=
    Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  have _h₂ :=
    Space.surjective_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  have _h₃ : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  obtain ⟨U, R, s, t, f, hls, hker, hsurj, hetale⟩ :=
    exists_sheafPullback_atlas B B' h S hS F hF
  exact
    { isSheaf := ((i.sheafPullback (Type u) J K).obj ⟨F, hF.isSheaf⟩).property
      diagonal_representable := hdiag
      exists_atlas := ⟨i.obj U, f,
        Space.presheaf_of_isLocallySurjective_of_kernelPair _ hls (hdiag.of_diag f) hker hsurj,
        Space.presheaf_of_isLocallySurjective_of_kernelPair _ hls (hdiag.of_diag f) hker
          hetale⟩ }

/-- Effective descent along the covering sieves of the larger site at the monomorphisms locally
of finite type implies the hypothesis of
`AlgebraicGeometry.isAlgebraicSpace_sheafPullback_of_relativelyRepresentable_diag`, so that
hypothesis is the weaker of the two: it is the representable diagonal of the inverse image read
off `AlgebraicGeometry.isAlgebraicSpace_sheafPullback_of_descent`. Nothing is known in the other
direction. -/
theorem relativelyRepresentable_diag_sheafPullback_of_descent (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hdesc : Space.IsEffectiveDescentAlongCoveringSieve B' S (largerContains h hS)
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
      inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
    yoneda.relativelyRepresentable
      (diag ((i.sheafPullback (Type u) J K).obj ⟨F, hF.isSheaf⟩).obj) :=
  (isAlgebraicSpace_sheafPullback_of_descent B B' h S hS F hF hdesc).diagonal_representable

end AlgebraicGeometry

end
