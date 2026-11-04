module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitBasicOpenCover
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTrivialisedHom

/-!
# The faithfulness half of the trivialising-cover argument for Tag 0EXD

Full faithfulness of the comparison functor of [Stacks, Tag 0EXD] is, by
`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff_isPullback`,
cartesianness of a square of Hom-sets at every pair of objects, and by
`CategoryTheory.Limits.Types.isPullback_iff` that is commutativity, joint injectivity and
existence. At a pair of modules trivialised over the whole base all three are available —
`AlgebraicGeometry.isPullback_squareComparison_homSquare_trivialised_twoGenerator`. This file
assembles the **joint injectivity** clause at an *arbitrary* pair from the trivialised case over
the members of a cover, and instantiates it at the almost blowup square of
[Stacks, Example 0EVH]: the comparison functor of [Stacks, Tag 0EXD] **is faithful**, under
exactly that example's hypotheses and with no further assumption.

Joint injectivity is the half that needs no gluing and no cube coherence. Its two inputs are the
localisation of the two global hypotheses to a member of the cover, which is the naturality of
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso` at a side face of the cube, and
separatedness over the cover, which is
`AlgebraicGeometry.frobeniusColimitPullback_map_injective_of_openImmersion`. The *existence*
clause is a different matter: it is the gluing
`Stacks.SheafOfModules.existsUnique_hom_of_over`, and the compatibility of the local solutions
has to be converted across the cube.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectorBundlesPullback_map_eq_of_square`: **a commuting square
  of schemes localises an equation between the transitions of two morphisms**, by the naturality
  of the square comparison. This is how a hypothesis about the whole base becomes a hypothesis
  about a member of a cover.
* `AlgebraicGeometry.jointly_injective_frobeniusColimitVectorBundles_of_cover`: **the two legs of
  a commutative square of schemes in characteristic `p` are jointly injective on the Hom-sets of
  finite locally free modules over the Frobenius colimit, as soon as they are so over the members
  of a cover of the initial corner by open immersions.** This is the faithfulness half of the
  trivialising-cover argument, stated with all of the local data as variables, so that nothing of
  the almost blowup square of [Stacks, Example 0EVH] enters.
* `AlgebraicGeometry.jointly_injective_frobeniusColimitVectorBundles_twoGenerator`: the same at
  the almost blowup square of [Stacks, Example 0EVH], under exactly that example's hypotheses —
  a ring `A`, two elements of it and a prime `p` vanishing in `A`.
* `AlgebraicGeometry.faithful_twoGeneratorFrobeniusColimitComparison`: **the comparison functor
  of [Stacks, Tag 0EXD] is faithful**, at *every* pair of finite locally free
  `colim_F 𝒪_{Spec A}`-modules and not merely at a trivialised pair. This is one of the two
  halves of the full faithfulness that the tag asserts; the tag itself asserts an equivalence, so
  it carries no `@[stacks 0EXD]` attribute here.

## Implementation notes

Everything is stated with the local squares and the four vertical morphisms as variables subject
to the two side-face equations, which is why no transport across opens appears: the cover is
given by open immersions `jV s : V s ⟶ X` and the local corner `V s` is an arbitrary scheme over
`X`, not an open subscheme of it. That is what lets the instantiation take `V s` to be
`Spec (A_g)` itself rather than the basic open `D(g)`, and it is the same choice the cube
coherence `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app` makes.

The descent from the category of finite locally free modules to all sheaves of modules is
`AlgebraicGeometry.frobeniusColimitVectorBundlesPullback_map_hom`, which holds on the nose, and
`CategoryTheory.ObjectProperty.hom_ext`: the category of finite locally free modules is a full
subcategory, so an equation between morphisms there is an equation between the underlying
morphisms of sheaves of modules.

**What this file does not prove, and what Tag 0EXD still owes.** Faithfulness is half of full
faithfulness. The other half, fullness, is the *existence* clause: a pair `(g, k)` of morphisms
over the centre and over the modification, compatible over the exceptional line, has to come from
a morphism over the base. Locally it does, by the same trivialised result; globally the local
solutions have to be glued, which is `Stacks.SheafOfModules.existsUnique_hom_of_over`, and their
compatibility over a member of the cover has to be deduced from the global compatibility, which
is what the cube coherence
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app` is for. Neither step is taken
here. And full faithfulness is itself only half of the tag, which asserts that the comparison is
an **equivalence**: essential surjectivity is a separate matter, resting on the Noetherian
descent of a compatible triple and the `ℐ`-adic induction, and is untouched by this file.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CommRingCat
open Stacks.Frobenius Stacks.AlmostBlowUp

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- **A commuting square of schemes localises an equation between the transitions of two
morphisms.**

If `zV ≫ ιV = ιW ≫ z` and two morphisms of finite locally free `colim_F 𝒪_X`-modules have equal
transitions along `z`, then their transitions along `ιV` have equal transitions along `zV`. This
is the naturality of `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso` at the square,
with the comparison cancelled because it is an isomorphism.

It is how the two hypotheses of joint injectivity over the whole base become the two hypotheses
of joint injectivity over a member of a cover, and it is the only thing the faithfulness half of
the trivialising-cover argument needs the square comparison for — the cube coherence is needed
only for the existence half. -/
theorem frobeniusColimitVectorBundlesPullback_map_eq_of_square
    {X Z V W : Scheme.{u}} (z : Z ⟶ X) (ιV : V ⟶ X) (zV : W ⟶ V) (ιW : W ⟶ Z)
    (hX : IsInCharacteristic X p) (hZ : IsInCharacteristic Z p)
    (hV : IsInCharacteristic V p) (hW : IsInCharacteristic W p)
    (sz : zV ≫ ιV = ιW ≫ z)
    {M N : frobeniusColimitVectorBundles X p hX} (φ₁ φ₂ : M ⟶ N)
    (h : (frobeniusColimitVectorBundlesPullback p z hZ hX).map φ₁ =
      (frobeniusColimitVectorBundlesPullback p z hZ hX).map φ₂) :
    (frobeniusColimitVectorBundlesPullback p zV hW hV).map
        ((frobeniusColimitVectorBundlesPullback p ιV hV hX).map φ₁) =
      (frobeniusColimitVectorBundlesPullback p zV hW hV).map
        ((frobeniusColimitVectorBundlesPullback p ιV hV hX).map φ₂) := by
  have σ := frobeniusColimitVectorBundlesSquareIso p ιV z zV ιW hX hV hZ hW sz
  rw [← cancel_epi (σ.hom.app M)]
  simp only [← Functor.comp_map]
  rw [← σ.hom.naturality φ₁, ← σ.hom.naturality φ₂]
  simp only [Functor.comp_map, h]

/-- **Joint injectivity of the two legs of a commutative square of schemes on the Hom-sets of
finite locally free modules over the Frobenius colimit is local on the initial corner.**

Given a commutative square with initial corner `X`, a family of open immersions `jV s : V s ⟶ X`
whose images cover `X`, and over each `s` a square with initial corner `V s` whose two side faces
commute with the given one, joint injectivity over each `V s` implies joint injectivity over `X`.

By `CategoryTheory.Limits.CategoricalPullback.faithful_squareComparison_of_jointly_injective`
this is the **faithfulness** of the comparison functor of [Stacks, Tag 0EXD]; what it is not is
its fullness, which needs the gluing of morphisms over a cover and the cube coherence.

The hypothesis `hloc` is the local joint injectivity. At the almost blowup square of
[Stacks, Example 0EVH] over a localisation `A_g` it is
`AlgebraicGeometry.isPullback_squareComparison_homSquare_trivialised_twoGenerator` read through
`CategoryTheory.Limits.Types.ext_of_isPullback`, the trivialisations being supplied by
`AlgebraicGeometry.exists_cover_free_localizationAway_frobeniusColimit`. -/
theorem jointly_injective_frobeniusColimitVectorBundles_of_cover
    {X X' Z : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
    (hZ : IsInCharacteristic Z p)
    {σ : Type*} {V V' W : σ → Scheme.{u}} (jV : ∀ s, V s ⟶ X)
    [∀ s, IsOpenImmersion (jV s)]
    (bV : ∀ s, V' s ⟶ V s) (zV : ∀ s, W s ⟶ V s)
    (jV' : ∀ s, V' s ⟶ X') (jW : ∀ s, W s ⟶ Z)
    (hV : ∀ s, IsInCharacteristic (V s) p) (hV' : ∀ s, IsInCharacteristic (V' s) p)
    (hW : ∀ s, IsInCharacteristic (W s) p)
    (sb : ∀ s, bV s ≫ jV s = jV' s ≫ b) (sz : ∀ s, zV s ≫ jV s = jW s ≫ z)
    (hcov : ⨆ s, (jV s).opensRange = ⊤)
    {M N : frobeniusColimitVectorBundles X p hX} (φ₁ φ₂ : M ⟶ N)
    (hloc : ∀ s, ∀ F₁ F₂ : (frobeniusColimitVectorBundlesPullback p (jV s) (hV s) hX).obj M ⟶
        (frobeniusColimitVectorBundlesPullback p (jV s) (hV s) hX).obj N,
      (frobeniusColimitVectorBundlesPullback p (zV s) (hW s) (hV s)).map F₁ =
          (frobeniusColimitVectorBundlesPullback p (zV s) (hW s) (hV s)).map F₂ →
        (frobeniusColimitVectorBundlesPullback p (bV s) (hV' s) (hV s)).map F₁ =
          (frobeniusColimitVectorBundlesPullback p (bV s) (hV' s) (hV s)).map F₂ → F₁ = F₂)
    (hz : (frobeniusColimitVectorBundlesPullback p z hZ hX).map φ₁ =
      (frobeniusColimitVectorBundlesPullback p z hZ hX).map φ₂)
    (hb : (frobeniusColimitVectorBundlesPullback p b hX' hX).map φ₁ =
      (frobeniusColimitVectorBundlesPullback p b hX' hX).map φ₂) :
    φ₁ = φ₂ := by
  refine ObjectProperty.hom_ext _ ?_
  refine frobeniusColimitPullback_map_injective_of_openImmersion p X hX jV hV hcov
    φ₁.hom φ₂.hom fun s => ?_
  rw [← frobeniusColimitVectorBundlesPullback_map_hom p (jV s) (hV s) hX φ₁,
    ← frobeniusColimitVectorBundlesPullback_map_hom p (jV s) (hV s) hX φ₂]
  refine congrArg _ (hloc s _ _ ?_ ?_)
  · exact frobeniusColimitVectorBundlesPullback_map_eq_of_square p z (jV s) (zV s) (jW s)
      hX hZ (hV s) (hW s) (sz s) φ₁ φ₂ hz
  · exact frobeniusColimitVectorBundlesPullback_map_eq_of_square p b (jV s) (bV s) (jV' s)
      hX hX' (hV s) (hV' s) (sb s) φ₁ φ₂ hb

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The two legs of the almost blowup square of [Stacks, Example 0EVH] are jointly injective on
the Hom-sets of finite locally free modules over the Frobenius colimit**, at every pair of such
modules and under exactly that example's hypotheses: a ring `A`, two elements `f₁, f₂` of it and
a prime `p` vanishing in `A`.

This is `AlgebraicGeometry.jointly_injective_frobeniusColimitVectorBundles_of_cover` instantiated
at the cover of `Spec A` by the spectra of the localisations `A_g` supplied by
`AlgebraicGeometry.exists_cover_free_localizationAway_frobeniusColimit`. The local corner is
`Spec (A_g)` itself, so the local square is literally the two-generator square over `A_g` and the
two side faces are the base-change squares
`Stacks.AlmostBlowUp.isPullback_centerToBase_coeff` and `…isPullback_modificationToBase_coeff` at
`R := A`, `A := A_g`, whose generators are therefore the images `algebraMap A (A_g) fᵢ`. No
transport across opens occurs anywhere.

The local joint injectivity is
`AlgebraicGeometry.isPullback_squareComparison_homSquare_trivialised_twoGenerator` read through
`CategoryTheory.Limits.Types.ext_of_isPullback`, which is exactly where the trivialisations over
`A_g` are consumed. -/
theorem jointly_injective_frobeniusColimitVectorBundles_twoGenerator (hp : p.Prime)
    (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∀ (M N : frobeniusColimitVectorBundles (Spec (.of A)) p (isInCharacteristic_spec A p hpA))
      (φ₁ φ₂ : M ⟶ N),
      (frobeniusColimitVectorBundlesPullback p (centerToBase A f₁ f₂)
            (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
            (isInCharacteristic_spec A p hpA)).map φ₁ =
          (frobeniusColimitVectorBundlesPullback p (centerToBase A f₁ f₂)
            (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
            (isInCharacteristic_spec A p hpA)).map φ₂ →
      (frobeniusColimitVectorBundlesPullback p (modificationToBase A f₁ f₂)
            (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
            (isInCharacteristic_spec A p hpA)).map φ₁ =
          (frobeniusColimitVectorBundlesPullback p (modificationToBase A f₁ f₂)
            (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
            (isInCharacteristic_spec A p hpA)).map φ₂ →
      φ₁ = φ₂ := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  intro M N φ₁ φ₂ hz hb
  obtain ⟨σ, g, K, L, hcov, hKfin, hLfin, hMfree, hNfree⟩ :=
    exists_cover_free_localizationAway_frobeniusColimit p A hpA M.obj N.obj M.property N.property
  have hpAg : ∀ s, (p : Localization.Away (g s)) = 0 := fun s => by
    rw [← map_natCast (algebraMap A (Localization.Away (g s))) p, hpA, map_zero]
  refine jointly_injective_frobeniusColimitVectorBundles_of_cover p
    (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
    (isInCharacteristic_spec A p hpA)
    (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (fun s => Spec.map (ofHom (algebraMap A (Localization.Away (g s)))))
    (fun s => let := (twoGeneratorSquare (Localization.Away (g s))
        (algebraMap A _ f₁) (algebraMap A _ f₂)).modificationGraded
      modificationToBase (Localization.Away (g s))
        (algebraMap A (Localization.Away (g s)) f₁) (algebraMap A (Localization.Away (g s)) f₂))
    (fun s => centerToBase (Localization.Away (g s))
      (algebraMap A (Localization.Away (g s)) f₁) (algebraMap A (Localization.Away (g s)) f₂))
    (fun s => modificationCoeffProjMap A (Localization.Away (g s)) f₁ f₂)
    (fun s => Spec.map (ofHom (centerCoeffHom A (Localization.Away (g s)) f₁ f₂)))
    (fun s => isInCharacteristic_spec_localizationAway p A hpA (g s))
    (fun s => isInCharacteristic_twoGeneratorModification _ _ _ p (hpAg s))
    (fun s => isInCharacteristic_twoGeneratorCenter _ _ _ p (hpAg s))
    (fun s => (isPullback_modificationToBase_coeff A (Localization.Away (g s)) f₁ f₂).w)
    (fun s => (isPullback_centerToBase_coeff A (Localization.Away (g s)) f₁ f₂).w)
    hcov φ₁ φ₂ ?_ hz hb
  intro s F₁ F₂ h1 h2
  have := hKfin s
  have := hLfin s
  exact Types.ext_of_isPullback
    (isPullback_squareComparison_homSquare_trivialised_twoGenerator p hp
      (Localization.Away (g s)) (algebraMap A (Localization.Away (g s)) f₁)
      (algebraMap A (Localization.Away (g s)) f₂) (hpAg s) (K s) (L s) _ _
      (ObjectProperty.isoMk _ (hMfree s).some) (ObjectProperty.isoMk _ (hNfree s).some))
    h1 h2

/-- **The comparison functor of [Stacks, Tag 0EXD] is faithful**, under exactly the hypotheses of
[Stacks, Example 0EVH]: a ring `A`, two elements `f₁, f₂` of it and a prime `p` vanishing in `A`.

A morphism of the categorical fibre product is a pair of morphisms over the centre and over the
modification together with a compatibility over the exceptional line, so two morphisms of the
base with the same image have the same restriction to the centre and to the modification; joint
injectivity of those two restrictions is
`AlgebraicGeometry.jointly_injective_frobeniusColimitVectorBundles_twoGenerator`.

This is **one of the two halves of full faithfulness, and full faithfulness is one of the two
halves of the tag**, which asserts that the comparison is an equivalence. Fullness needs the
gluing of morphisms over the cover and the cube coherence; essential surjectivity is a separate
matter altogether. So no `@[stacks 0EXD]` attribute appears. -/
theorem faithful_twoGeneratorFrobeniusColimitComparison (hp : p.Prime)
    (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).Faithful := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  constructor
  intro M N φ₁ φ₂ h
  exact jointly_injective_frobeniusColimitVectorBundles_twoGenerator p hp A f₁ f₂ hpA M N φ₁ φ₂
    (congrArg CategoricalPullback.Hom.fst h) (congrArg CategoricalPullback.Hom.snd h)

end AlgebraicGeometry

end
