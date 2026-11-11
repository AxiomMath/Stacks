module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismLimitPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Limits of algebraic spaces (Stacks 07SE)

Let `D` be a cofiltered inverse system of algebraic spaces over a scheme `S` with affine
transition morphisms. Its inverse limit, computed as a presheaf, is an algebraic space over
`S`, every projection from it to a stage is affine, and base change along a morphism to a
stage commutes with the limit. This is how the section thinks of limits of algebraic spaces.
When every stage carries an affine morphism to one fixed algebraic space `T`, compatibly with
the transitions, the transitions are affine of their own accord, the limit is an algebraic
space and its structure morphism to `T` is affine; when `T` is an affine object of the site,
the limit is represented by an affine object of the site. A limiting cone of such a system,
taken in the category of algebraic spaces affine over `T`, is computed in the presheaves over
`T`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_limit_and_isAffineHom_limitπ_of_limitInSite`:
  the limit of a system with affine transitions is an algebraic space with affine projections,
  and base change commutes with it.
* `AlgebraicGeometry.Space.isAffineHom_map_of_isAffineHom_app`: a transition morphism of a
  system affine over `T` is affine.
* `AlgebraicGeometry.Space.limitπ_comp_app_eq`: the structure morphism of the limit does not
  depend on the stage at which it is read off.
* `AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_isAffineHom_app_of_limitInSite`: the
  limit of a system affine over `T` is an algebraic space.
* `AlgebraicGeometry.Space.isAffineHom_limitπ_comp_app_of_limitInSite`: its structure morphism
  to `T` is affine.
* `AlgebraicGeometry.Space.exists_isAffine_representation_limit_of_limitInSite`: over an
  affine base the limit is represented by an affine object of the site.
* `AlgebraicGeometry.Space.isLimit_affineOverToOver_of_size`: a limiting cone of a cofiltered
  system in the category of algebraic spaces affine over `T`, over a small enough index
  category, is computed in the presheaves over `T`.

## Implementation notes

Stacks 07SE is a section. Its prose fixes how limits of algebraic spaces are understood in the
chapter, through its first lemma, Stacks 07SF, and announces that base change of an affine
morphism is affine (Stacks 03WI, `AlgebraicGeometry.Space.IsAffineHom.of_isPullback` in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHomTfae.lean`) is used without mention. The
registrations of the tag here are that description of limits and the forms in which the
section is cited elsewhere in the source, together with Limits, Section 01YV, in the proof of
Stacks 08K6: a limit of spaces affine over a base is an algebraic space affine over the base,
and over an affine base it is affine. The section's numbered results are registered
on their own declarations: 07SF in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineLimitExistence.lean` (existence) and
`StacksFrontier/AlgebraicGeometry/Spaces/ApproximationSteps.lean` (parts (1) and (2)), 07SG in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/QuotientPresentation.lean`, 07SH in
`StacksFrontier/AlgebraicGeometry/Spaces/ApproximationSteps.lean`, 0CUH in
`StacksFrontier/AlgebraicGeometry/Spaces/LimitClosedImmersion.lean`, 0CUI in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/Reduced.lean`, and 0CP4 in
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentation/QcqsCriterion.lean`.

*Size.* The source puts no condition on the index of an inverse system; it relies on the
standing convention of Section 70.2 (Stacks 07SD), that every ring considered has its spectrum
in the big fppf site. The registered results carry exactly that convention, in the form used
for Stacks 07SF by `AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_limitInSite`: the limits
of the base-change diagrams the proof forms lie in the site. For the affine test objects of
07SF, part (1) this is derived by
`AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_limitInSite`. The variants with
cardinality bounds on the index category (`hSize`, `hHomSize`) are kept, since a small index
category implies the convention and they are what
`AlgebraicGeometry.Space.isLimit_affineOverToOver_of_size` uses; they are strictly less
general and do not carry the tag.

Affineness of the transition morphisms, which is the hypothesis of 07SF, is not assumed for a
system affine over `T`. It is derived from affineness of the structure morphisms by Stacks
08GB, part (2): a composite `D i ⟶ D j ⟶ T` which is affine and whose second factor is
separated has an affine first factor, and an affine morphism of algebraic spaces is separated.

Over an affine base, the representing affine object is read off from affineness of the
structure morphism at the test object `Z` and the identity, a base change along an
isomorphism.

`AlgebraicGeometry.Space.isLimit_affineOverToOver_of_size` is a different reading of the same
limit, and the one a limit presentation of an affine morphism needs. The anti-equivalence of
Stacks 081V produces limits of inverse systems of affine morphisms in the *full subcategory*
`AlgebraicGeometry.Space.AffineOver` of the algebraic spaces affine over a base, and a limit in
a full subcategory need not be a limit in the ambient category. It is here: the presheaf limit
of the system is an algebraic space affine over the base by the results above, hence an
object of that subcategory, and there it is a limiting cone, because the inclusion of the
subcategory into the presheaves over the base is faithful and a presheaf lift of a cone of
spaces affine over the base is again a morphism over the base. Any other limiting cone is then
isomorphic to that one, and the isomorphism transports the presheaf limit property. Neither
finiteness of the limit over the base nor the closed-immersion hypothesis on the transition
morphisms of `StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitPresentation` is needed,
and that is what makes the result apply to an integral morphism, whose system has finite
surjections as transitions and a limit which is not finite over the base.

## References

* [Stacks Project, Tag 07SE](https://stacks.math.columbia.edu/tag/07SE)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 01YV](https://stacks.math.columbia.edu/tag/01YV)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section AffineOverBase

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (τ : D ⟶ (Functor.const I).obj T)

omit [IsCofiltered I] in
/-- A transition morphism of an inverse system of algebraic spaces affine over `T` is itself
affine. It composes with the structure morphism of its target to the structure morphism of
its source, so Stacks 08GB, part (2) applies: the composite is affine and the structure
morphism of the target is separated, being affine. -/
theorem isAffineHom_map_of_isAffineHom_app
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (hT : IsAlgebraicSpace B S hS T)
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) {i j : I} (φ : i ⟶ j) :
    IsAffineHom B S hS (D.map φ) := by
  have hnat : D.map φ ≫ τ.app j = τ.app i := by simp
  refine isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS (D.map φ) (τ.app j) ?_ ?_
  · rw [hnat]; exact hτ i
  · exact isSeparated_of_isAffineHom B S hS (τ.app j) (hD j) hT (hτ j)

omit [IsCofiltered I] in
/-- The structure morphism of the inverse limit does not depend on the stage at which it is
read off: the projections of the limit cone are compatible with the transitions, and the
transitions are compatible with the structure morphisms. -/
theorem limitπ_comp_app_eq {i j : I} (φ : i ⟶ j) :
    limit.π D i ≫ τ.app i = limit.π D j ≫ τ.app j := by
  have hnat : D.map φ ≫ τ.app j = τ.app i := by simp
  rw [← hnat, ← Category.assoc, limit.w]

/-- The inverse limit of a cofiltered inverse system of algebraic spaces over `S`, each affine
over one fixed algebraic space `T`, is an algebraic space over `S`, provided the index category
is small enough for the site. The form under the source's standing convention, with no
condition on the index, is
`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_isAffineHom_app_of_limitInSite`.

Affineness of the transition morphisms, which is what Stacks 07SF asks for, is supplied by
`AlgebraicGeometry.Space.isAffineHom_map_of_isAffineHom_app`. -/
theorem isAlgebraicSpace_limit_of_isAffineHom_app (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (hT : IsAlgebraicSpace B S hS T)
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) :
    IsAlgebraicSpace B S hS (limit D) :=
  isAlgebraicSpace_limit B S hS D hSize hHomSize hD fun {_ _} φ =>
    isAffineHom_map_of_isAffineHom_app B S hS D τ hD hT hτ φ

/-- The structure morphism of the inverse limit of a cofiltered inverse system of algebraic
spaces each affine over one fixed algebraic space `T` is affine over `T`, provided the index
category is small enough for the site. The form under the source's standing convention is
`AlgebraicGeometry.Space.isAffineHom_limitπ_comp_app_of_limitInSite`.

It factors as the projection to a stage, which is affine by Stacks 07SF, part (1), followed
by the structure morphism of that stage. -/
theorem isAffineHom_limitπ_comp_app (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (hT : IsAlgebraicSpace B S hS T)
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) (i : I) :
    IsAffineHom B S hS (limit.π D i ≫ τ.app i) :=
  isAffineHom_comp B S hS _ _
    (isAffineHom_limitπ B S hS D hSize hHomSize
      (fun {_ _} φ => isAffineHom_map_of_isAffineHom_app B S hS D τ hD hT hτ φ) i) (hτ i)

end AffineOverBase

section AffineBase

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (Z : BigAffineFppf B S hS)
variable (τ : D ⟶ (Functor.const I).obj
  (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)))

/-- The inverse limit of a cofiltered inverse system of algebraic spaces over `S`, each affine
over one fixed affine object `Z` of the site, is represented by an affine object of the site,
by an isomorphism carrying the structure morphism of the limit to a morphism of the site,
provided the index category is small enough for the site. The form under the source's
standing convention is
`AlgebraicGeometry.Space.exists_isAffine_representation_limit_of_limitInSite`.

The structure morphism of the limit is affine, so its base change along the identity of
`yoneda Z` is represented by an affine object of the site; a base change along an identity is
an isomorphism. -/
theorem exists_isAffine_representation_limit (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) (i₀ : I) :
    ∃ (W : BigAffineFppf B S hS)
      (e : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ≅ limit D)
      (q : (BigAffineFppf.inclusion B S hS).obj W ⟶
        (BigAffineFppf.inclusion B S hS).obj Z),
      e.hom ≫ limit.π D i₀ ≫ τ.app i₀ = yoneda.map q := by
  have hZ : IsAlgebraicSpace B S hS
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)) :=
    isAlgebraicSpace_yoneda B S hS _
  obtain ⟨W, p, q, hpb⟩ :=
    isAffineHom_limitπ_comp_app B S hS D τ hSize hHomSize hD hZ hτ i₀ Z (𝟙 _)
  have hid : IsPullback (𝟙 (limit D)) (limit.π D i₀ ≫ τ.app i₀)
      (limit.π D i₀ ≫ τ.app i₀) (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨W, IsPullback.isoIsPullback _ _ hpb hid, q,
    IsPullback.isoIsPullback_hom_snd _ _ hpb hid⟩

end AffineBase

/-! ### Under the standing convention of the chapter

Section 70.2 of the source (Stacks 07SD) assumes that every ring `A` considered has `Spec(A)`
isomorphic to an object of the big fppf site, and the section states no condition on the index
of an inverse system. The results below carry that convention in the form Stacks 07SF is stated
in this development (`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_limitInSite`): for every
stage `i`, test object `Z` of the site and morphism `g : yoneda Z ⟶ D i`, every lift through the
Yoneda embedding of the diagram of base changes along `g` of the stages over `i` has the limit
of its underlying schemes in the site. Smallness of the index category implies it, and is
strictly stronger. -/

section StandingConvention

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

omit [IsCofiltered I] in
/-- The standing convention for base changes to arbitrary test objects implies it for base
changes to affine test objects, which is the form
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits` used by Stacks 07SF, part (1): a lift
through the affine site composed with the inclusion of the affine site is a lift through the
whole site. -/
theorem siteContainsBaseChangeLimits_of_limitInSite
    (hconv : ∀ (i : I) (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i)
      (W : Over i ⥤ BigFppfOver B S hS),
      (W ⋙ yoneda ≅ (Over.post (X := i) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj Z)) → BigFppfOver.LimitInSite W) :
    SiteContainsBaseChangeLimits B S hS D := by
  intro i _ g W hiso
  exact hconv i _ g (W ⋙ BigAffineFppf.inclusion B S hS) (Functor.associator _ _ _ ≪≫ hiso)

/-- **Stacks 07SE.** Let `D` be a cofiltered inverse system of algebraic spaces over `S` whose
transition morphisms are affine. Then the inverse limit of `D`, computed as a presheaf (hence as
an fppf sheaf), is an algebraic space over `S`; every projection from it to a stage is affine;
and for every stage `i` and every morphism `g : T ⟶ D i` the base change of the limit along `g`
is the limit of the base changes along `g` of the stages over `i`.

This is the description of limits of algebraic spaces which the section sets up and uses in
the rest of the chapter, under the chapter's standing convention (Stacks 07SD). The three
conclusions are Stacks 07SF: its existence assertion is
`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_limitInSite`, part (1) is
`AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits`, and part (2),
which is also Stacks 07SH, is `AlgebraicGeometry.Space.isLimitPullbackLimitOverPost`. -/
@[stacks 07SE "the description of limits of algebraic spaces the section sets up: a \
cofiltered limit of algebraic spaces with affine transitions is an algebraic space with affine \
projections, and base change commutes with it; its numbered results are 07SF (existence, \
parts (1) and (2)), 07SG (the presentation U/R of the limit), 07SH, 0CUH, 0CUI and 0CP4, each \
registered on its own declaration"]
theorem isAlgebraicSpace_limit_and_isAffineHom_limitπ_of_limitInSite
    (hconv : ∀ (i : I) (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i)
      (W : Over i ⥤ BigFppfOver B S hS),
      (W ⋙ yoneda ≅ (Over.post (X := i) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj Z)) → BigFppfOver.LimitInSite W)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    IsAlgebraicSpace B S hS (limit D) ∧ (∀ i, IsAffineHom B S hS (limit.π D i)) ∧
      ∀ (i : I) {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : T ⟶ D.obj i),
        Nonempty (IsLimit ((Over.forget T).mapCone
          ((Over.pullback g).mapCone ((limit.cone D).overPost i)))) :=
  ⟨isAlgebraicSpace_limit_of_limitInSite B S hS D hconv hD hAffine,
    isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D
      (siteContainsBaseChangeLimits_of_limitInSite B S hS D hconv) hAffine,
    fun i {_} g => ⟨isLimitPullbackLimitOverPost B S hS D i g⟩⟩

variable {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (τ : D ⟶ (Functor.const I).obj T)

/-- **Stacks 07SE, systems affine over a base.** The inverse limit of a cofiltered inverse
system of algebraic spaces over `S`, each affine over one fixed algebraic space `T`, is an
algebraic space over `S`, under the chapter's standing convention (Stacks 07SD).

The transition morphisms are affine by
`AlgebraicGeometry.Space.isAffineHom_map_of_isAffineHom_app`, so Stacks 07SF applies. -/
@[stacks 07SE "a cofiltered limit of algebraic spaces affine over a fixed algebraic space is \
an algebraic space, the form in which the section is cited in the proof of 08K6"]
theorem isAlgebraicSpace_limit_of_isAffineHom_app_of_limitInSite
    (hconv : ∀ (i : I) (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i)
      (W : Over i ⥤ BigFppfOver B S hS),
      (W ⋙ yoneda ≅ (Over.post (X := i) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj Z)) → BigFppfOver.LimitInSite W)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (hT : IsAlgebraicSpace B S hS T)
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) :
    IsAlgebraicSpace B S hS (limit D) :=
  isAlgebraicSpace_limit_of_limitInSite B S hS D hconv hD fun {_ _} φ =>
    isAffineHom_map_of_isAffineHom_app B S hS D τ hD hT hτ φ

/-- **Stacks 07SE, systems affine over a base.** The structure morphism to `T` of the inverse
limit of a cofiltered inverse system of algebraic spaces, each affine over one fixed algebraic
space `T`, is affine, under the chapter's standing convention (Stacks 07SD).

It factors as the projection to a stage, which is affine by Stacks 07SF, part (1), followed by
the structure morphism of that stage; a composite of affine morphisms is affine. -/
@[stacks 07SE "the structure morphism of a cofiltered limit of algebraic spaces affine over a \
fixed algebraic space is affine, the form in which the section is cited in the proof of 08K6"]
theorem isAffineHom_limitπ_comp_app_of_limitInSite
    (hconv : ∀ (i : I) (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i)
      (W : Over i ⥤ BigFppfOver B S hS),
      (W ⋙ yoneda ≅ (Over.post (X := i) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj Z)) → BigFppfOver.LimitInSite W)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (hT : IsAlgebraicSpace B S hS T)
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) (i : I) :
    IsAffineHom B S hS (limit.π D i ≫ τ.app i) :=
  isAffineHom_comp B S hS _ _
    (isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D
      (siteContainsBaseChangeLimits_of_limitInSite B S hS D hconv)
      (fun {_ _} φ => isAffineHom_map_of_isAffineHom_app B S hS D τ hD hT hτ φ) i) (hτ i)

end StandingConvention

section StandingConventionAffineBase

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (Z : BigAffineFppf B S hS)
variable (τ : D ⟶ (Functor.const I).obj
  (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)))

/-- **Stacks 07SE, over an affine base.** The inverse limit of a cofiltered inverse system of
algebraic spaces over `S`, each affine over one fixed affine object `Z` of the site, is
represented by an affine object of the site, by an isomorphism carrying the structure morphism
of the limit to a morphism of the site, under the chapter's standing convention (Stacks 07SD).

The structure morphism of the limit is affine by
`AlgebraicGeometry.Space.isAffineHom_limitπ_comp_app_of_limitInSite`, so its base change along
the identity of `yoneda Z` is represented by an affine object of the site; a base change along
an identity is an isomorphism. -/
@[stacks 07SE "a cofiltered limit of algebraic spaces affine over an affine scheme is an \
affine scheme, the form in which the section is cited, together with Limits, Section 01YV, in \
the proof of 08K6"]
theorem exists_isAffine_representation_limit_of_limitInSite
    (hconv : ∀ (i : I) (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ D.obj i)
      (W : Over i ⥤ BigFppfOver B S hS),
      (W ⋙ yoneda ≅ (Over.post (X := i) D ⋙ Over.pullback g) ⋙
        Over.forget (yoneda.obj Z)) → BigFppfOver.LimitInSite W)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hτ : ∀ i, IsAffineHom B S hS (τ.app i)) (i₀ : I) :
    ∃ (W : BigAffineFppf B S hS)
      (e : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ≅ limit D)
      (q : (BigAffineFppf.inclusion B S hS).obj W ⟶
        (BigAffineFppf.inclusion B S hS).obj Z),
      e.hom ≫ limit.π D i₀ ≫ τ.app i₀ = yoneda.map q := by
  obtain ⟨W, p, q, hpb⟩ :=
    isAffineHom_limitπ_comp_app_of_limitInSite B S hS D τ hconv hD
      (isAlgebraicSpace_yoneda B S hS _) hτ i₀ Z (𝟙 _)
  have hid : IsPullback (𝟙 (limit D)) (limit.π D i₀ ≫ τ.app i₀)
      (limit.π D i₀ ≫ τ.app i₀) (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨W, IsPullback.isoIsPullback _ _ hpb hid, q,
    IsPullback.isoIsPullback_hom_snd _ _ hpb hid⟩

end StandingConventionAffineBase

section AffineOverPresheafLimit

variable {Y : AlgebraicSpaces B S hS} {J : Type u} [SmallCategory J] [IsCofiltered J]

/-- The system of presheaves underlying a system of algebraic spaces affine over `Y`. -/
private abbrev affineOverPresheafDiagram (D : J ⥤ AffineOver B S hS Y) :
    J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (D ⋙ affineOverToOver B S hS Y) ⋙ Over.forget Y.obj

/-- The cone of presheaves underlying a cone of algebraic spaces affine over `Y`. -/
private abbrev affineOverPresheafCone (D : J ⥤ AffineOver B S hS Y) (s : Cone D) :
    Cone (affineOverPresheafDiagram B S hS D) :=
  (Over.forget Y.obj).mapCone ((affineOverToOver B S hS Y).mapCone s)

/-- A morphism of spaces affine over `Y` commutes with the structure morphisms to `Y`. -/
private theorem affineOver_hom_left_comp_hom {D E : AffineOver B S hS Y} (f : D ⟶ E) :
    f.hom.left.hom ≫ E.obj.hom.hom = D.obj.hom.hom := by
  have h := congrArg (fun k => k.hom) (Over.w f.hom)
  rwa [ObjectProperty.FullSubcategory.comp_hom] at h

/-- A limiting cone of a cofiltered system of algebraic spaces affine over `Y`, over an index
category small enough for the site, is computed in the presheaves over `Y`.

The presheaf limit of the system is an algebraic space by
`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_isAffineHom_app` and is affine over `Y` by
`AlgebraicGeometry.Space.isAffineHom_limitπ_comp_app`, so it is itself an object of
`AlgebraicGeometry.Space.AffineOver`, and there the projections of the presheaf limit are a
limiting cone: a presheaf lift of a cone of spaces affine over `Y` is again a morphism over `Y`,
and the inclusion into the presheaves over `Y` is faithful.  The given cone is therefore
isomorphic to that one, and the isomorphism transports the presheaf limit property. -/
theorem isLimit_affineOverToOver_of_size (D : J ⥤ AffineOver B S hS Y) (c : Cone D)
    (hc : IsLimit c) (hSize : #J < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : J, #(i ⟶ j) < B.cutoff.ord.cof) :
    Nonempty (IsLimit ((affineOverToOver B S hS Y).mapCone c)) := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := J)
  set Dp := affineOverPresheafDiagram B S hS D
  set τ : Dp ⟶ (Functor.const J).obj Y.obj :=
    { app := fun i => (D.obj i).obj.hom.hom
      naturality := fun i j g => by
        change (D.map g).hom.left.hom ≫ (D.obj j).obj.hom.hom =
          (D.obj i).obj.hom.hom ≫ 𝟙 Y.obj
        rw [Category.comp_id]
        exact affineOver_hom_left_comp_hom B S hS (D.map g) }
  have hDsp : ∀ i, IsAlgebraicSpace B S hS (Dp.obj i) := fun i => (D.obj i).obj.left.property
  have hDaff : ∀ i, IsAffineHom B S hS (τ.app i) := fun i => (D.obj i).property
  have hLsp : IsAlgebraicSpace B S hS (limit Dp) :=
    isAlgebraicSpace_limit_of_isAffineHom_app B S hS Dp τ hSize hHomSize hDsp Y.property hDaff
  have hLaff : IsAffineHom B S hS (limit.π Dp i₀ ≫ τ.app i₀) :=
    isAffineHom_limitπ_comp_app B S hS Dp τ hSize hHomSize hDsp Y.property hDaff i₀
  have hconst : ∀ i : J, limit.π Dp i ≫ τ.app i = limit.π Dp i₀ ≫ τ.app i₀ := fun i =>
    (limitπ_comp_app_eq B S hS Dp τ (IsCofiltered.minToLeft i i₀)).symm.trans
      (limitπ_comp_app_eq B S hS Dp τ (IsCofiltered.minToRight i i₀))
  set W : AffineOver B S hS Y :=
    ⟨Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS)
      (X := (⟨limit Dp, hLsp⟩ : AlgebraicSpaces B S hS)) (Y := Y)
      (limit.π Dp i₀ ≫ τ.app i₀)), hLaff⟩
  set cW : Cone D :=
    { pt := W
      π :=
        { app := fun i => ObjectProperty.homMk (Over.homMk
            (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (limit.π Dp i))
            (ObjectProperty.hom_ext _ (hconst i)))
          naturality := fun i j g =>
            ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
              (limit.w Dp g).symm)) } }
  have hcWlim : IsLimit cW :=
    { lift := fun s => ObjectProperty.homMk (Over.homMk
        (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS)
          (limit.lift Dp (affineOverPresheafCone B S hS D s)))
        (by
          apply ObjectProperty.hom_ext
          rw [ObjectProperty.FullSubcategory.comp_hom]
          change limit.lift Dp (affineOverPresheafCone B S hS D s) ≫
            limit.π Dp i₀ ≫ τ.app i₀ = s.pt.obj.hom.hom
          rw [← Category.assoc, limit.lift_π]
          exact affineOver_hom_left_comp_hom B S hS (s.π.app i₀)))
      fac := fun s i =>
        ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
          (limit.lift_π (affineOverPresheafCone B S hS D s) i)))
      uniq := fun s m hm => by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        change m.hom.left.hom = limit.lift Dp (affineOverPresheafCone B S hS D s)
        exact limit.hom_ext fun i =>
          (congrArg (fun t : s.pt ⟶ D.obj i => t.hom.left.hom) (hm i)).trans
            (limit.lift_π (affineOverPresheafCone B S hS D s) i).symm }
  have hmapW : IsLimit ((affineOverToOver B S hS Y).mapCone cW) :=
    isLimitOfReflects (Over.forget Y.obj) (limit.isLimit Dp)
  refine ⟨IsLimit.ofIsoLimit hmapW (Cone.ext
    ((affineOverToOver B S hS Y).mapIso (hc.conePointUniqueUpToIso hcWlim)).symm fun i => ?_)⟩
  change (affineOverToOver B S hS Y).map (cW.π.app i) =
    (affineOverToOver B S hS Y).map (hc.conePointUniqueUpToIso hcWlim).inv ≫
      (affineOverToOver B S hS Y).map (c.π.app i)
  rw [← Functor.map_comp, IsLimit.conePointUniqueUpToIso_inv_comp]

end AffineOverPresheafLimit

end AlgebraicGeometry.Space

end
