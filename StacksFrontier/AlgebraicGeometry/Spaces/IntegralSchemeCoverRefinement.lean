module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRefiningFiniteCover
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget

/-!
# Quasi-compactness of an integral cover, and its Zariski-local factorizations

Let `X` be a quasi-compact algebraic space over a scheme `S` and let `f : h_Y ⟶ X` be an
*integral* morphism from the presheaf represented by an object `Y` of the site. This file proves
that `Y` is then quasi-compact, and draws the consequence for the Zariski-local factorization
statement of `StacksFrontier/AlgebraicGeometry/Spaces/EtaleRefiningFiniteCover.lean`.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isIntegralHom`: the source of an integral
  morphism of algebraic spaces whose target is quasi-compact is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinite`: the same for a finite morphism.
* `AlgebraicGeometry.Space.exists_finite_affine_cover_factoring_of_isIntegralHom`: for an
  integral `f : h_Y ⟶ X` over a quasi-compact `X`, a Zariski-local factorization of `f` through
  a morphism `p : U ⟶ X` refines to a *finite* covering of `Y` by affine open subschemes along
  each of which `f` factors through `p`.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_factoring_of_isIntegralHom`:
  the same hypotheses yield the factorization clause in its *representable open subspace* form,
  which is the form the local clause of Stacks 09YC (2) is stated in.

## Implementation notes

The quasi-compactness statement is the composition of three results already in this
development, and that composition is what was missing. Integrality is affineness together with
universal closedness (Stacks 0415), and only the affine half is used:

* an integral morphism is affine, `AlgebraicGeometry.Space.isAffineHom_of_isIntegralHom`;
* an affine morphism is quasi-compact,
  `AlgebraicGeometry.Space.isQuasiCompact_of_isAffineHom'`;
* the source of a quasi-compact morphism over a quasi-compact target is quasi-compact,
  `AlgebraicGeometry.Space.isQuasiCompactSpace_source_of_isQuasiCompact`.

The last of these is already recorded as filling the prose gap of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleRefiningFiniteCover.lean`; what that file asks for,
however, is the hypothesis in the shape in which an integral cover delivers it, and supplying
it needs the two preceding steps as well. With them,
`AlgebraicGeometry.Space.exists_finite_affine_cover_factoring_of_isQuasiCompactSpace` applies
to the source of an integral morphism with no quasi-compactness hypothesis on `Y` at all.

**Nothing here is tagged.** Quasi-compactness of the source of an integral morphism is an
unlabelled step, and the two factorization results are steps inside the proof of Stacks
09YC (2), not any part of its statement: both take the Zariski-local factorization as a
hypothesis rather than producing it, and neither asserts the existence of the cover `Y ⟶ X`.
The covering morphism whose existence Stacks 09YC (2) asserts is not constructed in this
development; see `StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactPresentation.lean` for the
reduction of part (1) of that tag to part (2), and the references below.

No hypothesis is placed on `X` beyond being a quasi-compact algebraic space, and none at all on
`U` or on `p : U ⟶ X`, which is an arbitrary morphism of presheaves.

## References

* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-compactness of the source -/

/-- **The source of an integral morphism over a quasi-compact target is quasi-compact.**
An integral morphism of algebraic spaces over `S` is affine, an affine morphism is
quasi-compact, and the source of a quasi-compact morphism whose target is a quasi-compact
algebraic space is quasi-compact. -/
theorem isQuasiCompactSpace_of_isIntegralHom
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hGqc : IsQuasiCompactSpace B S hS G) (hf : IsIntegralHom B S hS f) :
    IsQuasiCompactSpace B S hS F :=
  isQuasiCompactSpace_source_of_isQuasiCompact B S hS hG hGqc
    (isQuasiCompact_of_isAffineHom' B S hS f hF hG (isAffineHom_of_isIntegralHom f hf))

/-- **The source of a finite morphism over a quasi-compact target is quasi-compact.**
A finite morphism is integral, by Stacks 0414. -/
theorem isQuasiCompactSpace_of_isFinite
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hGqc : IsQuasiCompactSpace B S hS G) (hf : IsFinite B S hS f) :
    IsQuasiCompactSpace B S hS F :=
  isQuasiCompactSpace_of_isIntegralHom B S hS f hF hG hGqc hf.isIntegralHom

/-- **The scheme underlying an integral cover of a quasi-compact algebraic space is
quasi-compact.** If `f : h_Y ⟶ X` is integral and `X` is a quasi-compact algebraic space, then
the scheme underlying the object `Y` of the site is a compact topological space.

This is `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isIntegralHom` transported along the
identification of the point topology of a represented presheaf with the topology of the
representing scheme: the map `AlgebraicGeometry.Space.pointsToScheme` is surjective, and it is
continuous because the preimage of an open set has open image, so the scheme is the continuous
image of a compact space. -/
theorem compactSpace_of_isIntegralHom
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Y : BigFppfOver B S hS)
    (f : yoneda.obj Y ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hf : IsIntegralHom B S hS f) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj Y) := by
  have hpts : CompactSpace (points B S hS (yoneda.obj Y)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _
      (isAlgebraicSpace_yoneda B S hS Y)).1
      (isQuasiCompactSpace_of_isIntegralHom B S hS f
        (isAlgebraicSpace_yoneda B S hS Y) hX hXqc hf)
  have hcont : Continuous (pointsToScheme B S hS Y) := by
    rw [continuous_def]
    intro V hV
    refine (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS Y _).2 ?_
    rwa [Set.image_preimage_eq _ (surjective_pointsToScheme B S hS Y)]
  refine ⟨?_⟩
  rw [← Set.image_univ_of_surjective (surjective_pointsToScheme B S hS Y)]
  exact isCompact_univ.image hcont

/-! ### The Zariski-local factorizations of an integral cover -/

/-- **The finite affine refinement step of Stacks 09YC (2), for an integral cover.**
Let `p : U ⟶ X` be a morphism of presheaves on the big fppf site of `S` with `X` a
quasi-compact algebraic space, and let `f : h_Y ⟶ X` be an *integral* morphism from the
presheaf represented by an object `Y` of the site. Assume that every point of `h_Y` lies in the
point set of an open subspace of `h_Y` over which `f` factors through `p`. Then there are
finitely many objects `Z i` of the site with affine underlying schemes and open immersions
`Z i ⟶ Y` whose images cover `Y`, such that `f` restricted along each of them factors through
`p`.

This is `AlgebraicGeometry.Space.exists_finite_affine_cover_factoring_of_isQuasiCompactSpace`
with its quasi-compactness hypothesis on `Y` discharged: the cover produced by Stacks 09YB (2)
is only integral over `X`, not finite and not of finite presentation, and
`AlgebraicGeometry.Space.isQuasiCompactSpace_of_isIntegralHom` is what covers that case. -/
theorem exists_finite_affine_cover_factoring_of_isIntegralHom
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : U ⟶ X) (Y : BigFppfOver B S hS)
    (f : yoneda.obj Y ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hf : IsIntegralHom B S hS f)
    (hloc : ∀ y : points B S hS (yoneda.obj Y),
      ∃ W : Subfunctor (yoneda.obj Y), IsOpenSubspace B S hS W ∧
        y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        ∃ g : W.toFunctor ⟶ U, W.ι ≫ f = g ≫ p) :
    ∃ (ι : Type u) (_ : Finite ι) (Z : ι → BigFppfOver B S hS) (q : ∀ i, Z i ⟶ Y),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (q i))) ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (Z i))) ∧
      (∀ y : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q i))) ∧
      ∀ i, ∃ g : yoneda.obj (Z i) ⟶ U, yoneda.map (q i) ≫ f = g ≫ p :=
  exists_finite_affine_cover_factoring_of_isQuasiCompactSpace B S hS p Y f
    (isQuasiCompactSpace_of_isIntegralHom B S hS f
      (isAlgebraicSpace_yoneda B S hS Y) hX hXqc hf) hloc

/-- **The local clause of Stacks 09YC (2) for an integral cover.** Under the hypotheses of
`AlgebraicGeometry.Space.exists_finite_affine_cover_factoring_of_isIntegralHom`, every point of
`h_Y` lies in an open subspace of `h_Y` which is *representable* and over which `f` factors
through `p`.

Representability is the content: the hypothesis `hloc` provides an open subspace
neighbourhood, but makes no representability assertion about it, whereas the local clause of
Stacks 09YC (2) asks for an open neighbourhood in the *scheme* `Y`. Passing between the two is
exactly the refinement to a covering by affine open subschemes followed by
`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_factoring_of_openCover`, so this
result is idempotent on its own conclusion: the output is again a hypothesis of the shape
`hloc`, now with representability. -/
theorem exists_isOpenSubspace_isRepresentable_factoring_of_isIntegralHom
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : U ⟶ X) (Y : BigFppfOver B S hS)
    (f : yoneda.obj Y ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hf : IsIntegralHom B S hS f)
    (hloc : ∀ y : points B S hS (yoneda.obj Y),
      ∃ W : Subfunctor (yoneda.obj Y), IsOpenSubspace B S hS W ∧
        y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        ∃ g : W.toFunctor ⟶ U, W.ι ≫ f = g ≫ p)
    (y : points B S hS (yoneda.obj Y)) :
    ∃ W : Subfunctor (yoneda.obj Y), IsOpenSubspace B S hS W ∧
      W.toFunctor.IsRepresentable ∧
      y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
      ∃ g : W.toFunctor ⟶ U, W.ι ≫ f = g ≫ p := by
  obtain ⟨ι, _, Z, q, hqoi, _, hcov, hfac⟩ :=
    exists_finite_affine_cover_factoring_of_isIntegralHom B S hS p Y f hX hXqc hf hloc
  exact exists_isOpenSubspace_isRepresentable_factoring_of_openCover B S hS p Y f Z q hqoi
    hcov hfac y

end AlgebraicGeometry.Space

end
