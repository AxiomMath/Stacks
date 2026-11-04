module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain
public import StacksFrontier.AlgebraicGeometry.Spaces.CompletionBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsBaseChangeNormal
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteRegularAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAlterationImpliedProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularCompletionProper
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfAdicCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.Normal
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.RegularRing.FaithfullyFlatDescent

/-!
# The implied properties of a regular algebraic space alteration of a local Noetherian domain

Let `(A, 𝔪, κ)` be a Noetherian local domain and suppose that `Spec A` admits an alteration
`f : X ⟶ Spec A` whose source is a *regular algebraic space*. Then

1. there is a nonzero `a ∈ A` with `A_a` regular;
2. the integral closure `B` of `A` in its fraction field is a finite `A`-module;
3. the `𝔪`-adic completion of `B` is a normal ring;
4. the generic formal fibre `Aˆ ⊗_A Frac(A)` of `A` is regular.

This is [Stacks, Tag 0BHU]. The module proves all four parts at the source's hypotheses.
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomainSpaceAlteration`
names the same four parts as aliases of the declarations here.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `exists_isRegularRing_localizationAway_of_isAlteration_of_isRegular` — part (1).
* `module_finite_integralClosure_of_isAlteration_of_isRegular` — part (2).
* `isNormalRing_adicCompletion_integralClosure_of_isAlteration_of_isRegular` — part (3).
* `isRegularRing_genericFormalFibre_of_isAlteration_of_isRegular` — part (4).

Auxiliary:

* `AlgebraicGeometry.Space.exists_opens_dense_isRegular_of_isDenseOpenSubspace` — a dense
  regular open subspace of a representable algebraic space is a dense regular open subscheme of
  the representing scheme.
* `AlgebraicGeometry.Space.denseRegularOpenOfRegularAlteration` — a Noetherian domain `R`
  altered by a regular algebraic space has a dense regular open subscheme of `Spec R`.
* `AlgebraicGeometry.Space.isRegular_toScheme_completionChart` — the completed base change of an
  étale chart of a regular alteration is a regular scheme.
* `AlgebraicGeometry.Space.exists_isAffine_etaleChart_overGenericPoint` — an alteration of
  `Spec A` by an algebraic space has an affine étale chart carrying a point over the generic
  point of `Spec A`.
* `AlgebraicGeometry.Space.exists_injective_isRegularRing_adicCompletion_tensorProduct` — such a
  chart `V` has `A ⟶ Γ(V, 𝒪_V)` injective and `Aˆ ⊗_A Γ(V, 𝒪_V)` regular.
* `AlgebraicGeometry.Space.isNormalDomain_globalFunctions_of_isAlteration_of_isRegular` —
  `C = Γ(X, 𝒪_X)` is a normal domain.
* `AlgebraicGeometry.Space.globalFunctions_of_isAlteration_of_isRegular` — `C = Γ(X, 𝒪_X)` is a
  finite `A`-module containing `A`, and `Aˆ ⊗_A C` is a normal ring.

## Implementation notes

An algebraic space is a presheaf on the big fppf site over `Spec A` together with
`AlgebraicGeometry.IsAlgebraicSpace`; its regularity is the étale-local property
`AlgebraicGeometry.Space.HasEtaleLocalProperty` at `AlgebraicGeometry.IsRegular`, and the
alteration is `AlgebraicGeometry.Space.IsAlteration`. The target is `Spec A` read as the terminal
object `Over.mk (𝟙 (B.obj hA))` of that category. The generic formal fibre is
`AdicCompletion 𝔪 A ⊗[A] FractionRing A`, the localization of `Aˆ` at the image of `A ∖ {0}`.

**Part (1).** The dense regular open *subspace* of [Stacks, Tag 0BHT] is
`AlgebraicGeometry.Space.exists_isDenseOpenSubspace_hasEtaleLocalProperty_isRegular`. At the
representable target `Y = Spec A` it becomes an open *subscheme*: an open subspace of
`yoneda.obj Z` is cut out by an open of the representing scheme
(`AlgebraicGeometry.Space.subspaceOfOpens_opensOfOpenSubspace`) and is represented by that open
subscheme, whose regularity is the étale-local regularity of the subspace read through the
representable case of [Stacks, Tag 03E8]; density transports along the homeomorphism
`AlgebraicGeometry.Space.schemePointsHomeomorph` of clause (1) of [Stacks, Tag 03BX].

**Part (2).** The normalization half of [Stacks, Tag 0BHT] is
`AlgebraicGeometry.Space.isFinite_normalization_of_regular_alteration`, proved without any appeal
to [Stacks, Tag 08AR] by Chow's lemma for algebraic spaces and the degree-zero case of
[Stacks, Tag 02O6] for schemes. Part (2) uses its chart-level form,
`AlgebraicGeometry.Space.NormalizationData.isFinite_normalization_chart_of_regular_alteration`,
at the chart `Spec A` of the representable `Spec A`, together with
`AlgebraicGeometry.module_finite_integralClosure_of_isFinite_normalization` ([Stacks, Tag 035P]).

**Part (3).** This follows the source. Put `C = Γ(X, 𝒪_X)`. It is a finite `A`-module by the
degree-zero case of [Stacks, Tag 08AR] for the reduced space `X`, proved here by Chow's lemma
(`AlgebraicGeometry.Space.module_finite_globalFunctions_of_isProper`), and a normal domain by
[Stacks, Tag 0BGT] and [Stacks, Tag 0BH3]; so `B ⊆ C`, and [Stacks, Tag 0BGH] reduces normality
of `Bˆ` to that of `Cˆ = Aˆ ⊗_A C`. The base change `Y = X ×_{Spec A} Spec Aˆ` is regular by
part (3) of [Stacks, Tag 0BHQ], and `Γ(Y, 𝒪_Y) = Aˆ ⊗_A C` by the degree-zero flat base change
of [Stacks, Tag 073K] for the quasi-compact separated `X`
(`AlgebraicGeometry.Space.nonempty_ringEquiv_globalFunctions_baseChange`). Where the source then
localizes at the maximal ideals of `C` to make `Y` connected, hence integral, and applies
[Stacks, Tag 0BH3] to `Y`, the argument here reads `Γ(Y, 𝒪_Y)` as the equalizer of the two flat
restriction maps `Γ(U', 𝒪) ⇉ Γ(V', 𝒪)` of an affine étale chart `U'` of `Y` and its affine kernel
pair, `Γ(U', 𝒪)` being a normal Noetherian ring; such an equalizer is normal
(`IsNormalRing.eqLocus_of_flat`). This avoids any theory of irreducible components of algebraic
spaces.

**Part (4).** Part (3) of [Stacks, Tag 0BHQ],
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_completionSpace_iff_of_isProper`, makes
the base change of `X` to `Spec Aˆ` regular; `Spec Aˆ` is an object of the site by
`AlgebraicGeometry.BigFppfSite.contains_spec_adicCompletion`. The base change of an affine étale
chart `V` of `X` through the generic point is `Spec (Γ(V, 𝒪_V) ⊗_A Aˆ)`, a regular scheme, and
`A ⟶ Γ(V, 𝒪_V)` is injective. Inverting `A ∖ {0}` and descending regularity along the faithfully
flat `Frac(A)`-algebra `Frac(A) ⊗_A Γ(V, 𝒪_V)` is [Stacks, Tag 07NG].

## References

* [Stacks Project, Tag 0BHU](https://stacks.math.columbia.edu/tag/0BHU)
* [Stacks Project, Tag 0BHT](https://stacks.math.columbia.edu/tag/0BHT)
* [Stacks Project, Tag 0BHQ](https://stacks.math.columbia.edu/tag/0BHQ)
* [Stacks Project, Tag 07NG](https://stacks.math.columbia.edu/tag/07NG)
* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0BGH](https://stacks.math.columbia.edu/tag/0BGH)
* [Stacks Project, Tag 0BH3](https://stacks.math.columbia.edu/tag/0BH3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-! ### Scheme-theoretic preliminaries -/

/-- **A regular scheme Cartesian over `Spec A` above `Spec Λ` and `Spec C` makes `Λ ⊗_A C` a
regular ring.** The apex of such a Cartesian square is isomorphic to `Spec (Λ ⊗_A C)` by
`AlgebraicGeometry.pullbackSpecIso`, and the ring of global sections of a regular affine scheme
is regular by [Stacks, Tag 02IU]. -/
private theorem isRegularRing_tensorProduct_of_isPullback
    (A Λ C : Type u) [CommRing A] [CommRing Λ] [CommRing C] [Algebra A Λ] [Algebra A C]
    {P : Scheme.{u}} {p₁ : P ⟶ Spec (.of Λ)} {p₂ : P ⟶ Spec (.of C)}
    (hsq : IsPullback p₁ p₂ (Spec.map (CommRingCat.ofHom (algebraMap A Λ)))
      (Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (hP : IsRegular P) : IsRegularRing (Λ ⊗[A] C) := by
  have hreg : IsRegular (Spec (.of (Λ ⊗[A] C))) :=
    IsRegular.of_iso ((pullbackSpecIso A Λ C).symm ≪≫
      (IsPullback.of_hasPullback _ _).isoIsPullback _ _ hsq) hP
  have : IsRegularRing Γ(Spec (.of (Λ ⊗[A] C)), ⊤) :=
    ((isRegular_tfae_cover (Spec (.of (Λ ⊗[A] C)))).out 1 2 rfl rfl).mp hreg
      ⟨⊤, isAffineOpen_top _⟩
  exact IsRegularRing.of_ringEquiv
    (Scheme.ΓSpecIso (.of (Λ ⊗[A] C))).commRingCatIsoToRingEquiv

namespace Space

attribute [local instance] pointTopology

/-! ### A dense regular open subspace of a representable algebraic space -/

/-- **A dense regular open subspace of a representable algebraic space is a dense regular open
subscheme of the representing scheme.** Let `Z` be an object of the big fppf site over `S` and
let `V ⊆ h_Z` be an open subspace whose point set is dense and which is regular as an
étale-local property. Then the representing scheme of `Z` has a dense open subscheme which is a
regular scheme.

An open subspace of `h_Z` is cut out by an open `Q` of the representing scheme
(`AlgebraicGeometry.Space.subspaceOfOpens_opensOfOpenSubspace`), so `V` is the image of the open
immersion of site objects `AlgebraicGeometry.BigFppfOver.openSubHom` of that open
(`AlgebraicGeometry.Space.range_yoneda_map_eq_subspaceOfOpens`) and hence is represented by `Q`.
The representable case of [Stacks, Tag 03E8],
`AlgebraicGeometry.Space.exists_atlas_iff_of_representable`, then reads the étale-local
regularity of `V` as regularity of the scheme `Q`, and density transports along the comparison
`AlgebraicGeometry.Space.pointsToScheme` of clause (1) of [Stacks, Tag 03BX], which is a
homeomorphism, so that the image of the dense point set of `V` is the dense open `Q`. -/
public theorem exists_opens_dense_isRegular_of_isDenseOpenSubspace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Z : BigFppfOver B S hS)
    (V : Subfunctor (yoneda.obj Z)) (hVopen : IsOpenSubspace B S hS V)
    (hVdense : Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)))
    (hVreg : HasEtaleLocalProperty B S hS V.toFunctor (fun T : Scheme.{u} => IsRegular T)) :
    ∃ Q : ((BigFppfOver.toScheme B S hS).obj Z).Opens,
      Dense (Q : Set ((BigFppfOver.toScheme B S hS).obj Z)) ∧ IsRegular Q.toScheme := by
  refine ⟨opensOfOpenSubspace B S hS Z V hVopen, ?_, ?_⟩
  · change Dense (pointsToScheme B S hS Z '' Set.range (pointsMap B S hS V.toFunctor V.ι))
    exact (surjective_pointsToScheme B S hS Z).denseRange.dense_image
      (schemePointsHomeomorph B S hS Z).continuous hVdense
  · have hoi : _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map
          (BigFppfOver.openSubHom B S hS Z (opensOfOpenSubspace B S hS Z V hVopen))) :=
      inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion
        (opensOfOpenSubspace B S hS Z V hVopen).ι)
    have hpre : IsOpenImmersion B S hS (yoneda.map
        (BigFppfOver.openSubHom B S hS Z (opensOfOpenSubspace B S hS Z V hVopen))) :=
      (presheaf_yoneda_map_iff B S hS inferInstance _).2 hoi
    have hrange : Subfunctor.range (yoneda.map
        (BigFppfOver.openSubHom B S hS Z (opensOfOpenSubspace B S hS Z V hVopen))) = V := by
      rw [range_yoneda_map_eq_subspaceOfOpens B S hS _ hoi
        (opensOfOpenSubspace B S hS Z V hVopen)
        (opensOfOpenSubspace B S hS Z V hVopen).range_ι]
      exact subspaceOfOpens_opensOfOpenSubspace B S hS Z V hVopen
    have e : yoneda.obj (BigFppfOver.openSubObj B S hS Z
        (opensOfOpenSubspace B S hS Z V hVopen)) ≅ V.toFunctor :=
      rangeIsoOfIsOpenImmersion _ _ hpre ≪≫ eqToIso (by rw [hrange])
    exact (exists_atlas_iff_of_representable B S hS V.toFunctor
      (fun T : Scheme.{u} => IsRegular T) _ e.symm).mp hVreg

/-- **The dense regular open of [Stacks, Tag 0BHT] at a representable target.** For every
Noetherian domain `R` and every alteration of `Spec R` by a regular algebraic space, `Spec R` has a
dense regular open subscheme. The dense regular open *subspace* of [Stacks, Tag 0BHT] is
`AlgebraicGeometry.Space.exists_isDenseOpenSubspace_hasEtaleLocalProperty_isRegular`; at the
representable target `Spec R` it becomes a dense regular open *subscheme* by
`AlgebraicGeometry.Space.exists_opens_dense_isRegular_of_isDenseOpenSubspace`. -/
public theorem denseRegularOpenOfRegularAlteration :
    ∀ (R : Type u) [CommRing R], IsDomain R → IsNoetherianRing R →
      ∀ (B : BigFppfSite.{u}) (hR : B.Contains (Spec (.of R)))
        (X : (BigFppfOver B (Spec (.of R)) hR)ᵒᵖ ⥤ Type u)
        (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hR)))),
        IsAlteration B (Spec (.of R)) hR g →
        HasEtaleLocalProperty B (Spec (.of R)) hR X (fun T : Scheme.{u} => IsRegular T) →
        ∃ V : (Spec (.of R)).Opens,
          Dense (V : Set (Spec (.of R))) ∧ IsRegular V.toScheme := by
  intro R _ _ _ B hR X g hg hreg
  obtain ⟨V, hVdense, hVreg⟩ :=
    exists_isDenseOpenSubspace_hasEtaleLocalProperty_isRegular B (Spec (.of R)) hR g hg hreg
  exact exists_opens_dense_isRegular_of_isDenseOpenSubspace B (Spec (.of R)) hR
    (Over.mk (𝟙 (B.obj hR))) V hVdense.1 hVdense.2 hVreg

/-! ### Affine étale charts of a regular alteration and their completed base change -/

/-- The completed base change of a regular alteration of `Spec A` is regular, by part (3) of
[Stacks, Tag 0BHQ]. -/
private theorem hasEtaleLocalProperty_isRegular_completionSpace_of_isAlteration
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (hAc : B.Contains (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))))
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T)) :
    HasEtaleLocalProperty B (Spec (.of A)) hA (completionSpace A B hA hAc g)
      (fun T : Scheme.{u} => IsRegular T) :=
  (hasEtaleLocalProperty_isRegular_completionSpace_iff_of_isProper A B hA hAc g
    (IsAlteration.isAlgebraicSpace_source B (Spec (.of A)) hA hg)
    (IsAlteration.isIntegralSpace_source B (Spec (.of A)) hA hg).isDecentSpace
    (IsAlteration.isProper B (Spec (.of A)) hA hg)).mp hreg

/-- **The completed base change of an étale chart of a regular alteration is regular.** Let
`(A, 𝔪)` be a Noetherian local ring, let `g : X ⟶ Spec A` be an alteration whose source is
regular and let `c : h_W ⟶ X` be an étale chart. Then the base change
`W ×_{Spec A} Spec Aˆ` is a regular scheme.

The base change `X ×_{Spec A} Spec Aˆ` is regular by part (3) of [Stacks, Tag 0BHQ],
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_completionSpace_iff_of_isProper`, whose
decency hypothesis is supplied by the integrality of the source of an alteration and whose
properness hypothesis by the properness of an alteration. The base change of the chart is an
étale chart of it by `AlgebraicGeometry.Space.isEtale_completionChartMap`, so the étale-local
regularity of the base change is regularity of that chart scheme by [Stacks, Tag 03E8]. -/
public theorem isRegular_toScheme_completionChart
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (hAc : B.Contains (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))))
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T))
    (W : BigFppfOver B (Spec (.of A)) hA) (c : yoneda.obj W ⟶ X)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf c) :
    IsRegular ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
      (completionChart A B hA hAc W)) := by
  have hYreg := hasEtaleLocalProperty_isRegular_completionSpace_of_isAlteration A B hA hAc g hg hreg
  refine (exists_atlas_iff_forall_etale B (Spec (.of A)) hA
    (completionSpace A B hA hAc g) (fun T : Scheme.{u} => IsRegular T)
    (isAlgebraicSpace_completionSpace A B hA hAc g
      (IsAlteration.isAlgebraicSpace_source B (Spec (.of A)) hA hg))).mp hYreg
    (completionChart A B hA hAc W) (completionChartMap A B hA hAc g c) ?_
  rw [← isEtale_iff_presheaf_of_yoneda]
  exact isEtale_completionChartMap A B hA hAc g c
    ((isEtale_iff_presheaf_of_yoneda B (Spec (.of A)) hA c).mpr hc)

/-- **An alteration of `Spec A` by an algebraic space has an affine étale chart through the
generic point.** For `A` a domain and `g : X ⟶ Spec A` an alteration there is an object `W` of
the site whose scheme is affine, an étale chart `c : h_W ⟶ X` and a point of that scheme whose
image under the structure morphism `W ⟶ Spec A` is the generic point of `Spec A`.

An alteration is proper and dominant, hence surjective on points
(`AlgebraicGeometry.Space.isSurjective_of_isProper_of_isDominant`), so the generic point of
`Spec A` — the zero ideal, `A` being a domain — is the image of a point of `X`; that point comes
from a point of an étale atlas of `X`, and an affine open neighbourhood of the corresponding
point of the atlas scheme is an affine étale chart through it
(`AlgebraicGeometry.Space.exists_isAffine_etaleChart_pointsMap_eq`). The chart is read on
schemes through the comparison `AlgebraicGeometry.Space.pointsToScheme` of clause (1) of
[Stacks, Tag 03BX], and its structure morphism is the chart followed by `g` because `Spec A` is
terminal in the site. -/
public theorem exists_isAffine_etaleChart_overGenericPoint
    (A : Type u) [CommRing A] [IsDomain A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g) :
    ∃ (W : BigFppfOver B (Spec (.of A)) hA) (c : yoneda.obj W ⟶ X)
      (p : (BigFppfOver.toScheme B (Spec (.of A)) hA).obj W),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj W) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf c ∧
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (Over.homMk W.hom : W ⟶ Over.mk (𝟙 (B.obj hA)))) p =
          (⊥ : PrimeSpectrum A) := by
  have hsurj : IsSurjective B (Spec (.of A)) hA g :=
    isSurjective_of_isProper_of_isDominant B (Spec (.of A)) hA
      (IsAlteration.isAlgebraicSpace_target B (Spec (.of A)) hA hg) g
      (IsAlteration.isProper B (Spec (.of A)) hA hg)
      (IsAlteration.isDominant B (Spec (.of A)) hA hg)
  obtain ⟨x, hx⟩ := hsurj ((schemePointsHomeomorph B (Spec (.of A)) hA
    (Over.mk (𝟙 (B.obj hA)))).symm (⊥ : PrimeSpectrum A))
  obtain ⟨U, a, hasurj, haetale⟩ :=
    (IsAlteration.isAlgebraicSpace_source B (Spec (.of A)) hA hg).exists_atlas
  obtain ⟨u, hu⟩ := (presheafSurjective_iff_isSurjective_yoneda B (Spec (.of A)) hA X
    (IsAlteration.isAlgebraicSpace_source B (Spec (.of A)) hA hg) U a).mp hasurj x
  obtain ⟨W, j, v, hWaff, hjetale, hv⟩ :=
    exists_isAffine_etaleChart_pointsMap_eq B (Spec (.of A)) hA U u
  refine ⟨W, yoneda.map j ≫ a, pointsToScheme B (Spec (.of A)) hA W v, hWaff, ?_, ?_⟩
  · rw [← isEtale_iff_presheaf_of_yoneda]
    exact isEtale_comp B (Spec (.of A)) hA
      ((isEtale_iff_presheaf_of_yoneda B (Spec (.of A)) hA (yoneda.map j)).mpr hjetale)
      ((isEtale_iff_presheaf_of_yoneda B (Spec (.of A)) hA a).mpr haetale)
  · have hσ : yoneda.map (Over.homMk W.hom : W ⟶ Over.mk (𝟙 (B.obj hA))) =
        (yoneda.map j ≫ a) ≫ g :=
      (comp_eq_yoneda_structureHom A B hA g (yoneda.map j ≫ a)).symm
    have hval := pointsToScheme_pointsMap_yoneda B (Spec (.of A)) hA
      (Over.homMk W.hom : W ⟶ Over.mk (𝟙 (B.obj hA))) v
    rw [hσ] at hval
    rw [← hval, pointsMap_comp, pointsMap_comp, Function.comp_apply, Function.comp_apply,
      hv, hu, hx]
    exact (schemePointsHomeomorph B (Spec (.of A)) hA
      (Over.mk (𝟙 (B.obj hA)))).apply_symm_apply _

/-- **The two conclusions of
`AlgebraicGeometry.Space.exists_injective_isRegularRing_adicCompletion_tensorProduct` for an
affine `V`.** Let `(R, 𝔪)` be a
local ring, let `q : V ⟶ Spec R` be a morphism from an affine scheme whose associated ring map
is `R ⟶ Γ(V, 𝒪_V)`, let `P` be the fibre product of `q` with `Spec Rˆ ⟶ Spec R` and suppose `P`
is regular and that `q` carries some point of `V` to the generic point of `Spec R`. Then
`R ⟶ Γ(V, 𝒪_V)` is injective and `Rˆ ⊗_R Γ(V, 𝒪_V)` is a regular ring.

`V` being affine, `q` is `Spec` of `R ⟶ Γ(V, 𝒪_V)` read through `V ≅ Spec Γ(V, 𝒪_V)`, so the
Cartesian square is the standard one of `AlgebraicGeometry.pullbackSpecIso` and `P` is
`Spec (Γ(V, 𝒪_V) ⊗_R Rˆ)`. Injectivity is the statement that the kernel vanishes: it is
contained in the contraction along `R ⟶ Γ(V, 𝒪_V)` of the prime of `Γ(V, 𝒪_V)` given by the
point, and that contraction is the zero ideal. -/
private theorem injective_and_isRegularRing_adicCompletion_tensorProduct
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] {V P : Scheme.{u}} [IsAffine V]
    (q : V ⟶ Spec (.of R)) [Algebra R Γ(V, ⊤)]
    (hψ : CommRingCat.ofHom (algebraMap R Γ(V, ⊤)) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop)
    {p₁ : P ⟶ V} {p₂ : P ⟶ Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal R) R))}
    (hsq : IsPullback p₁ p₂ q (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))))
    (hP : IsRegular P) (p : V) (hp : q p = (⊥ : PrimeSpectrum R)) :
    Function.Injective (algebraMap R Γ(V, ⊤)) ∧
      IsRegularRing (AdicCompletion (IsLocalRing.maximalIdeal R) R ⊗[R] Γ(V, ⊤)) := by
  have hqfac : (Scheme.isoSpec V).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(V, ⊤))) = q := by
    rw [hψ, Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc,
      ← Scheme.toSpecΓ_naturality q]
    simp
  have ht : IsPullback (Scheme.isoSpec V).hom q
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(V, ⊤)))) (𝟙 (Spec (.of R))) :=
    IsPullback.of_horiz_isIso ⟨hqfac.trans (Category.comp_id q).symm⟩
  have hsq' : IsPullback (p₁ ≫ (Scheme.isoSpec V).hom) p₂
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(V, ⊤))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))) := by
    simpa using hsq.paste_horiz ht
  have : IsRegularRing (Γ(V, ⊤) ⊗[R] AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    isRegularRing_tensorProduct_of_isPullback R Γ(V, ⊤)
      (AdicCompletion (IsLocalRing.maximalIdeal R) R) hsq' hP
  refine ⟨?_, IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm R Γ(V, ⊤)
    (AdicCompletion (IsLocalRing.maximalIdeal R) R)).toRingEquiv⟩
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
  have hpt : Spec.map (CommRingCat.ofHom (algebraMap R Γ(V, ⊤)))
      ((Scheme.isoSpec V).hom p) = (⊥ : PrimeSpectrum R) := by
    rwa [← Scheme.Hom.comp_apply, hqfac]
  have hcomap : Ideal.comap (algebraMap R Γ(V, ⊤))
      ((Scheme.isoSpec V).hom p).asIdeal = ⊥ :=
    congrArg PrimeSpectrum.asIdeal
      (hpt : PrimeSpectrum.comap (algebraMap R Γ(V, ⊤)) ((Scheme.isoSpec V).hom p) =
        (⊥ : PrimeSpectrum R))
  exact le_antisymm (hcomap ▸ Ideal.comap_mono bot_le) bot_le

/-- **An affine étale chart through the generic point has regular completed base change.** Let
`(R, 𝔪)` be a Noetherian local domain and let `g : X ⟶ Spec R` be an alteration whose source is a
regular algebraic space. Then there is a scheme `V` with a morphism `q : V ⟶ Spec R` for which
`R ⟶ Γ(V, 𝒪_V)` is injective and `Rˆ ⊗_R Γ(V, 𝒪_V)` is a regular ring.

Take for `V` an affine étale chart of `X` through the generic point of `Spec R`
(`AlgebraicGeometry.Space.exists_isAffine_etaleChart_overGenericPoint`). The chart carries a point
over the zero ideal of `R`, which makes `R ⟶ Γ(V, 𝒪_V)` injective; the base change
`V ×_{Spec R} Spec Rˆ` is a regular scheme by
`AlgebraicGeometry.Space.isRegular_toScheme_completionChart`, and `V` being affine it is
`Spec (Γ(V, 𝒪_V) ⊗_R Rˆ)` by `AlgebraicGeometry.pullbackSpecIso`. -/
public theorem exists_injective_isRegularRing_adicCompletion_tensorProduct
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    (B : BigFppfSite.{u}) (hR : B.Contains (Spec (.of R)))
    (X : (BigFppfOver B (Spec (.of R)) hR)ᵒᵖ ⥤ Type u)
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hR))))
    (hg : IsAlteration B (Spec (.of R)) hR g)
    (hreg : HasEtaleLocalProperty B (Spec (.of R)) hR X (fun T : Scheme.{u} => IsRegular T)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Spec (.of R)),
      letI : Algebra R Γ(V, ⊤) :=
        ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop).hom.toAlgebra
      Function.Injective (algebraMap R Γ(V, ⊤)) ∧
        IsRegularRing (AdicCompletion (IsLocalRing.maximalIdeal R) R ⊗[R] Γ(V, ⊤)) := by
  have hRc : B.Contains (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal R) R))) :=
    B.contains_spec_adicCompletion hR _
  obtain ⟨W, c, p, hWaff, hc, hp⟩ :=
    exists_isAffine_etaleChart_overGenericPoint R B hR g hg
  let : Algebra R Γ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj W, ⊤) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ ((BigFppfOver.toScheme B (Spec (.of R)) hR).map
      (Over.homMk W.hom : W ⟶ Over.mk (𝟙 (B.obj hR)))).appTop).hom.toAlgebra
  exact ⟨_, _, injective_and_isRegularRing_adicCompletion_tensorProduct R
    ((BigFppfOver.toScheme B (Spec (.of R)) hR).map
      (Over.homMk W.hom : W ⟶ Over.mk (𝟙 (B.obj hR)))) rfl
    (isPullback_toScheme_completionChart R B hR hRc W)
    (isRegular_toScheme_completionChart R B hR hRc g hg hreg W c hc) p hp⟩

/-! ### The global functions of a regular algebraic space alteration -/

/-- The global functions of an alteration of `Spec A` by a regular algebraic space form a normal
domain: the space is normal by [Stacks, Tag 0BGT] and integral by definition of an alteration,
and [Stacks, Tag 0BH3] applies. -/
public theorem isNormalDomain_globalFunctions_of_isAlteration_of_isRegular
    (A : Type u) [CommRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T)) :
    IsNormalDomain (globalFunctions B (Spec (.of A)) hA X) :=
  isNormalDomain_globalSections_of_isIntegralSpace B (Spec (.of A)) hA X
    (IsAlteration.isAlgebraicSpace_source B (Spec (.of A)) hA hg)
    (IsAlteration.isIntegralSpace_source B (Spec (.of A)) hA hg)
    (isNormal_of_isRegular B (Spec (.of A)) hA X hreg)

/-! ### The implied properties -/

/-- **A Noetherian local domain admitting an alteration by a regular algebraic space is regular
after inverting one nonzero element.** The dense regular open of [Stacks, Tag 0BHT], read at the
representable target `Spec A` by
`AlgebraicGeometry.Space.denseRegularOpenOfRegularAlteration`, contains a nonempty basic open
`D(a)` of `Spec A`, and `Γ(D(a)) = A_a`. -/
@[stacks 0BHU "part (1)"]
public theorem exists_isRegularRing_localizationAway_of_isAlteration_of_isRegular
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T)) :
    ∃ a : A, a ≠ 0 ∧ IsRegularRing (Localization.Away a) := by
  obtain ⟨V, hVdense, hVreg⟩ :=
    denseRegularOpenOfRegularAlteration A inferInstance inferInstance B hA X g hg hreg
  obtain ⟨x, hx⟩ := hVdense.nonempty
  exact exists_isRegularRing_localizationAway_of_isRegular_opens A V hVreg ⟨x, hx⟩

/-- **The integral closure of a Noetherian local domain admitting an alteration by a regular
algebraic space is a finite module over it.** This is clause (2) of [Stacks, Tag 0BHU]: `A` is
N-1 (`IsN1`).

The alteration makes `Spec A` an integral algebraic space carrying a regular alteration, so
[Stacks, Tag 0BHT] applies to it; `Spec A` is its own affine surjective étale scheme chart, the
identity being surjective and étale, and along that chart
`AlgebraicGeometry.Space.NormalizationData.isFinite_normalization_chart_of_regular_alteration`
gives that the normalization morphism of the *scheme* `Spec A` is finite. By [Stacks, Tag 035P]
that morphism is the spectrum map of `A ⟶ integralClosure A (Frac A)`, so the integral closure is
a finite `A`-module; that reading is
`AlgebraicGeometry.module_finite_integralClosure_of_isFinite_normalization`, which takes the
presenting ring of the scheme — here `A` itself — rather than its ring of global sections.

The source argues instead that `C = Γ(X, 𝒪_X)` is a finite `A`-module by [Stacks, Tag 08AR] and
integrally closed, and that the integral closure embeds into `C`; the route above replaces that
by Chow's lemma for algebraic spaces over the chart and the degree-zero case of
[Stacks, Tag 02O6] for *schemes*, which is how [Stacks, Tag 0BHT] is proved here. -/
@[stacks 0BHU "part (2)"]
public theorem module_finite_integralClosure_of_isAlteration_of_isRegular
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T)) :
    Module.Finite A ↥(integralClosure A (FractionRing A)) := by
  have hUaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
      (Over.mk (𝟙 (B.obj hA)))) := inferInstanceAs (IsAffine (Spec (.of A)))
  have hUred : _root_.AlgebraicGeometry.IsReduced
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (Over.mk (𝟙 (B.obj hA)))) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsReduced (Spec (.of A)))
  have hUnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
      (Over.mk (𝟙 (B.obj hA)))) := inferInstanceAs (IsLocallyNoetherian (Spec (.of A)))
  have hYsp : IsAlgebraicSpace B (Spec (.of A)) hA (yoneda.obj (Over.mk (𝟙 (B.obj hA)))) :=
    IsAlteration.isAlgebraicSpace_target B (Spec (.of A)) hA hg
  have hYnoeth : HasEtaleLocalProperty B (Spec (.of A)) hA
      (yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_of_representable B (Spec (.of A)) hA _ _ _ (Iso.refl _) hUnoeth
  have hU : ∀ V : ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
        (Over.mk (𝟙 (B.obj hA)))).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
        (Over.mk (𝟙 (B.obj hA))))) → (irreducibleComponents V).Finite :=
    fun V hV => finite_irreducibleComponents_of_isCompact _ V hV
  exact module_finite_integralClosure_of_isFinite_normalization hU (Iso.refl _)
    (NormalizationData.isFinite_normalization_chart_of_regular_alteration B (Spec (.of A)) hA
      g hg hreg hYnoeth
      (normalizationData B (Spec (.of A)) hA hYsp
        (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B (Spec (.of A)) hA _
          hYsp hYnoeth))
      hUaff (𝟙 _) (isSurjective_id B (Spec (.of A)) hA _)
      (isEtale_id B (Spec (.of A)) hA _) hU)

/-- The global functions of an alteration of `Spec A` by a regular algebraic space form a finite
`A`-module, by the degree-zero case of [Stacks, Tag 08AR]. -/
private theorem module_finite_globalFunctions_of_isAlteration
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g) :
    Module.Finite A (globalFunctions B (Spec (.of A)) hA X) :=
  module_finite_globalFunctions_of_isProper B A hA
    ⟨X, IsAlteration.isAlgebraicSpace_source B (Spec (.of A)) hA hg⟩ g
    (IsAlteration.isProper B (Spec (.of A)) hA hg)
    (IsAlteration.isIntegralSpace_source B (Spec (.of A)) hA hg).1

/-- **The completed base change of the global functions of a regular alteration is normal.** For
`A` a Noetherian local domain and `g : X ⟶ Spec A` an alteration with `X` regular, `Aˆ ⊗_A C` is a
normal ring, where `C = Γ(X, 𝒪_X)`.

`Y = X ×_{Spec A} Spec Aˆ` is regular by part (3) of [Stacks, Tag 0BHQ], hence normal
([Stacks, Tag 0BGT]); `Γ(Y, 𝒪_Y) = Aˆ ⊗_A C` by the degree-zero flat base change of
[Stacks, Tag 073K], which makes it Noetherian; and the global functions of `Y` are a normal ring by
`AlgebraicGeometry.Space.isNormalRing_globalFunctions_of_isPullback`. -/
public theorem isNormalRing_adicCompletion_tensorProduct_globalFunctions_of_isAlteration
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T)) :
    IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A]
      globalFunctions B (Spec (.of A)) hA X) := by
  classical
  have hX : IsAlgebraicSpace B (Spec (.of A)) hA X :=
    IsAlteration.isAlgebraicSpace_source B (Spec (.of A)) hA hg
  let Xs : AlgebraicSpaces B (Spec (.of A)) hA := ⟨X, hX⟩
  have hprop : IsProper B (Spec (.of A)) hA g := IsAlteration.isProper B (Spec (.of A)) hA hg
  have := module_finite_globalFunctions_of_isAlteration A B hA g hg
  let Ac := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have hAc : B.Contains (Spec (.of Ac)) := B.contains_spec_adicCompletion hA _
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let Ys : AlgebraicSpaces B (Spec (.of A)) hA :=
    ⟨completionSpace A B hA hAc g, isAlgebraicSpace_completionSpace A B hA hAc g hX⟩
  have hX' : IsPullback (completionProjection A B hA hAc g)
      (pullback.snd g (completionBaseMap A B hA hAc)) g
      (yoneda.map (siteTerminalHom B (Spec (.of A)) hA (specAlgebraObj A Ac B hA hAc))) :=
    IsPullback.of_hasPullback g (completionBaseMap A B hA hAc)
  have hqc : IsQuasiCompactSpace B (Spec (.of A)) hA X :=
    isQuasiCompactSpace_of_isProper_baseObject A B hA X hX g hprop
  have hsep : IsAbsolutelySeparated B (Spec (.of A)) hA hZ X :=
    (isAbsolutelySeparated_iff_isSeparatedOver B (Spec (.of A)) hA hZ inferInstance hX).mpr
      ((isSeparatedOver_iff_isSeparated_of_isTerminal B (Spec (.of A)) hA
        (IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal) g).mpr hprop.1)
  have hYreg := hasEtaleLocalProperty_isRegular_completionSpace_of_isAlteration A B hA hAc g hg hreg
  have hYnoeth : HasEtaleLocalProperty B (Spec (.of A)) hA (completionSpace A B hA hAc g)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
    obtain ⟨U, φ, hs, he, hr⟩ := hYreg
    exact ⟨U, φ, hs, he, isLocallyNoetherian_of_isRegular hr⟩
  obtain ⟨e⟩ := nonempty_ringEquiv_globalFunctions_baseChange A Ac hAc (X := Xs) (X' := Ys) g hX'
    hZ hqc hsep
  have hTnoeth : IsNoetherianRing (Ac ⊗[A] globalFunctions B (Spec (.of A)) hA X) :=
    IsNoetherianRing.of_finite Ac _
  have hGnoeth : IsNoetherianRing (globalFunctions B (Spec (.of A)) hA Ys.obj) :=
    isNoetherianRing_of_ringEquiv _ e.symm
  exact IsNormalRing.congr e (isNormalRing_globalFunctions_of_isPullback A Ac hAc (X := Xs)
    (X' := Ys) g hX' hZ hqc hsep (isNormal_of_isRegular B (Spec (.of A)) hA _ hYreg)
    hYnoeth hGnoeth)

/-- **The global functions of a regular alteration of `Spec A`.** For `A` a Noetherian local
domain and `g : X ⟶ Spec A` an alteration with `X` regular, `C = Γ(X, 𝒪_X)` is a finite
`A`-module, `A ⟶ C` is injective, and the completed base change `Aˆ ⊗_A C` is a normal ring.

Finiteness is the degree-zero case of [Stacks, Tag 08AR] for the reduced space `X`,
`AlgebraicGeometry.Space.module_finite_globalFunctions_of_isProper`; injectivity holds because
`g` is proper and dominant, hence surjective. For normality, `Y = X ×_{Spec A} Spec Aˆ` is regular
by part (3) of [Stacks, Tag 0BHQ], hence normal ([Stacks, Tag 0BGT]); `Γ(Y, 𝒪_Y) = Aˆ ⊗_A C` by
the degree-zero flat base change of [Stacks, Tag 073K], which makes it Noetherian; and the global
functions of `Y` are a normal ring by
`AlgebraicGeometry.Space.isNormalRing_globalFunctions_of_isPullback`. -/
public theorem globalFunctions_of_isAlteration_of_isRegular
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T)) :
    Module.Finite A (globalFunctions B (Spec (.of A)) hA X) ∧
      Function.Injective (algebraMap A (globalFunctions B (Spec (.of A)) hA X)) ∧
      IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A]
        globalFunctions B (Spec (.of A)) hA X) := by
  let Xs : AlgebraicSpaces B (Spec (.of A)) hA :=
    ⟨X, IsAlteration.isAlgebraicSpace_source B (Spec (.of A)) hA hg⟩
  have hprop : IsProper B (Spec (.of A)) hA g := IsAlteration.isProper B (Spec (.of A)) hA hg
  exact ⟨module_finite_globalFunctions_of_isAlteration A B hA g hg,
    injective_algebraMap_globalFunctions_of_isProper B A hA Xs g hprop
      (isSurjective_of_isProper_of_isDominant B (Spec (.of A)) hA
        (IsAlteration.isAlgebraicSpace_target B (Spec (.of A)) hA hg) g hprop
        (IsAlteration.isDominant B (Spec (.of A)) hA hg)),
    isNormalRing_adicCompletion_tensorProduct_globalFunctions_of_isAlteration A B hA X g hg hreg⟩

/-- **The completion of the integral closure of a Noetherian local domain admitting an
alteration by a regular algebraic space is normal.** This is part (3) of [Stacks, Tag 0BHU]. Let
`B` be the integral closure of `A` in `Frac(A)` and `C = Γ(X, 𝒪_X)`. Then `C` is a finite
`A`-module and a normal domain containing `A` ([Stacks, Tag 0BH3]), so `B ⊆ C`, and `Cˆ = Aˆ ⊗_A C`
is normal by `AlgebraicGeometry.Space.globalFunctions_of_isAlteration_of_isRegular`;
[Stacks, Tag 0BGH] gives normality of `Bˆ`. Normality is `IsNormalRing`: every localization at a
prime is a normal domain, which for the finite algebra `Bˆ` over the complete local `Aˆ` is
normality of the completions of `B` at its maximal ideals. -/
@[stacks 0BHU "part (3)"]
public theorem isNormalRing_adicCompletion_integralClosure_of_isAlteration_of_isRegular
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T)) :
    IsNormalRing
      (AdicCompletion
        ((IsLocalRing.maximalIdeal A).map
          (algebraMap A ↥(integralClosure A (FractionRing A))))
        ↥(integralClosure A (FractionRing A))) := by
  obtain ⟨hfin, hinj, hCD⟩ := globalFunctions_of_isAlteration_of_isRegular A B hA X g hg hreg
  have hnd : IsNormalDomain (globalFunctions B (Spec (.of A)) hA X) :=
    isNormalDomain_globalFunctions_of_isAlteration_of_isRegular A B hA X g hg hreg
  have := hnd.isDomain
  have := hnd.isIntegrallyClosed
  have : Algebra.IsIntegral A (globalFunctions B (Spec (.of A)) hA X) :=
    Algebra.IsIntegral.of_finite A _
  have : IsNormalDomain ↥(integralClosure A (FractionRing A)) :=
    integralClosure_isNormalDomain (R := A) (S := FractionRing A) ⟨inferInstance, inferInstance⟩
  let φ : ↥(integralClosure A (FractionRing A)) →ₐ[A] globalFunctions B (Spec (.of A)) hA X :=
    integralClosureToIntegrallyClosed (K := FractionRing A) hinj
  let : Algebra ↥(integralClosure A (FractionRing A)) (globalFunctions B (Spec (.of A)) hA X) :=
    φ.toAlgebra
  have : IsScalarTower A ↥(integralClosure A (FractionRing A))
      (globalFunctions B (Spec (.of A)) hA X) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have hBC : Function.Injective (algebraMap ↥(integralClosure A (FractionRing A))
      (globalFunctions B (Spec (.of A)) hA X)) :=
    integralClosureToIntegrallyClosed_injective hinj
  have : Module.Finite A ↥(integralClosure A (FractionRing A)) :=
    module_finite_integralClosure_of_isAlteration_of_isRegular A B hA X g hg hreg
  exact isNormalRing_adicCompletion_of_finite_injective A
    ↥(integralClosure A (FractionRing A)) (globalFunctions B (Spec (.of A)) hA X) hBC
    (IsNormalRing.of_isIntegrallyClosed _)
    (IsNormalRing.congr (ofTensorProductAlgEquiv (IsLocalRing.maximalIdeal A)
      (globalFunctions B (Spec (.of A)) hA X)).toRingEquiv hCD)

/-- **The generic formal fibre of a Noetherian local domain admitting an alteration by a regular
algebraic space is regular.** For an affine étale chart `V` of `X` through the generic point the
ring `Aˆ ⊗_A Γ(V, 𝒪_V)` is regular, and the generic formal fibre is recovered by inverting
`A ∖ {0}` and descending along the faithfully flat `Frac(A)`-algebra `Frac(A) ⊗_A Γ(V, 𝒪_V)`
by [Stacks, Tag 07NG]. Regularity of the completed base change of the chart is part (3) of
[Stacks, Tag 0BHQ], applied through
`AlgebraicGeometry.Space.exists_injective_isRegularRing_adicCompletion_tensorProduct`. -/
@[stacks 0BHU "part (4)", ega "IV 7.9.3" "special case"]
public theorem isRegularRing_genericFormalFibre_of_isAlteration_of_isRegular
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hg : IsAlteration B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T)) :
    IsRegularRing ((AdicCompletion (IsLocalRing.maximalIdeal A) A) ⊗[A] (FractionRing A)) := by
  obtain ⟨V, q, hinj, hregular⟩ :=
    exists_injective_isRegularRing_adicCompletion_tensorProduct A B hA X g hg hreg
  let : Algebra A Γ(V, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom.toAlgebra
  have := hregular
  exact isRegularRing_tensorProduct_fractionRing_of_baseChange
    (C := AdicCompletion (IsLocalRing.maximalIdeal A) A) (R := Γ(V, ⊤))
    (K := FractionRing A) hinj

end Space

end AlgebraicGeometry

end
