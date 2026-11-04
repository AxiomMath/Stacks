module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.UnconditionalArtinianPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria

/-!
# An injective quasi-coherent module is acyclic on the chart base changes of a morphism

Let `X` be a Noetherian algebraic space over a scheme `S`, let `f : X ⟶ Y` be a morphism of
algebraic spaces with `Y` quasi-separated, and let `𝒥` be an injective object of `QCoh(𝒪_X)`.
For every affine étale scheme chart `V` of `Y` the algebraic space `U = V ×_Y X` is
quasi-compact, quasi-separated and étale over `X`, so `H^p(V ×_Y X, 𝒥) = 0` for `p > 0`.

## Main results

* `AlgebraicGeometry.Space.isZero_etaleRestrictionCohomology_chartBaseChange_of_isNoetherian`:
  the vanishing `H^p(V ×_Y X, 𝒥) = 0` for `p > 0` and `V` an affine étale scheme chart of `Y`.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_injective_of_isNoetherian`:
  the vanishing `R^p f_*𝒥 = 0` for `p > 0`, granted the carried input `hdetect` below.

## Implementation notes

*Where quasi-separatedness of `Y` is used.*  `U = V ×_Y X` is the fibre product of `f` and the
étale structure morphism of `V`, so Stacks 073B, part (3) applies: `U` is quasi-compact because
`X` and `V` are and `Y` is quasi-separated, which is the only place the hypothesis on `Y` enters,
and `U` is quasi-separated because the structure morphism `U ⟶ X` is a base change of the
quasi-separated `V ⟶ Y` and `X` is quasi-separated.  Quasi-separatedness of `V ⟶ Y` needs no
hypothesis on `Y`, being part (2) of the same lemma.  The vanishing is then Stacks 09TL,
part (1), `isZero_etaleRestrictionCohomology_of_injective_of_isNoetherian`, at the étale
morphism `U ⟶ X`.

*What is carried, and why.*  The passage from that chart-local vanishing to `R^p f_*𝒥 = 0` is
Stacks 072W read for `AlgebraicGeometry.Space.modulePushforward`: the sheaf `R^p f_*𝒥` is the
sheafification of the presheaf `V ↦ H^p(V ×_Y X, 𝒥)`, and the affine étale charts cover every
object of the small étale site of `Y`
(`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`).  This repository has Stacks 072W
only for the direct image `SheafOfModules.pushforward φ` along a continuous functor of sites
(`Stacks.Cohomology.HigherDirectImage.higherDirectImage_iso_sheafify_cohomologyPresheaf`),
whereas `AlgebraicGeometry.Space.modulePushforward` is built from a right Kan extension along the
comparison of Stacks 03G1 and the structure map of Stacks 03G8, and the comparison of the two is
not available; the route through
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_chartwise` is no substitute,
since it asks for `f` to be representable, which Stacks 09TL does not assume.  So that passage is
carried, as a hypothesis `hdetect` quantified over every morphism of algebraic spaces and every
quasi-coherent coefficient module, by
`AlgebraicGeometry.Space.ChartLocalCohomologyDetectsHigherDirectImage`.  No Stacks tag
attribute is attached to anything below: the conclusion of
`isZero_rightDerived_modulePushforward_of_injective_of_isNoetherian` is part (2) of the source
statement, but it is reached only with that result of the Stacks project assumed.

## References

* [Stacks Project, Tag 09TL](https://stacks.math.columbia.edu/tag/09TL)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Acyclicity on the chart base changes -/

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules in
/-- **The chart-local half of Stacks 09TL, part (2).**  Let `X` be a Noetherian algebraic space
over a scheme `S`, let `f : X ⟶ Y` be a morphism of algebraic spaces with `Y` quasi-separated and
let `𝒥` be an injective object of `QCoh(𝒪_X)`.  Then `H^p(V ×_Y X, 𝒥) = 0` for `p > 0` and every
affine étale scheme chart `V` of `Y`.

The fibre product `V ×_Y X` is quasi-compact and quasi-separated by Stacks 073B, part (3), and
étale over `X` by Stacks 03FU, so part (1) of Stacks 09TL applies to it. -/
theorem isZero_etaleRestrictionCohomology_chartBaseChange_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS}
    (hX : IsNoetherian B S hS hZ X.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J]
    (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((etaleRestrictionCohomology B S hS (chartBaseChangeInclusion B S hS f V)
      (isEtale_chartBaseChangeInclusion B S hS f V) p).obj J) := by
  have hsq : IsPullback (chartBaseChangeInclusion B S hS f V).hom
      (chartBaseChangeProjection B S hS f V).hom f.hom (chartToSpace B S hS Y V).hom :=
    AlgebraicSpaces.isPullback_hom B S hS (isPullback_chartBaseChangeInclusion B S hS f V)
  have hVqc : IsQuasiCompactSpace B S hS (chartSpace B S hS Y V).1 :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS _ hV
  have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ (chartSpace B S hS Y V).1 :=
    isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ (isAffineSpace_yoneda B S hS _ hV)
  have hUqc : IsQuasiCompactSpace B S hS (chartBaseChangeSpace B S hS f V).1 :=
    isQuasiCompactSpace_of_iso B S hS hsq.isoPullback.symm
      (isQuasiCompactSpace_pullback B S hS hZ f.hom (chartToSpace B S hS Y V).hom X.2 Y.2
        hX.1 hVqc hYqs)
  have hUqs : IsAbsolutelyQuasiSeparated B S hS hZ (chartBaseChangeSpace B S hS f V).1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
      (chartBaseChangeSpace B S hS f V).2 hX.2.1
      (isQuasiSeparated_of_isPullback B S hS hsq.flip
        (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ
          (chartSpace B S hS Y V).2 hVqs (chartToSpace B S hS Y V).hom))
  exact isZero_etaleRestrictionCohomology_of_injective_of_isNoetherian B S hS hZ hX J
    (chartBaseChangeInclusion B S hS f V) (isEtale_chartBaseChangeInclusion B S hS f V)
    hUqc hUqs p hp

/-! ### Stacks 09TL, part (2), with Stacks 072W carried -/

/-- The carried input `hdetect`: **Stacks 072W read for
`AlgebraicGeometry.Space.modulePushforward`**, in its vanishing form.  The degree-`p` higher
direct image of a quasi-coherent module along a morphism of algebraic spaces vanishes as soon as
`H^p(V ×_Y X, M) = 0` for every affine étale scheme chart `V` of the target.

The source's `R^p f_*M` is the sheafification of the presheaf `V ↦ H^p(V ×_Y X, M)` and the
affine étale charts cover every object of the small étale site; see the implementation notes of
this file for why neither step is available here. -/
def ChartLocalCohomologyDetectsHigherDirectImage (p : ℕ) : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : QuasicoherentSheaves.{u, u} B S hS X.1 X.2),
    (∀ V : SmallEtale B S hS Y.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
        IsZero ((etaleRestrictionCohomology B S hS (chartBaseChangeInclusion B S hS f V)
          (isEtale_chartBaseChangeInclusion B S hS f V) p).obj M)) →
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      IsZero (((modulePushforward B S hS f).rightDerived p).obj M.obj)

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules in
/-- **Stacks 09TL, part (2), granted the carried input `hdetect`.**  Let `X` be a Noetherian
algebraic space over a scheme `S`, let `𝒥` be an injective object of `QCoh(𝒪_X)` and let
`f : X ⟶ Y` be a morphism of algebraic spaces with `Y` quasi-separated.  Then `R^p f_*𝒥 = 0`
for `p > 0`.

The chart-local vanishing that `hdetect` consumes is
`isZero_etaleRestrictionCohomology_chartBaseChange_of_isNoetherian`; `hdetect` itself, which is
Stacks 072W for the direct image of modules on the small étale sites, is not proved here. -/
theorem isZero_rightDerived_modulePushforward_of_injective_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS}
    (hX : IsNoetherian B S hS hZ X.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J]
    (f : X ⟶ Y) (p : ℕ) (hp : 0 < p)
    (hdetect : ChartLocalCohomologyDetectsHigherDirectImage B S hS p) :
    IsZero (((modulePushforward B S hS f).rightDerived p).obj J.obj) :=
  hdetect f J fun V hV =>
    isZero_etaleRestrictionCohomology_chartBaseChange_of_isNoetherian B S hS hZ hX hYqs J f V
      hV p hp

end AlgebraicGeometry.Space

end

end
