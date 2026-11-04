module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartQuasicoherentGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange

/-!
# Quasi-coherence of the direct image along an affine morphism of algebraic spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` of a big fppf site
`B` and let `F` be a quasi-coherent `𝒪_X`-module. Stacks 07U8 asserts that `f_*F` is
quasi-coherent, that it agrees with the total derived direct image, and that its formation
commutes with arbitrary base change; the source proves all three by reducing to the affine
morphism of schemes of Stacks 02KG.

This file carries out that reduction for the first assertion. Quasi-coherence of an
`𝒪_Y`-module is quasi-coherence of its restrictions to the étale scheme charts of `Y`
(Stacks 03LZ); the restriction of `f_*F` to a chart is the direct image of the restriction of
`F` along the base change of `f` to that chart (Stacks 03LX); and that base change is again
affine. What remains — quasi-coherence of the direct image along an affine morphism whose
target is the algebraic space of a scheme of the site — is the hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.SchemeTargetAffinePushforwardQuasicoherent` is the first assertion
  of Stacks 07U8 restricted to a target represented by a scheme of the site.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom` is the first
  assertion of **Stacks 07U8** for an arbitrary target, granted that restriction.
* `AlgebraicGeometry.Space.schemeTargetAffinePushforwardQuasicoherent_of_isAffineHom` is the
  converse: the restricted statement is a special case, so the two are equivalent.

## Implementation notes

The comparison of `f_*F` with the total derived direct image and the base-change assertion of
Stacks 07U8 are not treated, and the attribute carries a part string naming the one assertion
that is.

The hypothesis is genuinely missing from this development rather than merely unproved here. The
identification of quasi-coherent modules on the
small étale site of the algebraic space of a scheme with quasi-coherent modules on the scheme —
the equivalence of Stacks 03LY cut down to the quasi-coherent objects — *is* available, as
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, and it is compatible with
the direct image by `AlgebraicGeometry.Space.representedModulePushforwardSquareIso`. For a
represented source and target the hypothesis is therefore exactly equivalent to a statement
about schemes, by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_representedSpaceMap_iff`: that
the direct image on the small étale site of a scheme along an affine morphism preserves
quasi-coherence. The Zariski form of that is proved, as
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`, which
carries the `@[stacks 02KG]` attribute; what is missing is carrying it across the Zariski-étale
comparison.  The two inputs for that are in the library as well — Stacks 070S (2) on the small étale
site, `AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso`, and the base-change
assertion of Stacks 02KG,
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom` — so what
is owed is the assembly of the natural comparison whose bijectivity they supply pointwise.

The module universe is the universe `u` of the structure rings, which is the only one at which
`AlgebraicGeometry.Space.modulePushforward` exists.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LZ](https://stacks.math.columbia.edu/tag/03LZ)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The first assertion of Stacks 07U8 for a target represented by a scheme of the site**, as
a proposition: for every affine morphism `f : X ⟶ V` of algebraic spaces whose target is the
algebraic space of a scheme `V` of the big fppf site, and every quasi-coherent `𝒪_X`-module
`F`, the direct image `f_*F` is quasi-coherent.

This is the case in which the source reduces to the affine morphism of schemes of
Stacks 02KG. -/
def SchemeTargetAffinePushforwardQuasicoherent : Prop :=
  ∀ (V : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V),
    IsAffineHom B S hS f.hom →
      ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite →
        ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite

/-- **Stacks 07U8, the quasi-coherence of the direct image.** Let `f : X ⟶ Y` be an affine
morphism of algebraic spaces over `S` and let `F` be a quasi-coherent `𝒪_X`-module. Then the
direct image `f_*F` is quasi-coherent.

The hypothesis `h` is the same statement for a target represented by a scheme of the site.
Everything else is the reduction of the source: quasi-coherence is chartwise by Stacks 03LZ,
the restriction of `f_*F` to a chart is the direct image along the base change of `f` by
Stacks 03LX, and a base change of an affine morphism is affine. -/
@[stacks 07U8 "quasi-coherence of the direct image, reduced chartwise to the case of a target \
represented by a scheme of the site, which is the hypothesis h"]
theorem isQuasicoherentOnSite_modulePushforward_of_isAffineHom
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite := by
  rw [isQuasicoherentOnSite_iff_forall_chartModuleRestriction]
  intro U
  let c : schemeSpace ((SmallEtale.toOver B S hS Y.1).obj U) ⟶ Y :=
    chartToSpace B S hS Y U
  have hc : IsEtale B S hS c.hom := isEtale_chartToSpace B S hS Y U
  let X' := AlgebraicSpaces.fiberProduct B S hS c f
  let f' : X' ⟶ schemeSpace ((SmallEtale.toOver B S hS Y.1).obj U) :=
    ObjectProperty.homMk (pullback.fst c.hom f.hom)
  let i : X' ⟶ X := ObjectProperty.homMk (pullback.snd c.hom f.hom)
  have sq : IsPullback i f' f c := (AlgebraicSpaces.isPullback_fiberProduct B S hS c f).flip
  have hiEt : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS f' i c f sq.flip hc
  have hf' : IsAffineHom B S hS f'.hom :=
    isAffineHom_of_isPullback ((IsPullback.of_hasPullback c.hom f.hom).flip) hf
  have h1 : ((modulePushforward B S hS f').obj
      ((etaleModulePullback B S hS i hiEt).obj F)).IsQuasicoherentOnSite :=
    h ((SmallEtale.toOver B S hS Y.1).obj U) f' hf' _
      (isQuasicoherentOnSite_etaleModulePullback B S hS i hiEt F hF)
  have h2 : ((etaleModulePullback B S hS c hc).obj
      ((modulePushforward B S hS f).obj F)).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePushforwardEtaleBaseChangeIso B S hS i f' f c sq hc).app F) h1
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS c hc).app
      ((modulePushforward B S hS f).obj F)).symm h2

/-- The scheme-target case of the quasi-coherence assertion of Stacks 07U8 is a special case of
the general one, so the hypothesis of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom` is exactly as
strong as its conclusion. -/
theorem schemeTargetAffinePushforwardQuasicoherent_of_isAffineHom
    (h : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), IsAffineHom B S hS f.hom →
      ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite →
        ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite) :
    SchemeTargetAffinePushforwardQuasicoherent B S hS :=
  fun _ _ f hf F hF ↦ h f hf F hF

end AlgebraicGeometry.Space

end
