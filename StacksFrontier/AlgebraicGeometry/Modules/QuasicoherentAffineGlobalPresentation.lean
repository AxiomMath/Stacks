module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-coherent module on an affine scheme has a global presentation

Quasi-coherence of a sheaf of modules on a site, `SheafOfModules.IsQuasicoherentOnSite`, is
Stacks 03DL(6): every object of the site has a covering on whose members the restricted module
admits a *global* presentation, `SheafOfModules.HasGlobalPresentation`.  On the small Zariski
site `T.Opens` of an **affine** scheme no covering is needed: a quasi-coherent `𝒪_T`-module is
the module associated with a module over the coordinate ring `Γ(T, ⊤)`, so a presentation of
that module by generators and relations transports to a presentation of the sheaf on the nose.
That is the presentation step of Stacks 03DX, and it is what this file proves.  The registration
below carries that step with a clause string naming it; 03DX states its clauses as equivalences
of categories, and those statements are carried in
`StacksDraft.AlgebraicGeometry.Descent.AssociatedModule`, clause (1) at
`AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite_fppf` and clause (2) at
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'` and
`AlgebraicGeometry.SmallZariski.isEquivalence_associatedModuleQcohOnSite`, whose descent
arguments consume what is proved here.

The presentation is *constructed*, not extracted from an existence statement.  On `Spec R` a
quasi-coherent module `N` is `Γ(N, ⊤)^~` by Mathlib's
`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`, and
`AlgebraicGeometry.presentationTilde` presents `M^~` from a spanning set of `M` together with a
spanning set of the kernel of the resulting free cover; taking both to be everything gives a
presentation with no choices.  An arbitrary affine `T` is carried to `Spec Γ(T, ⊤)` by
`AlgebraicGeometry.Scheme.isoSpec`, and a presentation is carried back along that isomorphism by
`AlgebraicGeometry.Scheme.Modules.presentationRestrict`.

## Main definitions

* `Stacks.AlgebraicGeometry.AffinePresentation.quasicoherentPresentationOfIsoSpec`: on a
  scheme isomorphic to a spectrum, a `SheafOfModules.Presentation` of a quasi-coherent module,
  as data.
* `Stacks.AlgebraicGeometry.AffinePresentation.quasicoherentPresentationOfIsAffine`: the
  same on an affine scheme, through `AlgebraicGeometry.Scheme.isoSpec`.

## Main results

* `Stacks.AlgebraicGeometry.AffinePresentation.hasGlobalPresentation_of_isQuasicoherent`:
  a quasi-coherent `𝒪_T`-module on an affine scheme `T` has a global presentation, from
  Mathlib's quasi-coherence.
* `Stacks.AlgebraicGeometry.AffinePresentation.hasGlobalPresentation_of_isQuasicoherentOnSite`
  is **the presentation step of Stacks 03DX, from Stacks 03DL(6)**: a module quasi-coherent in
  that sense on an affine scheme has a global presentation, with no covering.
* `Stacks.AlgebraicGeometry.AffinePresentation.isQuasicoherentOnSite_iff_hasGlobalPresentation`
  says that on an affine scheme the two conditions are equivalent, the converse being formal.

## Implementation notes

The two quasi-coherence predicates are compared by
`SheafOfModules.IsQuasicoherentOnSite.isQuasicoherent`, whose hypothesis `UnivLE.{max u v r, r}`
is automatic here: the Zariski site of `T : Scheme.{u}` has its objects in `Type u`, its
morphisms in `Type u` and its structure sheaf in `CommRingCat.{u}`, so the hypothesis reads
`UnivLE.{u, u}`.  This is exactly why the argument does not transfer to a big site, where the
objects live one universe above the sections; see `not_univLE_succ`.

A `SheafOfModules.Presentation` is turned into a `SheafOfModules.HasGlobalPresentation` by
`SheafOfModules.Presentation.hasGlobalPresentation`, which raises the universe of the sections
and checks that the lift carries the two colimits of the presentation to colimits.

Only `Set.univ` is used as the spanning family of generators and only the whole kernel as the
family of relations, so the presentation produced is the tautological one.  A caller who wants a
smaller presentation — finitely many generators and relations, say — should use
`AlgebraicGeometry.presentationTilde` directly, which takes both families as arguments.

`Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec` is the same
statement as `quasicoherentPresentationOfIsoSpec` with the presentation wrapped in `Nonempty`;
it is a theorem and therefore cannot be used where data is wanted, so the construction is
performed again here.  Both are kept: the existing statement is the one Stacks 02KG consumes.

## What is not proved

This is the clause of Stacks 03DX on the small **Zariski** site of an affine scheme.  It does
*not* discharge the étale-chart form
`AlgebraicGeometry.Space.HasAffineChartPresentations`, which quantifies over the modules on the
slices of the small étale site of an algebraic space with sections in the enlarged universe
`max (u + 1) m`.  Two things separate the two statements.  First,
`SheafOfModules.IsQuasicoherentOnSite.isQuasicoherent`, the comparison with Mathlib's
quasi-coherence used here, is stated for a module whose sections lie in the universe of the
coefficient rings — `SheafOfModules.{r} R` over `R : Sheaf J RingCat.{r}` — which the enlarged
module universe over a `CommRingCat.{u}`-valued structure sheaf is not.  Second, the associated
module over the coordinate ring is `AlgebraicGeometry.tilde`, a construction on the Zariski site
of `Spec R` with no small-étale counterpart in Mathlib.  The small étale analogue is
Stacks 03DX(2) at `τ = étale`, reduced in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssentialImage` to essential
surjectivity of `𝓕 ↦ 𝓕^a`; that hypothesis still stands.

The clause of Stacks 03DX stating that `𝓕 ↦ 𝓕^a` is an equivalence onto the quasi-coherent
modules of a big or small τ-site is also not this one; see
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssentialImage`.  The Stacks
attribute below therefore carries a clause string naming the presentation clause and is never
written bare, as is the case for the separate clause
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffinePresentation

/-! ### The presentation, as data -/

/-- **On a scheme isomorphic to a spectrum, a quasi-coherent module has a presentation**, as
data.

Restricting along `e.inv` puts the module on `Spec R`, where quasi-coherence makes the counit
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ` invertible: the module *is* the module associated
with its module of global sections over `R`.  `AlgebraicGeometry.presentationTilde` presents
that associated module, taking every global section as a generator and every element of the
kernel of the resulting free cover as a relation, and the presentation is carried back along
`e.hom` by `AlgebraicGeometry.Scheme.Modules.presentationRestrict`. -/
noncomputable def quasicoherentPresentationOfIsoSpec {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (e : Y ≅ Spec R) (N : Y.Modules) [N.IsQuasicoherent] : N.Presentation := by
  have hqc : (N.restrict e.inv).IsQuasicoherent := inferInstance
  have hiso : IsIso (N.restrict e.inv).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ (N.restrict e.inv)).mp hqc
  have e₀ := asIso (N.restrict e.inv).fromTildeΓ
  have P₀ : (N.restrict e.inv).Presentation :=
    AffinePushforward.presentationOfIso e₀
      (presentationTilde.{u} _ Set.univ (by simp) _ (Submodule.span_eq _))
  have P₁ : ((N.restrict e.inv).restrict e.hom).Presentation :=
    Scheme.Modules.presentationRestrict e.hom P₀
  have iso : (N.restrict e.inv).restrict e.hom ≅ N :=
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app N ≪≫
      Scheme.Modules.restrictFunctorId.app N
  exact AffinePushforward.presentationOfIso iso P₁

/-- **On an affine scheme, a quasi-coherent module has a presentation**, as data: the previous
construction at the canonical isomorphism `AlgebraicGeometry.Scheme.isoSpec` with the spectrum
of the coordinate ring `Γ(T, ⊤)`. -/
noncomputable def quasicoherentPresentationOfIsAffine (T : Scheme.{u}) [IsAffine T]
    (M : T.Modules) [M.IsQuasicoherent] : M.Presentation :=
  quasicoherentPresentationOfIsoSpec T.isoSpec M

/-! ### The global presentation -/

/-- **A quasi-coherent module on an affine scheme has a global presentation.**  This is the
conclusion for Mathlib's `SheafOfModules.IsQuasicoherent`; see
`Stacks.AlgebraicGeometry.AffinePresentation.hasGlobalPresentation_of_isQuasicoherentOnSite`
for the predicate of Stacks 03DL(6).

The presentation of `quasicoherentPresentationOfIsAffine` is converted into the universal-property
form of Stacks 03DE(6) by `SheafOfModules.Presentation.hasGlobalPresentation`. -/
theorem hasGlobalPresentation_of_isQuasicoherent (T : Scheme.{u}) [IsAffine T]
    (M : SheafOfModules.{u} T.ringCatSheaf) (hM : M.IsQuasicoherent) :
    M.HasGlobalPresentation :=
  have := hM
  (quasicoherentPresentationOfIsAffine T M).hasGlobalPresentation

/-- **Stacks 03DX, the presentation step, on the Zariski site.**  A quasi-coherent
`𝒪_T`-module on an affine scheme `T` has a *global* presentation: it is the module associated
with a module over the coordinate ring `Γ(T, ⊤)`, and a presentation of that module by
generators and relations transports to a presentation of the sheaf over the whole of `T`.

Quasi-coherence here is `SheafOfModules.IsQuasicoherentOnSite`, Stacks 03DL(6), which asks only
for a presentation *locally*; the content of the step is that on an affine no covering is
needed.  The two quasi-coherence predicates agree on the Zariski site by
`SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite`, whose size hypothesis is automatic
there.

The clause string records exactly this much: a quasi-coherent module on an affine has a global
presentation.  Stacks 03DX states its clauses as equivalences of categories, and those are
carried by the declarations named in the module docstring, whose descent arguments consume what
is proved here; the same statement at an affine object of the big fppf site is
`AlgebraicGeometry.BigFppfOver.hasGlobalPresentation_over_of_isQuasicoherentOnSite`. -/
@[stacks 03DX "a quasi-coherent module on an affine has a global presentation",
  sga "6 0 2.5" "partial"]
theorem hasGlobalPresentation_of_isQuasicoherentOnSite (T : Scheme.{u}) [IsAffine T]
    (M : SheafOfModules.{u} T.ringCatSheaf) (hM : M.IsQuasicoherentOnSite) :
    M.HasGlobalPresentation :=
  hasGlobalPresentation_of_isQuasicoherent T M hM.isQuasicoherent

/-- **On an affine scheme, quasi-coherence is a global presentation.**  The forward direction is
the presentation clause of Stacks 03DX; the converse holds on any site, because the identity
covering witnesses quasi-coherence once a global presentation is available. -/
theorem isQuasicoherentOnSite_iff_hasGlobalPresentation (T : Scheme.{u}) [IsAffine T]
    (M : SheafOfModules.{u} T.ringCatSheaf) :
    M.IsQuasicoherentOnSite ↔ M.HasGlobalPresentation :=
  ⟨hasGlobalPresentation_of_isQuasicoherentOnSite T M,
    Stacks.SheafOfModules.isQuasicoherentOnSite_of_hasGlobalPresentation M⟩

end Stacks.AlgebraicGeometry.AffinePresentation

end
