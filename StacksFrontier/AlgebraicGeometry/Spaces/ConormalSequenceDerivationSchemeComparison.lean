module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDerivationBothEnds

/-!
# The first arrow of the conormal sequence read through the whole comparison of Stacks 04CS

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDerivationBothEnds.lean` reads the
derivation that induces the first arrow of Stacks 05ZA through
`AlgebraicGeometry.Space.schemeDifferentialsIso`, which is only the **first factor** of the
comparison of Stacks 04CS: it lands on `Ω_{U_étale/V_étale}`, transported to the small étale
site of `yoneda.obj U`, and not on the associated module of the Zariski sheaf of differentials
`Ω_{U/V}` that `Stacks.ConormalSequenceRight.conormalDifferentialTranspose` is written over.

**This file reads it through the whole comparison.**  For a morphism `α : U ⟶ V` of schemes of
the big fppf site over `S`, `AlgebraicGeometry.Space.representedAssociatedDifferentialsIso` is
the composite isomorphism `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` is
built from, named rather than produced inside a `Nonempty`:
```
  Ω_{yoneda U/yoneda V} ≅ (Ω_{U/V})^a
```
with `(-)^a` the associated module of Stacks 03DU (4) read on the small étale site of
`yoneda.obj U`, that is `AlgebraicGeometry.Space.representedAssociatedModule`.  Its
compatibility with the universal derivations is the composite of the two factors':
`AlgebraicGeometry.Space.postcomp_schemeDifferentialsHom` and
`AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_hom`.  Feeding it to
`AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_map_map` reads the spaces-side
derivation, and then the spaces-side value formula of the first arrow, in the vocabulary of the
Zariski side.

## Main definitions

* `AlgebraicGeometry.Space.representedAssociatedDifferentialsIso`: the comparison isomorphism of
  Stacks 04CS at a morphism of schemes of the site, as a named isomorphism onto
  `AlgebraicGeometry.Space.representedAssociatedModule` of `Ω_{U/V}`.
* `AlgebraicGeometry.Space.transportedAssociatedDerivation`: the associated derivation `d^a` of
  Stacks 04CS, read on the small étale site of `yoneda.obj U` and over the spaces-level
  structure map, which is the derivation the comparison carries `d_{yoneda U/yoneda V}` to.

## Main results

* `AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_inv`:
  `AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_hom` read through the inverse — the
  inverse of the canonical isomorphism of Stacks 04CS carries the universal
  `V_étale`-derivation back to `d^a`.
* `AlgebraicGeometry.Space.postcomp_representedAssociatedDifferentialsIso`: **the comparison
  isomorphism carries the spaces-level universal derivation to `d^a`.**
* `AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_representedAssociatedDifferentialsIso`:
  **the derivation inducing the first arrow of Stacks 05ZA, read through the whole
  comparison.**  For a morphism `φ : X' ⟶ yoneda.obj U` of algebraic spaces,
  `d_{yoneda U/yoneda V}` followed by the unit of `φ^* ⊣ φ_*`, read through `φ_*φ^*` of the
  comparison, is `d^a` followed by that same unit.
* `kernelIdealUnitDifferential_val_app_apply_representedAssociatedDifferentialsIso`, in the
  namespace `AlgebraicGeometry.Space` and written without the prefix so that it fits:
  **the value formula of the first arrow in the Zariski side's vocabulary.**  Read through the
  comparison, the value of `AlgebraicGeometry.Space.kernelIdealUnitDifferential` on a local
  section `a` of the kernel ideal sheaf of `φ` is the unit of `φ^* ⊣ φ_*` applied to `d^a a`.
  This is the shape `Stacks.ConormalSequenceRight.conormalDifferentialTranspose_val_app` is
  written in, with the target now the associated module of the Zariski `Ω_{U/V}`.

## Route

Everything is an instance of a general statement already in the library.

* The isomorphism is the one inside
  `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`, so nothing new is built: its
  two factors are `AlgebraicGeometry.Space.schemeDifferentialsIso` (Stacks 04CS spaces-side, the
  transport along the identification of the small étale site of `yoneda.obj U` with that of the
  scheme underlying `U`) and `AlgebraicGeometry.SmallEtale.differentialsIso` (Stacks 04CS
  scheme-side, `(Ω_{U/V})^a ≅ Ω_{U_étale/V_étale}`).
* The derivation is `AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation` transported by
  `AlgebraicGeometry.Space.transportDerivation` and re-based over the spaces-level structure map
  by `AlgebraicGeometry.Space.Derivation'.ofChartPullback`, exactly as
  `AlgebraicGeometry.Space.transportedUniversalDerivation` is built from
  `AlgebraicGeometry.SmallEtale.universalDerivation`; the vanishing condition the re-basing asks
  for is discharged by the same two inputs,
  `AlgebraicGeometry.Space.transportDerivation_d_chartPullback_eq_zero` and
  `AlgebraicGeometry.SmallEtale.d_structureSharp_eq_zero`.
* The compatibility is proved on values: the transport of a derivation and
  `AlgebraicGeometry.Space.Derivation'.ofChartPullback` both leave the underlying additive map
  untouched, so after `PresheafOfModulesOfCommRing.Derivation.ext` the goal is the two factors'
  compatibilities applied in turn, each by
  `PresheafOfModulesOfCommRing.Derivation.congr_d`.
* The last two statements are
  `AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_map_map` and
  `AlgebraicGeometry.Space.kernelIdealUnitDifferential_val_app_apply_map_map` — which are stated
  for an *arbitrary* comparison of the sheaves of differentials compatible with the universal
  derivations precisely so that they can be instantiated here — at this comparison.

## Implementation notes

`AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_inv` is proved here rather than beside
`AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_hom`: it is needed only by this file, and
stating it in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentialsIso.lean` puts it
upstream of a hundred and thirty modules that do not use it.

The morphism of algebraic spaces `φ` is a variable in the last two statements, for the reason the
implementation notes of `AlgebraicGeometry.Space.pullbackUnitDerivation` record: at a concrete
morphism of small étale ringed topoi the coefficient module of that derivation does not elaborate
against the one the adjunction writes through the composite functor.

No declaration here carries a `stacks` tag.  Reading the first arrow through the comparison of
Stacks 04CS is a step of the identification of the spaces-level first arrow of Stacks 05ZA with
the scheme-level first arrow of Stacks 01UZ, which the proof of Stacks 05ZB needs; it is not an
assertion of any of those tags.  Stacks 04CS itself is registered on
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` and on
`AlgebraicGeometry.SmallEtale.differentialsIso`.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  two sheaves of differentials, which this file reads the first arrow through.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the universal derivation
  and its universal property.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), clause (4), the
  associated module on the small étale site.
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence
  whose first arrow is read here, and
  [Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), its scheme-level counterpart.
* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), the tag whose proof the
  identification of the two first arrows serves.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- **Stacks 04CS, compatibility with the universal derivations, read through the inverse**: the
inverse of the canonical isomorphism `(Ω_{X/Y})^a ≅ Ω_{X_étale/Y_étale}` carries the universal
`Y_étale`-derivation back to `d^a`.

This is `AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_hom` composed with the inverse,
the composite of the two directions of the isomorphism being the identity. -/
theorem postcomp_differentialsIso_inv :
    (universalDerivation B f).postcomp (differentialsIso B f).inv.val =
      etaleAssociatedDerivation B f := by
  refine Eq.trans (congrArg (fun D => PresheafOfModulesOfCommRing.Derivation.postcomp D
    (differentialsIso B f).inv.val) (postcomp_differentialsIso_hom B f).symm) ?_
  refine Eq.trans (PresheafOfModules.Derivation.postcomp_postcomp
    (etaleAssociatedDerivation B f) (differentialsIso B f).hom.val
    (differentialsIso B f).inv.val).symm ?_
  refine Eq.trans (congrArg (fun m => (etaleAssociatedDerivation B f).postcomp m)
    (congrArg SheafOfModules.Hom.val (differentialsIso B f).hom_inv_id)) ?_
  exact PresheafOfModulesOfCommRing.Derivation.ext (funext fun _ => AddMonoidHom.ext fun _ => rfl)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {U V : BigFppfOver B S hS}

/-- **The comparison isomorphism of Stacks 04CS at a morphism of schemes of the site, named.**
For `α : U ⟶ V` the spaces-level sheaf of differentials of `α` read as a morphism of represented
algebraic spaces is the associated module of Stacks 03DU (4) of the Zariski sheaf of relative
differentials `Ω_{U/V}`, read on the small étale site of `yoneda.obj U`.

This is the isomorphism inside `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`,
which produces it under a `Nonempty`; it is named here because a comparison of the two first
arrows of the conormal sequence has to read a derivation and a value formula through it.  Its
two factors are `AlgebraicGeometry.Space.schemeDifferentialsIso` and
`AlgebraicGeometry.SmallEtale.differentialsIso`. -/
noncomputable def representedAssociatedDifferentialsIso (α : U ⟶ V) :
    sheafOfDifferentials B S hS (schemeSpaceMap α) ≅
      (representedAssociatedModule B S hS U (schemeSpace U).property).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α)) :=
  schemeDifferentialsIso B S hS α ≪≫
    (representedModulePushforward B S hS U).mapIso
      (_root_.AlgebraicGeometry.SmallEtale.differentialsIso (associatedBigEtaleSite B)
        α.left).symm

/-- **`d^a`, read on the small étale site of `yoneda.obj U` and over the spaces-level structure
map.**  The associated derivation
`AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation` of Stacks 04CS is a derivation of the
structure sheaf of the small étale site of the scheme underlying `U` with values in
`(Ω_{U/V})^a`; transported along the identification of that site with the small étale site of
`yoneda.obj U` and re-based over `AlgebraicGeometry.Space.structureSharpInverseImage`, it is a
`yoneda.obj V`-derivation with values in
`AlgebraicGeometry.Space.representedAssociatedModule` of `Ω_{U/V}`.

This is built exactly as `AlgebraicGeometry.Space.transportedUniversalDerivation` is built from
`AlgebraicGeometry.SmallEtale.universalDerivation`, and it is the derivation that
`AlgebraicGeometry.Space.representedAssociatedDifferentialsIso` carries the spaces-level
universal derivation to. -/
noncomputable def transportedAssociatedDerivation (α : U ⟶ V) :
    PresheafOfModulesOfCommRing.Derivation' (R := structurePresheaf B S hS (yoneda.obj U))
      ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α))).val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom :=
  Derivation'.ofChartPullback B S hS (schemeSpaceMap α)
    (transportDerivation B S hS U
      (_root_.AlgebraicGeometry.SmallEtale.etaleStructureMap (associatedBigEtaleSite B)
        α.left).hom
      (_root_.AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation (associatedBigEtaleSite B)
        α.left))
    (transportDerivation_d_chartPullback_eq_zero B S hS α
      (_root_.AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation (associatedBigEtaleSite B)
        α.left)
      (fun W t => _root_.AlgebraicGeometry.SmallEtale.d_structureSharp_eq_zero
        (associatedBigEtaleSite B) α.left
        (_root_.AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation
          (associatedBigEtaleSite B) α.left)
        (fun _ s => PresheafOfModulesOfCommRing.Derivation'.d_app _ s) W t))

/-- **The comparison isomorphism of Stacks 04CS carries the universal derivation to `d^a`.**
This is the compatibility of
`AlgebraicGeometry.Space.representedAssociatedDifferentialsIso` with the universal derivations,
and it is the composite of its two factors' compatibilities:
`AlgebraicGeometry.Space.postcomp_schemeDifferentialsHom` and
`AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_inv`.

The transport of a derivation and `AlgebraicGeometry.Space.Derivation'.ofChartPullback` both
leave the underlying additive map untouched, so the two compatibilities compose on values with
no further identification. -/
theorem postcomp_representedAssociatedDifferentialsIso (α : U ⟶ V) :
    (universalDerivation B S hS (schemeSpaceMap α)).postcomp
        (representedAssociatedDifferentialsIso B S hS α).hom.val =
      transportedAssociatedDerivation B S hS α := by
  refine PresheafOfModulesOfCommRing.Derivation.ext (funext fun W => AddMonoidHom.ext fun x => ?_)
  change ((((representedModulePushforward B S hS U).map
      (_root_.AlgebraicGeometry.SmallEtale.differentialsIso (associatedBigEtaleSite B)
        α.left).inv).val.app W)).hom
      (((schemeDifferentialsHom B S hS α).val.app W).hom
        ((universalDerivation B S hS (schemeSpaceMap α)).d x)) = _
  refine Eq.trans (congrArg (fun y => ((((representedModulePushforward B S hS U).map
      (_root_.AlgebraicGeometry.SmallEtale.differentialsIso (associatedBigEtaleSite B)
        α.left).inv).val.app W)).hom y)
    (PresheafOfModulesOfCommRing.Derivation.congr_d (postcomp_schemeDifferentialsHom B S hS α)
      x)) ?_
  exact PresheafOfModulesOfCommRing.Derivation.congr_d
    (_root_.AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_inv (associatedBigEtaleSite B)
      α.left)
    (X := op ((representedSmallEtaleEquivalence B S hS U).functor.obj W.unop)) x

/-- **The derivation that induces the first arrow of Stacks 05ZA, read through the whole
comparison of Stacks 04CS.**  For a morphism `α : U ⟶ V` of schemes of the site and a morphism
`φ : X' ⟶ yoneda.obj U` of algebraic spaces, the spaces-level universal derivation followed by
the unit of `φ^* ⊣ φ_*` (`AlgebraicGeometry.Space.pullbackUnitDerivation`), read through
`φ_*φ^*` of `AlgebraicGeometry.Space.representedAssociatedDifferentialsIso`, is `d^a` followed
by that same unit.

This is `AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_map_map` at the comparison;
`AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_schemeDifferentialsIso` is the same
statement at its first factor alone, whose target is `Ω_{U_étale/V_étale}` rather than the
associated module of the Zariski `Ω_{U/V}`. -/
theorem pullbackUnitDerivation_postcomp_representedAssociatedDifferentialsIso (α : U ⟶ V)
    {X' : AlgebraicSpaces B S hS} (φ : X' ⟶ schemeSpace U) :
    (pullbackUnitDerivation B S hS φ (schemeSpaceMap α)).postcomp
        ((modulePushforward B S hS φ).map
          ((modulePullback B S hS φ).map
            (representedAssociatedDifferentialsIso B S hS α).hom)).val =
      (transportedAssociatedDerivation B S hS α).postcomp
        ((modulePullbackAdjunction B S hS φ).unit.app
          ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
            (Scheme.Hom.relativeDifferentials
              ((BigFppfOver.toScheme B S hS).map α)))).val :=
  pullbackUnitDerivation_postcomp_map_map B S hS φ (schemeSpaceMap α)
    ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
      (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α)))
    (representedAssociatedDifferentialsIso B S hS α).hom
    (transportedAssociatedDerivation B S hS α)
    (postcomp_representedAssociatedDifferentialsIso B S hS α)

/-- **The value formula of the first arrow of Stacks 05ZA in the Zariski side's vocabulary.**
Read through `φ_*φ^*` of `AlgebraicGeometry.Space.representedAssociatedDifferentialsIso`, the
value of `AlgebraicGeometry.Space.kernelIdealUnitDifferential` on a local section `a` of the
kernel ideal sheaf of `φ` is the unit of `φ^* ⊣ φ_*` applied to `d^a a`.

That is the shape `Stacks.ConormalSequenceRight.conormalDifferentialTranspose_val_app` is
written in — the unit of a pullback–pushforward adjunction applied to the universal differential
of the section — now with the target the associated module of the Zariski `Ω_{U/V}`, which is
the module the scheme-level transpose is a morphism into. -/
theorem kernelIdealUnitDifferential_val_app_apply_representedAssociatedDifferentialsIso
    (α : U ⟶ V) {X' : AlgebraicSpaces B S hS} (φ : X' ⟶ schemeSpace U)
    (W : (SmallEtale B S hS (schemeSpace U).1)ᵒᵖ)
    (x : (kernelIdealSheaf B S hS φ).toSheafOfModules.val.obj W) :
    (ModuleCat.Hom.hom (((modulePushforward B S hS φ).map
          ((modulePullback B S hS φ).map
            (representedAssociatedDifferentialsIso B S hS α).hom)).val.app W))
        ((ModuleCat.Hom.hom
          ((kernelIdealUnitDifferential B S hS φ (schemeSpaceMap α)).val.app W)) x) =
      (ModuleCat.Hom.hom (((modulePullbackAdjunction B S hS φ).unit.app
            ((representedAssociatedModule B S hS U (schemeSpace U).property).obj
              (Scheme.Hom.relativeDifferentials
                ((BigFppfOver.toScheme B S hS).map α)))).val.app W))
        ((transportedAssociatedDerivation B S hS α).d x.1) :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    (pullbackUnitDerivation_postcomp_representedAssociatedDifferentialsIso B S hS α φ) x.1

end AlgebraicGeometry.Space

end
