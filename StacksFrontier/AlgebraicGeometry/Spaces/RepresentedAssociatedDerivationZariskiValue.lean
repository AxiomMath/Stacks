module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDerivationSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsInvertible

/-!
# The value of `d^a` at a Zariski open is a Zariski universal differential

Let `α : U ⟶ V` be a morphism of schemes of the big fppf site over `S`.
`AlgebraicGeometry.Space.transportedAssociatedDerivation` is the derivation `d^a` of
Stacks 04CS, read on the small étale site of the represented algebraic space `yoneda.obj U` and
over the spaces-level structure map, with values in
`AlgebraicGeometry.Space.representedAssociatedModule` of the Zariski sheaf of relative
differentials `Ω_{U/V}`.  **This file computes its values over the Zariski-open objects of that
site** in terms of `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation`, the universal
derivation `d_{U/V}` of `Ω_{U/V}` itself.

This is the link that joins the small-étale end of the comparison chain of Stacks 04CS to its
Zariski end.  The chain's small-étale end is settled on the spaces side — the chart-square
comparison carries `d_{Y/B}` to `d^a`,
`AlgebraicGeometry.Space.universalDerivation_chartSquareDifferentialsAssociatedIso` — and its
Zariski end is settled on Zariski global sections, by
`AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap_pullbackSection` and
`AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_postcomp_cotangentSheafIso_hom`.  What
the join needs is the element of `Γ(Ω_{U/V}, W)` whose image in the associated module is `d^a`,
and that is what the single statement below supplies.

## Main results

* `AlgebraicGeometry.Space.transportedAssociatedDerivation_d_opensToSmallEtale`: over the object
  of the small étale site of `yoneda.obj U` that an open `W` of the scheme underlying `U` names,
  `d^a` of a regular function `a` on `W` is the universal relative differential `d_{U/V} a`,
  pulled back to the open subscheme `W` by
  `AlgebraicGeometry.pullbackSectionHom` and read into the associated module through the
  isomorphism of Stacks 070S (2).

## Route

Nothing here is new mathematics; the statement is a transport of its scheme-level counterpart
across the identification of the two small étale sites.

* `AlgebraicGeometry.SmallEtale.universalRelativeDerivation_postcomp_sectionsUnit` is the same
  statement one level down: for a morphism of *schemes*, over the small Zariski site, it says
  that `d_{U/V}` followed by the section-pullback map
  `AlgebraicGeometry.SmallEtale.sectionsUnit` is the small Zariski restriction of `d^a` in its
  sections form, `AlgebraicGeometry.SmallEtale.associatedSectionsDerivation`.  Read at one open
  and one section by `PresheafOfModules.Derivation.congr_d`, that is the whole content.
* Carrying it up to the small étale site of `yoneda.obj U` costs nothing on values.
  `AlgebraicGeometry.Space.transportedAssociatedDerivation` is built from
  `AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation` by
  `AlgebraicGeometry.Space.transportDerivation` and
  `AlgebraicGeometry.Space.Derivation'.ofChartPullback`, and both leave the underlying additive
  map untouched — only the indexing object moves, and it moves back because
  `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_counit_app` is the identity.  So the
  two sides differ only by the component of the isomorphism of Stacks 070S (2) which converts
  `AlgebraicGeometry.SmallEtale.associatedSectionsDerivation` into
  `AlgebraicGeometry.SmallEtale.associatedDerivation`, and `congrArg` at that component finishes.

## Implementation notes

The statement is written at a variable open `W` and a variable section `a`, and the proof is a
single `congrArg` in term mode rather than a rewrite.  Both are deliberate.  The small étale site
of `yoneda.obj U` and the small étale site of the scheme underlying `U` are identified on the
nose, so the two spellings of the indexing object are definitionally equal but not syntactically
equal; a `rw` motive over them does not typecheck, while the term-mode chain checks in seconds.
For the same reason the identification is kept at the level of *objects* of the sites — an
equality of the transported sheaves of modules themselves, such as
`(representedModuleRestriction B S hS U).obj ((representedModulePushforward B S hS U).obj N) = N`,
is definitionally true but exhausts the heartbeat budget, because projecting it drags the whole
transported module structure through `whnf`.

No declaration here carries a `stacks` tag.  Computing the values of `d^a` is a step of the
identification of the spaces-level first arrow of Stacks 05ZA with the scheme-level first arrow
of Stacks 01UZ; it is not an assertion of either tag.  Stacks 04CS itself is registered on
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` and on
`AlgebraicGeometry.SmallEtale.differentialsIso`.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  two sheaves of differentials, whose derivation `d^a` is computed here.
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S), clause (2), the
  isomorphism between the associated module and its sections form.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), clause (4), the
  associated module on the small étale site.
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM), the universal property
  of the Zariski sheaf of relative differentials.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {U V : BigFppfOver B S hS}

/-- **The value of `d^a` at a Zariski-open object of the small étale site is a Zariski universal
differential.**  Let `α : U ⟶ V` be a morphism of schemes of the big fppf site over `S`, let `W`
be an open of the scheme underlying `U` and let `a` be a regular function on `W`.  The associated
derivation `AlgebraicGeometry.Space.transportedAssociatedDerivation` of Stacks 04CS, evaluated at
`a` over the object of the small étale site of `yoneda.obj U` that `W` names, is the universal
relative differential `d_{U/V} a` of `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation`,
pulled back to the open subscheme `W` by `AlgebraicGeometry.pullbackSectionHom` and read into the
associated module through the inverse of the isomorphism of Stacks 070S (2).

This is the transport of
`AlgebraicGeometry.SmallEtale.universalRelativeDerivation_postcomp_sectionsUnit` — the same
statement for a morphism of schemes over the small Zariski site — across the identification of
the small étale site of the scheme underlying `U` with that of `yoneda.obj U`.  The transport
changes no value: `AlgebraicGeometry.Space.transportDerivation` and
`AlgebraicGeometry.Space.Derivation'.ofChartPullback` both leave the underlying additive map
untouched, so the two sides differ only by the component of Stacks 070S (2) which carries the
sections form `AlgebraicGeometry.SmallEtale.associatedSectionsDerivation` of `d^a` to
`AlgebraicGeometry.SmallEtale.associatedDerivation`. -/
theorem transportedAssociatedDerivation_d_opensToSmallEtale (α : U ⟶ V)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, W)) :
    (transportedAssociatedDerivation B S hS α).d
        (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)))
        (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op W)).hom a) =
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf
            (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α))).inv.val.app
          (op ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))).hom
        (_root_.AlgebraicGeometry.pullbackSectionHom W.ι
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α)) W ⊤
          (Scheme.Opens.top_le_ι_preimage le_rfl)
          ((Scheme.Hom.universalRelativeDerivation
            ((BigFppfOver.toScheme B S hS).map α)).d a)) :=
  congrArg
    (fun y => ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf
            (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α))).inv.val.app
          (op ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))).hom y)
    (PresheafOfModules.Derivation.congr_d
      (_root_.AlgebraicGeometry.SmallEtale.universalRelativeDerivation_postcomp_sectionsUnit
        (associatedBigEtaleSite B) U.left.property
        ((BigFppfOver.toScheme B S hS).map α)) a).symm

end AlgebraicGeometry.Space

end
