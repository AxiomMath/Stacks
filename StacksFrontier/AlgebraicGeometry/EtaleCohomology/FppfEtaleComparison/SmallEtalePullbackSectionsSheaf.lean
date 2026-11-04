module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPullback

/-!
# The inverse image from the small étale site as a sheafified sections presheaf

Let `S` be a scheme in a chosen big fppf site `B` and let `𝓕` be a quasi-coherent `𝒪_S`-module.
On the one category `(Sch/S)` carrying the five localized topologies the inverse image along the
comparison morphism of ringed sites `((Sch/S)_τ, 𝒪) ⟶ (S_étale, 𝒪)` of `𝓕ᵃ` on `S_étale` is the
`τ`-sheafification of the pullback-sections presheaf `(f : T → S) ↦ Γ(T, f⁺𝓕)` of Stacks 03DS.

This is **strictly narrower than Stacks 070S part (3)**, which states the same identification for
an *arbitrary* sheaf of `𝒪`-modules `𝓖` on `S_étale` and the rule `(f : T → S) ↦ Γ(T, f_small^*𝓖)`
formed with the inverse image along the morphisms of ringed sites of Stacks 070R (2).  Here `𝓖` is
restricted to be the associated module `𝓕ᵃ` of a quasi-coherent module on the *scheme* `S`, and
the sections rule is then the one of Stacks 03DS, with no small-étale inverse image in it at all:
what makes the statement available is `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`
(Stacks 03FH (2)), which replaces `f_small^*(𝓕ᵃ)` by `(f^*𝓕)ᵃ`.  Accordingly **no
`@[stacks 070S]` attribute is claimed**.

For the source's own generality the sections rule has to be built as a presheaf of modules out
of `ε_f^*` itself, and **it now is**:
`AlgebraicGeometry.BigFppfOver.smallEtaleSectionsPresheafOfModules` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSectionsSheafTauBigSite.lean`
is the presheaf of `𝒪`-modules `(f : T → S) ↦ Γ(T, f_small^*𝓖)` on the big `τ`-site, for an
arbitrary sheaf of `𝒪`-modules `𝓖` on `S_étale`.  Both halves of its functoriality are proved:
the composition half is `AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleFinalPullbackUnitComposition.lean`
and the identity half is `AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp_id` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleFinalPullbackUnitIdentity.lean`.
What part (3) still needs is the
comparison of that presheaf's `τ`-sheafification with `(id_{τ,étale})^*𝓖`, i.e. the analogue for
it of the local-bijectivity ladder that
`StacksFrontier/AlgebraicGeometry/Descent/SectionsPullbackComparison/Comparison.lean` runs for
part (1).

## Main definitions

* `AlgebraicGeometry.BigFppfOver.smallEtalePullbackIsoSectionsSheafification`: the narrow
  statement, at every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` for which the inclusion of
  the small étale site is continuous.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind)
  [(smallEtaleToFppf B S hS).IsContinuous (SmallEtale.topology B.toBigEtaleSite S hS)
    (baseOverTopology B S hS τ)]
  (F : S.Modules) [F.IsQuasicoherent]

/-- **Stacks 070S part (3) for `𝓖 = 𝓕ᵃ` with `𝓕` quasi-coherent on the scheme `S`** — a strictly
narrower statement than the source's, which quantifies over an arbitrary sheaf of `𝒪`-modules on
`S_étale`; hence no `stacks` attribute.

The inverse image along `((Sch/S)_τ, 𝒪) ⟶ (S_étale, 𝒪)` of the associated module of `𝓕` on
`S_étale` is the `τ`-sheafification of the pullback-sections presheaf of Stacks 03DS.  The two
inputs are `AlgebraicGeometry.BigFppfOver.baseAssociatedSheafIsoSmallEtalePullback`, which
identifies that inverse image with `𝓕ᵃ` on `(Sch/S)_τ`, and
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`, which is **Stacks 070S part (1)**
and presents `𝓕ᵃ` on `(Sch/S)_τ` as that sheafification. -/
public def smallEtalePullbackIsoSectionsSheafification :
    (smallEtaleToBaseModulePullback B S hS τ).obj (smallEtaleAssociatedSheaf B S hS F) ≅
      (PresheafOfModules.sheafification.{u}
          (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).obj
        (sectionsPresheafOfModules B S hS F) :=
  baseAssociatedSheafIsoSmallEtalePullback B S hS τ F ≪≫
    (baseAssociatedModuleIsoBaseAssociatedSheaf B S hS τ F).symm ≪≫
      baseAssociatedModuleIsoSections B S hS τ F

end AlgebraicGeometry.BigFppfOver

end
