module

public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesReflect
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification

/-!
# The Comparison Lemma for modules on the big affine fppf site, at the unraised universe

Let `S` be a scheme inside a chosen big fppf site `B`. The affine objects of `(Sch/S)_fppf`
form a dense subsite, so restriction of sheaves of modules along the inclusion,
`AlgebraicGeometry.bigAffineFppfModuleRestriction`, is fully faithful with no hypothesis
(`AlgebraicGeometry.fullyFaithfulBigAffineFppfModuleRestriction`). **This file proves that it is
also essentially surjective**, hence an equivalence, at the universe `u` of the module sections
— the universe in which conditions (1)–(8) of Stacks 0GZV are stated.

That completes the implications **(1) ⇒ (7)** and **(1) ⇒ (8)** of Stacks 0GZV at `τ = fppf`:
condition (1) gives quasi-coherence on the affine subsite, which is condition (6), by
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_of_canonicalMap_isIso`; essential
surjectivity produces a module on the ambient site restricting to `𝓕`; and that ambient module
is automatically quasi-coherent by
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_reflect`. Condition (8) then follows from
condition (7) by the equivalence
`AlgebraicGeometry.bigAffineFppf_isRestrictionOfQuasicoherent_iff_isRestrictedAssociatedModule`.

## Main results

* `AlgebraicGeometry.bigAffineFppfModuleRestrictionEquivalence`: **the Comparison Lemma for
  sheaves of modules on the big affine fppf site, at the unraised module universe.** Essential
  surjectivity is the instance `Stacks.DenseSubsiteModules.essSurj_moduleRestriction`.
* `AlgebraicGeometry.bigAffineFppf_exists_moduleLift`: the existence statement on its own — every
  sheaf of `𝒪_Aff`-modules on `(Aff/S)_fppf` is the restriction of one on `(Sch/S)_fppf`.
* `AlgebraicGeometry.bigAffineFppf_isRestrictionOfQuasicoherent_of_canonicalMap_isIso`: **Stacks
  0GZV, (1) ⇒ (7) at `τ = fppf`.**
* `AlgebraicGeometry.bigAffineFppf_isRestrictedAssociatedModule_of_canonicalMap_isIso`: **Stacks
  0GZV, (1) ⇒ (8) at `τ = fppf`**, with the uniqueness of `𝒢`.

## Implementation notes

The whole content is the single limit hypothesis of Mathlib's Comparison Lemma,
`∀ X, HasLimitsOfShape (StructuredArrow X (BigAffineFppf.inclusion B S hS).op) AddCommGrpCat.{u}`.
Those structured-arrow categories do have their objects in `Type (u + 1)`, so they are not
`u`-small; but they are *essentially* `u`-small, and that is all
`CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` needs. Essential smallness comes
from `AlgebraicGeometry.essentiallySmall_bigAffineFppf` — the affine objects over `S` inside a
size-bounded category of schemes have only `u`-many isomorphism classes, which is Stacks 000J —
together with local smallness of `(Sch/S)_fppf`, whose morphisms are in `Type u`.

The same two inputs are already combined, for sheaves of **sets** at the same universe `u`, in
`AlgebraicGeometry.hasSheafifyBigFppfOver`; the step taken here is only to run that argument
with `AddCommGrpCat.{u}` in place of `Type u`, which is what
`Stacks.DenseSubsiteModules.essSurj_moduleRestriction` consumes. With `AddCommGrpCat.{u}` it is
already run for an affine base `S = Spec A`, in a private cohomology-vanishing lemma of
`StacksFrontier.AlgebraicGeometry.Topologies.Fppf.AffineBaseChangeDerived`; and the small-site
counterpart is `AlgebraicGeometry.SmallAffineEtale.hasLimitsOfShape_structuredArrow_addCommGrpCat`,
which is how the corresponding lift of Stacks 0GZX is obtained at `u`.

Accordingly the `u + 1` detour described by the coverage notes of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesReflect` and
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteAssociatedModuleUnique` — raising the
sections as `AlgebraicGeometry.uliftRingSheaf` does for Stacks 0GZU, then descending them along a
Zariski cover of each object by affine opens — is not needed: there is nothing to descend,
because the Comparison Lemma is available at `u` directly. Those notes located the obstruction
correctly on the existence side rather than the quasi-coherence side, but read non-smallness of
the index categories as an obstruction when only essential smallness was ever required. Stacks
0GZU remains recorded at the raised universe in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineRingedToposEquivalence`, which keeps a
free section universe `w`; nothing here replaces it.

## References

* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 0GZU](https://stacks.math.columbia.edu/tag/0GZU)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The affine objects of the big fppf site over `S` form an essentially small category, which
`AlgebraicGeometry.essentiallySmall_bigAffineFppf` proves; recorded here as an instance, which
is what the structured-arrow limits below need. -/
public instance essentiallySmallBigAffineFppf : EssentiallySmall.{u} (BigAffineFppf B S hS) :=
  essentiallySmall_bigAffineFppf B S hS

/-- The comma categories indexing the right Kan extension along the inclusion of the affine
objects of `(Sch/S)_fppf` have limits of abelian groups in the universe `u` of the sections:
they are essentially `u`-small, being structured-arrow categories on an essentially `u`-small
category over a locally `u`-small one, even though their objects lie in `Type (u + 1)`.

This is the abelian input to the Comparison Lemma for sheaves of modules along the inclusion of
the affine objects, and the big-site counterpart of
`AlgebraicGeometry.SmallAffineEtale.hasLimitsOfShape_structuredArrow_addCommGrpCat`. -/
public instance BigAffineFppf.hasLimitsOfShape_structuredArrow_addCommGrpCat
    (X : (BigFppfOver B S hS)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (BigAffineFppf.inclusion B S hS).op)
      AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- **Restriction of sheaves of modules to the big affine fppf site is an equivalence** at the
unraised universe `u`: this is Stacks 0GZU on modules, over the structure sheaf `𝒪` itself
rather than over a copy of it with its sections raised. -/
public noncomputable def bigAffineFppfModuleRestrictionEquivalence :
    SheafOfModules.{u} (BigFppfOver.structureSheaf B S hS) ≌
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O) :=
  (bigAffineFppfModuleRestriction B S hS).asEquivalence

/-- **Every sheaf of `𝒪_Aff`-modules on `(Aff/S)_fppf` is the restriction of a sheaf of
`𝒪`-modules on `(Sch/S)_fppf`**, at the unraised universe `u` of the module sections.

This is the input that condition (7) of Stacks 0GZV asks for besides quasi-coherence; the
quasi-coherence of the lift is then automatic, by
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_reflect`. -/
public theorem bigAffineFppf_exists_moduleLift
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O)) :
    ∃ M : SheafOfModules.{u} (BigFppfOver.structureSheaf B S hS),
      Nonempty (F ≅ (bigAffineFppfModuleRestriction B S hS).obj M) :=
  ⟨(bigAffineFppfModuleRestriction B S hS).objPreimage F,
    ⟨((bigAffineFppfModuleRestriction B S hS).objObjPreimageIso F).symm⟩⟩

/-- **Stacks 0GZV, (1) ⇒ (7) at `τ = fppf`.** A sheaf of `𝒪_Aff`-modules on `(Aff/S)_fppf` all
of whose base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms corresponds, under
the equivalence of ringed topoi of Stacks 0GZU, to a quasi-coherent module on `(Sch/S)_fppf`.

The three inputs are condition (6), by
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_of_canonicalMap_isIso`; the existence of
an ambient lift, by `AlgebraicGeometry.bigAffineFppf_exists_moduleLift`; and the quasi-coherence
of that lift, by `AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_reflect`. -/
@[stacks 0GZV "(1) ⇒ (7) at τ = fppf"]
public theorem bigAffineFppf_isRestrictionOfQuasicoherent_of_canonicalMap_isIso
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O))
    (h : ∀ ⦃U V : BigAffineFppf B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineFppfRingedSite B S hS) F f)) :
    BigAffineFppf.IsRestrictionOfQuasicoherent B S hS F :=
  (bigAffineFppf_isRestrictionOfQuasicoherent_iff_isQuasicoherentOnSite B S hS F).2
    ⟨bigAffineFppf_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS F h,
      bigAffineFppf_exists_moduleLift B S hS F⟩

/-- **Stacks 0GZV, (1) ⇒ (8) at `τ = fppf`**, with the uniqueness of `𝒢` included. A sheaf of
`𝒪_Aff`-modules on `(Aff/S)_fppf` all of whose base-change maps are isomorphisms is the
restriction to the affine objects of the associated module `𝒢^a` of a quasi-coherent
`𝒪_S`-module `𝒢`, unique up to isomorphism.

This is (1) ⇒ (7) followed by the equivalence of conditions (7) and (8),
`AlgebraicGeometry.bigAffineFppf_isRestrictionOfQuasicoherent_iff_isRestrictedAssociatedModule`.
-/
@[stacks 0GZV "(1) ⇒ (8) at τ = fppf, existence and uniqueness of 𝒢"]
public theorem bigAffineFppf_isRestrictedAssociatedModule_of_canonicalMap_isIso
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O))
    (h : ∀ ⦃U V : BigAffineFppf B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineFppfRingedSite B S hS) F f)) :
    BigAffineFppf.IsRestrictedAssociatedModule B S hS F :=
  bigAffineFppf_isRestrictedAssociatedModule_of_isRestrictionOfQuasicoherent B S hS F
    (bigAffineFppf_isRestrictionOfQuasicoherent_of_canonicalMap_isIso B S hS F h)

end AlgebraicGeometry

end
