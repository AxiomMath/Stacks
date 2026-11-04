module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteCoarserDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteModuleComparisonLemma
public import StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteQuasicoherentCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence

/-!
# Conditions (7) and (8) of Stacks 0GZV at all five topologies

Let `S` be a scheme inside a chosen big fppf site `B` and let `𝓕` be a sheaf of `𝒪_Aff`-modules
on the big affine `τ`-site `(Aff/S)_τ`, for one of the five topologies `τ` that `B` carries.
Condition (7) of Stacks 0GZV says that `𝓕` corresponds, under the equivalence of ringed topoi of
Stacks 0GZU, to a quasi-coherent module on `(Sch/S)_τ`; condition (8) says that `𝓕` arises from a
**unique** quasi-coherent `𝒪_S`-module `𝒢` by the construction of Descent, Section 35.8, that is,
is the restriction to the affine objects of `𝒢^a`.

`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteAssociatedModuleUnique` and
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteModuleComparisonLemma` prove **(1) ⇒ (7)**,
**(1) ⇒ (8)** and **(7) ⇔ (8)** at `τ = fppf`.  This file proves all of them at the four coarser
`τ` as well, so that conditions (7) and (8) are equivalent to one another, and to condition (1),
at every one of the five topologies.

## The argument

Everything rests on the dense-subsite inclusion of the affine objects at `τ`,
`AlgebraicGeometry.BigAffineFppf.inclusion_isDenseSubsite`.  Given it:

* restriction of sheaves of modules along the inclusion is **fully faithful** at `τ`, which with
  Stacks 0GN7 for the big `τ`-site gives the *uniqueness* of `𝒢` in condition (8);
* **(8) ⇒ (7)** is Stacks 03DV (1) at `τ`, which holds at every `τ`;
* restriction is moreover an **equivalence** at `τ`, by the Comparison Lemma for sheaves of
  modules — its limit hypothesis is `AlgebraicGeometry.BigAffineFppf`
  `.hasLimitsOfShape_structuredArrow_addCommGrpCat`, which depends on the *category* of affine
  objects only and so is the same instance at all five `τ`.  With the reflection of
  quasi-coherence along the inclusion this gives **(1) ⇒ (7)**, and the converse **(7) ⇒ (1)** is
  the restriction of a quasi-coherent module being quasi-coherent together with Stacks 0H04;
* **(1) ⇒ (8)** passes through `τ = fppf`.  A quasi-coherent module on `(Aff/S)_τ` is cartesian,
  and a cartesian module on the affine objects satisfies the *fppf* sheaf axiom by flat descent,
  `AlgebraicGeometry.bigAffineFppf_isSheaf_of_cartesian`; so `𝓕` is a sheaf of modules on
  `(Aff/S)_fppf` with the same underlying presheaf, where (1) ⇒ (8) is proved.  The resulting
  `𝒢^a|_{(Aff/S)_fppf}`, read back for `τ`, is `𝒢^a` computed on `(Sch/S)_τ` restricted to the
  affine objects, by Stacks 0GNE —
  `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso`.

The last step is what makes (7) ⇒ (8) available at the coarser `τ` without clause (1) of
Descent, Proposition 03DX there: the route goes (7) ⇒ (1) ⇒ (8) and never asks whether a
quasi-coherent module on `(Sch/S)_τ` is an fppf sheaf.

## Main definitions

* `AlgebraicGeometry.bigAffineRingedSiteOf`: the ringed site `((Aff/S)_τ, 𝒪_Aff)`.  At each `τ`
  it is the big affine `τ`-ringed site of
  `StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines`, on the nose.
* `AlgebraicGeometry.bigAffineModuleRestrictionOf`: restriction of sheaves of modules from
  `(Sch/S)_τ` to `(Aff/S)_τ`.
* `AlgebraicGeometry.bigAffineAssociatedModuleQcohOf`: the functor `𝒢 ↦ 𝒢^a|_{(Aff/S)_τ}` of
  condition (8).
* `AlgebraicGeometry.BigAffineFppf.IsRestrictionOfQuasicoherentOf` and
  `AlgebraicGeometry.BigAffineFppf.IsRestrictedAssociatedModuleOf`: conditions (7) and (8) at
  `τ`, as predicates on `𝓕`.

## Main results

* `AlgebraicGeometry.fullyFaithfulBigAffineAssociatedModuleQcohOf` and
  `AlgebraicGeometry.bigAffine_iso_of_associatedModuleQcohOf_restriction_iso`: **Stacks 0GZV, the
  uniqueness of `𝒢` in condition (8), at every `τ`.**
* `AlgebraicGeometry.bigAffine_isRestrictionOfQuasicoherentOf_of_isRestrictedAssociatedModuleOf`:
  **Stacks 0GZV, (8) ⇒ (7) at every `τ`.**
* `AlgebraicGeometry.bigAffine_isRestrictionOfQuasicoherentOf_of_canonicalMap_isIso` and
  `AlgebraicGeometry.bigAffine_isIso_canonicalMapOf_of_isRestrictionOfQuasicoherentOf`:
  **Stacks 0GZV, (1) ⇔ (7) at every `τ`.**
* `AlgebraicGeometry.bigAffine_isRestrictedAssociatedModuleOf_of_canonicalMap_isIso`:
  **Stacks 0GZV, (1) ⇒ (8) at every `τ`**, uniqueness of `𝒢` included.
* `AlgebraicGeometry.bigAffine_isRestrictionOfQuasicoherentOf_iff_isRestrictedAssociatedModuleOf`:
  **Stacks 0GZV, conditions (7) and (8) are equivalent, at every `τ`.**

## Implementation notes

The five big affine `τ`-ringed sites of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines` are stated for
independently chosen big `τ`-sites.  Instantiated at the big `τ`-sites that `B` itself carries,
`AlgebraicGeometry.BigFppfSite.toBigZariskiSite` and its three companions, they become the
`AlgebraicGeometry.bigAffineRingedSiteOf` of this file **by `rfl`** — same category, same
topology, same structure presheaf — which is how the per-`τ` statements of that file and of
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteQuasicoherentCartesian` are used here.

The sheaf axiom produced by flat descent is stated at module sections in `Type (max m (u + 1))`,
because it is transported along the forgetful functor to types and the objects of `(Aff/S)_τ`
live in `Type (u + 1)`, while conditions (1)–(8) are stated at sections in `Type u`.  The gap is
crossed by `SheafOfModules.uliftForPresentation` in one direction and
`CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp` along `AddCommGrpCat.uliftFunctor` — which
reflects limits — in the other; no hypothesis is added.

## References

* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 0GZU](https://stacks.math.columbia.edu/tag/0GZU)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The ringed site `((Aff/S)_τ, 𝒪_Aff)` -/

/-- The big affine `τ`-site of `S` with the restriction of the sheaf of global functions as its
structure sheaf, for each of the five topologies a big fppf site carries. -/
public noncomputable abbrev bigAffineRingedSiteOf (τ : SiteKind) : RingedSite.{u + 1, u, u} :=
  affineRingedSite (BigAffineFppf.topologyOf B S hS τ)
    (BigFppfOver.baseOverTopology B S hS τ) (BigAffineFppf.inclusion B S hS)
    (FibredSite.baseStructureSheaf B S hS τ)

/-- At `τ = fppf` the ringed site is the big affine fppf one of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines`. -/
public theorem bigAffineRingedSiteOf_fppf :
    bigAffineRingedSiteOf B S hS .fppf = bigAffineFppfRingedSite B S hS := rfl

/-- At `τ = Zariski` the ringed site is the big affine Zariski one of the big Zariski site that
`B` carries. -/
public theorem bigAffineRingedSiteOf_zariski :
    bigAffineRingedSiteOf B S hS .zariski =
      bigAffineZariskiRingedSite B.toBigZariskiSite S hS := rfl

/-- At `τ = étale` the ringed site is the big affine étale one of the big étale site that `B`
carries. -/
public theorem bigAffineRingedSiteOf_etale :
    bigAffineRingedSiteOf B S hS .etale = bigAffineEtaleRingedSite B.toBigEtaleSite S hS := rfl

/-- At `τ = smooth` the ringed site is the big affine smooth one of the big smooth site that `B`
carries. -/
public theorem bigAffineRingedSiteOf_smooth :
    bigAffineRingedSiteOf B S hS .smooth = bigAffineSmoothRingedSite B.toBigSmoothSite S hS := rfl

/-- At `τ = syntomic` the ringed site is the big affine syntomic one of the big syntomic site
that `B` carries. -/
public theorem bigAffineRingedSiteOf_syntomic :
    bigAffineRingedSiteOf B S hS .syntomic =
      bigAffineSyntomicRingedSite B.toBigSyntomicSite S hS := rfl

/-- The big affine fppf ringed site, read with the coarser `τ`-topology, is the big affine
`τ`-ringed site: one category, one structure presheaf, two sheaf conditions. -/
public theorem ofLE_bigAffineFppfRingedSite (τ : SiteKind) :
    (bigAffineFppfRingedSite B S hS).ofLE (BigAffineFppf.topologyOf_le_topology B S hS τ) =
      bigAffineRingedSiteOf B S hS τ := rfl

/-! ### Restriction of sheaves of modules to the affine objects, at `τ` -/

/-- Restriction of sheaves of modules from `(Sch/S)_τ` to `(Aff/S)_τ`, taken over the restricted
structure sheaf.  This is the functor induced on modules by the equivalence of ringed topoi of
Stacks 0GZU for the topology `τ`. -/
public noncomputable abbrev bigAffineModuleRestrictionOf (τ : SiteKind) :=
  Stacks.DenseSubsiteModules.moduleRestriction (BigAffineFppf.topologyOf B S hS τ)
    (BigFppfOver.baseOverTopology B S hS τ) (BigAffineFppf.inclusion B S hS)
    (FibredSite.baseRingStructureSheaf B S hS τ)

/-- The structure sheaf over which `AlgebraicGeometry.bigAffineModuleRestrictionOf` takes its
values is the one the big affine `τ`-ringed site carries. -/
public theorem ringRestriction_baseRingStructureSheaf (τ : SiteKind) :
    Stacks.DenseSubsiteModules.ringRestriction (BigAffineFppf.topologyOf B S hS τ)
        (BigFppfOver.baseOverTopology B S hS τ) (BigAffineFppf.inclusion B S hS)
        (FibredSite.baseRingStructureSheaf B S hS τ) =
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O) := rfl

/-- **Restriction of sheaves of modules to `(Aff/S)_τ` is fully faithful**, with no hypothesis:
the inclusion of the affine objects is a dense subsite inclusion at every `τ`, and the
Comparison Lemma for sheaves of modules needs nothing more for full faithfulness. -/
public noncomputable def fullyFaithfulBigAffineModuleRestrictionOf (τ : SiteKind) :
    (bigAffineModuleRestrictionOf B S hS τ).FullyFaithful :=
  .ofFullyFaithful _

/-- **Every sheaf of `𝒪_Aff`-modules on `(Aff/S)_τ` is the restriction of a sheaf of
`𝒪`-modules on `(Sch/S)_τ`**, at the unraised universe `u` of the module sections. -/
public theorem bigAffine_exists_moduleLiftOf (τ : SiteKind)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O)) :
    ∃ M : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ),
      Nonempty (F ≅ (bigAffineModuleRestrictionOf B S hS τ).obj M) :=
  ⟨(bigAffineModuleRestrictionOf B S hS τ).objPreimage F,
    ⟨((bigAffineModuleRestrictionOf B S hS τ).objObjPreimageIso F).symm⟩⟩

/-! ### Quasi-coherence along the inclusion, at `τ` -/

/-- **The restriction to `(Aff/S)_τ` of a quasi-coherent module on `((Sch/S)_τ, 𝒪)` is
quasi-coherent.** -/
public theorem bigAffine_isQuasicoherentOnSite_restrictionOf (τ : SiteKind)
    (M : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))
    (hM : M.IsQuasicoherentOnSite) :
    ((bigAffineModuleRestrictionOf B S hS τ).obj M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite
    (BigAffineFppf.inclusion B S hS) (FibredSite.baseRingStructureSheaf B S hS τ) M hM

/-- **Quasi-coherence reflects along restriction to `(Aff/S)_τ`.** -/
public theorem bigAffine_isQuasicoherentOnSite_reflectOf (τ : SiteKind)
    (M : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))
    (hM : ((bigAffineModuleRestrictionOf B S hS τ).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_restriction
    (BigAffineFppf.inclusion B S hS) (FibredSite.baseRingStructureSheaf B S hS τ) M hM

/-- **Stacks 0GZV, each of conditions (2)–(6) implies condition (1), uniformly in `τ`.** A sheaf
of `𝒪_Aff`-modules on `(Aff/S)_τ` which is quasi-coherent there has all its base-change maps
`𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` isomorphisms.

This is the `SiteKind`-indexed packaging of
`AlgebraicGeometry.bigAffineFppf_isIso_canonicalMap_of_isQuasicoherentOnSite` and its four
counterparts, each read at the big `τ`-site that `B` carries. -/
public theorem bigAffine_isIso_canonicalMapOf_of_isQuasicoherentOnSite (τ : SiteKind)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O))
    (hM : M.IsQuasicoherentOnSite) {U V : BigAffineFppf B S hS} (f : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineRingedSiteOf B S hS τ) M f) := by
  cases τ with
  | zariski =>
      exact bigAffineZariski_isIso_canonicalMap_of_isQuasicoherentOnSite
        B.toBigZariskiSite S hS M hM f
  | etale =>
      exact bigAffineEtale_isIso_canonicalMap_of_isQuasicoherentOnSite
        B.toBigEtaleSite S hS M hM f
  | smooth =>
      exact bigAffineSmooth_isIso_canonicalMap_of_isQuasicoherentOnSite
        B.toBigSmoothSite S hS M hM f
  | syntomic =>
      exact bigAffineSyntomic_isIso_canonicalMap_of_isQuasicoherentOnSite
        B.toBigSyntomicSite S hS M hM f
  | fppf => exact bigAffineFppf_isIso_canonicalMap_of_isQuasicoherentOnSite B S hS M hM f

/-- **A quasi-coherent module on `(Aff/S)_τ` satisfies the fppf sheaf axiom.**  It is cartesian
by Stacks 0H04, and a cartesian presheaf of modules on the affine objects is an fppf sheaf by
flat descent of modules, Stacks 023M — `AlgebraicGeometry.bigAffineFppf_isSheaf_of_cartesian`.

That statement is at module sections in `Type (u + 1)`; the descent to the sections in `Type u`
in which conditions (1)–(8) are stated is `CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp` along
`AddCommGrpCat.uliftFunctor`, which reflects limits. -/
public theorem bigAffine_isSheaf_fppf_of_isQuasicoherentOnSite (τ : SiteKind)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O))
    (hM : M.IsQuasicoherentOnSite) :
    Presheaf.IsSheaf (BigAffineFppf.topology B S hS) M.val.presheaf := by
  have : HasPullbacks (BigAffineFppf B S hS) := hasPullbacks_bigAffineFppf B S hS
  have : HasPullbacks (BigAffineZariski B.toBigZariskiSite S hS) :=
    hasPullbacks_bigAffineFppf B S hS
  have : HasPullbacks (BigAffineEtale B.toBigEtaleSite S hS) :=
    hasPullbacks_bigAffineFppf B S hS
  have : HasPullbacks (BigAffineSmooth B.toBigSmoothSite S hS) :=
    hasPullbacks_bigAffineFppf B S hS
  have : HasPullbacks (BigAffineSyntomic B.toBigSyntomicSite S hS) :=
    hasPullbacks_bigAffineFppf B S hS
  have : PreservesLimitsOfShape WalkingCospan
      (BigAffineZariski.toScheme B.toBigZariskiSite S hS) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (BigAffineFppf.toScheme B S hS))
  have : PreservesLimitsOfShape WalkingCospan (BigAffineEtale.toScheme B.toBigEtaleSite S hS) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (BigAffineFppf.toScheme B S hS))
  have : PreservesLimitsOfShape WalkingCospan
      (BigAffineSmooth.toScheme B.toBigSmoothSite S hS) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (BigAffineFppf.toScheme B S hS))
  have : PreservesLimitsOfShape WalkingCospan
      (BigAffineSyntomic.toScheme B.toBigSyntomicSite S hS) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (BigAffineFppf.toScheme B S hS))
  have : ∀ X : BigAffineZariski B.toBigZariskiSite S hS,
      IsAffine ((BigAffineZariski.toScheme B.toBigZariskiSite S hS).obj X) := fun X => X.property
  have : ∀ X : BigAffineEtale B.toBigEtaleSite S hS,
      IsAffine ((BigAffineEtale.toScheme B.toBigEtaleSite S hS).obj X) := fun X => X.property
  have : ∀ X : BigAffineSmooth B.toBigSmoothSite S hS,
      IsAffine ((BigAffineSmooth.toScheme B.toBigSmoothSite S hS).obj X) := fun X => X.property
  have : ∀ X : BigAffineSyntomic B.toBigSyntomicSite S hS,
      IsAffine ((BigAffineSyntomic.toScheme B.toBigSyntomicSite S hS).obj X) := fun X => X.property
  have h2 := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation.{u + 1, u, u, u} hM
  have key : Presheaf.IsSheaf (BigAffineFppf.topology B S hS)
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} M).val.presheaf := by
    cases τ with
    | zariski =>
        exact bigAffineFppf_isSheaf_of_cartesian.{u, u + 1} B S hS _ fun {_ _} f =>
          Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
            (BigAffineZariski.toScheme B.toBigZariskiSite S hS)
            (BigAffineZariski.precoverage B.toBigZariskiSite S hS)
            (bigAffineZariski_covering_finite_flat B.toBigZariskiSite S hS) _ _ h2 f.unop
    | etale =>
        exact bigAffineFppf_isSheaf_of_cartesian.{u, u + 1} B S hS _ fun {_ _} f =>
          Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
            (BigAffineEtale.toScheme B.toBigEtaleSite S hS)
            (BigAffineEtale.precoverage B.toBigEtaleSite S hS)
            (bigAffineEtale_covering_finite_flat B.toBigEtaleSite S hS) _ _ h2 f.unop
    | smooth =>
        exact bigAffineFppf_isSheaf_of_cartesian.{u, u + 1} B S hS _ fun {_ _} f =>
          Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
            (BigAffineSmooth.toScheme B.toBigSmoothSite S hS)
            (BigAffineSmooth.precoverage B.toBigSmoothSite S hS)
            (bigAffineSmooth_covering_finite_flat B.toBigSmoothSite S hS) _ _ h2 f.unop
    | syntomic =>
        exact bigAffineFppf_isSheaf_of_cartesian.{u, u + 1} B S hS _ fun {_ _} f =>
          Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
            (BigAffineSyntomic.toScheme B.toBigSyntomicSite S hS)
            (BigAffineSyntomic.precoverage B.toBigSyntomicSite S hS)
            (bigAffineSyntomic_covering_finite_flat B.toBigSyntomicSite S hS) _ _ h2 f.unop
    | fppf =>
        exact bigAffineFppf_isSheaf_of_cartesian.{u, u + 1} B S hS _ fun {_ _} f =>
          Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
            (BigAffineFppf.toScheme B S hS) (BigAffineFppf.precoverage B S hS)
            (bigAffineFppf_covering_finite_flat B S hS) _ _ h2 f.unop
  exact Presheaf.isSheaf_of_isSheaf_comp _ _ AddCommGrpCat.uliftFunctor.{u + 1, u} key

/-- A sheaf of `𝒪_Aff`-modules on `(Aff/S)_τ` which is quasi-coherent, read as a sheaf of
modules on `(Aff/S)_fppf`: the underlying presheaf of modules is unchanged, and the sheaf
condition for the fppf topology is
`AlgebraicGeometry.bigAffine_isSheaf_fppf_of_isQuasicoherentOnSite`. -/
public noncomputable def bigAffineToFppfOf (τ : SiteKind)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O))
    (hF : F.IsQuasicoherentOnSite) :
    SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O) :=
  ⟨F.val, bigAffine_isSheaf_fppf_of_isQuasicoherentOnSite B S hS τ F hF⟩

/-- Reading a quasi-coherent module on `(Aff/S)_τ` as a module on `(Aff/S)_fppf` and back is the
identity. -/
public theorem coarsenModules_bigAffineToFppfOf (τ : SiteKind)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O))
    (hF : F.IsQuasicoherentOnSite) :
    (RingedSite.coarsenModules.{u + 1, u, u, u} (bigAffineFppfRingedSite B S hS)
      (BigAffineFppf.topologyOf_le_topology B S hS τ)).obj
        (bigAffineToFppfOf B S hS τ F hF) = F := rfl

/-! ### The functor of condition (8) at `τ`, and the uniqueness of `𝒢` -/

/-- **The functor of condition (8) of Stacks 0GZV at `τ`**: a quasi-coherent `𝒪_S`-module `𝒢` is
sent to the restriction to the affine objects of the associated module `𝒢^a` of Descent,
Definition 03DU, computed on `(Sch/S)_τ`. -/
public noncomputable abbrev bigAffineAssociatedModuleQcohOf (τ : SiteKind) :=
  BigFppfOver.baseAssociatedModuleQcoh B S hS τ ⋙ bigAffineModuleRestrictionOf B S hS τ

/-- **Stacks 0GZV, the uniqueness of `𝒢` in condition (8), at every `τ`.** The functor
`𝒢 ↦ 𝒢^a|_{(Aff/S)_τ}` from the quasi-coherent `𝒪_S`-modules to the `𝒪_Aff`-modules on
`(Aff/S)_τ` is fully faithful: it is Stacks 0GN7 for the big `τ`-site followed by the Comparison
Lemma for sheaves of modules on the dense subsite of affine objects.  No part of Descent,
Proposition 03DX is used. -/
@[stacks 0GZV "(8) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, uniqueness of 𝒢"]
public noncomputable def fullyFaithfulBigAffineAssociatedModuleQcohOf (τ : SiteKind) :
    (bigAffineAssociatedModuleQcohOf B S hS τ).FullyFaithful :=
  (BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh B S hS τ).comp
    (fullyFaithfulBigAffineModuleRestrictionOf B S hS τ)

/-- **Stacks 0GZV, the uniqueness of `𝒢` in condition (8) at every `τ`**, read as a uniqueness
statement: two quasi-coherent `𝒪_S`-modules whose associated modules have isomorphic
restrictions to `(Aff/S)_τ` are isomorphic. -/
@[stacks 0GZV "(8) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, uniqueness of 𝒢"]
public theorem bigAffine_iso_of_associatedModuleQcohOf_restriction_iso (τ : SiteKind)
    (G₁ G₂ : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (e : (bigAffineAssociatedModuleQcohOf B S hS τ).obj G₁ ≅
      (bigAffineAssociatedModuleQcohOf B S hS τ).obj G₂) :
    Nonempty (G₁.obj ≅ G₂.obj) :=
  ⟨(SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.mapIso
    ((fullyFaithfulBigAffineAssociatedModuleQcohOf B S hS τ).preimageIso e)⟩

/-- The value of the functor of condition (8) at `τ` is the value of the fppf one, read for the
coarser topology: this is Stacks 0GNE, the associated-module functor being given by one formula
for all five topologies. -/
public noncomputable def coarsenModulesBigAffineAssociatedModuleQcohIso (τ : SiteKind)
    (G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (RingedSite.coarsenModules.{u + 1, u, u, u} (bigAffineFppfRingedSite B S hS)
        (BigAffineFppf.topologyOf_le_topology B S hS τ)).obj
          ((bigAffineFppfAssociatedModuleQcoh B S hS).obj G) ≅
      (bigAffineAssociatedModuleQcohOf B S hS τ).obj G :=
  have : G.obj.IsQuasicoherent := G.property
  (bigAffineModuleRestrictionOf B S hS τ).mapIso
    (BigFppfOver.restrictTopologyAssociatedModuleIso B S hS τ G.obj)

/-! ### Conditions (7) and (8) at `τ` -/

namespace BigAffineFppf

/-- **Condition (7) of Stacks 0GZV at `τ`**: under the equivalence of ringed topoi of
Stacks 0GZU, `𝓕` corresponds to a quasi-coherent module on `(Sch/S)_τ`. -/
public abbrev IsRestrictionOfQuasicoherentOf (τ : SiteKind)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O)) : Prop :=
  ∃ M : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ),
    M.IsQuasicoherentOnSite ∧
      Nonempty (F ≅ (bigAffineModuleRestrictionOf B S hS τ).obj M)

/-- **Condition (8) of Stacks 0GZV at `τ`**: `𝓕` is the restriction to the affine objects of the
associated module `𝒢^a` of a quasi-coherent `𝒪_S`-module `𝒢`, and `𝒢` is unique up to
isomorphism. -/
public abbrev IsRestrictedAssociatedModuleOf (τ : SiteKind)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O)) : Prop :=
  ∃ G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
    Nonempty (F ≅ (bigAffineAssociatedModuleQcohOf B S hS τ).obj G) ∧
      ∀ H : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
        Nonempty (F ≅ (bigAffineAssociatedModuleQcohOf B S hS τ).obj H) →
          Nonempty (G.obj ≅ H.obj)

end BigAffineFppf

/-- **Stacks 0GZV, (8) ⇒ (7) at every `τ`.** The module on `(Sch/S)_τ` that condition (7) asks
for is `𝒢^a` itself, which is quasi-coherent there by Stacks 03DV (1). -/
@[stacks 0GZV "(8) ⇒ (7) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}"]
public theorem bigAffine_isRestrictionOfQuasicoherentOf_of_isRestrictedAssociatedModuleOf
    (τ : SiteKind) (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O))
    (hF : BigAffineFppf.IsRestrictedAssociatedModuleOf B S hS τ F) :
    BigAffineFppf.IsRestrictionOfQuasicoherentOf B S hS τ F := by
  obtain ⟨G, ⟨e⟩, -⟩ := hF
  refine ⟨(BigFppfOver.baseAssociatedModuleQcoh B S hS τ).obj G, ?_, ⟨e⟩⟩
  exact BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B S hS τ
    G.obj G.property

/-- **Stacks 0GZV, (1) ⇒ (7) at every `τ`.** A sheaf of `𝒪_Aff`-modules on `(Aff/S)_τ` all of
whose base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms corresponds, under the
equivalence of ringed topoi of Stacks 0GZU, to a quasi-coherent module on `(Sch/S)_τ`.

The three inputs are the quasi-coherence conjunct of condition (2)–(6) at `τ`; the existence of
an ambient lift, by the Comparison Lemma at `τ`; and the quasi-coherence of that lift, by the
reflection of quasi-coherence along the dense subsite. -/
@[stacks 0GZV "(1) ⇒ (7) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}"]
public theorem bigAffine_isRestrictionOfQuasicoherentOf_of_canonicalMap_isIso (τ : SiteKind)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O))
    (h : ∀ ⦃U V : BigAffineFppf B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineRingedSiteOf B S hS τ) F f)) :
    BigAffineFppf.IsRestrictionOfQuasicoherentOf B S hS τ F := by
  have hF : F.IsQuasicoherentOnSite :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ F h
  obtain ⟨M, ⟨e⟩⟩ := bigAffine_exists_moduleLiftOf B S hS τ F
  refine ⟨M, ?_, ⟨e⟩⟩
  exact bigAffine_isQuasicoherentOnSite_reflectOf B S hS τ M
    (SheafOfModules.IsQuasicoherentOnSite.of_iso e hF)

/-- **Stacks 0GZV, (7) ⇒ (1) at every `τ`.** The restriction to `(Aff/S)_τ` of the quasi-coherent
module given by condition (7) is quasi-coherent, hence cartesian by Stacks 0H04. -/
@[stacks 0GZV "(7) ⇒ (1) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}"]
public theorem bigAffine_isIso_canonicalMapOf_of_isRestrictionOfQuasicoherentOf (τ : SiteKind)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O))
    (hF : BigAffineFppf.IsRestrictionOfQuasicoherentOf B S hS τ F)
    ⦃U V : BigAffineFppf B S hS⦄ (f : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineRingedSiteOf B S hS τ) F f) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hF
  exact bigAffine_isIso_canonicalMapOf_of_isQuasicoherentOnSite B S hS τ F
    (SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm
      (bigAffine_isQuasicoherentOnSite_restrictionOf B S hS τ M hM)) f

/-- **Stacks 0GZV, (1) ⇒ (8) at every `τ`**, with the uniqueness of `𝒢` included.

A cartesian sheaf of modules on `(Aff/S)_τ` satisfies the fppf sheaf axiom, so it is a sheaf of
modules on `(Aff/S)_fppf` with the same underlying presheaf, where (1) ⇒ (8) is proved as
`AlgebraicGeometry.bigAffineFppf_isRestrictedAssociatedModule_of_canonicalMap_isIso`.  Reading
the resulting isomorphism back for `τ` and applying Stacks 0GNE to its right-hand side gives
condition (8) at `τ`; the uniqueness is
`AlgebraicGeometry.fullyFaithfulBigAffineAssociatedModuleQcohOf`. -/
@[stacks 0GZV "(1) ⇒ (8) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, existence and \
uniqueness of 𝒢"]
public theorem bigAffine_isRestrictedAssociatedModuleOf_of_canonicalMap_isIso (τ : SiteKind)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O))
    (h : ∀ ⦃U V : BigAffineFppf B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (bigAffineRingedSiteOf B S hS τ) F f)) :
    BigAffineFppf.IsRestrictedAssociatedModuleOf B S hS τ F := by
  have hF : F.IsQuasicoherentOnSite :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ F h
  obtain ⟨G, ⟨e⟩, -⟩ := bigAffineFppf_isRestrictedAssociatedModule_of_canonicalMap_isIso B S hS
    (bigAffineToFppfOf B S hS τ F hF) h
  have e' : F ≅ (bigAffineAssociatedModuleQcohOf B S hS τ).obj G :=
    (RingedSite.coarsenModules.{u + 1, u, u, u} (bigAffineFppfRingedSite B S hS)
      (BigAffineFppf.topologyOf_le_topology B S hS τ)).mapIso e ≪≫
      coarsenModulesBigAffineAssociatedModuleQcohIso B S hS τ G
  exact ⟨G, ⟨e'⟩, fun H ⟨g⟩ =>
    bigAffine_iso_of_associatedModuleQcohOf_restriction_iso B S hS τ G H (e'.symm ≪≫ g)⟩

/-- **Stacks 0GZV, (7) ⇒ (8) at every `τ`**, with the uniqueness of `𝒢` included.  The route is
(7) ⇒ (1) ⇒ (8); in particular clause (1) of Descent, Proposition 03DX at `τ` is not used. -/
@[stacks 0GZV "(7) ⇒ (8) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, existence and \
uniqueness of 𝒢"]
public theorem bigAffine_isRestrictedAssociatedModuleOf_of_isRestrictionOfQuasicoherentOf
    (τ : SiteKind) (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O))
    (hF : BigAffineFppf.IsRestrictionOfQuasicoherentOf B S hS τ F) :
    BigAffineFppf.IsRestrictedAssociatedModuleOf B S hS τ F :=
  bigAffine_isRestrictedAssociatedModuleOf_of_canonicalMap_isIso B S hS τ F
    (bigAffine_isIso_canonicalMapOf_of_isRestrictionOfQuasicoherentOf B S hS τ F hF)

/-- **Stacks 0GZV, conditions (7) and (8) are equivalent, at every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`**, which is how the source reads them off each
other from Descent, Proposition 03DX. -/
@[stacks 0GZV "(7) ⇔ (8) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}"]
public theorem bigAffine_isRestrictionOfQuasicoherentOf_iff_isRestrictedAssociatedModuleOf
    (τ : SiteKind) (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineRingedSiteOf B S hS τ).O)) :
    BigAffineFppf.IsRestrictionOfQuasicoherentOf B S hS τ F ↔
      BigAffineFppf.IsRestrictedAssociatedModuleOf B S hS τ F :=
  ⟨bigAffine_isRestrictedAssociatedModuleOf_of_isRestrictionOfQuasicoherentOf B S hS τ F,
    bigAffine_isRestrictionOfQuasicoherentOf_of_isRestrictedAssociatedModuleOf B S hS τ F⟩

end AlgebraicGeometry

end
