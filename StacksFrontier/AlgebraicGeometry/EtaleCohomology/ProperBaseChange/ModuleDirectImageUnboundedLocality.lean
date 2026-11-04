module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TermwiseAcyclicComputesRightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# The unbounded derived direct image of sheaves of modules is computed étale locally on the base

Let `Λ` be a ring, `f : X ⟶ Y` a morphism of schemes, and `{j_i : U_i ⟶ Y}` an étale covering
of `Y`, with base changes `f_i : X_i = X ×_Y U_i ⟶ U_i` and `p_i : X_i ⟶ X`. A complex `J` of
sheaves of `Λ`-modules on `X_étale` computes the unbounded derived direct image `Rf_*` as soon
as each restriction `J|_{X_i}` computes `R(f_i)_*`: the unit `f_* J ⟶ Rf_* J` is an isomorphism
in `D(Y_étale, Λ)` if each unit `(f_i)_* (J|_{X_i}) ⟶ R(f_i)_*(J|_{X_i})` is one in
`D((U_i)_étale, Λ)`.

This is the localization step "it is enough to prove this when `Y` is quasi-compact" of the
proofs of [Stacks, Tag 0F0C] and [Stacks, Tag 0F0D], read on the comparison map. Three inputs
are combined:

* restriction to `X_i` is exact and carries K-injective complexes to K-injective complexes,
  its left adjoint, extension by zero, being exact ([Stacks, Tag 08BJ], [Stacks, Tag 03S5]);
* restriction to `U_i` commutes with direct image,
  `(f_* G)|_{U_i} = (f_i)_*(G|_{X_i})`
  (`Stacks.EtaleCohomology.etaleRestrictionPushforwardIsoOfIsPullback`);
* being a quasi-isomorphism is local on the small étale site, because invertibility of a
  morphism of sheaves is (`Stacks.EtaleCohomology.isIso_of_isIso_etaleRestrictionAt`).

## Main results

* `Stacks.EtaleCohomology.isKInjective_etaleModuleRestriction`: restriction along an étale
  morphism preserves K-injective complexes.
* `Stacks.EtaleCohomology.quasiIso_of_quasiIso_etaleModuleRestriction`: a morphism of complexes
  of sheaves of `Λ`-modules is a quasi-isomorphism if its restrictions to the members of an
  étale covering are.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_cover`: the
  statement above.

## References

* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- **Restriction along an étale morphism preserves K-injective complexes** of sheaves of
`Λ`-modules ([Stacks, Tag 08BJ]): its left adjoint, extension by zero, is exact. -/
theorem isKInjective_etaleModuleRestriction {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((etaleModuleRestriction.{u, r} Λ j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j) I

/-- **Being a quasi-isomorphism is étale local.** A morphism of complexes of sheaves of
`Λ`-modules on `Y_étale` is a quasi-isomorphism if its restriction to the small étale site of
each member of an étale covering of `Y` is one. -/
theorem quasiIso_of_quasiIso_etaleModuleRestriction {Y : Scheme.{u}} {ι : Type*}
    {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ Y) [∀ i, Etale (j i)]
    (hcov : Y.smallEtaleTopology.CoversTop fun i ↦ smallEtaleObj (j i))
    {K L : CochainComplex (EtaleModules.{u, r} Λ Y) ℤ} (φ : K ⟶ L)
    (h : ∀ i, QuasiIso (((etaleModuleRestriction.{u, r} Λ (j i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff]
  let ψ := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) k).map φ
  let γ : ShortComplex.LeftHomologyMapData ψ
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) k).obj K).leftHomologyData
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) k).obj L).leftHomologyData :=
    default
  rw [γ.quasiIso_iff]
  refine isIso_of_isIso_etaleRestrictionAt γ.φH j hcov fun i ↦ ?_
  have hi := (h i).quasiIsoAt k
  rw [quasiIsoAt_iff] at hi
  have hi' : ShortComplex.QuasiIso
      ((etaleModuleRestriction.{u, r} Λ (j i)).mapShortComplex.map ψ) := hi
  rwa [(γ.map (etaleModuleRestriction.{u, r} Λ (j i))).quasiIso_iff,
    ShortComplex.LeftHomologyMapData.map_φH] at hi'

/-- **The unit of the unbounded derived direct image is étale local on the base.** Let
`f : X ⟶ Y` be a morphism of schemes, `{j_i : U_i ⟶ Y}` an étale covering, and
`X_i = U_i ×_Y X` with projections `f_i : X_i ⟶ U_i` and `p_i : X_i ⟶ X`. If for every `i` the
restriction `J|_{X_i}` of a complex `J` of sheaves of `Λ`-modules on `X_étale` computes
`R(f_i)_*`, then `J` computes `Rf_*`. -/
theorem isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_cover {X Y : Scheme.{u}}
    (f : X ⟶ Y) {ι : Type*} {U XU : ι → Scheme.{u}} (j : ∀ i, U i ⟶ Y) [∀ i, Etale (j i)]
    (hcov : Y.smallEtaleTopology.CoversTop fun i ↦ smallEtaleObj (j i))
    (fU : ∀ i, XU i ⟶ U i) (pX : ∀ i, XU i ⟶ X) (hpb : ∀ i, IsPullback (fU i) (pX i) (j i) f)
    (J : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (h : ∀ i, haveI := AlgebraicGeometry.Scheme.Etale.etale_of_isPullback_snd (hpb i)
      IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (fU i)).app
        (((etaleModuleRestriction.{u, r} Λ (pX i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J))) :
    IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app J) := by
  obtain ⟨I, s, hI, hs⟩ :=
    Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
      (EtaleModules.{u, r} Λ X) J
  refine Functor.isIso_rightDerivedUnit_app_of_quasiIso_map.{max (u + 1) r} _ _ _ s hI ?_
  refine quasiIso_of_quasiIso_etaleModuleRestriction Λ j hcov _ fun i ↦ ?_
  have := AlgebraicGeometry.Scheme.Etale.etale_of_isPullback_snd (hpb i)
  have hloc := Functor.quasiIso_map_of_isIso_rightDerivedUnit_app_Q.{max (u + 1) r}
    (etaleModuleDirectImage.{u, r} Λ (fU i)) _
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (fU i))
    (((etaleModuleRestriction.{u, r} Λ (pX i)).mapHomologicalComplex (ComplexShape.up ℤ)).map s)
    (isKInjective_etaleModuleRestriction Λ (pX i) I) (h i)
  let e := NatIso.mapHomologicalComplex
    (etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{max (u + 1) r} Λ) (hpb i))
    (ComplexShape.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app J) (e.app I) (e.hom.naturality s).symm)).1 hloc

end Stacks.EtaleCohomology

end
