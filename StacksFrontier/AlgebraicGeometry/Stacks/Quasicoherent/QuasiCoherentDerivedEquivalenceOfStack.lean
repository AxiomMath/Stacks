module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsTerminalObject
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasiCoherentDerivedEquivalenceSucc

/-!
# `QC(𝒳) ≌ D_QCoh(𝒪_𝒳)` for an algebraic stack (Stacks 0H15, 0H16)

Let `𝒳` be an algebraic stack and `g : Sh(𝒳_{flat, fppf}) ⟶ Sh(𝒳_{fppf})` the morphism of topoi
of the flat objects. This file assembles

* **Stacks 0H15**: for `H ∈ D_QCoh(𝒪_{𝒳_{flat, fppf}})` the object `Lg_! H` has the base change
  property `RΓ(x', Lg_! H) ⊗^L_{𝒪(x')} 𝒪(x) ≅ RΓ(x, Lg_! H)` along every morphism `x ⟶ x'` of
  `𝒳_{affine}`. The proof is the one of the source: the flat case
  (`isIso_derivedSectionsBaseChange_of_flat`, from Stacks 07B9 (2)(c)), étale locality
  (`hasAffineDerivedSectionsBaseChange_of_covering`), the reduction to a smooth chart
  (`hasAffineDerivedSectionsBaseChange_derivedModuleLowerShriekSucc_of_affine`, Stacks 06XH and
  07AV) and the case of an affine scheme
  (`hasAffineDerivedSectionsBaseChange_derivedModuleLowerShriekSucc_schemeStack`);
* **Stacks 0H16**: `QC(𝒳) ≌ D_QCoh(𝒪_𝒳)`, as `QC(𝒳) ≌ Q_𝒳 = 𝒜 ≌ D_QCoh(𝒪_𝒳)`
  (`quasiCoherentDerivedEquivalenceOfEqInterLeftOrthogonal`), where `Q_𝒳 = 𝒜` follows from the
  comparison of `Q_𝒳` with the base change property
  (`quasiCoherentDerivedFppfSucc_iff_hasAffineDerivedSectionsBaseChange`) and Stacks 0H15
  (`quasiCoherentDerivedFppfSucc_eq_interLeftOrthogonal_of`).

## Universes

Both statements are at module universe `u + 1`, the module universe of `QC(𝒳)` (Stacks 0H0H) for
a stack whose objects form a `Type (u + 1)`. At module universe `u` the equivalence of Stacks 0H16
cannot hold: `QC(𝒳)` contains the free objects `x ↦ 𝒪(x)^{(κ)}` for every cardinal `κ` of
`Type (u + 1)`, pairwise non-isomorphic, while the derived category of sheaves of modules with
sections in `Type u` has fewer isomorphism classes. `D_QCoh(𝒪_𝒳)` is the Verdier quotient
`D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of Stacks 07B6 at that universe
(`DerivedCategory.KernelColocalization.quotient`).

## References

* [Stacks Project, Tag 0H15](https://stacks.math.columbia.edu/tag/0H15)
* [Stacks Project, Tag 0H16](https://stacks.math.columbia.edu/tag/0H16)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0H15.** Let `𝒳` be an algebraic stack and `H` an object of
`D_QCoh(𝒪_{𝒳_{flat, fppf}})` (module universe `u + 1`). Then `Lg_! H` has the following
property: for every morphism `x ⟶ x'` of `𝒳_{affine}` the map
`RΓ(x', Lg_! H) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, Lg_! H)` is a quasi-isomorphism
(`HasAffineDerivedSectionsBaseChange`). The derived categories are the standard models. -/
@[stacks 0H15]
theorem hasAffineDerivedSectionsBaseChange_derivedModuleLowerShriekSucc :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    ∀ H : DerivedCategory (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)),
      DerivedCategoryB.derivedCategoryB (flatQuasicoherentModulesSucc B S hS 𝒳) H →
        HasAffineDerivedSectionsBaseChange B S hS 𝒳
          ((derivedModuleLowerShriekSucc B S hS 𝒳).obj H) :=
  fun H hH => hasAffineDerivedSectionsBaseChange_derivedModuleLowerShriekSucc_of_affine B S hS 𝒳
    B.toBigEtaleSite (BigFppfSite.toBigEtaleSite_cutoff B)
    (fun X hX H hH => hasAffineDerivedSectionsBaseChange_derivedModuleLowerShriekSucc_schemeStack
      B B.toBigEtaleSite (BigFppfSite.toBigEtaleSite_cutoff B) S hS X hX H hH) H hH

section ZH16

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafify_fppfTopology_largeSections
  wEqualsLocallyBijective_fppfTopology_largeSections
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance] isGrothendieckAbelian_ambientModulesSucc
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory

/-- **Stacks 0H16.** For an algebraic stack `𝒳`, `QC(𝒳)` is canonically equivalent to
`D_QCoh(𝒪_𝒳)`, both at module universe `u + 1` (see the module docstring for why `u + 1`):
`QC(𝒳) ≌ Q_𝒳` by Stacks 0H0X and 0H0C, `Q_𝒳 = 𝒜` by Stacks 0H15, and `𝒜 ≌ D_QCoh(𝒪_𝒳)` by
Stacks 0H11, where `D_QCoh(𝒪_𝒳)` is the quotient of `D_{LQCoh^fbc}(𝒪_𝒳)` by
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` (Stacks 07B6). -/
@[stacks 0H16]
def quasiCoherentDerivedEquivalenceSucc :
    quasiCoherentDerived.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p ≌
      DerivedCategory.KernelColocalization.quotient (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) :=
  quasiCoherentDerivedEquivalenceOfEqInterLeftOrthogonal B S hS 𝒳 E h
    (quasiCoherentDerivedFppfSucc_eq_interLeftOrthogonal_of B S hS 𝒳 E h
      (fun K => quasiCoherentDerivedFppfSucc_iff_hasAffineDerivedSectionsBaseChange B S hS 𝒳 K)
      (hasAffineDerivedSectionsBaseChange_derivedModuleLowerShriekSucc B S hS 𝒳))

end ZH16

end AlgebraicGeometry.Stack.FlatFppf

end
