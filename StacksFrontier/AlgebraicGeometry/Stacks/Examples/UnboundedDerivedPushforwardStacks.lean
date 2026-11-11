module

public import StacksFrontier.AlgebraicGeometry.Stacks.Examples.CyclicClassifyingStackCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Examples.DerivedPushforwardNotQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcFbcFppfIffLqcohSheafFbc

/-!
# Stacks 07DD: the unbounded `Rf_*` of `[Spec k[x]/(ℤ/pℤ)] ⟶ Spec k[x]`

**Stacks 07DD**: a quasi-compact and quasi-separated morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks need
not induce a functor `Rf_* : D_QCoh(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒴)`. The source's proof is the discussion of
**Stacks 07DC**, whose example is formalized here: `k` a field of characteristic `p > 0`,
`S = Spec k[x]`, `𝒳 = [S/(ℤ/pℤ)]` for the trivial action, `f : 𝒳 ⟶ S` the structure morphism and
`E = ⊕_{m ≥ 0} 𝒪_𝒳[m]`.

`D_QCoh` is the Verdier quotient `D_{LQCoh^fbc} / D_{Parasitic ∩ LQCoh^fbc}` of **Stacks 07B6**
(`AlgebraicGeometry.Stack.derivedCategoryQuasicoherentSheaf`), so `Rf_*` induces a functor on it
only if it carries `D_{LQCoh^fbc}(𝒪_𝒳)` into `D_{LQCoh^fbc}(𝒪_𝒴)`. The theorems below show that it
does not: `E ∈ D_{LQCoh^fbc}(𝒪_𝒳)`, while `H⁰(Rf_*E)` is not locally quasi-coherent. The
subcategory is the library's `AlgebraicGeometry.Stack.lqcFbcFppf`, the one cutting out the `D_QCoh` of 07B6, and
`Rf_*` is the unbounded total derived direct image
`AlgebraicGeometry.Stack.fppfModulesDerivedPushforward` (computed by K-injective resolutions).

## The steps of the source and where they are

* `[S/G]` as an algebraic stack with `f` quasi-compact and quasi-separated:
  `StacksFrontier/AlgebraicGeometry/Stacks/Examples/CyclicClassifyingStack.lean`
  (**Stacks 04TK** through `AlgebraicGeometry.Stack.classifyingAlgebraicStack`).
* `E = ⊕_m 𝒪_𝒳[m] ∈ D_{LQCoh^fbc}(𝒪_𝒳)`, `E = ∏_m 𝒪_𝒳[m]` (**Stacks 08IZ**), `Rf_*` commuting with
  products through K-injective resolutions, and the sections of `H⁰(Rf_*E)` over affine objects
  as `∏_m Γ(-, R^m f_*𝒪_𝒳)` (**Stacks 0BKZ**, **Stacks 0771**):
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedPushforwardShiftedSum.lean`.
* `R^m Γ(S, f_*(-))(𝒪_𝒳)` through Čech cochains of the trivial torsor and the group cohomology of
  `ℤ/pℤ`, with `Γ(S, 𝒪_S) = k[x]` as a linear retract:
  `StacksFrontier/AlgebraicGeometry/Stacks/Examples/CyclicClassifyingStackCohomology.lean`
  (`StacksFrontier/RingTheory/GroupCohomology/TrivialCochainPairing.lean` for the cochains).
* Local quasi-coherence on `Spec R` makes sections over `D(r)` the localization
  (`Stacks/Quasicoherent/LocallyQuasicoherentAffineLocalization.lean`),
  and a product of modules with rank-one retracts does not localize
  (`StacksFrontier/RingTheory/Localization/ProductOfRetracts.lean`), so `H⁰(Rf_*E)` is not locally
  quasi-coherent: `Stacks/Examples/DerivedPushforwardNotQuasicoherent.lean`.
* The two readings of `LQCoh^fbc` with the flat base change property of **Stacks 0762** on sheaves
  agree: `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LqcFbcFppfIffLqcohSheafFbc.lean`.

## Relation to the other registration of 07DD

`not_forall_derivedPushforward_mem_derivedLocallyQuasicoherentFlatBaseChange`
(`StacksFrontier/AlgebraicGeometry/Stacks/Examples/UnboundedDerivedPushforwardCounterexample.lean`)
registers 07DD for `p = 2` at module universe `u + 1`, through the subcategory
`AlgebraicGeometry.Stack.derivedLocallyQuasicoherentFlatBaseChangeUnivLE`, whose flat base change
property is read on presheaves of modules. The statements here are at the module universe `u` of
the `D_QCoh` of 07B6, with the flat base change property read on sheaves as in **Stacks 0762**,
for every prime `p`, every field of characteristic `p` and every big fppf site containing
`Spec k[x]`.

## Main results

* `exists_not_derivedCategoryB_lqcFbcFppf_derivedPushforward`:
  **Stacks 07DD** for the source's example, over every big fppf site containing `Spec k[x]`.
* `exists_isQuasiCompact_isQuasiSeparated_not_derivedCategoryB_derivedPushforward`:
  **Stacks 07DD** as an existence statement.

## References

* [Stacks Project, Tag 07DD](https://stacks.math.columbia.edu/tag/07DD)
* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Examples.UnboundedDerivedPushforward

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

section Stack

open AlgebraicGeometry.Stack Opposite

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  enoughInjectives_fppfSiteModules_of_essentiallySmall
  Stacks.Cohomology.AcyclicCover.evaluation_additive
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall

universe w t

/-- **Stacks 07DD**, for the source's own example. Let `k` be a field of characteristic `p > 0`,
`S = Spec k[x]`, and let `𝒞` be any big fppf site containing `S`. The classifying stack
`𝒳 = [S/(ℤ/pℤ)]` and `S` itself are algebraic stacks over `S`, the structure morphism
`f : 𝒳 ⟶ S` is quasi-compact and quasi-separated, and for every choice of derived categories
the object `E = ⊕_{m ≥ 0} 𝒪_𝒳[m]` lies in `D_{LQCoh^fbc}(𝒪_𝒳)` while `Rf_*E` does not lie in
`D_{LQCoh^fbc}(𝒪_S)`. So `Rf_*` does not carry `D_{LQCoh^fbc}(𝒪_𝒳)` into `D_{LQCoh^fbc}(𝒪_S)`
and does not induce a functor `D_QCoh(𝒪_𝒳) ⟶ D_QCoh(𝒪_S)` on the Verdier quotients of
**Stacks 07B6** (`AlgebraicGeometry.Stack.derivedCategoryQuasicoherentSheaf`, whose subcategory
`LQCoh^fbc` is `AlgebraicGeometry.Stack.lqcFbcFppf`).

`Rf_*` is the total right derived functor of the direct image of **Stacks 06WE** on the
unbounded derived categories of fppf modules
(`AlgebraicGeometry.Stack.fppfModulesDerivedPushforward`).
The proof is the discussion of **Stacks 07DC**: see the module documentation. -/
@[stacks 07DD "for the source's example: f : [Spec k[x]/(Z/pZ)] -> Spec k[x] with char k = p, \
over any big fppf site containing Spec k[x], E = sum of O_X[m] in D_LQCoh^fbc(O_X) and Rf_*E not \
in D_LQCoh^fbc(O_S), with LQCoh^fbc the class of the Verdier quotient D_QCoh of 07B6 and Rf_* the \
unbounded total derived direct image"]
theorem exists_not_derivedCategoryB_lqcFbcFppf_derivedPushforward (p : ℕ) [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p] (𝒞 : BigFppfSite.{u})
    (hS : 𝒞.Contains (Spec (.of (Polynomial k)))) :
    ∃ (𝒳 𝒴 : AlgebraicStacks.{u, w} 𝒞 (Spec (.of (Polynomial k))) hS) (f : 𝒳 ⟶ 𝒴),
      IsQuasiCompactMorphism 𝒞 _ hS f ∧ AlgebraicStacks.IsQuasiSeparated 𝒞 _ hS f ∧
      ∀ [HasDerivedCategory.{t} (fppfModules 𝒞 _ hS 𝒳)]
        [HasDerivedCategory.{t} (fppfModules 𝒞 _ hS 𝒴)],
        ∃ E : DerivedCategory (fppfModules 𝒞 _ hS 𝒳),
          DerivedCategoryB.derivedCategoryB (lqcFbcFppf 𝒞 _ hS 𝒳) E ∧
            ¬ DerivedCategoryB.derivedCategoryB (lqcFbcFppf 𝒞 _ hS 𝒴)
              ((fppfModulesDerivedPushforward 𝒞 _ hS f).obj E) := by
  refine ⟨cyclicClassifyingStack.{u, w} p 𝒞 hS, baseStack.{u, w} 𝒞 hS,
    cyclicStructureMorphism.{u, w} p 𝒞 hS,
    isQuasiCompactMorphism_cyclicStructureMorphism.{u, w} p 𝒞 hS,
    isQuasiSeparated_cyclicStructureMorphism.{u, w} p 𝒞 hS, fun {_ _} => ?_⟩
  refine ⟨fppfModulesShiftedUnitSum 𝒞 _ hS _, ?_, ?_⟩
  · rw [derivedCategoryB_lqcFbcFppf_eq]
    exact derivedCategoryB_lqcohSheafFbcFppfModules_fppfModulesShiftedUnitSum 𝒞
      (associatedBigEtaleSite 𝒞) rfl _ hS _
  · rw [derivedCategoryB_lqcFbcFppf_eq]
    exact not_derivedCategoryB_of_retracts (𝒴 := baseStack.{u, w} 𝒞 hS) 𝒞 hS Polynomial.X
      (affineSchemeStack.isDomain_sectionsRing_terminalObj_polynomial.{u, w} 𝒞 hS)
      (affineSchemeStack.terminalElement_X_ne_zero.{u, w} 𝒞 hS)
      (affineSchemeStack.not_isUnit_terminalElement_X.{u, w} 𝒞 hS) rfl
      (cyclicStructureMorphism.{u, w} p 𝒞 hS)
      (isQuasiCompactMorphism_cyclicStructureMorphism.{u, w} p 𝒞 hS)
      (isQuasiSeparated_cyclicStructureMorphism.{u, w} p 𝒞 hS) (cyclicBaseStackTerminal 𝒞 hS)
      HEq.rfl
      (fun m => by
        obtain ⟨e, ψ, he⟩ := exists_linearMap_rightDerived_cyclicPushforwardSections.{u, w} p 𝒞 hS m
        exact ⟨e, ψ.hom, he⟩)

/-- **Stacks 07DD.** A quasi-compact and quasi-separated morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks need not induce a functor `Rf_* : D_QCoh(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒴)`: there are a big fppf site
`𝒞`, a scheme `S` in it, algebraic stacks `𝒳`, `𝒴` over `S` and a quasi-compact and
quasi-separated `f : 𝒳 ⟶ 𝒴` such that, for every choice of derived categories, some object `E` of
`D_{LQCoh^fbc}(𝒪_𝒳)` has `Rf_*E` outside `D_{LQCoh^fbc}(𝒪_𝒴)`. The witness is the source's, with
`p = 2`: `exists_not_derivedCategoryB_lqcFbcFppf_derivedPushforward`. -/
@[stacks 07DD "Rf_* does not carry D_LQCoh^fbc(O_X) into D_LQCoh^fbc(O_Y) for some qcqs f of \
algebraic stacks, so it does not induce D_QCoh(O_X) -> D_QCoh(O_Y) on the Verdier quotients of \
07B6; Rf_* is the unbounded total derived direct image"]
theorem exists_isQuasiCompact_isQuasiSeparated_not_derivedCategoryB_derivedPushforward :
    ∃ (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
      (𝒳 𝒴 : AlgebraicStacks.{u, w} 𝒞 S hS) (f : 𝒳 ⟶ 𝒴),
      IsQuasiCompactMorphism 𝒞 S hS f ∧ AlgebraicStacks.IsQuasiSeparated 𝒞 S hS f ∧
      ∀ [HasDerivedCategory.{t} (fppfModules 𝒞 S hS 𝒳)]
        [HasDerivedCategory.{t} (fppfModules 𝒞 S hS 𝒴)],
        ∃ E : DerivedCategory (fppfModules 𝒞 S hS 𝒳),
          DerivedCategoryB.derivedCategoryB (lqcFbcFppf 𝒞 S hS 𝒳) E ∧
            ¬ DerivedCategoryB.derivedCategoryB (lqcFbcFppf 𝒞 S hS 𝒴)
              ((fppfModulesDerivedPushforward 𝒞 S hS f).obj E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨𝒞, hS⟩ := BigFppfSite.exists_contains (Spec (.of (Polynomial (ULift.{u} (ZMod 2)))))
  exact ⟨𝒞, _, hS, exists_not_derivedCategoryB_lqcFbcFppf_derivedPushforward.{u, w, t} 2 𝒞 hS⟩

end Stack

end Stacks.Examples.UnboundedDerivedPushforward

end
