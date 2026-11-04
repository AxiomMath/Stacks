module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedQuasicoherentRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedModuleLowerShriekSheafFlatBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07B9 (2)(c) and (2)(d): `Lg_!` on `D_QCoh(𝒪_{𝒳_{flat,fppf}})`

Let `𝒳` be an algebraic stack, `g` the morphism of ringed topoi of **Stacks 0788** for the
flat-fppf site, with `g^*` restriction to the flat objects and `Lg_!` its left adjoint
(**Stacks 07AS** (4)).  `LQCoh^fbc(𝒪_𝒳)` is the class with the flat base change property of
**Stacks 0762** read with the pullback of sheaves.

The dévissage of the source reduces (2)(c) to a quasi-coherent module in degree `0`
(`FlatFppf.derivedCategoryB_derivedModuleLowerShriek_of_single`), which is **Stacks 07B3** (2)
(`FlatFppf.locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek`). Everything
here is stated at the standard models of the derived categories, named by `letI` in the statements,
which is where Stacks 07B3 (2) is.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.derivedCategoryB_derivedModuleLowerShriek`: **Stacks 07B9**
  (2)(c), `Lg_!` carries `D_QCoh(𝒪_{𝒳_{flat,fppf}})` into `D_{LQCoh^fbc}(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.FlatFppf.derivedSheafFlatBaseChange_parasiticFreePart`: for `K` in
  `D_{LQCoh^fbc}(𝒪_𝒳)`, the parasitic-free part `Lg_! g^* K` of Stacks 07BA lies in
  `D_{LQCoh^fbc}(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.FlatFppf.derivedQuasicoherentEquivalence`: **Stacks 07B9** (2)(d),
  `D_QCoh(𝒪_𝒳) ≌ D_QCoh(𝒪_{𝒳_{flat,fppf}})`, with functor induced by `g^*` and inverse
  `q ∘ Lg_!`.

## References

* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] AlgebraicGeometry.Stack.abelianFppfModules abelianFlatFppfModulesSpelling

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 07B9** (2)(c).  `Lg_!` carries `D_QCoh(𝒪_{𝒳_{flat,fppf}})` into `D_{LQCoh^fbc}(𝒪_𝒳)`,
the flat base change property of Stacks 0762 being read with the pullback of sheaves.

This is the dévissage of the source
(`AlgebraicGeometry.Stack.FlatFppf.derivedCategoryB_derivedModuleLowerShriek_of_single`): `Lg_!` is
triangulated, right t-exact and commutes with direct sums, `LQCoh^fbc(𝒪_𝒳)` is weak Serre and
closed under colimits of sequences (Stacks 0771 (2), (5)), and on a quasi-coherent module in
degree `0` it is Stacks 07B3 (2). -/
@[stacks 07B9 "part (2)(c): Lg_! carries D_QCoh(𝒪_{𝒳_flat,fppf}) into D_LQCoh^fbc(𝒪_𝒳), for \
the derived lower shriek of Stacks 07AS (4) and LQCoh^fbc with the flat base change property of \
Stacks 0762 read with the pullback of sheaves, at module universe u, at the standard models of \
the derived categories"]
theorem derivedCategoryB_derivedModuleLowerShriek :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    ∀ H : DerivedCategory (flatFppfModules B S hS 𝒳),
      DerivedCategoryB.derivedCategoryB (flatQuasicoherentModules B S hS 𝒳) H →
        DerivedCategoryB.derivedCategoryB
          (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
          ((derivedModuleLowerShriek B S hS 𝒳).obj H) :=
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  derivedCategoryB_derivedModuleLowerShriek_of_single B E h S hS 𝒳 fun M hM p =>
    locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek B E h S hS 𝒳 M hM p

/-- **Stacks 07B9** (2)(a) followed by (2)(c): for `K` in `D_{LQCoh^fbc}(𝒪_𝒳)`, the parasitic-free
part `Lg_! g^* K` of Stacks 07BA lies in `D_{LQCoh^fbc}(𝒪_𝒳)` again. -/
theorem derivedSheafFlatBaseChange_parasiticFreePart :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    ∀ K : DerivedCategory (fppfModules B S hS 𝒳),
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) K →
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
        (parasiticFreePart B S hS 𝒳 (derivedModuleLowerShriek B S hS 𝒳) K) :=
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  derivedSheafFlatBaseChange_parasiticFreePart_of_single B E h S hS 𝒳 fun M hM p =>
    locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek B E h S hS 𝒳 M hM p

/-- **Stacks 07B9** (2)(d).  Restriction `g^*` to the flat-fppf site and `Lg_!` define mutually
inverse equivalences between `D_QCoh(𝒪_𝒳)` — the Verdier quotient
`D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of Stacks 07B6 — and
`D_QCoh(𝒪_{𝒳_{flat,fppf}})`, the flat base change property of Stacks 0762 being read with the
pullback of sheaves.  The functor is the functor `c` induced by `g^*` (Stacks 07B9 (2)(a), (2)(b)),
the inverse is `q ∘ Lg_!` (Stacks 07B9 (2)(c));
see `AlgebraicGeometry.Stack.FlatFppf.derivedQuasicoherentEquivalenceOfSingle`. -/
@[stacks 07B9 "part (2)(d): g^* and Lg_! define mutually inverse equivalences between \
D_QCoh(𝒪_𝒳), the Verdier quotient of Stacks 07B6, and D_QCoh(𝒪_{𝒳_flat,fppf}): the functor is \
induced by g^*, the inverse is q ∘ Lg_!; for LQCoh^fbc with the flat base change property of \
Stacks 0762 read with the pullback of sheaves, at module universe u, at the standard models of \
the derived categories"]
def derivedQuasicoherentEquivalence :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    ParasiticQuotient.quotient B S hS 𝒳
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) ≌
      (DerivedCategoryB.derivedCategoryB (flatQuasicoherentModules B S hS 𝒳)).FullSubcategory :=
  letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  derivedQuasicoherentEquivalenceOfSingle B E h S hS 𝒳 fun M hM p =>
    locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek B E h S hS 𝒳 M hM p

end AlgebraicGeometry.Stack.FlatFppf
