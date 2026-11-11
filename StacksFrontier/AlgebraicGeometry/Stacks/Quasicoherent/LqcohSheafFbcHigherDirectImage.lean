module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalRule
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcDirectImageAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcRuleClauses

/-!
# Higher direct images preserve `LQCoh^fbc` (Stacks 0765, Stacks 0771 (4)(b), étale)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks and `F` a
module on `𝒳_étale` which is locally quasi-coherent (**Stacks 06WJ**) and has the flat base change
property (**Stacks 0762**). Then every higher direct image `Rⁱf_*F`, computed in the étale
topology, has the flat base change property (**Stacks 0765**), and is again in `LQCoh^fbc(𝒪_𝒴)`
(**Stacks 0771** part (4)(b), in the étale topology).

The proof is the source's: the criterion of **Stacks 076Z** applied to the rule `LQCoh^fbc`,
whose four clauses are **Stacks 0771** (2), **Stacks 0771** (3), **Stacks 06WL** with
**Stacks 0764**, and the affine case, which the source reads off **Stacks 075P** and
**Stacks 073K**.

## Main results

* `AlgebraicGeometry.Stack.lqcohSheafFbcModuleRule_stackModuleHigherDirectImage`:
  **Stacks 0771** part (4)(b), étale.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_stackModuleHigherDirectImage`:
  **Stacks 0765**.

## References

* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open CategoryTheory

universe u t

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0771, part (4)(b), in the étale topology.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and
quasi-separated 1-morphism of algebraic stacks and `F` an object of `LQCoh^fbc(𝒪_𝒳)`, a module on
`𝒳_étale` which is locally quasi-coherent with the flat base change property. Then each higher
direct image `Rⁱf_*F`, computed in the étale topology, is an object of `LQCoh^fbc(𝒪_𝒴)`.

Modules have sections in the universe `u` of the schemes, local quasi-coherence is read against an
auxiliary big étale site `E` with `E.cutoff = B.cutoff`, and the flat base change property is the
sheaf-level one of **Stacks 0762** (`AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`). -/
@[stacks 0771 "part (4)(b), étale topology: for f quasi-compact and quasi-separated, each \
  R^i f_*F computed in the étale topology lies in LQCoh^fbc(𝒪_𝒴), with the flat base change \
  property of 0762 read on sheaves; modules at the module universe u of the schemes"]
theorem lqcohSheafFbcModuleRule_stackModuleHigherDirectImage
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : StackModules B S hS .etale 𝒳)
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F.val) (i : ℕ) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids ((stackModuleHigherDirectImage B S hS f .etale i).obj F).val := by
  have key : lqcohSheafFbcModuleRule B E h S hS 𝒴
      (((stackModuleDirectImageData.{u, t} B S hS .etale).higherDirectImage f i).obj F) :=
    StackModuleRule.preservesHigherDirectImages_etale (lqcohSheafFbcModuleRule.{u, t} B E h S hS)
      (isWeakSerre_lqcohSheafFbcModuleRule B E h S hS)
      (isStableUnderSmoothPullback_lqcohSheafFbcModuleRule B E h S hS)
      (isSmoothLocal_lqcohSheafFbcModuleRule.{u, t, u} B E h S hS)
      (preservesHigherDirectImagesOfAffine_lqcohSheafFbcModuleRule B E h S hS) f hqc hqs i F hF
  rwa [stackModuleDirectImageData_higherDirectImage] at key

/-- **Stacks 0765.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of
algebraic stacks and `F` an object of `Mod(𝒳_étale, 𝒪_𝒳)` which is locally quasi-coherent and has
the flat base change property. Then each `Rⁱf_*F`, computed in the étale topology, has the flat
base change property.

Modules have sections in the universe `u` of the schemes; the flat base change property is the
sheaf-level one of **Stacks 0762** (`AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`), and
local quasi-coherence is read against an auxiliary big étale site `E` with `E.cutoff = B.cutoff`.
-/
theorem hasSheafFlatBaseChangeProperty_stackModuleHigherDirectImage
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : StackModules B S hS .etale 𝒳)
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F.val) (i : ℕ) :
    HasSheafFlatBaseChangeProperty B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B)
      ((stackModuleHigherDirectImage B S hS f .etale i).obj F).val :=
  (lqcohSheafFbcModuleRule_stackModuleHigherDirectImage B E h S hS f hqc hqs F hF i).2

end AlgebraicGeometry.Stack
