module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFlatBaseChangeProved
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion

/-!
# Presheaf-level `LQCoh^fbc`: the fppf sheaf condition and the higher direct images

This file works with the *presheaf-level* reading of the flat base change property,
`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` and
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`, which asks the comparison map from the
presheaf inverse image to be an isomorphism of presheaves. That reading is strictly stronger than
**Stacks 0762** (see the module docstring of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SheafFlatBaseChangeProperty.lean`), so the
results here are not **Stacks 0771**. The proposition itself is formalized at the sheaf-level
reading `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithSheafFlatBaseChange`; its part (1) is
`AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange` and its
part (4)(b) is `AlgebraicGeometry.Stack.lqcohSheafFbcModuleRule_stackModuleHigherDirectImage`.

For orientation, **Stacks 0771** collects what the category `LQCoh^fbc(𝒪_𝒳)` of locally
quasi-coherent `𝒪_𝒳`-modules with the flat base change property satisfies. Its parts are

1. a member of `LQCoh^fbc(𝒪_𝒳)`, a condition on a module on the *étale* site, is already a sheaf
   for the *fppf* topology, hence is an object of `Mod(𝒪_𝒳)`;
2. `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒪_𝒳)` and of `Mod(𝒳_étale, 𝒪_𝒳)`;
3. the inverse image along a 1-morphism carries `LQCoh^fbc(𝒪_𝒴)` into `LQCoh^fbc(𝒪_𝒳)`;
4. for `f` quasi-compact and quasi-separated, (a) `Rf_*ℱ` and the `Rⁱf_*ℱ` do not depend on
   whether they are computed on the étale or on the fppf site, and (b) each `Rⁱf_*ℱ` lies again
   in `LQCoh^fbc(𝒪_𝒴)`.

This file has the presheaf-level analogue of part (1), and a presheaf-level statement of the
shape of part (4)(b) whose hypotheses cannot all hold (see its docstring).

## Main definitions

* `AlgebraicGeometry.Stack.fppfModuleOfLocallyQuasicoherentWithFlatBaseChange`: the object of
  `Mod(𝒪_𝒳)` which a member of the presheaf-level `LQCoh^fbc(𝒪_𝒳)` is.

## Main results

* `AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherentWithFlatBaseChange`: the
  fppf sheaf condition for a member of the presheaf-level `LQCoh^fbc`.
* `AlgebraicGeometry.Stack.fppfModuleOfLocallyQuasicoherentWithFlatBaseChange_mem`: the object
  `fppfModuleOfLocallyQuasicoherentWithFlatBaseChange` produces lies in the subcategory
  `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` whose derived category **Stacks 07B6** takes the Verdier
  quotient of.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChangeUnivLE_`
  `moduleSheafHigherDirectImage`: the presheaf-level statement of the shape of **Stacks 0771**
  part (4)(b); its hypotheses cannot all hold.

## Implementation notes

### The fppf sheaf condition, and what it carries

The source proves its part (1) by citing **Stacks 076T**: a locally quasi-coherent module whose
comparison map `c_φ` of **Stacks 06WC** is an isomorphism along every arrow lying over a flat
morphism *locally of finite presentation* is an fppf sheaf. Membership in `LQCoh^fbc` asks that
isomorphism along every arrow lying over a flat morphism, finitely presented or not, so it
implies the hypothesis of **Stacks 076T** by
`AlgebraicGeometry.Stack.hasFlatLfpBaseChangeProperty_of_hasFlatBaseChangeProperty`, and the
fppf sheaf condition here is that implication followed by **Stacks 076T**.

**Stacks 076T** is reduced to one step of its own proof, the sheaf condition along a family of
arrows lying over an fppf covering of schemes
(`AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily`), in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFromFlatBaseChange.lean`, and that
step is proved in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFlatBaseChangeProved.lean`.

The statement here is for an arbitrary category fibred in groupoids over the big fppf site,
which is the generality of **Stacks 076T**, and
`AlgebraicGeometry.Stack.fppfModuleOfLocallyQuasicoherentWithFlatBaseChange` is the
specialization to an algebraic stack that produces an object of `Mod(𝒪_𝒳)`.

### The statement of the shape of part (4)(b)

The statement of the shape of part (4)(b),
`AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChangeUnivLE_`
`moduleSheafHigherDirectImage`, runs the criterion of **Stacks 076Z** at the presheaf-level rule
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeRule`, over six hypotheses. Example 3
of the module docstring of `SheafFlatBaseChangeProperty.lean` (a closed point `i : pt ⟶ ℙ¹` over
a field, `ℱ = 𝒪_pt`, degree `0`) shows that its conclusion fails in the presheaf reading, so over
any base where that example can be built the six hypotheses cannot all hold together.

### Where the parts of Stacks 0771 are

At the sheaf-level reading of **Stacks 0762**: part (1) in
`FppfSheafFromSheafFlatBaseChange.lean`, part (2) in `SheafFlatBaseChangeWeakSerre.lean` and
`SheafFlatBaseChangeWeakSerreFppf.lean`, part (3) in `LqcohSheafFbcPullback.lean`, part (4)(a) in
`LqcohSheafFbcFppfHigherDirectImage.lean` and `LqcohSheafFbcTotalDirectImage.lean`, part (4)(b) in
`LqcohSheafFbcHigherDirectImage.lean` and `LqcohSheafFbcFppfHigherDirectImage.lean`, part (5) in
`SheafFlatBaseChangeColimits.lean`, part (6) in `SheafFlatBaseChangeTensor.lean` and part (7) in
`SheafFlatBaseChangeInternalHom.lean`, all under
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/`.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 075Z](https://stacks.math.columbia.edu/tag/075Z)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Part (1): a member of `LQCoh^fbc` is an fppf sheaf -/

section PartOne

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **The fppf sheaf condition for the presheaf-level `LQCoh^fbc`.** A presheaf of modules over
the structure sheaf of a category fibred in groupoids over the big fppf site which is locally
quasi-coherent (**Stacks 06WJ**) and has the presheaf-level flat base change property
`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` is a sheaf for the fppf topology of
**Stacks 06TP**.

This is not **Stacks 0771** part (1): the presheaf-level property is strictly stronger than
**Stacks 0762**, so its hypothesis leaves out members of `LQCoh^fbc` such as `𝒪(-1)` on `ℙ¹`.
Part (1) is
`AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange`.

Membership in `LQCoh^fbc` asks the comparison map `c_φ` of **Stacks 06WC** to be an isomorphism
along every arrow lying over a flat morphism of schemes, which is more than the hypothesis of
**Stacks 076T**, where only the arrows lying over a flat morphism locally of finite presentation
are looked at. So this is **Stacks 076T** after
`AlgebraicGeometry.Stack.hasFlatLfpBaseChangeProperty_of_hasFlatBaseChangeProperty`. -/
theorem isSheaf_fppf_of_isLocallyQuasicoherentWithFlatBaseChange
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp F) :
    Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf :=
  isSheaf_fppf_of_isLocallyQuasicoherent_of_flatBaseChange B E h S hS p hp F hF.1
    (hasFlatLfpBaseChangeProperty_of_hasFlatBaseChangeProperty B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) F hF.2)

end PartOne

section PartOneStack

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The module on the fppf site of an algebraic stack that a member of the presheaf-level
`LQCoh^fbc(𝒪_𝒳)` is, being a sheaf for the fppf topology by
`AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherentWithFlatBaseChange`. The
corresponding clause of **Stacks 0771** part (1), at the reading of **Stacks 0762**, is
`AlgebraicGeometry.Stack.fppfModuleOfLqcohSheafFbc`.

No transport is involved. The presheaf of rings underlying the structure sheaf of **Stacks 06TV**
is `p.op ⋙ (BigFppfOver.structureSheaf B S hS).obj` whichever of the five topologies of
**Stacks 06TP** it is read at, so the presheaf of modules is already a presheaf of modules over
the fppf structure sheaf, and only its sheaf condition has to be improved. -/
def fppfModuleOfLocallyQuasicoherentWithFlatBaseChange
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F) :
    fppfModules B S hS 𝒳 where
  val := F
  isSheaf := isSheaf_fppf_of_isLocallyQuasicoherentWithFlatBaseChange B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F hF

/-- The module on the fppf site produced by part (1) has the given presheaf of modules
underneath it: part (1) changes the sheaf condition and nothing else. -/
@[simp]
theorem fppfModuleOfLocallyQuasicoherentWithFlatBaseChange_val
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F) :
    (fppfModuleOfLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳 F hF).val = F :=
  rfl

/-- The module on the fppf site produced by part (1) lies in the subcategory
`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` whose derived category **Stacks 07B6** takes the Verdier quotient
of. Its membership condition is a condition on the underlying presheaf of modules, which part (1)
leaves alone. -/
theorem fppfModuleOfLocallyQuasicoherentWithFlatBaseChange_mem
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F) :
    locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳
      (fppfModuleOfLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳 F hF) :=
  hF

end PartOneStack

/-! ### A presheaf-level statement of the shape of part (4)(b) -/

/-- **A presheaf-level statement of the shape of Stacks 0771 part (4)(b), whose hypotheses cannot
all hold.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact (**Stacks 050U**) and
quasi-separated (**Stacks 04YW**) 1-morphism of algebraic stacks over `S` and let `ℱ` be a sheaf
of `𝒪_𝒳`-modules on `𝒳_étale` which is locally quasi-coherent (**Stacks 06WJ**) and has the flat
base change property in the presheaf-level reading. Then the higher direct image `Rⁱf_*ℱ` of
**Stacks 06WE**, computed in the étale topology, is again locally quasi-coherent *and* has the
flat base change property, in every degree `i`: that is, `Rⁱf_*` carries the presheaf-level
`LQCoh^fbc(𝒪_𝒳)` into the presheaf-level `LQCoh^fbc(𝒪_𝒴)`.

The flat base change property is the presheaf-level one, read at section universe `u + 1`, where
the higher direct images of module sheaves live, by
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`.

This is the conclusion of the criterion of **Stacks 076Z** at the rule `LQCoh^fbc`, so it is
obtained from exactly the six hypotheses
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_moduleSheafHigherDirectImage`
(**Stacks 0765**) carries, each a result of the source this library does not have: `hcrit` is
**Stacks 076Z** quantified over every rule, `hserre` is parts (1) to (3) of **Stacks 06WM** with
part (2) of **Stacks 0764**, `hfbcPull` is part (1) of **Stacks 0764**, `hconvLqc` and `hconvFbc`
are **Stacks 075Y** at section universe `u + 1` and part (3) of **Stacks 0764**, and `haffine` is
the affine case, from **Stacks 075P** and **Stacks 073K**. **Stacks 0765** is the same criterion
with only the flat base change conjunct of its conclusion kept, and **Stacks 075Z** is the
criterion at the rule of local quasi-coherence alone; neither of them states the conjunction, and
the conjunction is what part (4)(b) asserts.

In the presheaf reading the conclusion is false: Example 3 of the module docstring of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SheafFlatBaseChangeProperty.lean` takes a
closed point `i : pt ⟶ ℙ¹` over a field (a closed immersion, so quasi-compact and
quasi-separated), `ℱ = 𝒪_pt` (which has the presheaf-level property) and degree `0`, and shows
that `i_*𝒪_pt` does not have the presheaf-level property. So over any base where that example can
be built, the six hypotheses below cannot all hold, and this theorem is not **Stacks 0771**.
Part (4)(b), at the reading of **Stacks 0762**, is
`AlgebraicGeometry.Stack.lqcohSheafFbcModuleRule_stackModuleHigherDirectImage` (étale) and
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage` (fppf).

Hypothesis (2) of the criterion for local quasi-coherence is **Stacks 06WL** and is not carried:
it is supplied by
`AlgebraicGeometry.Stack.isStableUnderSmoothPullback_locallyQuasicoherentRule`, which also
supplies the forward half of hypothesis (3). -/
theorem isLocallyQuasicoherentWithFlatBaseChangeUnivLE_moduleSheafHigherDirectImage
    (hcrit : SmoothLocalHigherDirectImageCriterion.{u, t, s} B S hS)
    (hserre : StackEtaleModuleRule.IsWeakSerre.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS))
    (hfbcPull : StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS
      (flatBaseChangePropertyRule B E h S hS))
    (hconvLqc : StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (locallyQuasicoherentRule B E h S hS))
    (hconvFbc : StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (flatBaseChangePropertyRule B E h S hS))
    (haffine : StackEtaleModuleRule.PreservesHigherDirectImagesOfAffine.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) (i : ℕ) :
    letI := hasSheafify_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    ∀ ℱ : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
        (etaleTopology B) (etaleTopology_le_topology B)),
      IsLocallyQuasicoherent B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ℱ.val →
        HasFlatBaseChangePropertyUnivLE B E h S hS
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
            (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
            (etaleTopology B) (etaleTopology_le_topology B) ℱ.val →
          IsLocallyQuasicoherent B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
              ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
                (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
                (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
                (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
                (etaleTopology_le_topology B) i).obj ℱ).val ∧
            HasFlatBaseChangePropertyUnivLE B E h S hS 𝒴.val.val.p
              𝒴.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
              ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
                (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
                (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
                (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
                (etaleTopology_le_topology B) i).obj ℱ).val :=
  fun ℱ hlqc hfbc =>
    hcrit (locallyQuasicoherentFlatBaseChangeRule B E h S hS) hserre
      (isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeRule B E h S hS hfbcPull)
      (isSmoothLocal_locallyQuasicoherentFlatBaseChangeRule B E h S hS hfbcPull hconvLqc
        hconvFbc)
      haffine f hqc hqs i ℱ ⟨hlqc, hfbc⟩

end AlgebraicGeometry.Stack

end
