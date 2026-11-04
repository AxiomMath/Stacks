module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentPullbackSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfLowerShriekCounitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfLowerShriekQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfRestrictionQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyBijectiveRestrictComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerreLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeHigherDirectImageQuasiCompact

/-!
# Stacks 07BC: the derived direct image on quasi-coherent derived categories

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks.
**Stacks 07BC** asserts that `Rf_*` induces a commutative diagram

```
D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⟶ D⁺_{LQCoh^fbc}(𝒪_𝒳) ⟶ D(𝒪_𝒳)
        | Rf_*                         | Rf_*                | Rf_*
D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴) ⟶ D⁺_{LQCoh^fbc}(𝒪_𝒴) ⟶ D(𝒪_𝒴)
```

and hence a functor `Rf_{QCoh,*} : D⁺_QCoh(𝒪_𝒳) ⥤ D⁺_QCoh(𝒪_𝒴)` on the quotient categories, and
that the functors `Rⁱf_QCoh` of **Stacks 077A** are `Hⁱ ∘ Rf_{QCoh,*}` with `Hⁱ` as in
**Stacks 07B7**.

This file states all of it with no hypothesis beyond quasi-compactness and quasi-separatedness
of `f`, for the class `LQCoh^fbc` of the source (the flat base change property of
**Stacks 0762** read with the pullback of sheaves,
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`), at the
module universe `u + 1` in which the direct image of **Stacks 06WE** on an algebraic stack
exists. The construction is the class-generic one of
`AlgebraicGeometry.Stack.derivedPushforwardPlusSheafFlatBaseChange` and its companions, fed with
its inputs:

* part (4)(b) of **Stacks 0771**, fppf reading, for the faithful class
  (`AlgebraicGeometry.Stack.AlgebraicStacks.sheafFlatBaseChange_higherDirectImage`) — this is
  where quasi-compactness and quasi-separatedness are used, as in the source;
* part (2) of **Stacks 0771**, fppf, at module universe `u + 1`
  (`isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModulesSucc` in the namespace
  `AlgebraicGeometry.Stack`, read on the spelling used here by
  `AlgebraicGeometry.Stack.FlatFppf.isWeakSerreClass_sheafFlatBaseChangeFppfModulesUnivLE`);
* for the final assertion: the inclusion `QCoh(𝒪_𝒵) ⊆ LQCoh^fbc(𝒪_𝒵)` of **Stacks 06WK**
  (`isQuasicoherentOnSite_le_locallyQuasicoherentSheafFlatBaseChangeFppfModules_succ` in the
  namespace `AlgebraicGeometry.Stack`), the coherator `Q = g_! g^*` of **Stacks 0778** and the
  cohomology functor `Hⁱ` of **Stacks 07B7** at module universe `u + 1`
  (`AlgebraicGeometry.Stack.FlatFppf.coherator`,
  `AlgebraicGeometry.Stack.FlatFppf.quasicoherentCohomology`), over their three inputs, all in
  the namespace `AlgebraicGeometry.Stack.FlatFppf`: `g_! g^* = id` (**Stacks 0789** (2),
  `moduleLowerShriekSuccAdjunction`), `g^*` of a module of `LQCoh^fbc` is quasi-coherent
  (**Stacks 07B1** (2)(b),
  `isQuasicoherentOnSite_moduleInverseImage_of_sheafFlatBaseChangeModulesSucc`) and `g_!` of a
  quasi-coherent module is quasi-coherent (**Stacks 07B0** (2),
  `isQuasicoherentOnSite_moduleLowerShriekSucc`).

The right-hand column is the unbounded derived category, with the unbounded `Rf_*` of
`AlgebraicGeometry.Stack.fppfDerivedPushforwardOfStacks`. The functor `Hⁱ` of **Stacks 07B7**
is defined on the unbounded quotient `D_QCoh`; it is read on `D⁺_QCoh` through the functor
`D⁺_QCoh ⥤ D_QCoh` induced by the inclusion. `Rⁱf_QCoh` is the composite by which
**Stacks 077A** defines it, `QCoh(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒴) ⟶ QCoh(𝒪_𝒴)` with
`Rⁱf_*` in the middle and `Q` at the end; the equality of the source is the natural isomorphism
`Hⁱ(Rf_{QCoh,*}(M[0])) ≅ Rⁱf_QCoh(M)`, together with its form on all of `D⁺_{LQCoh^fbc}(𝒪_𝒳)`,
`Hⁱ ∘ Rf_{QCoh,*} ∘ q_𝒳 ≅ Q ∘ Hⁱ ∘ Rf_*`.

## Main definitions

* `AlgebraicGeometry.Stack.sheafFlatBaseChangeDerivedPushforwardPlus`,
  `AlgebraicGeometry.Stack.parasiticSheafFlatBaseChangeDerivedPushforwardPlus`: the middle and
  left vertical arrows.
* `AlgebraicGeometry.Stack.quasicoherentDerivedPushforwardPlus`: `Rf_{QCoh,*}`.
* `AlgebraicGeometry.Stack.plusQuasicoherentCohomology`: `Hⁱ` on `D⁺_QCoh`.
* `AlgebraicGeometry.Stack.sheafFlatBaseChangeQuasicoherentHigherDirectImage`: `Rⁱf_QCoh`.
* `AlgebraicGeometry.Stack.sheafFlatBaseChangeDerivedPushforwardPlusCompιIso`: the right square.
* `AlgebraicGeometry.Stack.quasicoherentDerivedPushforwardPlusCohomologyIso`:
  `Hⁱ(Rf_{QCoh,*}(𝓜[0])) ≅ Rⁱf_QCoh(𝓜)`.

## Main results

* `AlgebraicGeometry.Stack.ιOfLE_comp_sheafFlatBaseChangeDerivedPushforwardPlus`: the left square
  commutes.
* `AlgebraicGeometry.Stack.toSerreQuotient_comp_quasicoherentDerivedPushforwardPlus`:
  `Rf_{QCoh,*}` is induced by `Rf_*`.

## References

* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B7](https://stacks.math.columbia.edu/tag/07B7)
* [Stacks Project, Tag 07BC](https://stacks.math.columbia.edu/tag/07BC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

/- The universe-polymorphic `Abelian (SheafOfModules.{max u v r w} O)` instance leaves a universe
metavariable that the elaborator cannot solve against the module universe `u + 1` of these sites;
the abelian structure used here is the one the local sheafification instances above produce. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] FlatFppf.isWeakSerreClass_sheafFlatBaseChangeFppfModulesUnivLE

/-- The derived category of the fppf modules at module universe `u + 1`, read on the spelling
`SheafOfModules (FlatFppf.ambientRingStructureSheaf ..)` of `Mod(𝒪_𝒵)` on which the coherator and
the cohomology functor of **Stacks 07B7** are stated. -/
abbrev hasDerivedCategoryAmbientSucc (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [i : HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)] :
    HasDerivedCategory.{u + 2}
      (SheafOfModules.{u + 1} (FlatFppf.ambientRingStructureSheaf B S hS 𝒵)) := i

attribute [local instance] hasDerivedCategoryAmbientSucc

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]
  (f : 𝒳 ⟶ 𝒴) (hqc : IsQuasiCompactMorphism B S hS f)
  (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)

/-! ### The diagram -/

/-- **Stacks 07BC, the middle vertical arrow** `Rf_* : D⁺_{LQCoh^fbc}(𝒪_𝒳) ⥤ D⁺_{LQCoh^fbc}(𝒪_𝒴)`
for a quasi-compact quasi-separated `f`: the restriction of `Rf_*`. -/
@[stacks 07BC "the middle vertical arrow Rf_* : D⁺_LQCoh^fbc(𝒪_𝒳) ⥤ D⁺_LQCoh^fbc(𝒪_𝒴) of the \
  diagram, for the faithful LQCoh^fbc (flat base change with the sheaf pullback, Stacks 0762), at \
  module universe u + 1"]
def sheafFlatBaseChangeDerivedPushforwardPlus :
    (DerivedCategoryB.derivedCategoryBInPlus
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
        𝒳)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBInPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒴)).FullSubcategory :=
  derivedPushforwardPlusSheafFlatBaseChange B E h S hS f
    (FlatFppf.sheafFlatBaseChange_moduleSheafHigherDirectImage B E h S hS f hqc hqs)

/-- **Stacks 07BC, the left vertical arrow**
`Rf_* : D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⥤ D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)` for a quasi-compact
quasi-separated `f`: the restriction of `Rf_*` (the parasitic half is **Stacks 0775** (2)). -/
@[stacks 07BC "the left vertical arrow Rf_* : D⁺_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳) ⥤ \
  D⁺_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒴) of the diagram"]
def parasiticSheafFlatBaseChangeDerivedPushforwardPlus :
    (DerivedCategoryB.derivedCategoryBInPlus
      (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
        lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒳)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBInPlus
        (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒴)).FullSubcategory :=
  derivedPushforwardPlusParasiticSheafFlatBaseChange B E h S hS f
    (FlatFppf.sheafFlatBaseChange_moduleSheafHigherDirectImage B E h S hS f hqc hqs)

/-- **Stacks 07BC, the left square** of the diagram commutes: the inclusion
`D⁺_{Parasitic ∩ LQCoh^fbc} ⊆ D⁺_{LQCoh^fbc}` followed by the middle arrow is the left arrow
followed by the inclusion. -/
@[stacks 07BC "the left square of the diagram commutes (an equality of functors)"]
theorem ιOfLE_comp_sheafFlatBaseChangeDerivedPushforwardPlus :
    ObjectProperty.ιOfLE (derivedCategoryBInPlus_parasiticSheafFlatBaseChange_le B E h S hS 𝒳) ⋙
        sheafFlatBaseChangeDerivedPushforwardPlus B E h S hS f hqc hqs =
      parasiticSheafFlatBaseChangeDerivedPushforwardPlus B E h S hS f hqc hqs ⋙
        ObjectProperty.ιOfLE
          (derivedCategoryBInPlus_parasiticSheafFlatBaseChange_le B E h S hS 𝒴) :=
  rfl

/-- **Stacks 07BC, the right square** of the diagram commutes: the middle arrow followed by the
inclusion `D⁺_{LQCoh^fbc}(𝒪_𝒴) ⊆ D(𝒪_𝒴)` is the inclusion `D⁺_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)` followed
by the unbounded `Rf_* : D(𝒪_𝒳) ⥤ D(𝒪_𝒴)`, up to the canonical isomorphism identifying the
bounded below `Rf_*` with the restriction of the unbounded one. -/
@[stacks 07BC "the right square of the diagram, into the unbounded D(𝒪) with the unbounded Rf_*, \
  commutes up to the canonical isomorphism Rf_*⁺ ⋙ ι ≅ ι ⋙ Rf_*"]
def sheafFlatBaseChangeDerivedPushforwardPlusCompιIso :
    sheafFlatBaseChangeDerivedPushforwardPlus B E h S hS f hqc hqs ⋙
        (DerivedCategoryB.derivedCategoryBInPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒴)).ι ⋙ DerivedCategory.Plus.ι ≅
      (DerivedCategoryB.derivedCategoryBInPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒳)).ι ⋙ DerivedCategory.Plus.ι ⋙ fppfDerivedPushforwardOfStacks B S hS f :=
  derivedPushforwardPlusSheafFlatBaseChangeCompιIso B E h S hS f _

/-- In `D⁺` the middle arrow is the restriction of `Rf_*`, on the nose. -/
theorem sheafFlatBaseChangeDerivedPushforwardPlus_comp_ι :
    sheafFlatBaseChangeDerivedPushforwardPlus B E h S hS f hqc hqs ⋙
        (DerivedCategoryB.derivedCategoryBInPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒴)).ι =
      (DerivedCategoryB.derivedCategoryBInPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒳)).ι ⋙ fppfDerivedPushforwardPlusOfStacks B S hS f :=
  rfl

/-! ### The induced functor on the quotient categories -/

/-- **Stacks 07BC, the induced functor** `Rf_{QCoh,*} : D⁺_QCoh(𝒪_𝒳) ⥤ D⁺_QCoh(𝒪_𝒴)` on the
quotients `D⁺_QCoh = D⁺_{LQCoh^fbc} / D⁺_{Parasitic ∩ LQCoh^fbc}` of **Stacks 07B6**, for a
quasi-compact quasi-separated `f`. -/
@[stacks 07BC "the induced functor Rf_(QCoh,*) : D⁺_QCoh(𝒪_𝒳) ⥤ D⁺_QCoh(𝒪_𝒴) on the quotient \
  categories D⁺_LQCoh^fbc / D⁺_(Parasitic ∩ LQCoh^fbc)"]
def quasicoherentDerivedPushforwardPlus :
    (DerivedCategoryB.serreQuotientWPlus
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳)
      (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
        lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒳)).Localization ⥤
      (DerivedCategoryB.serreQuotientWPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
        (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒴)).Localization :=
  derivedPushforwardQuasicoherentPlusSheafFlatBaseChange B E h S hS f
    (FlatFppf.sheafFlatBaseChange_moduleSheafHigherDirectImage B E h S hS f hqc hqs)

/-- **Stacks 07BC: `Rf_{QCoh,*}` is induced by `Rf_*`** — the quotient functor of `𝒳` followed by
`Rf_{QCoh,*}` is the middle arrow followed by the quotient functor of `𝒴`. -/
@[stacks 07BC "Rf_(QCoh,*) is the functor induced by Rf_* on the quotient categories: the \
  quotient square commutes (an equality of functors)"]
theorem toSerreQuotient_comp_quasicoherentDerivedPushforwardPlus :
    (DerivedCategoryB.serreQuotientWPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳)
        (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒳)).Q ⋙
        quasicoherentDerivedPushforwardPlus B E h S hS f hqc hqs =
      sheafFlatBaseChangeDerivedPushforwardPlus B E h S hS f hqc hqs ⋙
        (DerivedCategoryB.serreQuotientWPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
          (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
            lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
              𝒴)).Q :=
  toSerreQuotient_comp_derivedPushforwardQuasicoherentPlus B E h S hS f _

/-! ### The final assertion -/

section FinalAssertion

open FlatFppf

/-- **`Hⁱ : D⁺_QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒴)`**: the cohomology functor of **Stacks 07B7** read on the
bounded below quotient, through `D⁺_QCoh(𝒪_𝒴) ⥤ D_QCoh(𝒪_𝒴)`. -/
def plusQuasicoherentCohomology (i : ℤ) :
    (DerivedCategoryB.serreQuotientWPlus
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
      (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
        lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒴)).Localization ⥤
      (quasicoherentModulesSucc B S hS 𝒴).FullSubcategory :=
  DerivedCategoryB.serreQuotientPlusToSerreQuotient _ _ ⋙
    quasicoherentCohomology (moduleLowerShriekSuccAdjunction B S hS 𝒴)
      (isQuasicoherentOnSite_le_locallyQuasicoherentSheafFlatBaseChangeFppfModules_succ
        B E h S hS 𝒴)
      (isQuasicoherentOnSite_moduleLowerShriekSucc_moduleInverseImage
        (isQuasicoherentOnSite_moduleLowerShriekSucc B S hS 𝒴)
        (isQuasicoherentOnSite_moduleInverseImage_of_sheafFlatBaseChangeModulesSucc B E h S hS 𝒴))
      (isIso_moduleLowerShriekSuccAdjunction_counit_app
        (isQuasicoherentOnSite_moduleLowerShriekSucc B S hS 𝒴)) i

include hqc hqs in
/-- **`Rⁱf_QCoh : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)` of Stacks 077A**, by its definition there: the
composite `QCoh(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒴) ⟶ QCoh(𝒪_𝒴)` of the inclusion
(**Stacks 06WK**), the higher direct image `Rⁱf_*` (which preserves `LQCoh^fbc` by
**Stacks 0771**) and the coherator `Q` of **Stacks 0778**. -/
def sheafFlatBaseChangeQuasicoherentHigherDirectImage (i : ℕ) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).FullSubcategory ⥤
      (quasicoherentModulesSucc B S hS 𝒴).FullSubcategory :=
  ObjectProperty.ιOfLE
      (isQuasicoherentOnSite_le_locallyQuasicoherentSheafFlatBaseChangeFppfModules_succ
        B E h S hS 𝒳) ⋙
    sheafFlatBaseChangeHigherDirectImage B E h S hS f
      (FlatFppf.sheafFlatBaseChange_moduleSheafHigherDirectImage B E h S hS f hqc hqs) i ⋙
      coherator (isQuasicoherentOnSite_moduleLowerShriekSucc_moduleInverseImage
        (isQuasicoherentOnSite_moduleLowerShriekSucc B S hS 𝒴)
        (isQuasicoherentOnSite_moduleInverseImage_of_sheafFlatBaseChangeModulesSucc B E h S hS 𝒴))

/-- **Stacks 07BC, the final assertion: `Rⁱf_QCoh = Hⁱ ∘ Rf_{QCoh,*}`.** For a quasi-coherent
`𝓜` on `𝒳`, placed in degree zero of `D⁺_QCoh(𝒪_𝒳)`, `Hⁱ(Rf_{QCoh,*}(𝓜[0])) ≅ Rⁱf_QCoh(𝓜)`,
naturally in `𝓜`, with `Hⁱ` the cohomology functor of **Stacks 07B7** and `Rⁱf_QCoh` the functor
of **Stacks 077A**. -/
@[stacks 07BC "the final assertion: the functors Rⁱf_QCoh of Stacks 077A are Hⁱ ∘ Rf_(QCoh,*) \
  with Hⁱ of Stacks 07B7, as a natural isomorphism of functors QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴) (𝓜 placed \
  in degree zero)"]
def quasicoherentDerivedPushforwardPlusCohomologyIso (i : ℕ) :
    ObjectProperty.ιOfLE
          (isQuasicoherentOnSite_le_locallyQuasicoherentSheafFlatBaseChangeFppfModules_succ
            B E h S hS 𝒳) ⋙
        sheafFlatBaseChangeSingleFunctor B E h S hS 𝒳 ⋙
        (DerivedCategoryB.serreQuotientWPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳)
          (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
            lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
              𝒳)).Q ⋙
          quasicoherentDerivedPushforwardPlus B E h S hS f hqc hqs ⋙
            plusQuasicoherentCohomology B E h S hS i ≅
      sheafFlatBaseChangeQuasicoherentHigherDirectImage B E h S hS f hqc hqs i :=
  Functor.isoWhiskerLeft _
    (singleCompDerivedPushforwardQuasicoherentPlusCompIso B E h S hS f _ i _ _
      (plusSerreQuotientCohomologyFac B E h S hS 𝒴 i _ _
        (quasicoherentCohomologyFac _ _ _ _ i)))

/-- **Stacks 07BC, the final assertion on all of `D⁺_{LQCoh^fbc}(𝒪_𝒳)`**: `Hⁱ ∘ Rf_{QCoh,*}`
composed with the quotient functor of `𝒳` is `Q ∘ Hⁱ ∘ Rf_*`, with `Hⁱ` the cohomology functor
of **Stacks 07B7** and `Q` the coherator of **Stacks 0778**. -/
@[stacks 07BC "the final assertion on D⁺_LQCoh^fbc(𝒪_𝒳): Hⁱ ∘ Rf_(QCoh,*) ∘ (quotient functor) \
  ≅ Q ∘ Hⁱ ∘ Rf_*, the identity the source reads off the definition of Hⁱ"]
def toSerreQuotient_comp_quasicoherentDerivedPushforwardPlusCohomologyIso (i : ℤ) :
    (DerivedCategoryB.serreQuotientWPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳)
        (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒳)).Q ⋙
        quasicoherentDerivedPushforwardPlus B E h S hS f hqc hqs ⋙
          plusQuasicoherentCohomology B E h S hS i ≅
      sheafFlatBaseChangeDerivedPushforwardPlus B E h S hS f hqc hqs ⋙
        sheafFlatBaseChangeHomologyFunctor B E h S hS 𝒴 i ⋙
          coherator (isQuasicoherentOnSite_moduleLowerShriekSucc_moduleInverseImage
            (isQuasicoherentOnSite_moduleLowerShriekSucc B S hS 𝒴)
            (isQuasicoherentOnSite_moduleInverseImage_of_sheafFlatBaseChangeModulesSucc
              B E h S hS 𝒴)) :=
  derivedPushforwardQuasicoherentPlusCompIso B E h S hS f _ _ _
    (plusSerreQuotientCohomologyFac B E h S hS 𝒴 i _ _
      (quasicoherentCohomologyFac _ _ _ _ i))

end FinalAssertion

end AlgebraicGeometry.Stack
