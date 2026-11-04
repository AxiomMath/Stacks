module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreQuotientCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreQuotientDerivedPullbackAdjunction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardOfStacksUnbounded
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardTriangulated
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSheaves
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOverStackOfFlatObject
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DirectImageSectionsRightKan
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticRightDerivedOfSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CocontinuousPushforwardCorepresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.RightDerivedThroughUnderlyingAbelianSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakSerreClassInf
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The derived direct image on `D⁺_{LQCoh^fbc}`, for the class of the source

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and `Rf_* : D⁺(𝒪_𝒳) ⥤ D⁺(𝒪_𝒴)` the total
right derived functor of the direct image of **Stacks 06WE** on fppf modules, at module
universe `u + 1` (`AlgebraicGeometry.Stack.fppfDerivedPushforwardPlusOfStacks`). Write `𝒜` for
the class `LQCoh^fbc` of **Stacks 0762**, with the flat base change property read with the
pullback of *sheaves* as in the source
(`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`), and
`𝒮 = Parasitic ∩ 𝒜`.

This file builds the whole diagram of **Stacks 07BC** out of the one input its proof uses
about `f`: that every higher direct image `Rᵖf_*` carries `𝒜(𝒳)` into `𝒜(𝒴)` (part (4)(b) of
**Stacks 0771**, which is where quasi-compactness and quasi-separatedness of `f` enter), together
with the weak Serre property of `𝒜` (part (2) of **Stacks 0771**). Given those:

* `Rf_*` carries `D⁺_𝒜(𝒪_𝒳)` into `D⁺_𝒜(𝒪_𝒴)`, by the spectral sequence `Rᵖf_*Hᵠ(K) ⇒ Rᵖ⁺ᵠf_*K`
  (`AlgebraicGeometry.Stack.fppfDerivedPushforwardPlusOfStacks_obj_mem_of_higherDirectImage`);
* it carries `D⁺_𝒮(𝒪_𝒳)` into `D⁺_𝒮(𝒪_𝒴)`, by the same spectral sequence and **Stacks 0775**
  part (2) (`AlgebraicGeometry.Stack.isParasitic_moduleSheafHigherDirectImage`);
* hence the two restricted functors, the commuting squares of the diagram, and the functor
  `Rf_{QCoh,*} : D⁺_QCoh(𝒪_𝒳) ⥤ D⁺_QCoh(𝒪_𝒴)` on the Verdier quotients of **Stacks 07B6**,
  which is `DerivedCategoryB.serreQuotientPushforwardPlus` — the functor **Stacks 07BE** pairs
  with the derived pullback — by definition;
* and the identification of `Hⁱ ∘ Rf_{QCoh,*}` with `Q ∘ Rⁱf_*`, for any functor `Hⁱ` on
  `D⁺_QCoh(𝒪_𝒴)` with the defining identity of **Stacks 07B7**, on all of `D⁺_𝒜(𝒪_𝒳)` and on
  objects placed in degree zero, where `Hⁱ(Rf_*(M[0]))` is the `i`-th right derived functor
  `Rⁱf_*M`.

## Main definitions

* `AlgebraicGeometry.Stack.derivedPushforwardPlusSheafFlatBaseChange`,
  `AlgebraicGeometry.Stack.derivedPushforwardPlusParasiticSheafFlatBaseChange`: the middle and
  left vertical functors of the diagram.
* `AlgebraicGeometry.Stack.derivedPushforwardQuasicoherentPlusSheafFlatBaseChange`:
  `Rf_{QCoh,*}`.
* `AlgebraicGeometry.Stack.sheafFlatBaseChangeSingleFunctor`: `M ↦ M[0]`,
  `𝒜(𝒳) ⥤ D⁺_𝒜(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.derivedCategoryB_sheafFlatBaseChange_fppfDerivedPushforwardPlus_obj`
  and its parasitic companion: the two preservation clauses.
* `AlgebraicGeometry.Stack.derivedPushforwardPlusSheafFlatBaseChange_comp_ι`,
  `AlgebraicGeometry.Stack.derivedPushforwardPlusParasiticSheafFlatBaseChange_comp_ι`,
  `AlgebraicGeometry.Stack.ιOfLE_comp_derivedPushforwardPlusSheafFlatBaseChange`: the commuting
  squares, read in `D⁺`.
* `AlgebraicGeometry.Stack.derivedPushforwardPlusSheafFlatBaseChangeCompιIso`,
  `AlgebraicGeometry.Stack.derivedPushforwardPlusParasiticSheafFlatBaseChangeCompιIso`: the
  squares into the right-hand column, the unbounded `Rf_* : D(𝒪_𝒳) ⥤ D(𝒪_𝒴)` of
  `AlgebraicGeometry.Stack.fppfDerivedPushforwardOfStacks`.
* `AlgebraicGeometry.Stack.toSerreQuotient_comp_derivedPushforwardQuasicoherentPlus`: the
  quotient square, which says that `Rf_{QCoh,*}` is induced by `Rf_*`.
* `AlgebraicGeometry.Stack.derivedPushforwardQuasicoherentPlusCompIso`,
  `AlgebraicGeometry.Stack.singleCompDerivedPushforwardQuasicoherentPlusCompIso`: the final
  assertion, over the defining identity of `Hⁱ`.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
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

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒳).IsWeakSerreClass]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒴).IsWeakSerreClass]
  (f : 𝒳 ⟶ 𝒴)
  (h𝒜 : ∀ M, lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
      𝒳 M → ∀ p : ℕ,
    lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴
      ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf) p).obj M))

/-! ### The two preservation clauses -/

include h𝒜 in
/-- **`Rf_*` carries `D⁺_{LQCoh^fbc}(𝒪_𝒳)` into `D⁺_{LQCoh^fbc}(𝒪_𝒴)`**, for the class of the
source, as soon as every higher direct image carries `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`. -/
theorem derivedCategoryB_sheafFlatBaseChange_fppfDerivedPushforwardPlus_obj
    (K : DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳))
    (hK : DerivedCategoryB.derivedCategoryB
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳)
      K.obj) :
    DerivedCategoryB.derivedCategoryB
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
      ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K).obj :=
  fppfDerivedPushforwardPlusOfStacks_obj_mem_of_higherDirectImage B S hS f _ _ h𝒜 K hK

omit [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒳).IsWeakSerreClass]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒴).IsWeakSerreClass] in
include h𝒜 in
/-- **The higher direct images carry `Parasitic ∩ LQCoh^fbc(𝒪_𝒳)` into
`Parasitic ∩ LQCoh^fbc(𝒪_𝒴)`**, for the class of the source, as soon as they carry
`LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`: the parasitic half is **Stacks 0775** part (2). -/
theorem parasiticSheafFlatBaseChange_moduleSheafHigherDirectImage
    (M : fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)
    (hM : (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
      lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳) M)
    (p : ℕ) :
    (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
      lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
      ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf) p).obj M) :=
  ⟨isParasitic_moduleSheafHigherDirectImage f .fppf (Or.inr rfl) M hM.1 p, h𝒜 M hM.2 p⟩

include h𝒜 in
/-- **`Rf_*` carries `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` into `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)`**,
for the class of the source, as soon as every higher direct image carries `LQCoh^fbc(𝒪_𝒳)` into
`LQCoh^fbc(𝒪_𝒴)`. -/
theorem derivedCategoryB_parasiticSheafFlatBaseChange_fppfDerivedPushforwardPlus_obj
    (K : DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳))
    (hK : DerivedCategoryB.derivedCategoryB
      (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
        lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳)
      K.obj) :
    DerivedCategoryB.derivedCategoryB
      (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
        lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
      ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K).obj :=
  fppfDerivedPushforwardPlusOfStacks_obj_mem_of_higherDirectImage B S hS f _ _
    (parasiticSheafFlatBaseChange_moduleSheafHigherDirectImage B E h S hS f h𝒜) K hK

/-! ### The diagram -/

section Diagram

attribute [local instance] additive_fppfModuleSheafPushforwardOfStacks
  enoughInjectives_fppfModulesUnivLESucc

/-- **Stacks 07BC, the middle vertical functor**
`Rf_* : D⁺_{LQCoh^fbc}(𝒪_𝒳) ⥤ D⁺_{LQCoh^fbc}(𝒪_𝒴)`, for the class of the source: the
restriction of `Rf_*`, which exists by
`AlgebraicGeometry.Stack.derivedCategoryB_sheafFlatBaseChange_fppfDerivedPushforwardPlus_obj`.
It is the functor `DerivedCategoryB.derivedCategoryBInPlusMap` of the direct image. -/
def derivedPushforwardPlusSheafFlatBaseChange :
    (DerivedCategoryB.derivedCategoryBInPlus
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
        𝒳)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBInPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒴)).FullSubcategory :=
  DerivedCategoryB.derivedCategoryBInPlusMap (fppfModuleSheafPushforwardOfStacks B S hS f)
    (derivedCategoryB_sheafFlatBaseChange_fppfDerivedPushforwardPlus_obj B E h S hS f h𝒜)

/-- **Stacks 07BC, the left vertical functor**
`Rf_* : D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⥤ D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)`, for the class of the
source: the restriction of `Rf_*`, which exists by
`derivedCategoryB_parasiticSheafFlatBaseChange_fppfDerivedPushforwardPlus_obj`.
-/
def derivedPushforwardPlusParasiticSheafFlatBaseChange :
    (DerivedCategoryB.derivedCategoryBInPlus
      (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
        lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒳)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBInPlus
        (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒴)).FullSubcategory :=
  DerivedCategoryB.derivedCategoryBInPlusMap (fppfModuleSheafPushforwardOfStacks B S hS f)
    (derivedCategoryB_parasiticSheafFlatBaseChange_fppfDerivedPushforwardPlus_obj B E h S hS f
      h𝒜)

/-- **Stacks 07BC, the middle-to-right square**: the middle vertical functor followed by the
inclusion of `D⁺_{LQCoh^fbc}(𝒪_𝒴)` into `D⁺(𝒪_𝒴)` is the inclusion of `D⁺_{LQCoh^fbc}(𝒪_𝒳)`
followed by `Rf_*`. -/
theorem derivedPushforwardPlusSheafFlatBaseChange_comp_ι :
    derivedPushforwardPlusSheafFlatBaseChange B E h S hS f h𝒜 ⋙
        (DerivedCategoryB.derivedCategoryBInPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒴)).ι =
      (DerivedCategoryB.derivedCategoryBInPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒳)).ι ⋙ fppfDerivedPushforwardPlusOfStacks B S hS f :=
  rfl

/-- The left vertical functor followed by the inclusion of `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)` into
`D⁺(𝒪_𝒴)` is the inclusion of `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` followed by `Rf_*`. -/
theorem derivedPushforwardPlusParasiticSheafFlatBaseChange_comp_ι :
    derivedPushforwardPlusParasiticSheafFlatBaseChange B E h S hS f h𝒜 ⋙
        (DerivedCategoryB.derivedCategoryBInPlus
          (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
            lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
              𝒴)).ι =
      (DerivedCategoryB.derivedCategoryBInPlus
          (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
            lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
              𝒳)).ι ⋙ fppfDerivedPushforwardPlusOfStacks B S hS f :=
  rfl

/-- **Stacks 07BC, the middle-to-right square, with the unbounded right-hand column**: the
middle vertical functor followed by the inclusion `D⁺_{LQCoh^fbc}(𝒪_𝒴) ⊆ D(𝒪_𝒴)` is the inclusion
`D⁺_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)` followed by the unbounded `Rf_* : D(𝒪_𝒳) ⥤ D(𝒪_𝒴)`
(`AlgebraicGeometry.Stack.fppfDerivedPushforwardOfStacks`), up to the canonical isomorphism
identifying the bounded below `Rf_*` with the restriction of the unbounded one. -/
def derivedPushforwardPlusSheafFlatBaseChangeCompιIso :
    derivedPushforwardPlusSheafFlatBaseChange B E h S hS f h𝒜 ⋙
        (DerivedCategoryB.derivedCategoryBInPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒴)).ι ⋙ DerivedCategory.Plus.ι ≅
      (DerivedCategoryB.derivedCategoryBInPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒳)).ι ⋙ DerivedCategory.Plus.ι ⋙ fppfDerivedPushforwardOfStacks B S hS f :=
  Functor.isoWhiskerLeft _ (fppfDerivedPushforwardPlusOfStacksCompιIso B S hS f)

/-- The left column followed by the inclusion into `D(𝒪_𝒴)` is the inclusion of
`D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` into `D(𝒪_𝒳)` followed by the unbounded `Rf_*`. -/
def derivedPushforwardPlusParasiticSheafFlatBaseChangeCompιIso :
    derivedPushforwardPlusParasiticSheafFlatBaseChange B E h S hS f h𝒜 ⋙
        (DerivedCategoryB.derivedCategoryBInPlus
          (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
            lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
              𝒴)).ι ⋙ DerivedCategory.Plus.ι ≅
      (DerivedCategoryB.derivedCategoryBInPlus
          (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
            lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
              𝒳)).ι ⋙ DerivedCategory.Plus.ι ⋙ fppfDerivedPushforwardOfStacks B S hS f :=
  Functor.isoWhiskerLeft _ (fppfDerivedPushforwardPlusOfStacksCompιIso B S hS f)

omit [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒳).IsWeakSerreClass]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒴).IsWeakSerreClass] in
/-- `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒵) ⊆ D⁺_{LQCoh^fbc}(𝒪_𝒵)`: the horizontal arrows of the left
square of the diagram of **Stacks 07BC**. -/
theorem derivedCategoryBInPlus_parasiticSheafFlatBaseChange_le (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)] :
    DerivedCategoryB.derivedCategoryBInPlus
        (parasiticModules.{u, w, u + 1} B S hS 𝒵 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒵) ≤
      DerivedCategoryB.derivedCategoryBInPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒵) :=
  fun _ hK n => (hK n).2

/-- **Stacks 07BC, the left square**: the inclusion
`D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D⁺_{LQCoh^fbc}(𝒪_𝒳)` followed by the middle vertical functor
is the left vertical functor followed by the inclusion
`D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴) ⊆ D⁺_{LQCoh^fbc}(𝒪_𝒴)`. -/
theorem ιOfLE_comp_derivedPushforwardPlusSheafFlatBaseChange :
    ObjectProperty.ιOfLE (derivedCategoryBInPlus_parasiticSheafFlatBaseChange_le B E h S hS 𝒳) ⋙
        derivedPushforwardPlusSheafFlatBaseChange B E h S hS f h𝒜 =
      derivedPushforwardPlusParasiticSheafFlatBaseChange B E h S hS f h𝒜 ⋙
        ObjectProperty.ιOfLE
          (derivedCategoryBInPlus_parasiticSheafFlatBaseChange_le B E h S hS 𝒴) :=
  rfl

/-! ### The induced functor on the quotients -/

/-- **Stacks 07BC, the induced functor**

`Rf_{QCoh,*} : D⁺_QCoh(𝒪_𝒳) ⥤ D⁺_QCoh(𝒪_𝒴)`

on the bounded below Verdier quotients
`D⁺_QCoh = D⁺_{LQCoh^fbc} / D⁺_{Parasitic ∩ LQCoh^fbc}` of **Stacks 07B6**, for the class of the
source. It is `DerivedCategoryB.serreQuotientPushforwardPlus` of the direct image, the functor
**Stacks 07BE** pairs with the derived pullback. -/
def derivedPushforwardQuasicoherentPlusSheafFlatBaseChange :
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
  DerivedCategoryB.serreQuotientPushforwardPlus (fppfModuleSheafPushforwardOfStacks B S hS f)
    (derivedCategoryB_sheafFlatBaseChange_fppfDerivedPushforwardPlus_obj B E h S hS f h𝒜)
    (derivedCategoryB_parasiticSheafFlatBaseChange_fppfDerivedPushforwardPlus_obj B E h S hS f
      h𝒜)

/-- **Stacks 07BC, the quotient square**: `Rf_{QCoh,*}` is the functor induced by `Rf_*` — the
quotient functor of `𝒳` followed by `Rf_{QCoh,*}` is the middle vertical functor followed by the
quotient functor of `𝒴`. -/
theorem toSerreQuotient_comp_derivedPushforwardQuasicoherentPlus :
    (DerivedCategoryB.serreQuotientWPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳)
        (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒳)).Q ⋙
        derivedPushforwardQuasicoherentPlusSheafFlatBaseChange B E h S hS f h𝒜 =
      derivedPushforwardPlusSheafFlatBaseChange B E h S hS f h𝒜 ⋙
        (DerivedCategoryB.serreQuotientWPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
          (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
            lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
              𝒴)).Q :=
  Localization.Construction.fac _ _

end Diagram

/-! ### The final assertion -/

/-- **Stacks 07BC, the final assertion, on `D⁺_{LQCoh^fbc}(𝒪_𝒳)`.** Let `Hⁱ` be any functor on
`D⁺_QCoh(𝒪_𝒴)` with an identification `α` of its composite with the quotient functor with a
functor `G` on `D⁺_{LQCoh^fbc}(𝒪_𝒴)` (for **Stacks 07B7**, `G = Q ∘ Hⁱ`). Then
`Hⁱ ∘ Rf_{QCoh,*}`, composed with the quotient functor of `𝒳`, is the middle vertical functor of
the diagram followed by `G`. -/
def derivedPushforwardQuasicoherentPlusCompIso {C : Type*} [Category* C]
    (G : (DerivedCategoryB.derivedCategoryBInPlus
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
        𝒴)).FullSubcategory ⥤ C)
    (H : (DerivedCategoryB.serreQuotientWPlus
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
      (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
        lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒴)).Localization ⥤ C)
    (α : (DerivedCategoryB.serreQuotientWPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
        (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒴)).Q ⋙ H ≅ G) :
    (DerivedCategoryB.serreQuotientWPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳)
        (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒳)).Q ⋙
        derivedPushforwardQuasicoherentPlusSheafFlatBaseChange B E h S hS f h𝒜 ⋙ H ≅
      derivedPushforwardPlusSheafFlatBaseChange B E h S hS f h𝒜 ⋙ G :=
  (Functor.associator _ _ _).symm ≪≫
    eqToIso (congrArg (fun F => F ⋙ H)
      (toSerreQuotient_comp_derivedPushforwardQuasicoherentPlus B E h S hS f h𝒜)) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ α

omit [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒳).IsWeakSerreClass]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒴).IsWeakSerreClass] in
/-- The `i`-th cohomology module `D⁺_{LQCoh^fbc}(𝒪_𝒵) ⥤ LQCoh^fbc(𝒪_𝒵)`, for the class of the
source: the cohomology modules of an object of `D⁺_{LQCoh^fbc}(𝒪_𝒵)` lie in `LQCoh^fbc(𝒪_𝒵)` by
definition. -/
def sheafFlatBaseChangeHomologyFunctor (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)] (i : ℤ) :
    (DerivedCategoryB.derivedCategoryBInPlus
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
        𝒵)).FullSubcategory ⥤
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
        𝒵).FullSubcategory :=
  ObjectProperty.lift _
    ((DerivedCategoryB.derivedCategoryBInPlus _).ι ⋙ DerivedCategory.Plus.homologyFunctor _ i)
    fun K => K.property i

omit [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒳).IsWeakSerreClass]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒴).IsWeakSerreClass] in
/-- The degree-zero embedding `LQCoh^fbc(𝒪_𝒵) ⥤ D⁺_{LQCoh^fbc}(𝒪_𝒵)`, `M ↦ M[0]`, for the class
of the source, which is a weak Serre class (**Stacks 0771** part (2)). -/
def sheafFlatBaseChangeSingleFunctor (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)]
    [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
      𝒵).IsWeakSerreClass] :
    (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
        𝒵).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBInPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒵)).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ DerivedCategory.Plus.singleFunctor _ 0)
    fun M => (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _) M.obj M.property).2

omit [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒳).IsWeakSerreClass]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒴).IsWeakSerreClass] in
/-- The higher direct image `Rᵖf_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)`, for the class of the
source: the middle slot of the composite by which **Stacks 077A** defines `Rᵖf_{QCoh,*}`. -/
def sheafFlatBaseChangeHigherDirectImage (p : ℕ) :
    (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
        𝒳).FullSubcategory ⥤
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
        𝒴).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
      𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf) p)
    fun M => h𝒜 M.obj M.property p

omit [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒳).IsWeakSerreClass]
  [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
    𝒴).IsWeakSerreClass] in
/-- **The cohomology functor of Stacks 07B7 read on `D⁺_QCoh(𝒪_𝒵)`.** A functor `Hⁿ` on the
unbounded quotient `D_QCoh(𝒪_𝒵)` with its defining identity `Hⁿ ∘ q = Φ ∘ Hⁿ` gives, through
`D⁺_QCoh(𝒪_𝒵) ⥤ D_QCoh(𝒪_𝒵)`, a functor on the bounded below quotient with the same defining
identity. -/
def plusSerreQuotientCohomologyFac (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)]
    [(lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
      𝒵).IsWeakSerreClass] (n : ℤ) {C : Type*} [Category* C]
    (Φ : (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
      𝒵).FullSubcategory ⥤ C)
    (Hn : (DerivedCategoryB.serreQuotientW
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒵)
      (parasiticModules.{u, w, u + 1} B S hS 𝒵 .fppf ⊓
        lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒵)).Localization ⥤ C)
    (β : (DerivedCategoryB.serreQuotientW
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒵)
        (parasiticModules.{u, w, u + 1} B S hS 𝒵 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒵)).Q ⋙ Hn ≅ DerivedCategoryB.derivedCategoryBHomology _ n ⋙ Φ) :
    (DerivedCategoryB.serreQuotientWPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒵)
        (parasiticModules.{u, w, u + 1} B S hS 𝒵 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒵)).Q ⋙
        (DerivedCategoryB.serreQuotientPlusToSerreQuotient _ _ ⋙ Hn) ≅
      sheafFlatBaseChangeHomologyFunctor B E h S hS 𝒵 n ⋙ Φ :=
  (Functor.associator _ _ _).symm ≪≫
    eqToIso (congrArg (fun F => F ⋙ Hn)
      (DerivedCategoryB.serreQuotientPlusToSerreQuotient_fac _ _)) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (DerivedCategoryB.plusInclusion _) β

section Single

attribute [local instance] additive_fppfModuleSheafPushforwardOfStacks
  enoughInjectives_fppfModulesUnivLESucc

/-- **The cohomology of `Rf_*` on a module placed in degree zero is the higher direct image**:
`Hⁱ(Rf_*(M[0])) ≅ Rⁱf_*M`, naturally in `M` in `LQCoh^fbc(𝒪_𝒳)`, for the class of the source.
This is the comparison `Stacks.DerivedIndexing.rightDerivedIso` of the `ℤ`-indexed derived
functors of `Rf_*` with Mathlib's `ℕ`-indexed ones, read inside `LQCoh^fbc(𝒪_𝒴)`. -/
def sheafFlatBaseChangeSingleCompHomologyIso (i : ℕ) :
    sheafFlatBaseChangeSingleFunctor B E h S hS 𝒳 ⋙
        derivedPushforwardPlusSheafFlatBaseChange B E h S hS f h𝒜 ⋙
          sheafFlatBaseChangeHomologyFunctor B E h S hS 𝒴 i ≅
      sheafFlatBaseChangeHigherDirectImage B E h S hS f h𝒜 i :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (ObjectProperty.ι _)
      (Stacks.DerivedIndexing.rightDerivedIso (fppfModuleSheafPushforwardOfStacks B S hS f)
        i).symm)

end Single

/-- **Stacks 07BC, the final assertion: `Rⁱf_QCoh = Hⁱ ∘ Rf_{QCoh,*}`.** Let `Φ` be a functor on
`LQCoh^fbc(𝒪_𝒴)` (for **Stacks 07B7** and **Stacks 077A**, the coherator `Q` of
**Stacks 0778**), and `Hⁱ` a functor on `D⁺_QCoh(𝒪_𝒴)` with the defining identity `α` of
**Stacks 07B7**: composed with the quotient functor it is `Φ ∘ Hⁱ`. Then for `M` in
`LQCoh^fbc(𝒪_𝒳)` placed in degree zero,

`Hⁱ(Rf_{QCoh,*}(M[0])) ≅ Φ(Rⁱf_*M)`,

naturally in `M`: the right-hand side is the composite by which **Stacks 077A** defines
`Rⁱf_{QCoh,*}`, restricted along any functor into `LQCoh^fbc(𝒪_𝒳)`. -/
def singleCompDerivedPushforwardQuasicoherentPlusCompIso (i : ℕ) {C : Type*} [Category* C]
    (Φ : (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
      𝒴).FullSubcategory ⥤ C)
    (H : (DerivedCategoryB.serreQuotientWPlus
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
      (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
        lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
          𝒴)).Localization ⥤ C)
    (α : (DerivedCategoryB.serreQuotientWPlus
        (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴)
        (parasiticModules.{u, w, u + 1} B S hS 𝒴 .fppf ⊓
          lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
            𝒴)).Q ⋙ H ≅ sheafFlatBaseChangeHomologyFunctor B E h S hS 𝒴 i ⋙ Φ) :
    sheafFlatBaseChangeSingleFunctor B E h S hS 𝒳 ⋙
        (DerivedCategoryB.serreQuotientWPlus
          (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳)
          (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓
            lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
              𝒳)).Q ⋙
          derivedPushforwardQuasicoherentPlusSheafFlatBaseChange B E h S hS f h𝒜 ⋙ H ≅
      sheafFlatBaseChangeHigherDirectImage B E h S hS f h𝒜 i ⋙ Φ :=
  Functor.isoWhiskerLeft _
      (derivedPushforwardQuasicoherentPlusCompIso B E h S hS f h𝒜 _ H α) ≪≫
    (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.associator _ _ _) ≪≫ sheafFlatBaseChangeSingleCompHomologyIso B E h S hS f h𝒜 i)
      Φ

end AlgebraicGeometry.Stack
