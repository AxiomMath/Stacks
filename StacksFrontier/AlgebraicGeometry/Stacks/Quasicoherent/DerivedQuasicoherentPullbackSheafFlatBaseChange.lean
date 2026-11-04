module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreQuotientColocalizationOfAdjunction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedModuleLowerShriekSuccSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedQuasicoherentRestrictionLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfRestrictionQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfColimitsLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeHigherDirectImageQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerreLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeInverseImage
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakSerreClassOfAbelian

/-!
# Derived pullback on `D_QCoh` of algebraic stacks (Stacks 07BE), faithful class

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks. **Stacks 07BE** says:

1. the exact functor `f^*` induces a functor `D_{LQCoh^fbc}(𝒪_𝒴) ⥤ D_{LQCoh^fbc}(𝒪_𝒳)` making the
   square with the inclusions into `D(𝒪_𝒴)`, `D(𝒪_𝒳)` commute;
2. the composite `D_{LQCoh^fbc}(𝒪_𝒴) ⥤ D_{LQCoh^fbc}(𝒪_𝒳) ⥤ D_QCoh(𝒪_𝒳)` is left derivable with
   respect to `D_{LQCoh^fbc}(𝒪_𝒴) ⥤ D_QCoh(𝒪_𝒴)`, and `Lf^*_QCoh` is its left derived functor;
3. for `f` quasi-compact and quasi-separated,
   `Hom_{D_QCoh(𝒪_𝒳)}(Lf^*_QCoh A, B) = Hom_{D_QCoh(𝒪_𝒴)}(A, Rf_{QCoh,*} B)` for
   `B ∈ D⁺_QCoh(𝒪_𝒳)`.

Everything is stated at module universe `u + 1`, with `LQCoh^fbc` the faithful class of
**Stacks 0762** (flat base change for the pullback of sheaves), on the ambient spelling
`SheafOfModules.{u + 1} (FlatFppf.ambientRingStructureSheaf B S hS 𝒳)` of `Mod(𝒪_𝒳)`
(`AlgebraicGeometry.Stack.FlatFppf.sheafFlatBaseChangeModulesSucc`).

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.derivedSheafFlatBaseChangePullbackSucc`: assertion 1, the
  induced functor `D_{LQCoh^fbc}(𝒪_𝒴) ⥤ D_{LQCoh^fbc}(𝒪_𝒳)`, for any models of the derived
  categories.
* `AlgebraicGeometry.Stack.FlatFppf.derivedQuasicoherentPullbackSucc`: `Lf^*_QCoh`, with its
  counit `AlgebraicGeometry.Stack.FlatFppf.derivedQuasicoherentPullbackSuccCounit`.
* `AlgebraicGeometry.Stack.FlatFppf.derivedQuasicoherentPullbackSuccHomEquiv`: assertion 3.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.derivedSheafFlatBaseChangePullbackSucc_comp_ι`: the square of
  assertion 1.
* `AlgebraicGeometry.Stack.FlatFppf.isLeftDerivable_derivedSheafFlatBaseChangePullbackSucc`:
  assertion 2, and `isLeftDerivedFunctor_derivedQuasicoherentPullbackSucc`.
* `AlgebraicGeometry.Stack.FlatFppf.hasColocalizations_sheafFlatBaseChangeModulesSucc`: the
  colocalization of **Stacks 07BA** at module universe `u + 1`, the input of assertions 2 and 3.
* `AlgebraicGeometry.Stack.FlatFppf.derivedQuasicoherentPullbackSuccHomEquiv_naturality_left`,
  `..._right`: naturality of the adjointness.

## Implementation notes

Assertion 1 is stated for arbitrary models of the derived categories, assertions 2 and 3 at the
standard models (`AlgebraicGeometry.Stack.FlatFppf.standardDerivedCategoryAmbientSucc`).
`D⁺_QCoh(𝒪_𝒳)` is the bounded below Verdier quotient of **Stacks 07BC**, read in `D_QCoh(𝒪_𝒳)`
through `DerivedCategoryB.serreQuotientPlusToSerreQuotient`, and `Rf_{QCoh,*}` is
`AlgebraicGeometry.Stack.derivedPushforwardQuasicoherentPlusSheafFlatBaseChange`.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 07BC](https://stacks.math.columbia.edu/tag/07BC)
* [Stacks Project, Tag 07BE](https://stacks.math.columbia.edu/tag/07BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w t₁ t₂

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- The inverse image `f^* : Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)` of **Stacks 06WE** at module universe `u + 1`,
on the ambient spelling of the module categories. -/
def modulePullbackSucc :
    SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴) ⥤
      SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳) :=
  fppfModulePullbackOfStacks B S hS f

/-- The direct image `f_* : Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒴)` of **Stacks 06WE** at module universe `u + 1`,
on the ambient spelling of the module categories. -/
def modulePushforwardSucc :
    SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳) ⥤
      SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴) :=
  fppfModuleSheafPushforwardOfStacks B S hS f

/-- The inverse image `modulePullbackSucc` is an additive functor. -/
instance additive_modulePullbackSucc : (modulePullbackSucc B S hS f).Additive :=
  additive_fppfModulePullbackOfStacks B S hS f

/-- The inverse image `modulePullbackSucc` preserves finite limits. -/
instance preservesFiniteLimits_modulePullbackSucc :
    PreservesFiniteLimits (modulePullbackSucc B S hS f) :=
  preservesFiniteLimits_fppfModulePullbackOfStacks B S hS f

/-- The inverse image `modulePullbackSucc` preserves finite colimits. -/
instance preservesFiniteColimits_modulePullbackSucc :
    PreservesFiniteColimits (modulePullbackSucc B S hS f) :=
  preservesFiniteColimits_fppfModulePullbackOfStacks B S hS f

/-- The direct image `modulePushforwardSucc` is an additive functor. -/
instance additive_modulePushforwardSucc : (modulePushforwardSucc B S hS f).Additive :=
  additive_fppfModuleSheafPushforwardOfStacks B S hS f

/-- **Stacks 06WE**, `f^* ⊣ f_*`, at module universe `u + 1` on the ambient spelling. -/
def moduleAdjunctionSucc : modulePullbackSucc B S hS f ⊣ modulePushforwardSucc B S hS f :=
  fppfModuleAdjunctionOfStacks B S hS f

section Models

variable [HasDerivedCategory.{t₁} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{t₂} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴))]

/-- The functor `D_{LQCoh^fbc}(𝒪_𝒴) ⥤ D_{LQCoh^fbc}(𝒪_𝒳)` induced by the exact functor
`f^* : D(𝒪_𝒴) ⥤ D(𝒪_𝒳)`. -/
@[stacks 07BE "the first assertion: the exact functor f^* induces D_LQCoh^fbc(𝒪_𝒴) ⥤ \
D_LQCoh^fbc(𝒪_𝒳), with LQCoh^fbc the class of Stacks 0762 (flat base change for the pullback of \
sheaves), at module universe u + 1, for any models of the derived categories"]
def derivedSheafFlatBaseChangePullbackSucc :
    (DerivedCategoryB.derivedCategoryB
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).FullSubcategory :=
  DerivedCategoryB.derivedCategoryBMap (modulePullbackSucc B S hS f)
    (fun M hM => locallyQuasicoherentSheafFlatBaseChange_fppfModulePullbackOfStacks B E h S hS f
      M hM)

/-- The induced functor followed by the inclusion `D_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)` is the inclusion
`D_{LQCoh^fbc}(𝒪_𝒴) ⊆ D(𝒪_𝒴)` followed by `f^* : D(𝒪_𝒴) ⥤ D(𝒪_𝒳)`. -/
@[stacks 07BE "the commutative square of the first assertion, at module universe u + 1, for the \
class of Stacks 0762 read with the pullback of sheaves, for any models of the derived categories"]
theorem derivedSheafFlatBaseChangePullbackSucc_comp_ι :
    derivedSheafFlatBaseChangePullbackSucc B E h S hS f ⋙
        (DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).ι =
      (DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)).ι ⋙
        (modulePullbackSucc B S hS f).mapDerivedCategory :=
  rfl

end Models

/-! ### The second and third assertions, at the standard models -/

section Standard

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  Stacks.hasSheafCompose_forget₂_commRingCat preservesCoveringPullbacks_inclusion_topology
  essentiallySmall_obj_largeSections essentiallySmall_flatFppf_largeSections
  hasSheafify_topology_largeSections wEqualsLocallyBijective_topology_largeSections
  hasSheafify_fppfTopology_largeSections wEqualsLocallyBijective_fppfTopology_largeSections
  hasPointwiseRightKanExtension_inclusion_ringCat_largeSections
  hasPointwiseRightKanExtension_inclusion_addCommGrpCat_largeSections

/-- The standard model of `D(𝒪_𝒵)` at module universe `u + 1`. -/
abbrev standardDerivedCategoryAmbientSucc (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒵)) :=
  HasDerivedCategory.standard _

/-- The standard model of `D(𝒪_{𝒵_{flat,fppf}})` at module universe `u + 1`. -/
abbrev standardDerivedCategorySubsiteSucc (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒵)) :=
  HasDerivedCategory.standard _

attribute [local instance] standardDerivedCategoryAmbientSucc standardDerivedCategorySubsiteSucc

/-- **The colocalization of Stacks 07BA at module universe `u + 1`**: every object `E` of
`D_{LQCoh^fbc}(𝒪_𝒵)` receives the counit `Lg_! g^* E ⟶ E`, whose cone lies in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒵)` and whose source is left orthogonal to it. -/
theorem hasColocalizations_sheafFlatBaseChangeModulesSucc
    (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    DerivedCategoryB.HasColocalizations (sheafFlatBaseChangeModulesSucc B E h S hS 𝒵)
      (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒵) :=
  DerivedCategoryB.hasColocalizations_of_adjunction (parasiticModulesSucc B S hS 𝒵)
    (sheafFlatBaseChangeModulesSucc B E h S hS 𝒵)
    (derivedModuleLowerShriekSuccAdjunction B S hS 𝒵)
    (isZero_moduleInverseImage_mapDerivedCategory_iff_forall_isParasitic B S hS 𝒵)
    (isIso_derivedModuleLowerShriekSuccAdjunction_unit B S hS 𝒵)
    (derivedCategoryB_derivedModuleLowerShriekSucc_moduleInverseImage B S hS 𝒵
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒵)
      (fun F hF => isQuasicoherentOnSite_moduleInverseImage_of_sheafFlatBaseChangeModulesSucc
        B E h S hS 𝒵 F hF)
      (fun F hF => ObjectProperty.prop_colimit _ F hF)
      (derivedCategoryB_derivedModuleLowerShriekSucc_singleFunctor B E h S hS 𝒵))

/-- The composite
`D_{LQCoh^fbc}(𝒪_𝒴) --f^*--> D_{LQCoh^fbc}(𝒪_𝒳) --q_𝒳--> D_QCoh(𝒪_𝒳)` is left derivable with
respect to the localization `D_{LQCoh^fbc}(𝒪_𝒴) ⥤ D_QCoh(𝒪_𝒴)` of **Stacks 07B6**, in the sense
of **Stacks 05SV**. -/
@[stacks 07BE "the second assertion: q_𝒳 ∘ f^* : D_LQCoh^fbc(𝒪_𝒴) ⥤ D_QCoh(𝒪_𝒳) is left \
derivable with respect to D_LQCoh^fbc(𝒪_𝒴) ⥤ D_QCoh(𝒪_𝒴) (Stacks 05SV), at module universe \
u + 1, for the class of Stacks 0762 read with the pullback of sheaves, at the standard models of \
the derived categories"]
theorem isLeftDerivable_derivedSheafFlatBaseChangePullbackSucc :
    (derivedSheafFlatBaseChangePullbackSucc B E h S hS f ⋙
        (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
          (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).Q).IsLeftDerivable
      (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
        (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)) :=
  DerivedCategoryB.isLeftDerivable_of_hasColocalizations _
    (hasColocalizations_sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)

/-- `Lf^*_QCoh : D_QCoh(𝒪_𝒴) ⥤ D_QCoh(𝒪_𝒳)`, the left derived functor of
`q_𝒳 ∘ f^*` with respect to the quotient functor of `𝒴` (Stacks 05S9, 05SV). -/
@[stacks 07BE "Lf^*_QCoh : D_QCoh(𝒪_𝒴) ⥤ D_QCoh(𝒪_𝒳), the left derived functor of q_𝒳 ∘ f^*, at \
module universe u + 1, at the standard models of the derived categories"]
def derivedQuasicoherentPullbackSucc :
    (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
        (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)).Localization ⥤
      (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
        (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).Localization :=
  DerivedCategoryB.serreQuotientDerivedPullback (modulePullbackSucc B S hS f)
    (fun M hM => locallyQuasicoherentSheafFlatBaseChange_fppfModulePullbackOfStacks B E h S hS f
      M hM)
    (hasColocalizations_sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)

/-- The counit `Lf^*_QCoh ∘ q_𝒴 ⟶ q_𝒳 ∘ f^*` exhibiting `Lf^*_QCoh` as the left derived functor. -/
def derivedQuasicoherentPullbackSuccCounit :
    (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
        (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)).Q ⋙
        derivedQuasicoherentPullbackSucc B E h S hS f ⟶
      derivedSheafFlatBaseChangePullbackSucc B E h S hS f ⋙
        (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
          (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).Q :=
  DerivedCategoryB.serreQuotientDerivedPullbackCounit (modulePullbackSucc B S hS f) _ _

/-- `Lf^*_QCoh` is the left derived functor of `q_𝒳 ∘ f^*`. -/
@[stacks 07BE "Lf^*_QCoh is the (total) left derived functor of q_𝒳 ∘ f^*, with counit \
derivedQuasicoherentPullbackSuccCounit, at module universe u + 1"]
instance isLeftDerivedFunctor_derivedQuasicoherentPullbackSucc :
    (derivedQuasicoherentPullbackSucc B E h S hS f).IsLeftDerivedFunctor
      (derivedQuasicoherentPullbackSuccCounit B E h S hS f)
      (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
        (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)) :=
  DerivedCategoryB.isLeftDerivedFunctor_serreQuotientDerivedPullback
    (A₁ := SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴))
    (A₂ := SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (𝒜₁ := sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
    (𝒮₁ := parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
    (𝒜₂ := sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
    (𝒮₂ := parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
    (modulePullbackSucc B S hS f) _ _


section Adjunction

/-- The standard model of `D(𝒪_𝒵)` at module universe `u + 1`, on the spelling
`fppfModulesUnivLE` of `Mod(𝒪_𝒵)`. -/
abbrev standardDerivedCategoryFppfModulesSucc (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵) :=
  standardDerivedCategoryAmbientSucc B S hS 𝒵

attribute [local instance] standardDerivedCategoryFppfModulesSucc

/-- The category of sheaves of `𝒪_𝒵`-modules at module universe `u + 1` has enough injectives. -/
theorem enoughInjectives_ambientModulesSucc (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    EnoughInjectives (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒵)) :=
  enoughInjectives_fppfModulesUnivLESucc.{u, w} B S hS 𝒵

/-- **Stacks 0771 (2)** at module universe `u + 1`, read on the spelling `fppfModulesUnivLE` of
`Mod(𝒪_𝒵)`, for the abelian structure found there. -/
theorem isWeakSerreClass_sheafFlatBaseChangeFppfModulesUnivLE
    (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS
      𝒵).IsWeakSerreClass :=
  ObjectProperty.isWeakSerreClass_of_abelian _ _ _
    (isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModulesSucc B E h S hS 𝒵)

variable (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)

include hqc hqs in
/-- **Stacks 0771 (4)(b)** for the higher direct images of **Stacks 06WE**: for a quasi-compact
quasi-separated `f`, every `Rᵖf_*` carries `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`. -/
theorem sheafFlatBaseChange_moduleSheafHigherDirectImage
    (M : fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)
    (hM : lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳 M)
    (p : ℕ) :
    lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒴
      ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf) p).obj M) :=
  AlgebraicStacks.sheafFlatBaseChange_higherDirectImage B E h S hS f hqc hqs p M hM

attribute [local instance] enoughInjectives_ambientModulesSucc

include hqc hqs in
/-- **Stacks 07BC, the preservation clauses, on the ambient spelling**: for a quasi-compact
quasi-separated `f`, `Rf_*` carries `D⁺_{LQCoh^fbc}(𝒪_𝒳)` into `D⁺_{LQCoh^fbc}(𝒪_𝒴)`. -/
theorem derivedCategoryB_modulePushforwardSucc_rightDerivedFunctorPlus_obj
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K.obj) :
    DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
      ((modulePushforwardSucc B S hS f).rightDerivedFunctorPlus.obj K).obj := by
  have := isWeakSerreClass_sheafFlatBaseChangeFppfModulesUnivLE B E h S hS 𝒳
  have := isWeakSerreClass_sheafFlatBaseChangeFppfModulesUnivLE B E h S hS 𝒴
  exact derivedCategoryB_sheafFlatBaseChange_fppfDerivedPushforwardPlus_obj B E h S hS f
    (sheafFlatBaseChange_moduleSheafHigherDirectImage B E h S hS f hqc hqs) K hK

include hqc hqs in
/-- **Stacks 07BC, the preservation clauses, on the ambient spelling**: for a quasi-compact
quasi-separated `f`, `Rf_*` carries `D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` into
`D⁺_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒴)`. -/
theorem derivedCategoryB_parasitic_modulePushforwardSucc_rightDerivedFunctorPlus_obj
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : DerivedCategoryB.derivedCategoryB
      (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K.obj) :
    DerivedCategoryB.derivedCategoryB (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
      ((modulePushforwardSucc B S hS f).rightDerivedFunctorPlus.obj K).obj := by
  have := isWeakSerreClass_sheafFlatBaseChangeFppfModulesUnivLE B E h S hS 𝒳
  have := isWeakSerreClass_sheafFlatBaseChangeFppfModulesUnivLE B E h S hS 𝒴
  exact derivedCategoryB_parasiticSheafFlatBaseChange_fppfDerivedPushforwardPlus_obj B E h S hS f
    (sheafFlatBaseChange_moduleSheafHigherDirectImage B E h S hS f hqc hqs) K hK

/-- `Rf_{QCoh,*} : D⁺_QCoh(𝒪_𝒳) ⥤ D⁺_QCoh(𝒪_𝒴)` of **Stacks 07BC** for a quasi-compact
quasi-separated `f`, at the standard models. -/
abbrev derivedPushforwardQuasicoherentPlusSucc
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) :
    (DerivedCategoryB.serreQuotientWPlus (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
        (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).Localization ⥤
      (DerivedCategoryB.serreQuotientWPlus (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
        (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)).Localization :=
  haveI := isWeakSerreClass_sheafFlatBaseChangeFppfModulesUnivLE B E h S hS 𝒳
  haveI := isWeakSerreClass_sheafFlatBaseChangeFppfModulesUnivLE B E h S hS 𝒴
  derivedPushforwardQuasicoherentPlusSheafFlatBaseChange B E h S hS f
    (sheafFlatBaseChange_moduleSheafHigherDirectImage B E h S hS f hqc hqs)

/-- For a quasi-compact quasi-separated
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, `A ∈ D_QCoh(𝒪_𝒴)` and `B ∈ D⁺_QCoh(𝒪_𝒳)`,

`Hom_{D_QCoh(𝒪_𝒳)}(Lf^*_QCoh A, B) ≃ Hom_{D_QCoh(𝒪_𝒴)}(A, Rf_{QCoh,*} B)`,

`D⁺_QCoh` being read inside `D_QCoh` through the functor induced by the inclusion. -/
@[stacks 07BE "the third assertion: for f quasi-compact and quasi-separated, \
Hom_D_QCoh(𝒪_𝒳)(Lf^*_QCoh A, B) = Hom_D_QCoh(𝒪_𝒴)(A, Rf_QCoh,* B) for A in D_QCoh(𝒪_𝒴) and B in \
D⁺_QCoh(𝒪_𝒳), at module universe u + 1, for the class of Stacks 0762 read with the pullback of \
sheaves, at the standard models of the derived categories"]
def derivedQuasicoherentPullbackSuccHomEquiv
    (A : (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
      (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)).Localization)
    (Bq : (DerivedCategoryB.serreQuotientWPlus (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
      (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).Localization) :
    ((derivedQuasicoherentPullbackSucc B E h S hS f).obj A ⟶
        (DerivedCategoryB.serreQuotientPlusToSerreQuotient
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
          (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).obj Bq) ≃
      (A ⟶ (DerivedCategoryB.serreQuotientPlusToSerreQuotient
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
          (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)).obj
        ((derivedPushforwardQuasicoherentPlusSucc B E h S hS f hqc hqs).obj Bq)) :=
  DerivedCategoryB.serreQuotientHomEquiv
    (A₁ := SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴))
    (A₂ := SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (𝒜₁ := sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
    (𝒮₁ := parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
    (𝒜₂ := sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
    (𝒮₂ := parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
    (moduleAdjunctionSucc B S hS f)
    (fun M hM => locallyQuasicoherentSheafFlatBaseChange_fppfModulePullbackOfStacks B E h S hS f
      M hM)
    (hasColocalizations_sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
    (derivedCategoryB_modulePushforwardSucc_rightDerivedFunctorPlus_obj B E h S hS f hqc hqs)
    (derivedCategoryB_parasitic_modulePushforwardSucc_rightDerivedFunctorPlus_obj B E h S hS f
      hqc hqs) A Bq

/-- Naturality of the adjointness of Stacks 07BE in `A`. -/
@[stacks 07BE "the third assertion: naturality of the adjointness in A"]
theorem derivedQuasicoherentPullbackSuccHomEquiv_naturality_left
    {A A' : (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
      (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)).Localization} (e : A' ⟶ A)
    (Bq : (DerivedCategoryB.serreQuotientWPlus (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
      (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).Localization)
    (g : (derivedQuasicoherentPullbackSucc B E h S hS f).obj A ⟶
      (DerivedCategoryB.serreQuotientPlusToSerreQuotient
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
        (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).obj Bq) :
    derivedQuasicoherentPullbackSuccHomEquiv B E h S hS f hqc hqs A' Bq
        ((derivedQuasicoherentPullbackSucc B E h S hS f).map e ≫ g) =
      e ≫ derivedQuasicoherentPullbackSuccHomEquiv B E h S hS f hqc hqs A Bq g :=
  DerivedCategoryB.serreQuotientHomEquiv_naturality_left _ _ _ _ _ e Bq g

/-- Naturality of the adjointness of Stacks 07BE in `B`. -/
@[stacks 07BE "the third assertion: naturality of the adjointness in B"]
theorem derivedQuasicoherentPullbackSuccHomEquiv_naturality_right
    (A : (DerivedCategoryB.serreQuotientW (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
      (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)).Localization)
    {Bq Bq' : (DerivedCategoryB.serreQuotientWPlus (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
      (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).Localization} (k : Bq ⟶ Bq')
    (g : (derivedQuasicoherentPullbackSucc B E h S hS f).obj A ⟶
      (DerivedCategoryB.serreQuotientPlusToSerreQuotient
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
        (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).obj Bq) :
    derivedQuasicoherentPullbackSuccHomEquiv B E h S hS f hqc hqs A Bq'
        (g ≫ (DerivedCategoryB.serreQuotientPlusToSerreQuotient
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
          (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).map k) =
      derivedQuasicoherentPullbackSuccHomEquiv B E h S hS f hqc hqs A Bq g ≫
        (DerivedCategoryB.serreQuotientPlusToSerreQuotient
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒴)
          (parasiticSheafFlatBaseChangeModulesSucc B E h S hS 𝒴)).map
          ((derivedPushforwardQuasicoherentPlusSucc B E h S hS f hqc hqs).map k) :=
  DerivedCategoryB.serreQuotientHomEquiv_naturality_right _ _ _ _ _ A k g

end Adjunction

end Standard

end AlgebraicGeometry.Stack.FlatFppf
