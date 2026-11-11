module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExactness
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# The direct images `Rjₙ,*` and `Riₙ,*` of Situation 0DIK

In Situation 0DIK (`AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem`) the infinitesimal base
changes `Xₙ` sit in `X` and in `Xₙ₊₁` by closed immersions `jₙ : Xₙ ⟶ X` and `iₙ : Xₙ ⟶ Xₙ₊₁`. The
direct image of modules along a closed immersion of algebraic spaces is exact, so its derived
functor is computed degreewise. This module records, for the tower `Rjₙ,* Kₙ` of the proof of
Stacks 0DIL:

* `SeparatedDerivedExistenceSystem.stagePushforward n : D(𝒪_{Xₙ}) ⥤ D(𝒪_X)` and
  `SeparatedDerivedExistenceSystem.transitionPushforward n : D(𝒪_{Xₙ}) ⥤ D(𝒪_{Xₙ₊₁})`, the exact
  direct
  images on the derived categories `derivedCategoryAt` of Situation 0DIK;
* `SeparatedDerivedExistenceSystem.stagePushforwardCompIso n : Riₙ,* ⋙ Rjₙ₊₁,* ≅ Rjₙ,*`, from the
  composition law of the direct image of modules (Stacks 03LU) and `iₙ ≫ jₙ₊₁ = jₙ`;
* `transitionToposDerivedAdjunction n : Liₙ^* ⊣ Riₙ,*` for the ringed-topos derived direct image
  `transitionToposDerivedPushforward n` (Stacks 07A6), with `Liₙ^*` the derived pullback of
  Situation 0DIK, identified with the exact `Riₙ,*` by
  `SeparatedDerivedExistenceSystem.transitionToposDerivedPushforwardIso` (both are right derived
  functors
  of degreewise direct image), giving `SeparatedDerivedExistenceSystem.transitionAdjunction`;
* `SeparatedDerivedExistenceSystem.pushforwardTower : ℕᵒᵖ ⥤ D(𝒪_X)`, the tower `n ↦ Rjₙ,* Kₙ` with
  transitions `SeparatedDerivedExistenceSystem.towerMap` built from the `φₙ`;
* `SeparatedDerivedExistenceSystem.isQuasicoherentOnSite_homology_towerObj`: its terms lie in
  `D_QCoh(𝒪_X)` (Stacks 08JL), and `SeparatedDerivedExistenceSystem.isZero_homology_towerObj`: they
  inherit upper bounds from the `Kₙ`.

## Implementation notes

The module categories are spelled through the small étale ringed *topos*
(`SeparatedDerivedExistenceSystem.toposModules`), as in `derivedCategoryAt`, and the derived
categories
are at the standard model, which Situation 0DIK fixes; taken by `letI`.

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (B : BigFppfSite.{u})
    (hS : B.Contains (limitBase F)) (hSn : ∀ n : ℕ, B.Contains (baseAt F n))
    (X : Over (schemeSpace (limitBaseObject F B hS)))


/-- The derived pushforward along the transition morphism, as the ringed-topos `Rf_*`. -/
abbrev transitionToposDerivedPushforward (n : ℕ) :
    derivedCategoryAt F B hS hSn X n ⥤ derivedCategoryAt F B hS hSn X (n + 1) :=
  haveI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B (limitBase F) hS (spaceAt F B hS hSn X n)).O)) :=
    isGrothendieckAbelian_modules B (limitBase F) hS _ (spaceAt F B hS hSn X n).2
  Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B (limitBase F) hS (transitionSpace F B hS hSn X n))

/-- `Liₙ^* ⊣ Riₙ,*`. -/
def transitionToposDerivedAdjunction (n : ℕ) :
    transitionDerivedPullback F B hS hSn X n ⊣ transitionToposDerivedPushforward F B hS hSn X n :=
  haveI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B (limitBase F) hS (spaceAt F B hS hSn X n)).O)) :=
    isGrothendieckAbelian_modules B (limitBase F) hS _ (spaceAt F B hS hSn X n).2
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
    (smallEtaleRingedToposHom B (limitBase F) hS (transitionSpace F B hS hSn X n))

/-- A functor `RF'` whose composite with a localization `L` is isomorphic to `F` is a right
derived functor of `F`, hence isomorphic to any right derived functor of `F`. Stated at abstract
binders so that the two functors are compared only through these isomorphisms. -/
def rightDerivedIsoOfFactors {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] {F : C ⥤ H} (RF RF' : D ⥤ H)
    (α : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor α W] (e : L ⋙ RF' ≅ F) : RF ≅ RF' :=
  haveI := Functor.isRightDerivedFunctor_of_inverts W RF' e
  Functor.rightDerivedUnique RF RF' α e.inv W

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- The infinitesimal base change `Xₙ`. -/
abbrev stage (n : ℕ) : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase :=
  spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n

/-- The modules on the small étale ringed topos of an algebraic space. -/
abbrev toposModules (Y : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos D.B (limitBase D.system) D.containsLimitBase Y).O)

/-- `D(𝒪_X)` at the standard model, in the ringed-topos spelling of the modules that the derived
categories `derivedCategoryAt` of Situation 0DIK use. -/
abbrev limitDerivedCategory :=
  @DerivedCategory (D.toposModules D.X.left) _ _ (HasDerivedCategory.standard _)

/-- The direct image of modules along the morphism of ringed topoi of a morphism of spaces. -/
abbrev toposPushforward {Y Z : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase}
    (f : Y ⟶ Z) : D.toposModules Y ⥤ D.toposModules Z :=
  (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase f).pushforwardModules

/-- The direct image of modules along a closed immersion of algebraic spaces preserves finite
colimits. -/
theorem preservesFiniteColimits_toposPushforward
    {Y Z : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase} (f : Y ⟶ Z)
    (hf : IsClosedImmersion D.B (limitBase D.system) D.containsLimitBase f.hom) :
    PreservesFiniteColimits (D.toposPushforward f) := by
  rw [toposPushforward, pushforwardModules_eq_modulePushforward]
  exact preservesFiniteColimits_modulePushforward_of_isClosedImmersion _ _ _ _ hf

/-- The direct image of modules along a morphism of algebraic spaces preserves finite limits. -/
theorem preservesFiniteLimits_toposPushforward
    {Y Z : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase} (f : Y ⟶ Z) :
    PreservesFiniteLimits (D.toposPushforward f) := by
  rw [toposPushforward, pushforwardModules_eq_modulePushforward]
  exact AlgebraicGeometry.Space.preservesFiniteLimits_modulePushforward _ _ _ f

/-- The direct image of modules along a morphism of algebraic spaces is additive. -/
theorem additive_toposPushforward
    {Y Z : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase} (f : Y ⟶ Z) :
    (D.toposPushforward f).Additive := by
  rw [toposPushforward, pushforwardModules_eq_modulePushforward]
  exact modulePushforward_additive _ _ _ f

/-- **`Rjₙ,* : D(𝒪_{Xₙ}) ⥤ D(𝒪_X)`**, the direct image along the closed immersion `jₙ`, which
is exact and so computed degreewise. -/
def stagePushforward (n : ℕ) :
    derivedCategoryAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n ⥤
      D.limitDerivedCategory :=
  letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
  letI := HasDerivedCategory.standard (D.toposModules D.X.left)
  haveI := D.additive_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteLimits_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteColimits_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    ((isClosedImmersion_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective n))
  (D.toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).mapDerivedCategory

/-- **`Riₙ,* : D(𝒪_{Xₙ}) ⥤ D(𝒪_{Xₙ₊₁})`**, the exact direct image along the closed immersion
`iₙ`. -/
def transitionPushforward (n : ℕ) :
    derivedCategoryAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n ⥤
      derivedCategoryAt D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1) :=
  letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
  letI := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
  haveI := D.additive_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteLimits_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteColimits_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    ((isClosedImmersion_transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective n))
  (D.toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).mapDerivedCategory

/-- **`Rjₙ₊₁,* ∘ Riₙ,* ≅ Rjₙ,*`**, from the composition law of the direct image of modules
(Stacks 03LU) and `iₙ ≫ jₙ₊₁ = jₙ`. -/
def stagePushforwardCompIso (n : ℕ) :
    D.transitionPushforward n ⋙ D.stagePushforward (n + 1) ≅ D.stagePushforward n :=
  letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
  letI := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
  letI := HasDerivedCategory.standard (D.toposModules D.X.left)
  haveI := D.additive_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteLimits_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteColimits_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    ((isClosedImmersion_transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective n))
  haveI := D.additive_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
  haveI := D.preservesFiniteLimits_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
  haveI := D.preservesFiniteColimits_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))
    ((isClosedImmersion_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective (n + 1)))
  haveI := D.additive_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteLimits_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteColimits_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    ((isClosedImmersion_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective n))
  RingTheory.TorIndependence.mapDerivedCategoryCompNatIso _ _ _
    (modulePushforwardCompIso' D.B (limitBase D.system) D.containsLimitBase
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)) ≪≫
      eqToIso (by rw [transitionSpace_spaceProjection]))

/-- Degreewise direct image along `iₙ` followed by localization, read into `derivedCategoryAt`. -/
abbrev transitionHomotopyPushforward (n : ℕ) :
    HomotopyCategory (D.toposModules (D.stage n)) (ComplexShape.up ℤ) ⥤
      derivedCategoryAt D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1) :=
  Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n))

/-- The localization functor on the homotopy category of `𝒪_{Xₙ}`-modules, into
`derivedCategoryAt`. -/
abbrev stageQh (n : ℕ) :
    HomotopyCategory (D.toposModules (D.stage n)) (ComplexShape.up ℤ) ⥤
      derivedCategoryAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n :=
  letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
  DerivedCategory.Qh

/-- The derivation unit of the ringed-topos `Riₙ,*`. -/
def transitionToposUnit (n : ℕ) :
    D.transitionHomotopyPushforward n ⟶ D.stageQh n ⋙
      transitionToposDerivedPushforward D.system D.B D.containsLimitBase D.containsBaseAt D.X n :=
  letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
  letI := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
  haveI : IsGrothendieckAbelian.{u} (D.toposModules (D.stage n)) :=
    isGrothendieckAbelian_modules D.B (limitBase D.system) D.containsLimitBase _ (D.stage n).2
  (Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy
    (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt
        D.X n))).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ))

/-- `stageQh n` is a localization functor with respect to the quasi-isomorphisms. -/
instance isLocalization_stageQh (n : ℕ) : (D.stageQh n).IsLocalization
    (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) := by
  let := HasDerivedCategory.standard (D.toposModules (D.stage n))
  exact (inferInstance : (DerivedCategory.Qh : HomotopyCategory (D.toposModules (D.stage n))
    (ComplexShape.up ℤ) ⥤ _).IsLocalization
      (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)))

/-- The derived direct image `Riₙ,*` of ringed topoi is a right derived functor of the degreewise
direct image along `iₙ`, with unit `transitionToposUnit n`. -/
instance isRightDerivedFunctor_transitionToposUnit (n : ℕ) :
    (transitionToposDerivedPushforward D.system D.B D.containsLimitBase D.containsBaseAt
      D.X n).IsRightDerivedFunctor (D.transitionToposUnit n)
      (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) := by
  let := HasDerivedCategory.standard (D.toposModules (D.stage n))
  let := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
  have : IsGrothendieckAbelian.{u} (D.toposModules (D.stage n)) :=
    isGrothendieckAbelian_modules D.B (limitBase D.system) D.containsLimitBase _ (D.stage n).2
  have := Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy_hasRightDerivedFunctor
    (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
  have : (Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy
      (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
        (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt
          D.X n))).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  unfold transitionToposUnit
  infer_instance

/-- The defining isomorphism of the exact direct image `Riₙ,*` on the homotopy category. -/
def transitionPushforwardFactorsh (n : ℕ) :
    D.stageQh n ⋙ D.transitionPushforward n ≅ D.transitionHomotopyPushforward n :=
  letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
  letI := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
  haveI := D.additive_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteLimits_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteColimits_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    ((isClosedImmersion_transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective n))
  Functor.mapDerivedCategoryFactorsh (D.toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n))

/-- **The ringed-topos `Riₙ,*` of Stacks 07A5 is the exact direct image along `iₙ`**: both are
right derived functors of degreewise direct image, the latter because `iₙ,*` is exact. -/
def transitionToposDerivedPushforwardIso (n : ℕ) :
    transitionToposDerivedPushforward D.system D.B D.containsLimitBase D.containsBaseAt D.X n ≅
      D.transitionPushforward n :=
  rightDerivedIsoOfFactors (D.stageQh n)
    (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) _ _
    (D.transitionToposUnit n) (D.transitionPushforwardFactorsh n)

/-- **`Liₙ^* ⊣ Riₙ,*`** with `Riₙ,*` the exact direct image (Stacks 07A6). -/
def transitionAdjunction (n : ℕ) :
    transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n ⊣
      D.transitionPushforward n :=
  (transitionToposDerivedAdjunction D.system D.B D.containsLimitBase D.containsBaseAt
    D.X n).ofNatIsoRight
    (D.transitionToposDerivedPushforwardIso n)

/-- The object `Eₙ = Rjₙ,* Kₙ` of `D(𝒪_X)`. -/
abbrev towerObj (n : ℕ) : D.limitDerivedCategory := (D.stagePushforward n).obj (D.K n)

/-- The transition `Eₙ₊₁ ⟶ Eₙ`: `Rjₙ₊₁,*` of the adjoint `Kₙ₊₁ ⟶ Riₙ,* Kₙ` of `φₙ`, followed by
`Rjₙ₊₁,* Riₙ,* ≅ Rjₙ,*`. -/
def towerMap (n : ℕ) : D.towerObj (n + 1) ⟶ D.towerObj n :=
  (D.stagePushforward (n + 1)).map ((D.transitionAdjunction n).homEquiv _ _ (D.φ n)) ≫
    (D.stagePushforwardCompIso n).hom.app (D.K n)

/-- **The tower `n ↦ Rjₙ,* Kₙ` of Stacks 0DIL**, an inverse system in `D(𝒪_X)`. -/
def pushforwardTower : ℕᵒᵖ ⥤ D.limitDerivedCategory :=
  Functor.ofOpSequence D.towerMap

/-- The `n`-th term of `pushforwardTower` is `Eₙ = Rjₙ,* Kₙ`. -/
lemma pushforwardTower_obj (n : ℕ) : D.pushforwardTower.obj ⟨n⟩ = D.towerObj n := rfl

/-- The map of `pushforwardTower` from `n + 1` to `n` is `towerMap n`. -/
lemma pushforwardTower_map_succ (n : ℕ) :
    D.pushforwardTower.map (homOfLE (Nat.le_succ n)).op = D.towerMap n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- Each `Kₙ` has quasi-coherent cohomology sheaves (Stacks 08JL). -/
theorem isQuasicoherentOnSite_homology_K (n : ℕ) (q : ℤ) :
    letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
    ((DerivedCategory.homologyFunctor (D.toposModules (D.stage n)) q).obj
      (D.K n)).IsQuasicoherentOnSite :=
  derivedCategoryB_of_isPseudoCoherent_unconditional D.B (limitBase D.system) D.containsLimitBase
    _ (D.stage n).2 (D.K n) (D.pseudoCoherent n) q

private instance (n : ℕ) : (D.toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).Additive :=
  D.additive_toposPushforward _

private instance (n : ℕ) : PreservesFiniteLimits (D.toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)) :=
  D.preservesFiniteLimits_toposPushforward _

private instance (n : ℕ) : PreservesFiniteColimits (D.toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)) :=
  D.preservesFiniteColimits_toposPushforward _
    ((isClosedImmersion_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective n))

/-- **The terms `Rjₙ,* Kₙ` of the tower lie in `D_QCoh(𝒪_X)`**: `jₙ,*` is exact, so
`Hᵠ(Rjₙ,* Kₙ) = jₙ,* Hᵠ(Kₙ)`, which is quasi-coherent, `jₙ` being affine (Stacks 08JL and the
quasi-coherence of the direct image along an affine morphism). -/
theorem isQuasicoherentOnSite_homology_towerObj (n : ℕ) (q : ℤ) :
    letI := HasDerivedCategory.standard (D.toposModules D.X.left)
    ((DerivedCategory.homologyFunctor (D.toposModules D.X.left) q).obj
      (D.towerObj n)).IsQuasicoherentOnSite := by
  let := HasDerivedCategory.standard (D.toposModules (D.stage n))
  let := HasDerivedCategory.standard (D.toposModules D.X.left)
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Functor.mapDerivedCategoryHomologyIso (D.toposPushforward
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)) q).app
      (D.K n)).symm ?_
  have h := isQuasicoherentOnSite_modulePushforward_isAffineHom D.B (limitBase D.system)
    D.containsLimitBase (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (isAffineHom_of_isClosedImmersion _ _ _ _
      ((isClosedImmersion_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective n)))
    _ (D.isQuasicoherentOnSite_homology_K n q)
  rw [← pushforwardModules_eq_modulePushforward] at h
  exact h

/-- **The bound passes to the tower**: `Hᵠ(Rjₙ,* Kₙ) = jₙ,* Hᵠ(Kₙ)` vanishes with `Hᵠ(Kₙ)`. -/
theorem isZero_homology_towerObj (n : ℕ) (q : ℤ)
    (h : letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
      IsZero ((DerivedCategory.homologyFunctor (D.toposModules (D.stage n)) q).obj (D.K n))) :
    letI := HasDerivedCategory.standard (D.toposModules D.X.left)
    IsZero ((DerivedCategory.homologyFunctor (D.toposModules D.X.left) q).obj (D.towerObj n)) := by
  let := HasDerivedCategory.standard (D.toposModules (D.stage n))
  let := HasDerivedCategory.standard (D.toposModules D.X.left)
  exact ((D.toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).map_isZero h).of_iso
    ((Functor.mapDerivedCategoryHomologyIso (D.toposPushforward
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)) q).app (D.K n))

end SeparatedDerivedExistenceSystem

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

/-- The modules on the small étale ringed topos of an algebraic space, in Situation 0DIK. -/
abbrev toposModules (Y : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos D.B (limitBase D.system) D.containsLimitBase Y).O)

/-- `D(𝒪_X)` at the standard model, in Situation 0DIK. -/
abbrev limitDerivedCategory :=
  @DerivedCategory (D.toposModules D.X.left) _ _ (HasDerivedCategory.standard _)

end DerivedExistenceSystem

end AlgebraicGeometry.Space

end
