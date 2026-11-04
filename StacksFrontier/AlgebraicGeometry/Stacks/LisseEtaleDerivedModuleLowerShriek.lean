module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleRingedModules
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.SmallModelModuleAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.FullyFaithfulModuleLowerShriekUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects

/-!
# The derived lower shriek of modules for the lisse-étale site (Stacks 07AS, part (2))

Let `𝒳` be an algebraic stack and let `g : Sh(𝒳_{lisse,étale}) ⟶ Sh(𝒳_{étale})` be the morphism
of ringed topoi of **Stacks 0788** (1), whose inverse image on sheaves of modules is restriction to
the smooth objects, `AlgebraicGeometry.Stack.subsiteRingedToposModuleRestriction` at the étale
topology and `AlgebraicGeometry.Stack.smoothObject` (identified with the pullback of modules by
**Stacks 0788** (1)(f), `AlgebraicGeometry.Stack.LisseEtale.modulePullbackIso`). **Stacks 07AS**
part (2) asserts that the lower shriek `g_! : Mod(𝒪_{𝒳_{lisse,étale}}) ⥤ Mod(𝒳_{étale}, 𝒪_𝒳)`
has a left derived functor

`Lg_! : D(𝒪_{𝒳_{lisse,étale}}) ⟶ D(𝒳_{étale}, 𝒪_𝒳)`,

left adjoint to `g^*` and with `g^* Lg_! = id`. All three are proved here, with no hypothesis, by
the argument of `StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedModuleLowerShriek.lean`
(part (4)): Stacks 07AC for the inclusion of the smooth objects, its acyclicity input being
Stacks 0D6X by transport to small models, and `g^* Lg_! = id` read off from the underived
`g^* g_! = id` for the fully faithful inclusion.

## Main definitions

* `AlgebraicGeometry.Stack.LisseEtale.derivedModuleRestriction`: `g^*` on the unbounded derived
  categories, restriction to the smooth objects applied degreewise.
* `AlgebraicGeometry.Stack.LisseEtale.derivedModuleLowerShriek`: `Lg_!`.
* `AlgebraicGeometry.Stack.LisseEtale.derivedModuleLowerShriekAdjunction`: `Lg_! ⊣ g^*`.
* `AlgebraicGeometry.Stack.LisseEtale.derivedModuleLowerShriekRestrictionIso`: `g^* Lg_! ≅ id`.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.hasPointwiseLeftDerivedFunctor_moduleLowerShriek`:
  **Stacks 07AS (2)**, existence of `Lg_!`.
* `AlgebraicGeometry.Stack.LisseEtale.isIso_derivedModuleLowerShriekAdjunction_unit`:
  **Stacks 07AS (2)**, `g^* Lg_! = id`.

Everything is stated for arbitrary models `[HasDerivedCategory]` of the two derived categories.

## References

* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w t t'

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  Stacks.hasSheafCompose_forget₂_commRingCat Stacks.essentiallySmall_over

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

attribute [local instance] preservesCoveringPullbacks_inclusion

/-- Right Kan extensions of presheaves of rings along the inclusion of the smooth objects exist,
the comma categories indexing them being essentially small. -/
theorem hasPointwiseRightKanExtension_inclusion_ringCat :
    ∀ F : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ RingCat.{u},
      (smoothObject.{u, w} B S hS 𝒳).ι.op.HasPointwiseRightKanExtension F := fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u}
    (StructuredArrow Y (smoothObject.{u, w} B S hS 𝒳).ι.op) RingCat.{u}
  infer_instance

/-- Right Kan extensions of presheaves of abelian groups along the inclusion of the smooth objects
exist, the comma categories indexing them being essentially small. -/
theorem hasPointwiseRightKanExtension_inclusion_addCommGrpCat :
    ∀ F : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smoothObject.{u, w} B S hS 𝒳).ι.op.HasPointwiseRightKanExtension F := fun _ Y => by
  have := hasLimitsOfShape_of_essentiallySmall.{u}
    (StructuredArrow Y (smoothObject.{u, w} B S hS 𝒳).ι.op) AddCommGrpCat.{u}
  infer_instance

attribute [local instance] hasPointwiseRightKanExtension_inclusion_ringCat
  hasPointwiseRightKanExtension_inclusion_addCommGrpCat

/-- **Stacks 0789 (1), `g^* g_! = id`, at restriction of modules**: the unit of the adjunction
between lower shriek and restriction of sheaves of modules along the inclusion of the flat
objects is invertible, the inclusion being fully faithful. -/
theorem isIso_adjunctionModules_unit_inclusion :
    IsIso (adjunctionModules (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)).unit :=
  isIso_adjunctionModules_unit _ _ _ _

/-- The lower shriek of sheaves of modules along the inclusion of the smooth objects into the
lisse-étale site carries every bounded above acyclic complex of direct sums of the `j_{U!} 𝒪_U` to
an acyclic complex. -/
theorem moduleLowerShriekAcyclic (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (inverseImageRing
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))) ℤ)
    (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) (L.X n))
    (hLac : L.Acyclic) :
    (((lowerShriekModules (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).Acyclic :=
  SmallModel.lowerShriekModules_acyclic_of_essentiallySmall _ _ _ _ a L hLE hLP hLac

section Derived

-- the abelian structure of the library on sheaves of modules whose sections contain the site
-- would be met first by instance search here, with a universe constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable [HasDerivedCategory.{t} (SheafOfModules.{u}
  (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))]
  [HasDerivedCategory.{t'} (SheafOfModules.{u}
    (inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))]

/-- **Stacks 07AS (2), existence**: the lower shriek `g_!` of sheaves of modules for the
lisse-étale site has an unbounded left derived functor, defined at every object, for any models of
the two derived categories. -/
instance hasPointwiseLeftDerivedFunctor_moduleLowerShriek :
    (lowerShriekOnHomotopy (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (sourceQuasiIso (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) :=
  hasPointwiseLeftDerivedLowerShriek_of_essentiallySmall _ _ _ _
    (moduleLowerShriekAcyclic B S hS 𝒳)

/-- Sheaves of modules on the étale site of an algebraic stack form a Grothendieck abelian
category, the site being essentially small. -/
instance isGrothendieckAbelian_etaleModules :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- **The functor `g^* : D(𝒳_{étale}, 𝒪_𝒳) ⥤ D(𝒪_{𝒳_{lisse,étale}})`**: restriction of sheaves of
modules to the smooth objects is exact, so it acts on the unbounded derived categories
degreewise. -/
abbrev derivedModuleRestriction :
    DerivedCategory (SheafOfModules.{u} (SmallModel.targetRing
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) ⥤ DerivedCategory
            (SheafOfModules.{u} (inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p
              (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))) :=
  (restrictionModules (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒳))
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
    (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)).mapDerivedCategory

/-- **The derived lower shriek `Lg_! : D(𝒪_{𝒳_{lisse,étale}}) ⥤ D(𝒪_𝒳)` of Stacks 07AS (2)**: the
total left derived functor of lower shriek of sheaves of modules along the inclusion of the smooth
objects, with no hypothesis, for any models of the two derived categories. -/
def derivedModuleLowerShriek :
    DerivedCategory (SheafOfModules.{u} (inverseImageRing
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))) ⥤ DerivedCategory
            (SheafOfModules.{u} (SmallModel.targetRing
              (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) :=
  totalLeftDerivedLowerShriek (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)

/-- The comparison `Qh ⋙ Lg_! ⟶ g_! ⋙ Qh` exhibiting `Lg_!` as the left derived functor of
`g_!`. -/
abbrev derivedModuleLowerShriekCounit :
    DerivedCategory.Qh ⋙ derivedModuleLowerShriek B S hS 𝒳 ⟶
      lowerShriekOnHomotopy (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O) ⋙ DerivedCategory.Qh :=
  totalLeftDerivedLowerShriekCounit (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)

/-- **Stacks 07AS (2), adjointness**: `Lg_!` is left adjoint to `g^*`, the restriction of
complexes of modules to the smooth objects, with no hypothesis, for any models. -/
def derivedModuleLowerShriekAdjunction :
    derivedModuleLowerShriek B S hS 𝒳 ⊣ LisseEtale.derivedModuleRestriction B S hS 𝒳 :=
  totalLeftDerivedLowerShriekAdjunction (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)
    (moduleLowerShriekAcyclic B S hS 𝒳)

/-- **Stacks 07AS (2), `g^* Lg_! = id`**: the unit of `Lg_! ⊣ g^*` is invertible, with no
hypothesis. -/
theorem isIso_derivedModuleLowerShriekAdjunction_unit :
    IsIso (LisseEtale.derivedModuleLowerShriekAdjunction B S hS 𝒳).unit :=
  isIso_totalLeftDerivedLowerShriekAdjunction_unit _ _ _ _ (moduleLowerShriekAcyclic B S hS 𝒳)
    (isIso_adjunctionModules_unit_inclusion B S hS 𝒳)

/-- **Stacks 07AS (2), `g^* Lg_! = id`, as an isomorphism of functors**: restriction after the
derived lower shriek is canonically the identity of `D(𝒪_{𝒳_{lisse,étale}})`, the inverse of the
unit of `Lg_! ⊣ g^*`. -/
def derivedModuleLowerShriekRestrictionIso :
    derivedModuleLowerShriek B S hS 𝒳 ⋙ LisseEtale.derivedModuleRestriction B S hS 𝒳 ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (inverseImageRing
        (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))) :=
  have := isIso_derivedModuleLowerShriekAdjunction_unit B S hS 𝒳
  (asIso (derivedModuleLowerShriekAdjunction B S hS 𝒳).unit).symm

/-- **`Lg_!` is computed degreewise on bounded above complexes of direct sums of the
`j_{U!} 𝒪_U`** (Stacks 0794, as used by Stacks 07B9): for such a complex `L` bounded above by `0`,
the comparison `Lg_!(L) ⟶ g_!(L)` exhibiting `Lg_!` as a left derived functor is an
isomorphism. -/
theorem isIso_derivedModuleLowerShriekCounit_app
    (L : CochainComplex (SheafOfModules.{u} (inverseImageRing
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))) ℤ)
    (hL0 : CochainComplex.IsStrictlyLE L 0)
    (hL : ∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) (L.X n)) :
    IsIso ((derivedModuleLowerShriekCounit B S hS 𝒳).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) :=
  isIso_totalLeftDerivedLowerShriekCounit_app _ _ _ _ (moduleLowerShriekAcyclic B S hS 𝒳) L hL0 hL

/-- `g^*` on the derived categories commutes with the shift, being induced by an exact functor. -/
local instance commShift_derivedModuleRestriction_local :
    (LisseEtale.derivedModuleRestriction B S hS 𝒳).CommShift ℤ :=
  inferInstanceAs ((restrictionModules (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)).mapDerivedCategory.CommShift ℤ)

/-- `g^*` on the derived categories is triangulated, being induced by an exact functor. -/
local instance isTriangulated_derivedModuleRestriction_local :
    (LisseEtale.derivedModuleRestriction B S hS 𝒳).IsTriangulated :=
  inferInstanceAs (restrictionModules (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)).mapDerivedCategory.IsTriangulated

/-- **`Lg_!` commutes with the shift**: the compatibility with the shift of the left adjoint of
the shift-compatible functor `g^*`. -/
instance commShift_derivedModuleLowerShriek :
    (LisseEtale.derivedModuleLowerShriek B S hS 𝒳).CommShift ℤ :=
  (LisseEtale.derivedModuleLowerShriekAdjunction B S hS 𝒳).leftAdjointCommShift ℤ

/-- The adjunction `Lg_! ⊣ g^*` is compatible with the shifts. -/
instance commShift_derivedModuleLowerShriekAdjunction :
    (LisseEtale.derivedModuleLowerShriekAdjunction B S hS 𝒳).CommShift ℤ :=
  (LisseEtale.derivedModuleLowerShriekAdjunction B S hS 𝒳).commShift_of_rightAdjoint ℤ

/-- **`Lg_!` is a triangulated functor**, being left adjoint to the triangulated functor `g^*`:
it carries distinguished triangles to distinguished triangles. -/
instance isTriangulated_derivedModuleLowerShriek :
    (LisseEtale.derivedModuleLowerShriek B S hS 𝒳).IsTriangulated :=
  Adjunction.isTriangulated_leftAdjoint (LisseEtale.derivedModuleLowerShriekAdjunction B S hS 𝒳)

end Derived

/-! ### The standard models

The abelian structures used by the consumers of the first version of this file, and the
degreewise computation read at the standard models `HasDerivedCategory.standard`, named in the
statement. -/

section StandardModels

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- Mathlib's abelian structure on the sheaves of modules on the étale site. -/
abbrev abelianEtaleModules : Abelian (SheafOfModules.{u}
  (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) :=
  SheafOfModules.instAbelian _

/-- Mathlib's abelian structure on `Mod(𝒪_{𝒳_{lisse,étale}})`. -/
abbrev abelianLisseEtaleModules : Abelian
  (SheafOfModules.{u} (inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))) :=
  SheafOfModules.instAbelian _

/-- **Stacks 07AS, existence of `Lg_!`, at the standard models** `HasDerivedCategory.standard`
of the two derived categories, named in the statement: the form in which the general theory
(`Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek`, formed at those models) consumes
it. -/
instance hasPointwiseLeftDerivedFunctor_moduleLowerShriek_standard :
    (lowerShriekOnHomotopy (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O) ⋙
        @DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard
          (SheafOfModules.{u} (SmallModel.targetRing
            (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))).HasPointwiseLeftDerivedFunctor
      (sourceQuasiIso (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))
  hasPointwiseLeftDerivedLowerShriek_of_essentiallySmall _ _ _ _ (moduleLowerShriekAcyclic B S hS 𝒳)

/-- **`Lg_!` is computed degreewise, at the standard models of the derived categories**: the
comparison `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriekComparison` of the general
theory, which is formed at `HasDerivedCategory.standard`, is invertible on a bounded above complex
of direct sums of the `j_{U!} 𝒪_U`. -/
theorem isIso_derivedModuleLowerShriekComparison_app
    (L : CochainComplex (SheafOfModules.{u} (inverseImageRing
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))) ℤ) [L.IsStrictlyLE 0]
    (hL : ∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) (L.X n)) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u}
      (inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
    letI := HasDerivedCategory.standard (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))
    haveI := hasPointwiseLeftDerivedLowerShriek_of_essentiallySmall
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
        (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)
      (moduleLowerShriekAcyclic B S hS 𝒳)
    IsIso ((derivedLowerShriekComparison (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) :=
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))
  isIso_totalLeftDerivedLowerShriekCounit_app _ _ _ _ (moduleLowerShriekAcyclic B S hS 𝒳) L
    inferInstance hL

end StandardModels


end AlgebraicGeometry.Stack.LisseEtale

end
