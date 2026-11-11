module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Restricting abelian sheaves from a big étale site to a small étale site

Let `B` be a big étale site. Restriction of abelian sheaves from the big étale category over a
scheme `S` to the small étale category of `S` preserves injective objects, and on complexes it
preserves K-injectivity. The same holds for restriction along an arbitrary morphism `f : T ⟶ S`
of `B`, where the restriction functor is the inverse image of the morphism of topoi `i_f`.

Restriction is the direct image of the projection from the big étale topos to the small étale
topos. On abelian sheaves it is Mathlib's `sheafPushforwardContinuous` for the small-site
inclusion, respectively for the continuous postcomposition functor
`AlgebraicGeometry.smallEtaleToBigEtaleFunctor`.

## Main results

* `AlgebraicGeometry.injective_smallEtaleRestriction` — restriction to the small étale site of
  `S` preserves injective abelian sheaves.
* `AlgebraicGeometry.injective_smallEtaleRestrictionAlong` — the same for restriction along a
  morphism `f : T ⟶ S` of the big étale site.
* `AlgebraicGeometry.isKInjective_smallEtaleRestriction` and
  `AlgebraicGeometry.isKInjective_smallEtaleRestrictionAlong` — restriction preserves
  K-injectivity of complexes of abelian sheaves.

The final sentence of Stacks 0758, that the corresponding statements for modules do not hold,
is `AlgebraicGeometry.exists_injective_not_injective_smallEtaleModuleRestriction` and
`AlgebraicGeometry.exists_isKInjective_not_isKInjective_smallEtaleModuleRestriction` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/RestrictionModules.lean`.

## Implementation notes

Preservation of injectives and of K-injectivity both follow from exactness of the left adjoint
of restriction: the lower shriek functor of the relevant continuous functor of sites. That
exactness is `Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits` together with
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits`, so no Kan-extension computation is
redone here.

The statements for a morphism `f : T ⟶ S` do not require `f` itself to be étale; only the
objects of the big étale site enter. Sheafification of abelian groups on these sites is
supplied by `CategoryTheory.hasSheafifyEssentiallySmallSite`, every such site being essentially
small, so the results need no sheafification hypothesis.

## References

* [Stacks Project, Tag 0758](https://stacks.math.columbia.edu/tag/0758)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Abelian sheaves on an essentially small site admit sheafification. -/
private noncomputable instance hasSheafifyAbSite
    {C : Type (u + 1)} [Category.{u + 1} C] (J : GrothendieckTopology C) :
    HasSheafify J Ab.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1, u + 1, u + 1} J

variable (B : BigEtaleSite.{u})

/-- The inclusion of the small étale category of `S` into the big étale category over `S`
preserves fibre products. -/
private instance smallEtaleInclusion_preservesPullbacks
    (S : Scheme.{u}) (hS : B.Contains S) :
    PreservesLimitsOfShape WalkingCospan (SmallEtale.inclusion B S hS) := by
  have hforget : PreservesLimitsOfShape WalkingCospan
      (SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS)) := by
    let : B.inclusion.Full := inferInstance
    let : B.inclusion.Faithful := inferInstance
    let : ReflectsLimitsOfShape WalkingCospan B.inclusion :=
      (fullyFaithful_reflectsLimits B.inclusion).reflectsLimitsOfShape
    let : PreservesLimitsOfShape WalkingCospan
        ((SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS)) ⋙ B.inclusion) :=
      preservesPullbacks_smallEtaleToScheme B S hS
    exact preservesLimitsOfShape_of_reflects_of_preserves _ B.inclusion
  let : PreservesLimitsOfShape WalkingCospan
      (SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS)) := hforget
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (SmallEtale.inclusion B S hS) (Over.forget (B.obj S hS))

/-- The small étale category of `S` has finite limits. -/
private instance smallEtale_hasFiniteLimits (S : Scheme.{u}) (hS : B.Contains S) :
    HasFiniteLimits (SmallEtale B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The inclusion of the small étale category of `S` preserves equalizers. -/
private instance smallEtaleInclusion_preservesEqualizers
    (S : Scheme.{u}) (hS : B.Contains S) :
    PreservesLimitsOfShape WalkingParallelPair (SmallEtale.inclusion B S hS) := by
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (SmallEtale.inclusion B S hS) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  let : PreservesLimitsOfShape (Discrete WalkingPair) (SmallEtale.inclusion B S hS) :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks _
  exact preservesEqualizers_of_preservesPullbacks_and_binaryProducts _

/-- The inclusion of the small étale category of `S` into the big étale category over `S` is a
continuous functor of sites. -/
private instance smallEtaleInclusion_isContinuous (S : Scheme.{u}) (hS : B.Contains S) :
    (SmallEtale.inclusion B S hS).IsContinuous
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS) :=
  (smallEtaleInclusion_isMorphismOfSites B S hS).toIsContinuous

/-- The inclusion of the small étale category of `S` preserves finite limits. -/
private instance smallEtaleInclusion_preservesFiniteLimits
    (S : Scheme.{u}) (hS : B.Contains S) :
    PreservesFiniteLimits (SmallEtale.inclusion B S hS) := by
  let : PreservesLimit (Functor.empty.{0} (SmallEtale B S hS))
      (SmallEtale.inclusion B S hS) := smallEtaleInclusion_preservesTerminal B S hS
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (SmallEtale.inclusion B S hS) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks
    (SmallEtale.inclusion B S hS)

/-- Postcomposition with a morphism of the big étale site preserves connected limits.

NOT removable in favour of the identical
`AlgebraicGeometry.overMap_preservesLimitsOfConnectedShape` of
`StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos`, even though this module
imports it: that copy is `private`, so it is not exported and does not take part in instance
search here. Deleting this one leaves `PreservesLimitsOfShape WalkingCospan` unsynthesizable
at the two `Over.map` sites below. -/
private instance overMap_preservesLimitsOfConnectedShape
    (T S : B.Scheme) (f : T ⟶ S) (I : Type*) [SmallCategory I] [IsConnected I]
    [HasLimitsOfShape I (Over (B.obj T.obj T.property))]
    [HasLimitsOfShape I (Over (B.obj S.obj S.property))] :
    PreservesLimitsOfShape I (Over.map f) := by
  have h : PreservesLimitsOfShape I
      ((Over.map f) ⋙ Over.forget (B.obj S.obj S.property)) := by
    rw [Over.mapForget_eq]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (Over.forget (B.obj S.obj S.property))

-- NO `smallEtaleToBigEtale_preservesPullbacks` / `_preservesEqualizers` HERE. Both stated and
-- proved exactly what `AlgebraicGeometry.smallEtaleToBigEtale_preservesPullbacks`:124 and
-- `..._preservesEqualizers`:128 of
-- `StacksFrontier/AlgebraicGeometry/Topologies/Etale/SmallToBigTopos.lean` state and prove
-- (`by infer_instance` over the same `smallEtaleToBigEtaleFunctor`), and this module imports
-- that one at :14.

/-- Restriction along a continuous functor of sites preserves injective abelian sheaves when its
left adjoint, the lower shriek functor, is exact. -/
private theorem injective_sheafPushforwardContinuous_obj
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] (G : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
    [HasPullbacks C] [HasEqualizers C] [PreservesLimitsOfShape WalkingCospan G]
    [PreservesLimitsOfShape WalkingParallelPair G]
    [∀ F : Cᵒᵖ ⥤ Ab.{u + 1}, G.op.HasPointwiseLeftKanExtension F]
    [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, G.op.HasLeftKanExtension F]
    [HasSheafify K Ab.{u + 1}] (I : Sheaf K Ab.{u + 1}) [Injective I] :
    Injective ((G.sheafPushforwardContinuous Ab.{u + 1} J K).obj I) := by
  let L := Functor.sheafPullbackConstruction.sheafPullback G Ab.{u + 1} J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{u + 1} J K
  let : (G.sheafPushforwardContinuous Ab.{u + 1} J K).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : L.Additive := Functor.additive_of_preserves_binary_products _
  let : (G.sheafPushforwardContinuous Ab.{u + 1} J K).PreservesInjectiveObjects :=
    preservesInjectiveObjects_of_isExact _ L adj ⟨inferInstance, inferInstance⟩
  exact Functor.injective_obj_of_injective _ inferInstance

/-- Restriction along a continuous functor of sites preserves K-injective complexes of abelian
sheaves when its left adjoint, the lower shriek functor, is exact. -/
private theorem isKInjective_mapHomologicalComplex_sheafPushforwardContinuous
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] (G : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
    [HasPullbacks C] [HasEqualizers C] [PreservesLimitsOfShape WalkingCospan G]
    [PreservesLimitsOfShape WalkingParallelPair G]
    [∀ F : Cᵒᵖ ⥤ Ab.{u + 1}, G.op.HasPointwiseLeftKanExtension F]
    [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, G.op.HasLeftKanExtension F]
    [HasSheafify K Ab.{u + 1}]
    (I : CochainComplex (Sheaf K Ab.{u + 1}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((G.sheafPushforwardContinuous Ab.{u + 1} J K).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let L := Functor.sheafPullbackConstruction.sheafPullback G Ab.{u + 1} J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{u + 1} J K
  let : (G.sheafPushforwardContinuous Ab.{u + 1} J K).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : L.Additive := Functor.additive_of_preserves_binary_products _
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ L adj I

/-- **Stacks Project, Tag 0758.** Restriction of an injective abelian sheaf
from the big étale site over `S` to the small étale site of `S` is injective. -/
@[stacks 0758 "part (1)(b): restriction to the small étale site preserves injective abelian \
sheaves"]
public theorem injective_smallEtaleRestriction
    (S : Scheme.{u}) (hS : B.Contains S)
    (I : Sheaf (BigEtaleOver.topology B S hS) Ab.{u + 1})
    [Injective I] :
    Injective (((SmallEtale.inclusion B S hS).sheafPushforwardContinuous
      Ab.{u + 1} (SmallEtale.topology B S hS)
      (BigEtaleOver.topology B S hS)).obj I) :=
  injective_sheafPushforwardContinuous_obj _ _ _ I

/-- **Stacks Project, Tag 0758.** Restriction to the small étale site of an
object of the big étale site preserves injectivity of abelian sheaves. -/
@[stacks 0758 "part (1)(a): restriction along a morphism of the big étale site preserves \
injective abelian sheaves"]
public theorem injective_smallEtaleRestrictionAlong
    (T S : B.Scheme) (f : T ⟶ S)
    (I : Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
    [Injective I] :
    Injective
      (((smallEtaleToBigEtaleFunctor B T S f).sheafPushforwardContinuous
        Ab.{u + 1} (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)).obj I) :=
  injective_sheafPushforwardContinuous_obj _ _ _ I

/-- **Stacks Project, Tag 0758.** Restriction of a K-injective complex of
abelian sheaves from the big étale site to the small étale site is K-injective. -/
@[stacks 0758 "part (2)(b): restriction to the small étale site preserves K-injective \
complexes of abelian sheaves"]
public theorem isKInjective_smallEtaleRestriction
    (S : Scheme.{u}) (hS : B.Contains S)
    (I : CochainComplex (Sheaf (BigEtaleOver.topology B S hS) Ab.{u + 1}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((SmallEtale.inclusion B S hS).sheafPushforwardContinuous
        Ab.{u + 1} (SmallEtale.topology B S hS)
        (BigEtaleOver.topology B S hS)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
  isKInjective_mapHomologicalComplex_sheafPushforwardContinuous _ _ _ I

/-- **Stacks Project, Tag 0758.** Restriction to the small étale site of an
object of the big étale site preserves K-injectivity of abelian sheaf complexes. -/
@[stacks 0758 "part (2)(a): restriction along a morphism of the big étale site preserves \
K-injective complexes of abelian sheaves"]
public theorem isKInjective_smallEtaleRestrictionAlong
    (T S : B.Scheme) (f : T ⟶ S)
    (I : CochainComplex (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((smallEtaleToBigEtaleFunctor B T S f).sheafPushforwardContinuous
        Ab.{u + 1} (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
  isKInjective_mapHomologicalComplex_sheafPushforwardContinuous _ _ _ I

end AlgebraicGeometry
