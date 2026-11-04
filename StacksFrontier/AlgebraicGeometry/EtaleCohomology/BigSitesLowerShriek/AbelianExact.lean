module

public import Mathlib.Algebra.Category.Grp.AB
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiCovering.BigZariskiMorphism
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Exactness of lower shriek on abelian sheaves of the big sites

Let `f : T ⟶ S` be a morphism in one of the big Zariski, étale, fppf, smooth or syntomic
sites of schemes. The inverse image of the induced morphism of topoi is restriction along
postcomposition with `f`, and it has a left adjoint `f_!` on abelian sheaves. This file records
that `f_!` is exact: it preserves both finite limits and finite colimits.

## Main results

* `AlgebraicGeometry.bigZariskiLowerShriek_preservesFiniteLimits`,
  `AlgebraicGeometry.bigEtaleLowerShriek_preservesFiniteLimits`,
  `AlgebraicGeometry.bigFppfLowerShriek_preservesFiniteLimits`,
  `AlgebraicGeometry.bigSmoothLowerShriek_preservesFiniteLimits`,
  `AlgebraicGeometry.bigSyntomicLowerShriek_preservesFiniteLimits` — left exactness.
* `AlgebraicGeometry.bigZariskiLowerShriek_preservesFiniteColimits`,
  `AlgebraicGeometry.bigEtaleLowerShriek_preservesFiniteColimits`,
  `AlgebraicGeometry.bigFppfLowerShriek_preservesFiniteColimits`,
  `AlgebraicGeometry.bigSmoothLowerShriek_preservesFiniteColimits`,
  `AlgebraicGeometry.bigSyntomicLowerShriek_preservesFiniteColimits` — right exactness.

## Implementation notes

Lower shriek is the sheaf pullback along postcomposition on the slices of the big site, and its
right adjoint is restriction along the same functor; the adjunction itself is
`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`. What is proved here
is exactness, and it is the general criterion
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits` and
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits` applied to postcomposition: the slices
have fibre products and equalizers, and postcomposition preserves them because it does so after
forgetting the structure morphism. Those two statements are about the Kan-extension model of the
sheaf pullback, so each conclusion is transported to the abstract left adjoint along
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`.

Abelian sheaves take values in `Ab` at the universe of the chosen big site, which is the universe
in which the sheafification of abelian presheaves on these slices is available.

## References

* [Stacks Project, Tag 04CC](https://stacks.math.columbia.edu/tag/04CC)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A slice of a category with fibre products has equalizers: it also has a terminal object,
hence binary products, and fibre products together with binary products give equalizers. -/
private instance over_hasEqualizers_of_hasPullbacks
    {C : Type*} [Category C] [HasPullbacks C] (X : C) :
    HasEqualizers (Over X) := by
  let : HasBinaryProducts (Over X) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  exact hasEqualizers_of_hasPullbacks_and_binary_products

/-- The abstract sheaf pullback preserves finite limits if the Kan-extension model does. -/
private theorem sheafPullback_preservesFiniteLimits
    {C D : Type*} [Category C] [Category D] {G : C ⥤ D} {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} [G.IsContinuous J K]
    [HasWeakSheafify K Ab.{u + 1}] [∀ F : Cᵒᵖ ⥤ Ab.{u + 1}, G.op.HasLeftKanExtension F]
    [PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback G Ab.{u + 1} J K)] :
    PreservesFiniteLimits (G.sheafPullback Ab.{u + 1} J K) :=
  preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso G Ab.{u + 1} J K).symm

/-- The abstract sheaf pullback preserves finite colimits if the Kan-extension model does. -/
private theorem sheafPullback_preservesFiniteColimits
    {C D : Type*} [Category C] [Category D] {G : C ⥤ D} {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} [G.IsContinuous J K]
    [HasWeakSheafify K Ab.{u + 1}] [∀ F : Cᵒᵖ ⥤ Ab.{u + 1}, G.op.HasLeftKanExtension F]
    [PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback G Ab.{u + 1} J K)] :
    PreservesFiniteColimits (G.sheafPullback Ab.{u + 1} J K) :=
  preservesFiniteColimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso G Ab.{u + 1} J K).symm

add_to_stacks 04CC "abelian_lower_shriek_exact"
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

/-- **Stacks 04CC(1), Zariski case.** Lower shriek on big Zariski abelian sheaves preserves
finite limits. -/
@[stacks 04CC "abelian_lower_shriek_exact", instance]
public theorem bigZariskiLowerShriek_preservesFiniteLimits
    (B : BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S) :
    PreservesFiniteLimits ((Over.map f).sheafPullback Ab.{u + 1}
      (BigZariskiOver.topology B T.1 T.property)
      (BigZariskiOver.topology B S.1 S.property)) :=
  sheafPullback_preservesFiniteLimits

/-- **Stacks 04CC(1), Zariski case.** Lower shriek on big Zariski abelian sheaves preserves
finite colimits. -/
@[stacks 04CC "abelian_lower_shriek_exact", instance]
public theorem bigZariskiLowerShriek_preservesFiniteColimits
    (B : BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S) :
    PreservesFiniteColimits ((Over.map f).sheafPullback Ab.{u + 1}
      (BigZariskiOver.topology B T.1 T.property)
      (BigZariskiOver.topology B S.1 S.property)) :=
  sheafPullback_preservesFiniteColimits

/-- **Stacks 04CC(1), étale case.** Lower shriek on big étale abelian sheaves preserves
finite limits. -/
@[stacks 04CC "abelian_lower_shriek_exact", instance]
public theorem bigEtaleLowerShriek_preservesFiniteLimits
    (B : BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S) :
    PreservesFiniteLimits ((Over.map f).sheafPullback Ab.{u + 1}
      (BigEtaleOver.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)) :=
  sheafPullback_preservesFiniteLimits

/-- **Stacks 04CC(1), étale case.** Lower shriek on big étale abelian sheaves preserves
finite colimits. -/
@[stacks 04CC "abelian_lower_shriek_exact", instance]
public theorem bigEtaleLowerShriek_preservesFiniteColimits
    (B : BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S) :
    PreservesFiniteColimits ((Over.map f).sheafPullback Ab.{u + 1}
      (BigEtaleOver.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)) :=
  sheafPullback_preservesFiniteColimits

/-- **Stacks 04CC(1), fppf case.** Lower shriek on big fppf abelian sheaves preserves
finite limits. -/
@[stacks 04CC "abelian_lower_shriek_exact", instance]
public theorem bigFppfLowerShriek_preservesFiniteLimits
    (B : BigFppfSite.{u}) (T S : B.Schemes) (f : T ⟶ S) :
    PreservesFiniteLimits ((Over.map f).sheafPullback Ab.{u + 1}
      (B.topology.over T) (B.topology.over S)) :=
  sheafPullback_preservesFiniteLimits

/-- **Stacks 04CC(1), fppf case.** Lower shriek on big fppf abelian sheaves preserves
finite colimits. -/
@[stacks 04CC "abelian_lower_shriek_exact", instance]
public theorem bigFppfLowerShriek_preservesFiniteColimits
    (B : BigFppfSite.{u}) (T S : B.Schemes) (f : T ⟶ S) :
    PreservesFiniteColimits ((Over.map f).sheafPullback Ab.{u + 1}
      (B.topology.over T) (B.topology.over S)) :=
  sheafPullback_preservesFiniteColimits

/-- **Stacks 04CC(1), smooth case.** Lower shriek on big smooth abelian sheaves preserves
finite limits. -/
@[stacks 04CC "abelian_lower_shriek_exact", instance]
public theorem bigSmoothLowerShriek_preservesFiniteLimits
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    PreservesFiniteLimits ((Over.map f).sheafPullback Ab.{u + 1}
      (BigSmoothOver.topology B T.1 T.2)
      (BigSmoothOver.topology B S.1 S.2)) :=
  sheafPullback_preservesFiniteLimits

/-- **Stacks 04CC(1), smooth case.** Lower shriek on big smooth abelian sheaves preserves
finite colimits. -/
@[stacks 04CC "abelian_lower_shriek_exact", instance]
public theorem bigSmoothLowerShriek_preservesFiniteColimits
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    PreservesFiniteColimits ((Over.map f).sheafPullback Ab.{u + 1}
      (BigSmoothOver.topology B T.1 T.2)
      (BigSmoothOver.topology B S.1 S.2)) :=
  sheafPullback_preservesFiniteColimits

/-- **Stacks 04CC(1), syntomic case.** Lower shriek on big syntomic abelian sheaves preserves
finite limits. -/
@[stacks 04CC "abelian_lower_shriek_exact", instance]
public theorem bigSyntomicLowerShriek_preservesFiniteLimits
    (B : BigSyntomicSite.{u}) {T S : B.category} (f : T ⟶ S) :
    PreservesFiniteLimits ((Over.map f).sheafPullback Ab.{u + 1}
      (BigSyntomicOver.topology B T.1 T.2)
      (BigSyntomicOver.topology B S.1 S.2)) :=
  sheafPullback_preservesFiniteLimits

/-- **Stacks 04CC(1), syntomic case.** Lower shriek on big syntomic abelian sheaves preserves
finite colimits. -/
@[stacks 04CC "abelian_lower_shriek_exact", instance]
public theorem bigSyntomicLowerShriek_preservesFiniteColimits
    (B : BigSyntomicSite.{u}) {T S : B.category} (f : T ⟶ S) :
    PreservesFiniteColimits ((Over.map f).sheafPullback Ab.{u + 1}
      (BigSyntomicOver.topology B T.1 T.2)
      (BigSyntomicOver.topology B S.1 S.2)) :=
  sheafPullback_preservesFiniteColimits

end AlgebraicGeometry

end
