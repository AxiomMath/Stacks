module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiCovering.BigZariskiMorphism

/-!
# Inverse image of direct image along a monomorphism of big sites

Let `f : X ⟶ Y` be a monomorphism in one of the big sites of a scheme. The counit of the
inverse-image/direct-image adjunction attached to `f` is an isomorphism: the inverse image of
the direct image of a sheaf on the big site over `X` is the sheaf itself. This is asserted for
the Zariski, étale, smooth, syntomic and fppf topologies.

## Main results

* `AlgebraicGeometry.bigZariskiMorphism_counit_isIso`,
  `AlgebraicGeometry.bigEtaleMorphism_counit_isIso`,
  `AlgebraicGeometry.bigSmoothMorphism_counit_isIso`,
  `AlgebraicGeometry.bigSyntomicMorphism_counit_isIso` and
  `AlgebraicGeometry.bigFppfMorphism_counit_isIso` — the five cases.

## Implementation notes

The statements are about the counit of the canonical adjunction carried by the morphism of
topoi, not about an unspecified isomorphism. All five reduce to one categorical fact: slicing
along a monomorphism is a fully faithful functor, and for a fully faithful cocontinuous functor
the counit of the sheaf adjunction between the slice topoi is invertible. The counit of the
adjunction supplied by cocontinuity is the one Mathlib already knows to be invertible, and the
two adjunctions have the same right adjoint, so their counits agree under the canonical
comparison of left adjoints.

## References

* [Stacks Project, Tag 04C7](https://stacks.math.columbia.edu/tag/04C7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Slice

universe v₂ w w'

/-- Slicing along a monomorphism is full: a morphism between the images is already a morphism
of the original slice objects. -/
private theorem overMapFullOfMono {C : Type (u + 1)} [Category.{u} C] {X Y : C}
    (f : X ⟶ Y) [Mono f] : (Over.map f).Full where
  map_surjective {A B} g :=
    ⟨Over.homMk g.left ((cancel_mono f).1 (by simpa [Category.assoc] using Over.w g)),
      by ext; rfl⟩

/-- Slicing along a monomorphism is faithful. -/
private theorem overMapFaithfulOfMono {C : Type (u + 1)} [Category.{u} C] {X Y : C}
    (f : X ⟶ Y) [Mono f] : (Over.map f).Faithful where
  map_injective {A B} g h e :=
    Over.OverMorphism.ext (by simpa using congrArg Over.Hom.left e)

/-- For a monomorphism `f`, the counit of the adjunction between the sheaf pullback and the
sheaf pushforward along `Over.map f` is an isomorphism. -/
private theorem pullbackCounit_isIso_of_full_faithful
    {D : Type (v₂ + 1)} [Category.{v₂} D] {X Y : D} (f : X ⟶ Y) [Mono f]
    {A : Type w} [Category.{w'} A]
    (J : GrothendieckTopology (Over X)) (K : GrothendieckTopology (Over Y))
    [(Over.map f).IsCocontinuous J K] [(Over.map f).IsContinuous J K]
    [HasWeakSheafify J A]
    [∀ G : (Over X)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension G]
    (F : Sheaf J A) :
    IsIso (((Over.map f).sheafAdjunctionPullbackCocontinuous A J K).counit.app F) := by
  have : (Over.map f).Full := overMapFullOfMono f
  have : (Over.map f).Faithful := overMapFaithfulOfMono f
  have := Functor.isIso_sheafAdjunctionCocontinuous_counit (Over.map f) A J K
  rw [← Adjunction.leftAdjointUniq_hom_app_counit
    ((Over.map f).sheafAdjunctionPullbackCocontinuous A J K)
    ((Over.map f).sheafAdjunctionCocontinuous A J K)]
  infer_instance

end Slice

/-- **Stacks 04C7, the Zariski case.** The inverse-image/direct-image counit is invertible for
a monomorphism on the big Zariski site. -/
@[stacks 04C7 "Zariski case"]
public theorem bigZariskiMorphism_counit_isIso
    (B : BigZariskiSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigZariskiOver.topology B X.1 X.2) (Type (u + 1))) :
    IsIso ((bigZariskiMorphism B X Y f).adj.counit.app F) :=
  pullbackCounit_isIso_of_full_faithful f _ _ F

/-- **Stacks 04C7, the étale case.** The inverse-image/direct-image counit is invertible for a
monomorphism on the big étale site. -/
@[stacks 04C7 "étale case"]
public theorem bigEtaleMorphism_counit_isIso
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigEtaleOver.topology B X.1 X.2) (Type (u + 1))) :
    IsIso ((bigEtaleMorphism B X Y f).adj.counit.app F) :=
  pullbackCounit_isIso_of_full_faithful f _ _ F

/-- **Stacks 04C7, the smooth case.** The inverse-image/direct-image counit is invertible for a
monomorphism on the big smooth site. -/
@[stacks 04C7 "smooth case"]
public theorem bigSmoothMorphism_counit_isIso
    (B : BigSmoothSite.{u}) {X Y : B.category} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigSmoothOver.topology B X.1 X.2) (Type (u + 1))) :
    IsIso ((bigSmoothMorphismOfTopoi B f).adj.counit.app F) :=
  pullbackCounit_isIso_of_full_faithful f _ _ F

/-- **Stacks 04C7, the syntomic case.** The inverse-image/direct-image counit is invertible for
a monomorphism on the big syntomic site. -/
@[stacks 04C7 "syntomic case"]
public theorem bigSyntomicMorphism_counit_isIso
    (B : BigSyntomicSite.{u}) {X Y : B.category} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigSyntomicOver.topology B X.1 X.2) (Type (u + 1))) :
    IsIso ((bigSyntomicMorphismOfTopoi B f).adj.counit.app F) :=
  pullbackCounit_isIso_of_full_faithful f _ _ F

/-- **Stacks 04C7, the fppf case.** The inverse-image/direct-image counit is invertible for a
monomorphism on the big fppf site. -/
@[stacks 04C7 "fppf case"]
public theorem bigFppfMorphism_counit_isIso
    (B : BigFppfSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (B.topology.over X) (Type (u + 1))) :
    IsIso ((bigFppfMorphism B X Y f).adj.counit.app F) :=
  pullbackCounit_isIso_of_full_faithful f _ _ F

end AlgebraicGeometry
