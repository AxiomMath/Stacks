module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiCovering.BigZariskiMorphism
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Continuous

/-!
# Lower shriek of a monomorphism of big sites is fully faithful

Let `f : X ⟶ Y` be a monomorphism in one of the big sites of a scheme. The unit of the
lower-shriek/inverse-image adjunction `f_big! ⊣ f_big⁻¹` is an isomorphism: a sheaf on the big
site over `X` is recovered from its extension to the big site over `Y`. This is asserted for the
Zariski, étale, smooth, syntomic and fppf topologies, and for both sheaves of sets and sheaves of
abelian groups.

## Main results

* `AlgebraicGeometry.bigZariskiLowerShriek_unit_isIso`,
  `AlgebraicGeometry.bigEtaleLowerShriek_unit_isIso`,
  `AlgebraicGeometry.bigSmoothLowerShriek_unit_isIso`,
  `AlgebraicGeometry.bigSyntomicLowerShriek_unit_isIso` and
  `AlgebraicGeometry.bigFppfLowerShriek_unit_isIso` — the five cases for sheaves of sets.
* `AlgebraicGeometry.bigZariskiAbelianLowerShriek_unit_isIso`,
  `AlgebraicGeometry.bigEtaleAbelianLowerShriek_unit_isIso`,
  `AlgebraicGeometry.bigSmoothAbelianLowerShriek_unit_isIso`,
  `AlgebraicGeometry.bigSyntomicAbelianLowerShriek_unit_isIso` and
  `AlgebraicGeometry.bigFppfAbelianLowerShriek_unit_isIso` — the five cases for sheaves of
  abelian groups.

## Implementation notes

The two lower shrieks are different functors and the statements keep them apart. For sheaves of
sets `f_big!` is the left adjoint of `f_big⁻¹` on sheaves of sets, which the library already
carries as `AlgebraicGeometry.bigZariskiLowerShriekAdjunction` and its four analogues (for the
smooth site the left adjoint is only named through the instance
`AlgebraicGeometry.bigSmoothInverseImage_isRightAdjoint`, so the adjunction is taken from that).
For sheaves of abelian groups `f_big!` is the functor of Modules on Sites, Section 04BE, namely
the left adjoint of `f_big⁻¹` on abelian sheaves, which the library carries as
`Stacks.Sites.LowerShriek.FullyFaithful.gShriek`; it is not the set-level functor.

Both halves reduce to one categorical fact: slicing along a monomorphism is fully faithful, and
for a fully faithful continuous and cocontinuous functor the unit of the lower-shriek adjunction
between the slice topoi is invertible. For sheaves of sets that is the `g_!` half of Stacks 00XT;
for abelian sheaves it is Stacks 077I. The private lemmas `overMapFull_of_mono` and
`overMapFaithful_of_mono` duplicate private helpers of
`StacksFrontier/AlgebraicGeometry/Topologies/ChangeOfSites/MonomorphismCounit.lean`.

## References

* [Stacks Project, Tag 04C8](https://stacks.math.columbia.edu/tag/04C8)
* [Stacks Project, Tag 04C7](https://stacks.math.columbia.edu/tag/04C7)
* [Stacks Project, Section 04BE](https://stacks.math.columbia.edu/tag/04BE)
* [Stacks Project, Tag 077I](https://stacks.math.columbia.edu/tag/077I)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Slice

universe v₂ u₂ w w'

/-- Slicing along a monomorphism is full: a morphism between the images is already a morphism
of the original slice objects. -/
private theorem overMapFull_of_mono {C : Type u₂} [Category.{v₂} C] {X Y : C}
    (f : X ⟶ Y) [Mono f] : (Over.map f).Full where
  map_surjective {A B} g :=
    ⟨Over.homMk g.left ((cancel_mono f).1 (by simpa [Category.assoc] using Over.w g)),
      by ext; rfl⟩

/-- Slicing along a monomorphism is faithful. -/
private theorem overMapFaithful_of_mono {C : Type u₂} [Category.{v₂} C] {X Y : C}
    (f : X ⟶ Y) [Mono f] : (Over.map f).Faithful where
  map_injective {A B} g h e :=
    Over.OverMorphism.ext (by simpa using congrArg Over.Hom.left e)

/-- For a monomorphism `f`, the lower shriek `g_!` along `Over.map f` is full and faithful. -/
private theorem sheafPullback_full_and_faithful_of_mono {C : Type u₂} [Category.{v₂} C]
    {X Y : C} (f : X ⟶ Y) [Mono f] {A : Type w} [Category.{w'} A]
    (J : GrothendieckTopology (Over X)) (K : GrothendieckTopology (Over Y))
    [(Over.map f).IsCocontinuous J K] [(Over.map f).IsContinuous J K]
    [∀ G : (Over X)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension G]
    [((Over.map f).sheafPushforwardContinuous A J K).IsRightAdjoint] :
    ((Over.map f).sheafPullback A J K).Full ∧ ((Over.map f).sheafPullback A J K).Faithful :=
  have : (Over.map f).Full := overMapFull_of_mono f
  have : (Over.map f).Faithful := overMapFaithful_of_mono f
  have := Functor.isIso_sheafAdjunctionContinuous_unit (Over.map f) A J K
  have := ((Over.map f).sheafAdjunctionContinuous A J K).fullyFaithfulLOfIsIsoUnit
  ⟨this.full, this.faithful⟩

/-- The unit of the abelian lower-shriek adjunction along `Over.map f` is invertible for a
monomorphism `f`. -/
private theorem abelian_unit_isIso_of_mono {C : Type u₂} [Category.{v₂} C] {X Y : C}
    (f : X ⟶ Y) [Mono f] (J : GrothendieckTopology (Over X)) (K : GrothendieckTopology (Over Y))
    [(Over.map f).IsCocontinuous J K] [(Over.map f).IsContinuous J K]
    (F : Sheaf J AbCat.{v₂, u₂}) :
    IsIso (((Over.map f).sheafAdjunctionContinuous AbCat.{v₂, u₂} J K).unit.app F) :=
  have : (Over.map f).Full := overMapFull_of_mono f
  have : (Over.map f).Faithful := overMapFaithful_of_mono f
  stacks077I_unit_isIso (Over.map f) J K F

end Slice

/-! ### Sheaves of sets -/

/-- **Stacks 04C8, the Zariski case for sheaves of sets.** The lower-shriek/inverse-image unit
`F ⟶ f_big⁻¹ f_big! F` is invertible for a monomorphism on the big Zariski site. -/
@[stacks 04C8 "sheaves of sets, Zariski case: the canonical map `F → f_big⁻¹ f_big! F` is an
  isomorphism, for the set-level `f_big!`"]
public theorem bigZariskiLowerShriek_unit_isIso
    (B : BigZariskiSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigZariskiOver.topology B X.1 X.2) (Type (u + 1))) :
    IsIso ((bigZariskiLowerShriekAdjunction B X Y f).unit.app F) :=
  have ⟨_, _⟩ := sheafPullback_full_and_faithful_of_mono f (A := Type (u + 1))
    (BigZariskiOver.topology B X.1 X.2) (BigZariskiOver.topology B Y.1 Y.2)
  inferInstance

/-- **Stacks 04C8, the étale case for sheaves of sets.** The lower-shriek/inverse-image unit
`F ⟶ f_big⁻¹ f_big! F` is invertible for a monomorphism on the big étale site. -/
@[stacks 04C8 "sheaves of sets, étale case: the canonical map `F → f_big⁻¹ f_big! F` is an
  isomorphism, for the set-level `f_big!`"]
public theorem bigEtaleLowerShriek_unit_isIso
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigEtaleOver.topology B X.1 X.2) (Type (u + 1))) :
    IsIso ((bigEtaleLowerShriekAdjunction B X Y f).unit.app F) :=
  have ⟨_, _⟩ := sheafPullback_full_and_faithful_of_mono f (A := Type (u + 1))
    (BigEtaleOver.topology B X.1 X.2) (BigEtaleOver.topology B Y.1 Y.2)
  inferInstance

/-- **Stacks 04C8, the smooth case for sheaves of sets.** The lower-shriek/inverse-image unit
`F ⟶ f_big⁻¹ f_big! F` is invertible for a monomorphism on the big smooth site. -/
@[stacks 04C8 "sheaves of sets, smooth case: the canonical map `F → f_big⁻¹ f_big! F` is an
  isomorphism, for the set-level `f_big!`"]
public theorem bigSmoothLowerShriek_unit_isIso
    (B : BigSmoothSite.{u}) {X Y : B.category} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigSmoothOver.topology B X.1 X.2) (Type (u + 1))) :
    IsIso ((Adjunction.ofIsRightAdjoint
      (bigSmoothMorphismOfTopoi B f).inverseImage).unit.app F) := by
  have hi : (bigSmoothMorphismOfTopoi B f).inverseImage ≅
      (Over.map f).sheafPushforwardContinuous (Type (u + 1))
        (BigSmoothOver.topology B X.1 X.2) (BigSmoothOver.topology B Y.1 Y.2) := by
    simpa [bigSmoothMorphismOfTopoi] using
      ((Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type (u + 1))
        (BigSmoothOver.topology B X.1 X.2) (BigSmoothOver.topology B Y.1 Y.2))
  have ⟨_, _⟩ := sheafPullback_full_and_faithful_of_mono f (A := Type (u + 1))
    (BigSmoothOver.topology B X.1 X.2) (BigSmoothOver.topology B Y.1 Y.2)
  have e := Adjunction.leftAdjointUniq
    (((Over.map f).sheafAdjunctionContinuous (Type (u + 1))
      (BigSmoothOver.topology B X.1 X.2)
      (BigSmoothOver.topology B Y.1 Y.2)).ofNatIsoRight hi.symm)
    (Adjunction.ofIsRightAdjoint (bigSmoothMorphismOfTopoi B f).inverseImage)
  have := Functor.Full.of_iso e
  have := Functor.Faithful.of_iso e
  infer_instance

/-- **Stacks 04C8, the syntomic case for sheaves of sets.** The lower-shriek/inverse-image unit
`F ⟶ f_big⁻¹ f_big! F` is invertible for a monomorphism on the big syntomic site. -/
@[stacks 04C8 "sheaves of sets, syntomic case: the canonical map `F → f_big⁻¹ f_big! F` is an
  isomorphism, for the set-level `f_big!`"]
public theorem bigSyntomicLowerShriek_unit_isIso
    (B : BigSyntomicSite.{u}) {X Y : B.category} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigSyntomicOver.topology B X.1 X.2) (Type (u + 1))) :
    IsIso ((bigSyntomicLowerShriekAdjunction B f).unit.app F) :=
  have ⟨_, _⟩ := sheafPullback_full_and_faithful_of_mono f (A := Type (u + 1))
    (BigSyntomicOver.topology B X.1 X.2) (BigSyntomicOver.topology B Y.1 Y.2)
  inferInstance

/-- **Stacks 04C8, the fppf case for sheaves of sets.** The lower-shriek/inverse-image unit
`F ⟶ f_big⁻¹ f_big! F` is invertible for a monomorphism on the big fppf site. -/
@[stacks 04C8 "sheaves of sets, fppf case: the canonical map `F → f_big⁻¹ f_big! F` is an
  isomorphism, for the set-level `f_big!`"]
public theorem bigFppfLowerShriek_unit_isIso
    (B : BigFppfSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (B.topology.over X) (Type (u + 1))) :
    IsIso ((bigFppfLowerShriekAdjunction B X Y f).unit.app F) :=
  have ⟨_, _⟩ := sheafPullback_full_and_faithful_of_mono f (A := Type (u + 1))
    (B.topology.over X) (B.topology.over Y)
  inferInstance

/-! ### Sheaves of abelian groups

Here `f_big!` is the lower shriek of Modules on Sites, Section 04BE: the left adjoint of
`f_big⁻¹` on abelian sheaves, which is in general different from the set-level `f_big!`. -/

/-- **Stacks 04C8, the Zariski case for sheaves of abelian groups.** The unit
`F ⟶ f_big⁻¹ f_big! F` of the abelian lower-shriek adjunction of Modules on Sites 04BE is
invertible for a monomorphism on the big Zariski site. -/
@[stacks 04C8 "sheaves of abelian groups, Zariski case: the canonical map `F → f_big⁻¹ f_big! F`
  is an isomorphism, where `f_big!` is the abelian lower shriek of Modules on Sites 04BE, i.e.
  the left adjoint of `f_big⁻¹` on abelian sheaves, not the set-level `f_big!`"]
public theorem bigZariskiAbelianLowerShriek_unit_isIso
    (B : BigZariskiSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigZariskiOver.topology B X.1 X.2) AbCat.{u, u + 1}) :
    IsIso (((Over.map f).sheafAdjunctionContinuous AbCat.{u, u + 1}
      (BigZariskiOver.topology B X.1 X.2)
      (BigZariskiOver.topology B Y.1 Y.2)).unit.app F) :=
  abelian_unit_isIso_of_mono f _ _ F

/-- **Stacks 04C8, the étale case for sheaves of abelian groups.** The unit
`F ⟶ f_big⁻¹ f_big! F` of the abelian lower-shriek adjunction of Modules on Sites 04BE is
invertible for a monomorphism on the big étale site. -/
@[stacks 04C8 "sheaves of abelian groups, étale case: the canonical map `F → f_big⁻¹ f_big! F`
  is an isomorphism, where `f_big!` is the abelian lower shriek of Modules on Sites 04BE, i.e.
  the left adjoint of `f_big⁻¹` on abelian sheaves, not the set-level `f_big!`"]
public theorem bigEtaleAbelianLowerShriek_unit_isIso
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigEtaleOver.topology B X.1 X.2) AbCat.{u, u + 1}) :
    IsIso (((Over.map f).sheafAdjunctionContinuous AbCat.{u, u + 1}
      (BigEtaleOver.topology B X.1 X.2)
      (BigEtaleOver.topology B Y.1 Y.2)).unit.app F) :=
  abelian_unit_isIso_of_mono f _ _ F

/-- **Stacks 04C8, the smooth case for sheaves of abelian groups.** The unit
`F ⟶ f_big⁻¹ f_big! F` of the abelian lower-shriek adjunction of Modules on Sites 04BE is
invertible for a monomorphism on the big smooth site. -/
@[stacks 04C8 "sheaves of abelian groups, smooth case: the canonical map `F → f_big⁻¹ f_big! F`
  is an isomorphism, where `f_big!` is the abelian lower shriek of Modules on Sites 04BE, i.e.
  the left adjoint of `f_big⁻¹` on abelian sheaves, not the set-level `f_big!`"]
public theorem bigSmoothAbelianLowerShriek_unit_isIso
    (B : BigSmoothSite.{u}) {X Y : B.category} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigSmoothOver.topology B X.1 X.2) AbCat.{u, u + 1}) :
    IsIso (((Over.map f).sheafAdjunctionContinuous AbCat.{u, u + 1}
      (BigSmoothOver.topology B X.1 X.2)
      (BigSmoothOver.topology B Y.1 Y.2)).unit.app F) :=
  abelian_unit_isIso_of_mono f _ _ F

/-- **Stacks 04C8, the syntomic case for sheaves of abelian groups.** The unit
`F ⟶ f_big⁻¹ f_big! F` of the abelian lower-shriek adjunction of Modules on Sites 04BE is
invertible for a monomorphism on the big syntomic site. -/
@[stacks 04C8 "sheaves of abelian groups, syntomic case: the canonical map
  `F → f_big⁻¹ f_big! F` is an isomorphism, where `f_big!` is the abelian lower shriek of
  Modules on Sites 04BE, i.e. the left adjoint of `f_big⁻¹` on abelian sheaves, not the
  set-level `f_big!`"]
public theorem bigSyntomicAbelianLowerShriek_unit_isIso
    (B : BigSyntomicSite.{u}) {X Y : B.category} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (BigSyntomicOver.topology B X.1 X.2) AbCat.{u, u + 1}) :
    IsIso (((Over.map f).sheafAdjunctionContinuous AbCat.{u, u + 1}
      (BigSyntomicOver.topology B X.1 X.2)
      (BigSyntomicOver.topology B Y.1 Y.2)).unit.app F) :=
  abelian_unit_isIso_of_mono f _ _ F

/-- **Stacks 04C8, the fppf case for sheaves of abelian groups.** The unit
`F ⟶ f_big⁻¹ f_big! F` of the abelian lower-shriek adjunction of Modules on Sites 04BE is
invertible for a monomorphism on the big fppf site. -/
@[stacks 04C8 "sheaves of abelian groups, fppf case: the canonical map `F → f_big⁻¹ f_big! F`
  is an isomorphism, where `f_big!` is the abelian lower shriek of Modules on Sites 04BE, i.e.
  the left adjoint of `f_big⁻¹` on abelian sheaves, not the set-level `f_big!`"]
public theorem bigFppfAbelianLowerShriek_unit_isIso
    (B : BigFppfSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y) [Mono f]
    (F : Sheaf (B.topology.over X) AbCat.{u, u + 1}) :
    IsIso (((Over.map f).sheafAdjunctionContinuous AbCat.{u, u + 1}
      (B.topology.over X) (B.topology.over Y)).unit.app F) :=
  abelian_unit_isIso_of_mono f _ _ F

end AlgebraicGeometry
