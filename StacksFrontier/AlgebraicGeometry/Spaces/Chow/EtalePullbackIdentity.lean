module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingGenericPointField
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.Topology.Sober.Generization

/-!
# The étale pullback of the cycle of an integral closed subspace (Stacks 0EPY)

In the situation of Stacks 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be an étale
morphism over the base and let `Z ⊆ Y` be an integral closed subspace. **Stacks 0EPY** is the
identity

`f^*[Z] = ∑ [Z']`,

the sum running over the irreducible components `Z'` of `f^{-1}(Z)`, each with coefficient one.

The left-hand side is the flat pullback `AlgebraicGeometry.Space.flatPullbackMap` of Stacks 0EP8
at relative dimension `0`, which an étale morphism has by
`AlgebraicGeometry.Space.hasRelativeDimension_zero_of_isEtale`, applied to the cycle
`AlgebraicGeometry.Space.integralCycle` of `Z`; by part (1) of Stacks 0EP8 its coefficients are
those of the cycle `[f^{-1}(Z)]_{δ(Z)}` of the scheme-theoretic inverse image. The right-hand side
is `AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponentsCycle`, and that it is a cycle
of δ-dimension `δ(Z)` is
`AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponentsCycle_mem_cyclesOfDimension`.

Each component enters with multiplicity one, because `f^{-1}(Z)` is étale over the integral,
hence reduced, algebraic space `Z`, and so is reduced.

## Main results

* `AlgebraicGeometry.Space.isEtale_fromPreimage`: the inverse image of a subspace along an étale
  morphism is étale over that subspace.
* `AlgebraicGeometry.Space.hasRelativeDimension_zero_of_isEtale`: an étale morphism has relative
  dimension zero.
* `IntegralClosedSubspace.exists_topComponentSubspaces_closedSubspaceComponentImage_iff`: the
  index set of the sum of Stacks 0EE9 for `f^{-1}(Z)` is the set of irreducible components
  of `f^{-1}(Z)`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.hasEtaleLocalProperty_isReduced_preimage`: the
  inverse image of an integral closed subspace along an étale morphism is reduced.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.closedSubspaceMultiplicity_preimage_eq_one`: a
  component of the inverse image enters with multiplicity one.
* `IntegralClosedSubspace.flatPullbackMap_integralCycle_eq_preimageComponentsCycle`:
  **Stacks 0EPY**, the identity `f^*[Z] = ∑ [Z']`.

## Implementation notes

**Why the multiplicity is one.** The multiplicity of a component `Z'` in `f^{-1}(Z)` is
`AlgebraicGeometry.Space.closedSubspaceMultiplicity`, the length of `𝒪_{f^{-1}(Z)}` at a
geometric point above the generic point of `Z'` read inside `f^{-1}(Z)`. That length is one as
soon as the étale local ring there is a field
(`AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_one_of_isField`), and it is a
field because `f^{-1}(Z)` is reduced and the point underneath is a generic point of an
irreducible component of `|f^{-1}(Z)|`
(`AlgebraicGeometry.Space.isField_etaleLocalRing_of_mem_genericPoints`). Reducedness of
`f^{-1}(Z)` is Stacks 0GB3 for the source of a smooth morphism, applied to
`AlgebraicGeometry.Space.isEtale_fromPreimage`.

**The index set.** `AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponent` and
`AlgebraicGeometry.Space.closedSetComponent` are both the reduced closed subspace on an
irreducible component of a closed set of points. The two readings of the ambient closed point
set, `Z.preimagePointSet f` and the set of points of the closed subspace `Z.subspace.preimage f`,
are only propositionally equal
(`AlgebraicGeometry.Space.IntegralClosedSubspace.preimagePointSet_eq`), so a component of one is
transported to a component of the other by `AlgebraicGeometry.Space.closedSetComponent_congr`.

**The degree.** `AlgebraicGeometry.Space.flatPullbackMap` is graded by a pair `m`, `n` with
`m + r = n`, so at `r = 0` the pullback of an `m`-cycle is written at a degree `n` with
`m + 0 = n`; the right-hand side
`AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponentsCycle` is a coefficient family
and mentions no degree, and the identity is the equality of the coefficient families of the two
cycles.

## References

* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0GB3](https://stacks.math.columbia.edu/tag/0GB3)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Étale morphisms: the inverse image of a subspace, and relative dimension zero -/

section Etale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The square exhibiting the inverse image of a subspace `Z ⊆ Y` along `f : X ⟶ Y` as the fibre
product of `Z` with `X` over `Y`, lifted from presheaves of types to the category of algebraic
spaces over `S`. -/
theorem isPullback_preimage_algebraicSpaces (f : X ⟶ Y) (Z : Subfunctor Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z.toFunctor)
    (hP : IsAlgebraicSpace B S hS (Z.preimage f).toFunctor) :
    IsPullback
      (ObjectProperty.homMk (Z.fromPreimage f) :
        (⟨(Z.preimage f).toFunctor, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZ⟩)
      (ObjectProperty.homMk (Z.preimage f).ι :
        (⟨(Z.preimage f).toFunctor, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk Z.ι :
        (⟨Z.toFunctor, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS T))
    (Subfunctor.isPullback_preimage f Z)

/-- If `f : X ⟶ Y` is an étale morphism of algebraic spaces over `S` and `Z ⊆ Y` is a subspace
which is an algebraic space with algebraic inverse image, then the morphism from the inverse
image of `Z` to `Z` is étale. -/
theorem isEtale_fromPreimage (f : X ⟶ Y) (Z : Subfunctor Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z.toFunctor)
    (hP : IsAlgebraicSpace B S hS (Z.preimage f).toFunctor)
    (hf : IsEtale B S hS f) :
    IsEtale B S hS (Z.fromPreimage f) :=
  isEtale_of_isPullback B S hS _ _ _ _
    (isPullback_preimage_algebraicSpaces B S hS f Z hX hY hZ hP).flip hf

/-- An étale morphism of algebraic spaces over `S` with algebraic target has relative dimension
`0`. -/
theorem hasRelativeDimension_zero_of_isEtale (f : X ⟶ Y) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsEtale B S hS f) :
    HasRelativeDimension 0 B S hS f :=
  (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS f
    (isLocallyOfFiniteType_of_isEtale B S hS hY hf)).1
    (isLocallyQuasiFinite_of_isEtale B S hS hY hf)

end Etale

/-! ### Transporting a component along an equality of closed sets -/

section Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Transport of a component of a closed set of points along a propositional equality of the
ambient set: a component of `T` is also a component of any set equal to it, with the same
attached integral closed subspace. -/
theorem closedSetComponent_congr (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    {T T' : Set (points B S hS X)} (h : T = T') (hT : IsClosed T) (hT' : IsClosed T')
    (C : irreducibleComponents T) :
    ∃ C' : irreducibleComponents T',
      closedSetComponent B S hS hX hXdec T hT C = closedSetComponent B S hS hX hXdec T' hT' C' := by
  subst h
  exact ⟨C, rfl⟩

end Transport

/-! ### The index set of the sum -/

section Index

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The subspace attached to a component of the inverse image by
`AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponent` is the generic
`AlgebraicGeometry.Space.closedSetComponent` on that same inverse image. -/
theorem IntegralClosedSubspace.preimageComponent_eq_closedSetComponent (f : X ⟶ Y)
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f)) :
    Z.preimageComponent D.site D.base D.base_mem f hX hXdec hY C =
      closedSetComponent D.site D.base D.base_mem hX hXdec
        (Z.preimagePointSet D.site D.base D.base_mem f)
        (Z.isClosed_preimagePointSet D.site D.base D.base_mem f hY) C :=
  rfl

/-- **The index correspondence for Stacks 0EPY.** Let `f : X ⟶ Y` be an étale morphism of good
algebraic spaces over the base and let `Z ⊆ Y` be an integral closed subspace. An integral
closed subspace `T ⊆ X` is the image of an integral closed subspace of `f^{-1}(Z)` of the
δ-dimension of `Z` exactly when `T` is an irreducible component of the inverse image of `Z`. -/
theorem IntegralClosedSubspace.exists_topComponentSubspaces_closedSubspaceComponentImage_iff
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hf : IsEtale D.site D.base D.base_mem f) (hfc : f ≫ sY = sX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (∃ V : topComponentSubspaces D sX hX (Z.subspace.preimage f)
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f Z)
        (deltaDimension D sY Z),
      closedSubspaceComponentImage D sX hX (Z.subspace.preimage f)
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f Z) V.1 = T) ↔
      ∃ C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f),
        Z.preimageComponent D.site D.base D.base_mem f hX.1 (D.isDecentSpace_of_isGood sX hX)
          hY.1 C = T := by
  have hclosed := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f Z
  have heq := Z.preimagePointSet_eq D.site D.base D.base_mem f
  have hr0 := deltaDimensionSubspace_preimage_integralClosedSubspace_le D sX hX sY hY f hfc 0
    (isFlat_of_isEtale D.site D.base D.base_mem hf)
    (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem f hY.1 hf) Z
  have hdim : deltaDimensionSubspace D sX hX (Z.subspace.preimage f) hclosed ≤
      ((deltaDimension D sY Z : ℤ) : EInt) := by simpa using hr0
  have hdec := D.isDecentSpace_of_isGood sX hX
  have hcl := isClosed_subspacePointSet_of_isClosedSubspace D hX.1 (Z.subspace.preimage f) hclosed
  have hcl' := Z.isClosed_preimagePointSet D.site D.base D.base_mem f hY.1
  have hcomp : (∃ C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f),
      closedSetComponent D.site D.base D.base_mem hX.1 hdec _ hcl' C = T) ↔
      ∃ C : irreducibleComponents (subspacePointSet D.site D.base D.base_mem X
        (Z.subspace.preimage f)),
      closedSetComponent D.site D.base D.base_mem hX.1 hdec _ hcl C = T := by
    constructor
    · rintro ⟨C, hC⟩
      obtain ⟨C', hC'⟩ := closedSetComponent_congr D.site D.base D.base_mem hX.1 hdec heq hcl' hcl C
      exact ⟨C', hC'.symm.trans hC⟩
    · rintro ⟨C, hC⟩
      obtain ⟨C', hC'⟩ :=
        closedSetComponent_congr D.site D.base D.base_mem hX.1 hdec heq.symm hcl hcl' C
      exact ⟨C', hC'.symm.trans hC⟩
  constructor
  · rintro ⟨⟨W, hWk⟩, hWT⟩
    obtain ⟨C', hC'⟩ := exists_irreducibleComponents_closedSubspaceComponentImage D sX hX
      (Z.subspace.preimage f) hclosed (deltaDimension D sY Z) hdim W hWk
    rw [hWT] at hC'
    exact hcomp.2 ⟨C', eq_closedSetComponent D.site D.base D.base_mem hX.1 hdec _ hcl C' T hC'⟩
  · rintro ⟨C, hCT⟩
    obtain ⟨C', hC'⟩ := hcomp.1 ⟨C, hCT⟩
    obtain ⟨W, hW⟩ := exists_closedSubspaceComponentImage_eq_closedSetComponent D sX hX
      (Z.subspace.preimage f) hclosed C'
    have hWT := hW.trans hC'
    refine ⟨⟨W, ?_⟩, hWT⟩
    rw [hWT, ← hCT]
    exact Z.deltaDimension_preimageComponent D sX hX sY hY hf hfc C

end Index

/-! ### A generic point of a component of the inverse image -/

section Generic

/-- A point of a closed set which is a generalization of a generic point of an irreducible
component of that set is that generic point. -/
private theorem eq_of_specializes_of_isGenericPoint_image_val {α : Type*} [TopologicalSpace α]
    [T0Space α] {T : Set α} (hT : IsClosed T) (C : irreducibleComponents T) {x y : α}
    (hx : IsGenericPoint x (Subtype.val '' (C : Set T))) (hy : y ∈ T) (hyx : y ⤳ x) :
    y = x := by
  have hxT : x ∈ T := Subtype.coe_image_subset _ _ hx.mem
  have hspec : (⟨y, hy⟩ : T) ⤳ (⟨x, hxT⟩ : T) := (subtype_specializes_iff _ _).2 hyx
  have himg := hT.isClosedEmbedding_subtypeVal.closure_image_eq ({(⟨x, hxT⟩ : T)} : Set T)
  rw [Set.image_singleton] at himg
  have hC : (C : Set T) = closure ({(⟨x, hxT⟩ : T)} : Set T) :=
    Subtype.val_injective.image_injective (hx.symm.trans himg)
  have hsub : (C : Set T) ⊆ closure ({(⟨y, hy⟩ : T)} : Set T) := by
    rw [hC]
    exact specializes_iff_closure_subset.mp hspec
  have heq : closure ({(⟨y, hy⟩ : T)} : Set T) = closure ({(⟨x, hxT⟩ : T)} : Set T) := by
    rw [← hC]
    exact Set.Subset.antisymm (C.2.2 isIrreducible_singleton.closure hsub) hsub
  exact congrArg Subtype.val (inseparable_iff_closure_eq.2 heq).eq

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The generic point of an integral closed subspace of `f^{-1}(Z)` whose image in `X` is an
irreducible component of the inverse image is a generic point of an irreducible component of the
point space of `f^{-1}(Z)`. -/
theorem IntegralClosedSubspace.mem_genericPoints_ambientGenericPoint_of_preimageComponent
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f))
    (W : IntegralClosedSubspace D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor)
    (hW : closedSubspaceComponentImage D sX hX (Z.subspace.preimage f)
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f Z) W =
      Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C) :
    W.ambientGenericPoint D.site D.base D.base_mem ∈
      genericPoints (points D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor) := by
  have hclosed := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f Z
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hPdec : IsDecentSpace D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor :=
    isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem hXdec hclosed
  have _hT0X : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hXdec
  have _hT0P : T0Space (points D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hclosed.1 hPdec
  have _hsober :
      QuasiSober (points D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor) :=
    quasiSober_points_of_isDecentSpace D.site D.base D.base_mem hclosed.1 hPdec
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
    hclosed.2
  have hamb : (Z.preimageComponent D.site D.base D.base_mem f hX.1 hXdec
        hY.1 C).ambientGenericPoint D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor
        (Z.subspace.preimage f).ι (W.ambientGenericPoint D.site D.base D.base_mem) := by
    rw [← hW]
    exact IntegralClosedSubspace.ambientGenericPoint_pushforward D.site D.base D.base_mem hX.1
      hclosed.1 hXdec hclosed.2 W
  have hgenx : IsGenericPoint
      ((Z.preimageComponent D.site D.base D.base_mem f hX.1 hXdec
        hY.1 C).ambientGenericPoint D.site D.base D.base_mem)
      (Subtype.val '' (C : Set (Z.preimagePointSet D.site D.base D.base_mem f))) := by
    have h := (Z.preimageComponent D.site D.base D.base_mem f hX.1 hXdec
      hY.1 C).isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1
    rwa [Z.subspacePointSet_preimageComponent D.site D.base D.base_mem f hX.1 hXdec hY.1 C] at h
  refine mem_genericPoints_of_forall_specializes_eq fun q hq => ?_
  have hyT : pointsMap D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor
      (Z.subspace.preimage f).ι q ∈ Z.preimagePointSet D.site D.base D.base_mem f := by
    rw [Z.preimagePointSet_eq D.site D.base D.base_mem f]
    exact ⟨q, rfl⟩
  have hqspec : pointsMap D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor
      (Z.subspace.preimage f).ι q ⤳
      (Z.preimageComponent D.site D.base D.base_mem f hX.1 hXdec
        hY.1 C).ambientGenericPoint D.site D.base D.base_mem := by
    rw [hamb]
    exact hq.map (continuous_pointsMap D.site D.base D.base_mem (Z.subspace.preimage f).ι)
  have hval := eq_of_specializes_of_isGenericPoint_image_val
    (Z.isClosed_preimagePointSet D.site D.base D.base_mem f hY.1) C hgenx hyT hqspec
  exact hemb.injective (hval.trans hamb)

end Generic

/-! ### Reducedness of the inverse image, and multiplicity one -/

section Multiplicity

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Reducedness of the inverse image.** The scheme-theoretic inverse image of an integral
closed subspace `Z ⊆ Y` along an étale morphism `f : X ⟶ Y` of algebraic spaces over the base is
reduced. -/
theorem IntegralClosedSubspace.hasEtaleLocalProperty_isReduced_preimage (f : X ⟶ Y)
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hf : IsEtale D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    HasEtaleLocalProperty D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor
      (fun T : Scheme.{u} => IsReduced T) :=
  isReduced_source_of_isSmooth D.site D.base D.base_mem
    (Z.isClosedSubspace_preimage D.site D.base D.base_mem f hX hY).1 Z.isClosedSubspace.1
    (Z.subspace.fromPreimage f)
    (isSmooth_of_isEtale D.site D.base D.base_mem Z.isClosedSubspace.1
      (isEtale_fromPreimage D.site D.base D.base_mem f Z.subspace hX hY Z.isClosedSubspace.1
        (Z.isClosedSubspace_preimage D.site D.base D.base_mem f hX hY).1 hf))
    Z.isIntegralSpace.1

/-- **Multiplicity one for the components of an étale inverse image.** Let `f : X ⟶ Y` be an
étale morphism of good algebraic spaces over the base of Situation 0EDT, let `Z ⊆ Y` be an
integral closed subspace and let `W` be an integral closed subspace of `f^{-1}(Z)` whose image in
`X` is an irreducible component of the inverse image. Then the multiplicity of `W` in `f^{-1}(Z)`
is one. -/
theorem IntegralClosedSubspace.closedSubspaceMultiplicity_preimage_eq_one (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hf : IsEtale D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f))
    (W : IntegralClosedSubspace D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor)
    (hW : closedSubspaceComponentImage D sX hX (Z.subspace.preimage f)
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f Z) W =
      Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C) :
    closedSubspaceMultiplicity D (Z.subspace.preimage f)
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f Z) W = 1 := by
  have hclosed := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f Z
  have hgen := Z.mem_genericPoints_ambientGenericPoint_of_preimageComponent D sX hX sY hY f
    C W hW
  set z := canonicalGeometricPoint D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor
    (W.ambientGenericPoint D.site D.base D.base_mem) with hz
  have hzgen : z.image ∈
      genericPoints (points D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor) := by
    rw [hz, canonicalGeometricPoint_image]
    exact hgen
  have hfield := isField_etaleLocalRing_of_mem_genericPoints D.site D.base D.base_mem hclosed.1
    (Z.hasEtaleLocalProperty_isReduced_preimage D f hX.1 hY.1 hf)
    (isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem
      (D.isDecentSpace_of_isGood sX hX) hclosed) z hzgen
  have hlen := geometricLength_structureSheafModule_eq_one_of_isField D.site D.base D.base_mem
    ⟨(Z.subspace.preimage f).toFunctor, hclosed.1⟩ z hfield
  have hmult : closedSubspaceMultiplicity D (Z.subspace.preimage f) hclosed W =
      (((1 : ℕ∞).toNat : ℤ)) := congrArg (fun d : ℕ∞ => ((d.toNat : ℤ))) hlen
  rw [hmult]
  simp

end Multiplicity

/-! ### The identity -/

section Identity

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EPY, at the level of multiplicities.** Let `f : X ⟶ Y` be an étale morphism of good
algebraic spaces over the base of Situation 0EDT and let `Z ⊆ Y` be an integral closed subspace.
The multiplicity family of `f^{-1}(Z)`, which by part (1) of Stacks 0EP8 is the coefficient family
of `f^*[Z]`, is the formal sum of the irreducible components of `f^{-1}(Z)` each with coefficient
one. -/
theorem IntegralClosedSubspace.flatPullbackMult_eq_preimageComponentsCycle (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hf : IsEtale D.site D.base D.base_mem f) (hfc : f ≫ sY = sX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    flatPullbackMult D sX hX sY hY f hfc 0
        (isFlat_of_isEtale D.site D.base D.base_mem hf)
        (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem f hY.1 hf) Z =
      Z.preimageComponentsCycle D sX hX sY hY f := by
  classical
  funext T
  have hclosed := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f Z
  have hdeg : deltaDimension D sY Z + ((0 : ℕ) : ℤ) = deltaDimension D sY Z := by simp
  have hiff := Z.exists_topComponentSubspaces_closedSubspaceComponentImage_iff D sX hX sY hY
    hf hfc T
  have hcoeff : flatPullbackMult D sX hX sY hY f hfc 0
      (isFlat_of_isEtale D.site D.base D.base_mem hf)
      (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem f hY.1 hf) Z T =
      cycleCoeffOfClosedSubspace D sX hX (Z.subspace.preimage f) hclosed
        (deltaDimension D sY Z + ((0 : ℕ) : ℤ))
        (canonicalGeometricPoint D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor)
        T := rfl
  rw [hcoeff]
  by_cases hex : T ∈ {V : IntegralClosedSubspace D.site D.base D.base_mem X |
      ∃ C, Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C = V}
  · obtain ⟨⟨W, hWk⟩, hWT⟩ := hiff.2 hex
    obtain ⟨C, hC⟩ := id hex
    rw [preimageComponentsCycle, Set.indicator_of_mem hex, Pi.one_apply, ← hWT,
      cycleCoeffOfClosedSubspace_eq_closedSubspaceMultiplicity D sX hX (Z.subspace.preimage f)
        hclosed (deltaDimension D sY Z + ((0 : ℕ) : ℤ))
        (canonicalGeometricPoint D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor) W
        (canonicalGeometricPoint_image _ _ _ _ _) (hWk.trans hdeg.symm)]
    exact Z.closedSubspaceMultiplicity_preimage_eq_one D sX hX sY hY hf C W
      (hWT.trans hC.symm)
  · rw [preimageComponentsCycle, Set.indicator_of_notMem hex]
    by_contra hne
    have hdimT : deltaDimension D sX T = deltaDimension D sY Z + ((0 : ℕ) : ℤ) := by
      by_contra h
      exact hne (by rw [cycleCoeffOfClosedSubspace, ite_eq_right h])
    obtain ⟨W, hWT⟩ : ∃ W : IntegralClosedSubspace D.site D.base D.base_mem
        (Z.subspace.preimage f).toFunctor,
        closedSubspaceComponentImage D sX hX (Z.subspace.preimage f) hclosed W = T := by
      by_contra h
      exact hne (cycleCoeffOfClosedSubspace_eq_zero D sX hX (Z.subspace.preimage f) hclosed
        (deltaDimension D sY Z + ((0 : ℕ) : ℤ))
        (canonicalGeometricPoint D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor) T
        fun W hW => h ⟨W, hW⟩)
    refine hex (hiff.1 ⟨⟨W, ?_⟩, hWT⟩)
    rw [hWT, hdimT]
    exact hdeg

/-- Let `f : X ⟶ Y` be an étale morphism of good algebraic spaces over the base
`B` of Situation 0EDT and let `Z ⊆ Y` be an integral closed subspace, of δ-dimension `m`. Then

`f^*[Z] = ∑ [Z']`,

the sum running over the irreducible components `Z'` of the inverse image `f^{-1}(Z)` (in the
sense of Remark 0EE8), each with coefficient one: the coefficient family of the cycle `f^*[Z]`
is the formal sum `AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponentsCycle` of
those components.

The left-hand side is the flat pullback `AlgebraicGeometry.Space.flatPullbackMap` of Stacks 0EP8
at relative dimension `0`, which an étale morphism has by
`AlgebraicGeometry.Space.hasRelativeDimension_zero_of_isEtale`, applied to the cycle `[Z]`; the
pullback lands in degree `n` for any `n` with `m + 0 = n`. -/
@[stacks 0EPY]
theorem IntegralClosedSubspace.flatPullbackMap_integralCycle_eq_preimageComponentsCycle
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hf : IsEtale D.site D.base D.base_mem f) (hfc : f ≫ sY = sX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) (m n : ℤ)
    (hm : deltaDimension D sY Z = m) (hmn : m + ((0 : ℕ) : ℤ) = n) :
    (flatPullbackMap D sX hX sY hY f hfc 0
          (isFlat_of_isEtale D.site D.base D.base_mem hf)
          (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem f hY.1 hf) m n hmn
        (integralCycle D sY m Z hm)).1 =
      Z.preimageComponentsCycle D sX hX sY hY f := by
  funext T
  rw [flatPullbackMap_integralCycle D sX hX sY hY f hfc 0
    (isFlat_of_isEtale D.site D.base D.base_mem hf)
    (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem f hY.1 hf) m n hmn Z hm T]
  exact congrFun (Z.flatPullbackMult_eq_preimageComponentsCycle D sX hX sY hY hf hfc) T

end Identity

end AlgebraicGeometry.Space

end
