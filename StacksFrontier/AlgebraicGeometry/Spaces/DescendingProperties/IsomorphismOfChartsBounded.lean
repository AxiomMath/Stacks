module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismPropertiesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
import all StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism

/-!
# IsomorphismOfChartsBounded

The generalizations made by this development of declarations of
`StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism`. That module keeps its
statements as they are; each declaration here restating one of them carries its name with the
suffix `_of_chartsBounded` (or `OfChartsBounded` for a definition), and the declarations that
depend on those restatements follow them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Criterion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

end Criterion

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_isomorphismOfChartsBounded {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

local instance (priority := high) hasPullback_presheaf_isomorphismOfChartsBounded
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace MorphismDescentSystemOfChartsBounded

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- The base change `f_i : X_i ⟶ Y_i` of `f₀` to a stage is itself a base change of `f₀`, along
the projections of `X_i` and `Y_i` to `X₀` and `Y₀`. -/
theorem isPullback_mapAt
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) (i : I) (hi : D.initial ≤ i) :
    IsPullback (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase) (D.mapAt i hi) D.map₀
      (pullback.snd (D.baseAtToInitial i hi) D.targetToBase) := by
  have e₁ : D.mapAt i hi ≫ pullback.fst (D.baseAtToInitial i hi) D.targetToBase =
      pullback.fst (D.baseAtToInitial i hi) D.sourceToBase := D.mapAt_fst i hi
  have e₂ : D.map₀ ≫ D.targetToBase = D.sourceToBase := D.map₀_over
  have e₃ : D.mapAt i hi ≫ pullback.snd (D.baseAtToInitial i hi) D.targetToBase =
      pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.map₀ := D.mapAt_snd i hi
  refine IsPullback.of_bot ?_ e₃.symm (D.targetAt_isPullback i hi).flip
  convert (D.sourceAt_isPullback i hi).flip using 2
  exact e₁

/-- The base change of `f₀` to a later stage is a base change of its base change to an earlier
one: `X_j = Y_j ×_{Y_i} X_i` for `i ≤ j`. -/
theorem exists_isPullback_mapAt_of_le
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) {i j : I} (hi : D.initial ≤ i)
    (hij : i ≤ j) :
    ∃ (α : D.sourceAt j (hi.trans hij) ⟶ D.sourceAt i hi)
      (β : D.targetAt j (hi.trans hij) ⟶ D.targetAt i hi),
      IsPullback α (D.mapAt j (hi.trans hij)) (D.mapAt i hi) β := by
  have hj : D.initial ≤ j := hi.trans hij
  have htb : D.base.map (homOfLE hij).op ≫ D.baseAtToInitial i hi = D.baseAtToInitial j hj :=
    (D.base.map_comp (homOfLE hij).op (homOfLE hi).op).symm.trans
      (congrArg D.base.map (Subsingleton.elim _ _))
  have hcomm : (pullback.fst (D.baseAtToInitial j hj) D.targetToBase ≫
        D.base.map (homOfLE hij).op) ≫ D.baseAtToInitial i hi =
      pullback.snd (D.baseAtToInitial j hj) D.targetToBase ≫ D.targetToBase := by
    rw [Category.assoc, htb]
    exact pullback.condition
  have hβ : (pullback.lift _ _ hcomm : D.targetAt j hj ⟶ D.targetAt i hi) ≫
      pullback.snd (D.baseAtToInitial i hi) D.targetToBase =
      pullback.snd (D.baseAtToInitial j hj) D.targetToBase := pullback.lift_snd _ _ _
  have hs : IsPullback (pullback.snd (D.baseAtToInitial j hj) D.sourceToBase) (D.mapAt j hj)
      D.map₀ ((pullback.lift _ _ hcomm : D.targetAt j hj ⟶ D.targetAt i hi) ≫
        pullback.snd (D.baseAtToInitial i hi) D.targetToBase) := by
    rw [hβ]
    exact D.isPullback_mapAt j hj
  exact ⟨_, pullback.lift _ _ hcomm, IsPullback.of_right' hs (D.isPullback_mapAt i hi)⟩

/-- Étaleness of the base change of `f₀` passes from a stage to every later stage. -/
theorem isEtale_mapAt_of_le
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) {i j : I} (hi : D.initial ≤ i)
    (hij : i ≤ j)
    (h : IsEtale B S hS (D.mapAt i hi)) : IsEtale B S hS (D.mapAt j (hi.trans hij)) := by
  obtain ⟨α, β, hpb⟩ := D.exists_isPullback_mapAt_of_le hi hij
  have hfst : hpb.flip.isoPullback.hom ≫ pullback.fst β (D.mapAt i hi) =
      D.mapAt j (hi.trans hij) := hpb.flip.isoPullback_hom_fst
  rw [← hfst]
  exact isEtale_comp B S hS (isEtale_of_iso B S hS hpb.flip.isoPullback)
    (isEtale_pullback_fst B S hS (D.targetAt_isAlgebraicSpace j (hi.trans hij))
      (D.targetAt_isAlgebraicSpace i hi) (D.sourceAt_isAlgebraicSpace i hi) β
      (D.mapAt i hi) h)

/-- Universal injectivity of the base change of `f₀` passes from a stage to every later
stage. -/
theorem universallyInjective_mapAt_of_le
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) {i j : I} (hi : D.initial ≤ i)
    (hij : i ≤ j) (h : UniversallyInjective B S hS (D.mapAt i hi)) :
    UniversallyInjective B S hS (D.mapAt j (hi.trans hij)) := by
  obtain ⟨α, β, hpb⟩ := D.exists_isPullback_mapAt_of_le hi hij
  exact universallyInjective_of_isPullback B S hS (D.sourceAt_isAlgebraicSpace i hi)
    (D.targetAt_isAlgebraicSpace j (hi.trans hij)) (D.targetAt_isAlgebraicSpace i hi)
    (D.mapAt i hi) β h hpb.flip

/-- Surjectivity of the base change of `f₀` passes from a stage to every later stage. -/
theorem isSurjective_mapAt_of_le
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) {i j : I} (hi : D.initial ≤ i)
    (hij : i ≤ j) (h : IsSurjective B S hS (D.mapAt i hi)) :
    IsSurjective B S hS (D.mapAt j (hi.trans hij)) := by
  obtain ⟨α, β, hpb⟩ := D.exists_isPullback_mapAt_of_le hi hij
  exact surjective_pointsMap_of_isPullback B S hS hpb h

/-- **Stacks 0852**, and **Stacks 084S**. In the situation of Stacks 084W, if the base change
`f` of `f₀` to the limit `B` is an isomorphism and `f₀` is locally of finite presentation, then
the base change `f_i` of `f₀` to some stage `B_i` is an isomorphism.

This is Stacks 0852. Stacks 084S draws the same conclusion in the limit situation of Stacks
084R, with the source and the target in addition assumed representable over the stage;
hypothesis (a) of that tag is not needed here, since the three properties into which being an
isomorphism is decomposed all descend without it. -/
theorem exists_isIso_mapAt
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) (hf : IsIso D.mapLimit)
    (hfp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsIso (D.mapAt i hi) := by
  have _ := hf
  have hEt : IsEtale B S hS D.mapLimit := isEtale_of_iso B S hS (asIso D.mapLimit)
  have hUI : UniversallyInjective B S hS D.mapLimit := universallyInjective_of_isIso B S hS _
  have hSurj : IsSurjective B S hS D.mapLimit := by
    intro y
    refine ⟨pointsMap B S hS D.targetLimit (inv D.mapLimit) y, ?_⟩
    rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id, id_eq]
  obtain ⟨i₁, hi₁, hEt₁⟩ := D.exists_isEtale_mapAt hEt hfp
  obtain ⟨i₂, hi₂, hUI₂⟩ := D.exists_universallyInjective_mapAt hUI
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp)
  obtain ⟨i₃, hi₃, hSurj₃⟩ := D.exists_isSurjective_mapAt hSurj hfp
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) i₁ i₂
  obtain ⟨j, hjk, hj₃⟩ := directed_of (· ≤ ·) k i₃
  refine ⟨j, hi₁.trans (hk₁.trans hjk), ?_⟩
  exact isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS
    (D.sourceAt_isAlgebraicSpace j _) (D.targetAt_isAlgebraicSpace j _) _
    (D.isEtale_mapAt_of_le hi₁ (hk₁.trans hjk) hEt₁)
    (D.universallyInjective_mapAt_of_le hi₂ (hk₂.trans hjk) hUI₂)
    (D.isSurjective_mapAt_of_le hi₃ hj₃ hSurj₃)

end MorphismDescentSystemOfChartsBounded

end AlgebraicGeometry.Space

end
