module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionLocalConstancy
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionLocalConstancyStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# The sublevel sets of the relative dimension of a 1-morphism of algebraic stacks are open

For a locally-of-finite-type 1-morphism `f : 𝒯 ⟶ 𝒳` of locally Noetherian algebraic stacks, the
function `t ↦ dim_t(𝒯_{f(t)})` of Stacks 0DRL is upper semi-continuous on `|𝒯|`, and it is locally
constant when `f` is smooth (Stacks 0DRQ). The locally Noetherian hypothesis is the one under which
the relative dimension of Stacks 0DRL is defined.

## Main results

* `AlgebraicGeometry.Stack.isOpen_setOf_relativeDimensionAt_le_of_stackTarget`: for a 1-morphism
  from an algebraic space to a locally Noetherian algebraic stack, the sublevel sets of the
  relative dimension of Stacks 0DRG are open.
* `AlgebraicGeometry.Stack.isOpen_setOf_relativeStackDimensionAt_le`: every sublevel set of
  `t ↦ dim_t(𝒯_{f(t)})` is open.
* `AlgebraicGeometry.Stack.upperSemicontinuous_relativeStackDimensionAt`: the function
  `t ↦ dim_t(𝒯_{f(t)})` is upper semi-continuous.
* `AlgebraicGeometry.Stack.isLocallyConstant_relativeStackDimensionAt_of_isSmooth`: it is locally
  constant when `f` is smooth.

## References

* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NT](https://stacks.math.columbia.edu/tag/04NT)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRM](https://stacks.math.columbia.edu/tag/0DRM)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology pointTopology

/-! ### An arithmetic step -/

/-- `δ ↦ δ - 0` is injective on the finite values of `WithBot ℕ∞`. -/
private theorem natCast_eq_of_dimensionSubNat_zero_eq {m n : ℕ}
    (h : dimensionSubNat ((m : ℕ∞) : WithBot ℕ∞) 0 =
      dimensionSubNat ((n : ℕ∞) : WithBot ℕ∞) 0) :
    ((m : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := by
  have hL : dimensionSubNat ((m : ℕ∞) : WithBot ℕ∞) 0 =
    (((m : ℤ) - ((0 : ℕ) : ℤ) : ℤ) : EInt) := rfl
  have hR : dimensionSubNat ((n : ℕ∞) : WithBot ℕ∞) 0 =
    (((n : ℤ) - ((0 : ℕ) : ℤ) : ℤ) : EInt) := rfl
  rw [hL, hR] at h
  have h1 : ((m : ℤ) - ((0 : ℕ) : ℤ)) ≤ ((n : ℤ) - ((0 : ℕ) : ℤ)) :=
    WithBotTop.coe_le_coe.mp (le_of_eq h)
  have h2 : ((n : ℤ) - ((0 : ℕ) : ℤ)) ≤ ((m : ℤ) - ((0 : ℕ) : ℤ)) :=
    WithBotTop.coe_le_coe.mp (le_of_eq h.symm)
  have hmn' : m = n := by omega
  rw [hmn']

/-! ### A 1-morphism of the stacks of two algebraic spaces, as a morphism of algebraic spaces -/

section SpaceMap

variable {Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hZ : IsAlgebraicSpace B S hS Z) (hT : IsAlgebraicSpace B S hS T)

/-- The representing equivalence of the algebraic stack of an algebraic space by that algebraic
space itself: the identity. -/
private noncomputable def reflEquivOfAlgebraicSpace
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y) :
    StacksRepresentableCFG.EquivalenceOver
      (algebraicSpaceStack.{u, w} B S hS Y hY).val.val.p
      (presheafOfCategories (Y ⋙ typeToCat)).p :=
  StacksRepresentableCFG.EquivalenceOver.refl _

/-- The morphism of algebraic spaces induced (Stacks 04SW) by a 1-morphism between the algebraic
stacks they define, both being represented by themselves. -/
private noncomputable def spaceMapOfStackMap
    (k : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ algebraicSpaceStack.{u, w} B S hS T hT) :
    Z ⟶ T :=
  representingMap B S hS (fibredCategory B S hS Z)
    (algebraicSpaceStack.{u, w} B S hS T hT).val Z T
    (reflEquivOfAlgebraicSpace.{u, w} B S hS Z hZ)
    (reflEquivOfAlgebraicSpace.{u, w} B S hS T hT) k.hom

/-- A smooth 1-morphism induces a smooth morphism of the representing algebraic spaces. -/
private theorem isSmooth_spaceMapOfStackMap
    (k : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ algebraicSpaceStack.{u, w} B S hS T hT)
    (hk : AlgebraicStacks.IsSmooth B S hS k) :
    Space.IsSmooth B S hS (spaceMapOfStackMap.{u, w} B S hS hZ hT k) :=
  isSmooth_representingMap_of_isSmooth.{u, w} B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) Z T hZ hT
    (reflEquivOfAlgebraicSpace.{u, w} B S hS Z hZ)
    (reflEquivOfAlgebraicSpace.{u, w} B S hS T hT) k hk

/-- A locally-of-finite-type 1-morphism induces a locally-of-finite-type morphism of the
representing algebraic spaces. -/
private theorem isLocallyOfFiniteType_spaceMapOfStackMap
    (k : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ algebraicSpaceStack.{u, w} B S hS T hT)
    (hk : AlgebraicStacks.IsLocallyOfFiniteType B S hS k) :
    Space.IsLocallyOfFiniteType B S hS (spaceMapOfStackMap.{u, w} B S hS hZ hT k) :=
  (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (isAlgebraicStack_fibredCategory.{u, w} B S hS Z hZ)
    (algebraicSpaceStack.{u, w} B S hS T hT).property Z T hZ hT
    (reflEquivOfAlgebraicSpace.{u, w} B S hS Z hZ)
    (reflEquivOfAlgebraicSpace.{u, w} B S hS T hT) k.hom).mp
    (hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS _
      (isAlgebraicStack_fibredCategory.{u, w} B S hS Z hZ)
      (algebraicSpaceStack.{u, w} B S hS T hT).property k.hom hk)

/-- The induced morphism of algebraic spaces acts on points the way the 1-morphism does. -/
private theorem stackPointOfSpacePoint_spaceMapOfStackMap
    (k : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ algebraicSpaceStack.{u, w} B S hS T hT)
    (z : Space.points B S hS Z) :
    stackPointOfSpacePoint B S hS T
        (Space.pointsMap B S hS Z (spaceMapOfStackMap.{u, w} B S hS hZ hT k) z) =
      pointsMap B S hS (fibredCategory B S hS Z).val (fibredCategory B S hS Z).property
        (algebraicSpaceStack.{u, w} B S hS T hT).val.property k.hom.hom
        (stackPointOfSpacePoint B S hS Z z) :=
  spacePointMap_representing_naturality B S hS Z T (fibredCategory B S hS Z)
    (algebraicSpaceStack.{u, w} B S hS T hT).val
    (reflEquivOfAlgebraicSpace.{u, w} B S hS Z hZ)
    (reflEquivOfAlgebraicSpace.{u, w} B S hS T hT) k.hom z

/-- The relative dimension (Stacks 0DRG) of a 1-morphism of the stacks of two algebraic spaces is
the relative dimension (Stacks 04NM) of the induced morphism of algebraic spaces. -/
private theorem relativeDimensionAt_eq_iff_spaceMapOfStackMap
    (k : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ algebraicSpaceStack.{u, w} B S hS T hT)
    (hk : AlgebraicStacks.IsLocallyOfFiniteType B S hS k)
    (z : Space.points B S hS Z) (d : ℕ∞) :
    relativeDimensionAt.{u, w} B S hS Z hZ (algebraicSpaceStack.{u, w} B S hS T hT) k hk z =
        (d : WithBot ℕ∞) ↔
      Space.HasRelativeDimensionAt d B S hS (spaceMapOfStackMap.{u, w} B S hS hZ hT k) z :=
  relativeDimensionAt_eq_iff_hasRelativeDimensionAt_representingMap.{u, w} B S hS Z hZ
    (algebraicSpaceStack.{u, w} B S hS T hT) k hk T hT
    (reflEquivOfAlgebraicSpace.{u, w} B S hS T hT) z d

end SpaceMap

/-! ### The stack-target case -/

/-- Let `f : T ⟶ 𝒳` be a locally-of-finite-type 1-morphism from an algebraic space to a locally
Noetherian algebraic stack, let `t₀ ∈ |T|`, let `bch : U ⟶ 𝒳` be a smooth 1-morphism from an
algebraic space whose image contains the image of `t₀`, and let `W` be a 2-fibre product of `bch`
and `f`. There are algebraic spaces `Z` and `U'`, a smooth morphism `pr : Z ⟶ T` of algebraic
spaces whose image on points contains `t₀`, and a locally-of-finite-type morphism `g : Z ⟶ U'` of
algebraic spaces, such that the relative dimension (Stacks 04NM) of `g` at `z` is the relative
dimension (Stacks 0DRG) of `f` at `pr(z)`; and `g` is smooth when `f` is. -/
private theorem exists_chart_aux
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (bch : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (hbsm : AlgebraicStacks.IsSmooth B S hS bch)
    (W : Bicategory.TwoCommSq bch f) (hW : Bicategory.IsTwoFibreProduct W)
    (hWc : Bicategory.IsTwoFibreProduct (Bicategory.TwoCommSq.underlying (F := Subtype.val) W))
    (t₀ : Space.points B S hS T) (u₀ : Space.points B S hS U)
    (hu₀ : pointsMap B S hS (fibredCategory B S hS U).val
        (fibredCategory B S hS U).property 𝒳.val.property bch.hom.hom
        (stackPointOfSpacePoint B S hS U u₀) =
      pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t₀)) :
    ∃ (Z U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hZ : IsAlgebraicSpace B S hS Z)
      (_hU' : IsAlgebraicSpace B S hS U') (pr : Z ⟶ T) (g : Z ⟶ U'),
      Space.IsSmooth B S hS pr ∧
        Space.IsLocallyOfFiniteType B S hS g ∧
        (AlgebraicStacks.IsSmooth B S hS f → Space.IsSmooth B S hS g) ∧
        t₀ ∈ Set.range (Space.pointsMap B S hS Z pr) ∧
        ∀ (z : Space.points B S hS Z) (d : ℕ∞),
          Space.HasRelativeDimensionAt d B S hS g z ↔
            relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf
                (Space.pointsMap B S hS Z pr z) = (d : WithBot ℕ∞) := by
  classical
  have hblft := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS bch hbsm
  have hWfst : AlgebraicStacks.IsLocallyOfFiniteType B S hS W.fst :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS f bch W hW hf
  have hWsnd : AlgebraicStacks.IsSmooth B S hS W.snd :=
    AlgebraicStacks.isSmooth_baseChange B S hS bch f W.swap
      (Bicategory.isTwoFibreProduct_swap hW) hbsm
  have hTN : IsLocallyNoetherianStack.{u, w} B S hS (algebraicSpaceStack.{u, w} B S hS T hT) :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS f hf h𝒳
  have hUN : IsLocallyNoetherianStack.{u, w} B S hS (algebraicSpaceStack.{u, w} B S hS U hU) :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS bch hblft h𝒳
  have hWN : IsLocallyNoetherianStack.{u, w} B S hS W.pt :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS W.fst hWfst hUN
  have hTrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT
  have hWrep : IsRepresentableByAlgebraicSpace B S hS W.pt.val :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS T) 𝒳.val (fibredCategory B S hS U) f.hom bch.hom
      (Bicategory.TwoCommSq.underlying (F := Subtype.val) W) hWc
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property hTrep f.hom)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := id hWrep
  let c := representingStackChart.{u, w} B S hS W.pt Z hZ eZ
  have hcsm := isSmooth_representingStackChart.{u, w} B S hS W.pt Z hZ eZ
  have hclft := isLocallyOfFiniteType_representingStackChart.{u, w} B S hS W.pt Z hZ eZ
  have hcfst : AlgebraicStacks.IsLocallyOfFiniteType B S hS (c ≫ W.fst) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS c W.fst hclft hWfst
  have hcsnd : AlgebraicStacks.IsSmooth B S hS (c ≫ W.snd) :=
    AlgebraicStacks.isSmooth_comp B S hS c W.snd hcsm hWsnd
  let g : Z ⟶ U := spaceMapOfStackMap.{u, w} B S hS hZ hU (c ≫ W.fst)
  let pr : Z ⟶ T := spaceMapOfStackMap.{u, w} B S hS hZ hT (c ≫ W.snd)
  have hprsm : Space.IsSmooth B S hS pr :=
    isSmooth_spaceMapOfStackMap.{u, w} B S hS hZ hT (c ≫ W.snd) hcsnd
  have hprpt : ∀ z : Space.points B S hS Z,
      stackPointOfSpacePoint B S hS T (Space.pointsMap B S hS Z pr z) =
        pointsMap B S hS (fibredCategory B S hS Z).val
          (fibredCategory B S hS Z).property
          (algebraicSpaceStack.{u, w} B S hS T hT).val.property (c ≫ W.snd).hom.hom
          (stackPointOfSpacePoint B S hS Z z) :=
    stackPointOfSpacePoint_spaceMapOfStackMap.{u, w} B S hS hZ hT (c ≫ W.snd)
  have hsnd : ∀ z : Space.points B S hS Z,
      pointsMap B S hS W.pt.val.val W.pt.val.property
          (algebraicSpaceStack.{u, w} B S hS T hT).val.property W.snd.hom.hom
          (spacePointMap B S hS Z W.pt.val
            (representingEquivalence B S hS Z W.pt.val eZ).functor z) =
        stackPointOfSpacePoint B S hS T (Space.pointsMap B S hS Z pr z) := by
    intro z
    rw [hprpt z, ← pointsMap_representingStackChart.{u, w} B S hS W.pt Z hZ eZ z]
    exact pointsMap_comp B S hS (fibredCategory B S hS Z).val
      (fibredCategory B S hS Z).property W.pt.val.property
      (algebraicSpaceStack.{u, w} B S hS T hT).val.property c.hom.hom W.snd.hom.hom
      (stackPointOfSpacePoint B S hS Z z)
  have hkey : ∀ z : Space.points B S hS Z,
      relativeDimensionAt.{u, w} B S hS Z hZ (algebraicSpaceStack.{u, w} B S hS U hU)
          (c ≫ W.fst) hcfst z =
        relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf (Space.pointsMap B S hS Z pr z) := by
    intro z
    have hA := relativeStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt_of_representing.{u,
      w} B S hS W.pt Z hZ eZ (algebraicSpaceStack.{u, w} B S hS U hU) W.fst hWfst hWN hUN hcfst z
      _ rfl
    have hbc := relativeStackDimensionAt_fst_eq_relativeStackDimensionAt.{u, w} B S hS bch f
      W hW hf hWfst hWN hTN hUN h𝒳
      (spacePointMap B S hS Z W.pt.val
        (representingEquivalence B S hS Z W.pt.val eZ).functor z)
    obtain ⟨p, q, hp, hq⟩ := exists_admissible_fieldFibreStackDimensionAt.{u, w} B S hS f
      (stackPointOfSpacePoint B S hS T (Space.pointsMap B S hS Z pr z))
    have hsrc : relativeStackDimensionAt.{u, w} B S hS f hf hTN h𝒳
        (stackPointOfSpacePoint B S hS T (Space.pointsMap B S hS Z pr z)) =
        dimensionSubNat (relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf
          (Space.pointsMap B S hS Z pr z)) 0 :=
      (relativeStackDimensionAt_eq_fieldFibreStackDimensionAt_of_algebraicSpace.{u, w} B S hS
          T hT 𝒳 f hf hTN h𝒳 _ p q hp hq).trans
        (fieldFibreStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt.{u, w} B S hS T hT
          𝒳 f hf (Space.pointsMap B S hS Z pr z) p q hp hq)
    rw [hA, hsnd z, hsrc] at hbc
    obtain ⟨m, hm⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS Z hZ
      (algebraicSpaceStack.{u, w} B S hS U hU) (c ≫ W.fst) hcfst z
    obtain ⟨n, hn⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS T hT 𝒳 f hf
      (Space.pointsMap B S hS Z pr z)
    rw [hm, hn] at hbc ⊢
    exact natCast_eq_of_dimensionSubNat_zero_eq hbc
  have ht₀ : t₀ ∈ Set.range (Space.pointsMap B S hS Z pr) := by
    obtain ⟨ζ, -, hζ2⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS W hW
      (stackPointOfSpacePoint B S hS U u₀) (stackPointOfSpacePoint B S hS T t₀) hu₀
    obtain ⟨z, hz⟩ := (bijective_spacePointMap_representing B S hS Z W.pt.val eZ).surjective ζ
    refine ⟨z, ?_⟩
    have := hsnd z
    rw [hz, hζ2] at this
    exact ((bijective_spacePointMap_representing B S hS T (fibredCategory B S hS T)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).injective this).symm
  refine ⟨Z, U, hZ, hU, pr, g, hprsm, ?_, ?_, ht₀, ?_⟩
  · exact isLocallyOfFiniteType_spaceMapOfStackMap.{u, w} B S hS hZ hU (c ≫ W.fst) hcfst
  · intro hfsm
    exact isSmooth_spaceMapOfStackMap.{u, w} B S hS hZ hU (c ≫ W.fst)
      (AlgebraicStacks.isSmooth_comp B S hS c W.fst hcsm
        (AlgebraicStacks.isSmooth_baseChange B S hS f bch W hW hfsm))
  · intro z d
    rw [← hkey z]
    exact (relativeDimensionAt_eq_iff_spaceMapOfStackMap.{u, w} B S hS hZ hU
      (c ≫ W.fst) hcfst z d).symm

/-- Let `f : T ⟶ 𝒳` be a locally-of-finite-type 1-morphism from an algebraic space to a locally
Noetherian algebraic stack and let `t₀ ∈ |T|`. There are algebraic spaces `Z` and `U`, a smooth
morphism `pr : Z ⟶ T` of algebraic spaces whose image on points contains `t₀`, and a
locally-of-finite-type morphism `g : Z ⟶ U` of algebraic spaces, such that the relative dimension
(Stacks 04NM) of `g` at `z` is the relative dimension (Stacks 0DRG) of `f` at `pr(z)`; and `g` is
smooth when `f` is. -/
private theorem exists_chart_hasRelativeDimensionAt_iff_relativeDimensionAt
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t₀ : Space.points B S hS T) :
    ∃ (Z U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hZ : IsAlgebraicSpace B S hS Z)
      (_hU : IsAlgebraicSpace B S hS U) (pr : Z ⟶ T) (g : Z ⟶ U),
      Space.IsSmooth B S hS pr ∧
        Space.IsLocallyOfFiniteType B S hS g ∧
        (AlgebraicStacks.IsSmooth B S hS f → Space.IsSmooth B S hS g) ∧
        t₀ ∈ Set.range (Space.pointsMap B S hS Z pr) ∧
        ∀ (z : Space.points B S hS Z) (d : ℕ∞),
          Space.HasRelativeDimensionAt d B S hS g z ↔
            relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf
                (Space.pointsMap B S hS Z pr z) = (d : WithBot ℕ∞) := by
  obtain ⟨U, hU, bch, hbsm, u₀, hu₀⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒳
      (pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t₀))
  exact exists_chart_aux B S hS hT 𝒳 h𝒳 f hf hU bch hbsm
    (twoFibreProductSquareAlgebraicStacks B S hS bch f)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS bch f)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      bch.hom f.hom)
    t₀ u₀ hu₀

/-- For a locally-of-finite-type 1-morphism `f : T ⟶ 𝒳` from an algebraic space to a locally
Noetherian algebraic stack, the locus of points of `|T|` at which the relative dimension
(Stacks 0DRG) of `f` is at most `n` is open. -/
theorem isOpen_setOf_relativeDimensionAt_le_of_stackTarget
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) (n : ℕ) :
    IsOpen {t : Space.points B S hS T |
      relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t ≤ (n : WithBot ℕ∞)} := by
  classical
  rw [isOpen_iff_forall_mem_open]
  rintro t₀ ht₀
  obtain ⟨Z, U, hZ, hU, pr, g, hprsm, hglft, -, ⟨z₀, hz₀⟩, hiff⟩ :=
    exists_chart_hasRelativeDimensionAt_iff_relativeDimensionAt B S hS hT 𝒳 h𝒳 f hf t₀
  refine ⟨Space.pointsMap B S hS Z pr ''
    {z : Space.points B S hS Z | ∃ d : ℕ∞, d ≤ (n : ℕ∞) ∧
      Space.HasRelativeDimensionAt d B S hS g z}, ?_, ?_, ?_⟩
  · rintro _ ⟨z, ⟨d, hdn, hd⟩, rfl⟩
    have hval := (hiff z d).mp hd
    change relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf _ ≤ (n : WithBot ℕ∞)
    rw [hval]
    exact_mod_cast WithBot.coe_le_coe.mpr hdn
  · exact Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS hZ hT pr
      (Space.isFlat_of_isSmooth B S hS pr hprsm)
      (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hprsm) _
      (Space.isOpen_setOf_hasRelativeDimensionAt_le B S hS hZ hU g hglft n)
  · refine ⟨z₀, ?_, hz₀⟩
    obtain ⟨d, hd⟩ := Space.exists_hasRelativeDimensionAt_natCast B S hS hZ hU g hglft z₀
    refine ⟨(d : ℕ∞), ?_, hd⟩
    have hval := (hiff z₀ (d : ℕ∞)).mp hd
    rw [hz₀] at hval
    have : ((d : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
      rw [← hval]; exact_mod_cast ht₀
    exact_mod_cast this

/-! ### Stacks 0DRQ -/

/-- Subtracting a fixed finite relative dimension is monotone on the finite values. -/
private theorem dimensionSubNat_natCast_le_natCast {e m : ℕ} (d : ℕ) (hem : e ≤ m) :
    dimensionSubNat ((e : ℕ∞) : WithBot ℕ∞) d ≤ dimensionSubNat ((m : ℕ∞) : WithBot ℕ∞) d := by
  have hL : dimensionSubNat ((e : ℕ∞) : WithBot ℕ∞) d = (((e : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
  have hR : dimensionSubNat ((m : ℕ∞) : WithBot ℕ∞) d = (((m : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
  rw [hL, hR]
  exact WithBotTop.coe_le_coe.mpr (by omega)

section Main

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
  (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
  (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
  (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)

/-- Let `f : 𝒯 ⟶ 𝒳` be a locally-of-finite-type 1-morphism of locally Noetherian algebraic stacks
over `S`. Then every sublevel set of the function `t ↦ dim_t(𝒯_{f(t)})` of Stacks 0DRL is open in
`|𝒯|`. -/
theorem isOpen_setOf_relativeStackDimensionAt_le (c : EInt) :
    IsOpen {t : points B S hS 𝒯.val.val 𝒯.val.property |
      relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t ≤ c} := by
  classical
  rw [isOpen_iff_forall_mem_open]
  intro t₀ ht₀
  obtain ⟨V, hV, h, hsm, v₀, hv₀⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒯 t₀
  have hh := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS h hsm
  have hhf := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS h f hh hf
  have hdlc := isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack B S hS hV 𝒯 h hsm hh
  obtain ⟨d₀, hd₀⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS V hV 𝒯 h hh v₀
  obtain ⟨m, hm⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v₀
  have hval : ∀ (v : Space.points B S hS V) (e : ℕ),
      relativeDimensionAt.{u, w} B S hS V hV 𝒯 h hh v = ((d₀ : ℕ) : WithBot ℕ∞) →
      relativeDimensionAt.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v = ((e : ℕ) : WithBot ℕ∞) →
      relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳
          (pointsMap B S hS (fibredCategory B S hS V).val
            (fibredCategory B S hS V).property 𝒯.val.property h.hom.hom
            (stackPointOfSpacePoint B S hS V v)) =
        dimensionSubNat ((e : ℕ) : WithBot ℕ∞) d₀ := by
    intro v e hvd hve
    rw [relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf h𝒯 h𝒳 _
      hV h hsm hh hhf v rfl d₀ hvd, hve]
  have hopen : ∀ O : Set (Space.points B S hS V), IsOpen O →
      IsOpen ((fun v => pointsMap B S hS (fibredCategory B S hS V).val
        (fibredCategory B S hS V).property 𝒯.val.property h.hom.hom
        (stackPointOfSpacePoint B S hS V v)) '' O) := by
    intro O hO
    have h1 := isOpenMap_spacePointMap_representing B S hS V (fibredCategory B S hS V)
      (reflEquivOfAlgebraicSpace.{u, w} B S hS V hV) O hO
    have h2 := AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS h hsm _ h1
    rwa [Set.image_image] at h2
  refine ⟨(fun v => pointsMap B S hS (fibredCategory B S hS V).val
      (fibredCategory B S hS V).property 𝒯.val.property h.hom.hom
      (stackPointOfSpacePoint B S hS V v)) ''
    ({v : Space.points B S hS V | relativeDimensionAt.{u, w} B S hS V hV 𝒯 h hh v =
        relativeDimensionAt.{u, w} B S hS V hV 𝒯 h hh v₀} ∩
      {v : Space.points B S hS V |
        relativeDimensionAt.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v ≤ ((m : ℕ) : WithBot ℕ∞)}),
    ?_, ?_, ⟨v₀, ⟨rfl, le_of_eq hm⟩, hv₀⟩⟩
  · rintro _ ⟨v, ⟨hvD, hvA⟩, rfl⟩
    obtain ⟨e, he⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v
    change relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 _ ≤ c
    rw [hval v e (hvD.trans hd₀) he]
    have hvA' : relativeDimensionAt.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v ≤
        ((m : ℕ) : WithBot ℕ∞) := hvA
    have hem : e ≤ m := by
      rw [he] at hvA'
      exact_mod_cast hvA'
    have h1 := dimensionSubNat_natCast_le_natCast (e := e) (m := m) d₀ hem
    have h2 : dimensionSubNat ((m : ℕ) : WithBot ℕ∞) d₀ ≤ c := by
      rw [← hval v₀ m hd₀ hm, hv₀]
      exact ht₀
    exact le_trans h1 h2
  · exact hopen _ ((hdlc.isOpen_fiber _).inter
      (isOpen_setOf_relativeDimensionAt_le_of_stackTarget B S hS hV 𝒳 h𝒳 (h ≫ f) hhf m))


/-- For a locally-of-finite-type 1-morphism `f : 𝒯 ⟶ 𝒳` of locally Noetherian algebraic stacks,
the function `t ↦ dim_t(𝒯_{f(t)})` of Stacks 0DRL is upper semi-continuous on `|𝒯|`. -/
@[stacks 0DRQ "part (1)"]
theorem upperSemicontinuous_relativeStackDimensionAt :
    UpperSemicontinuous (relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳) := by
  intro t y hy
  have hmem : t ∈ {t' : points B S hS 𝒯.val.val 𝒯.val.property |
      relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t' ≤
        relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t} := by
    change relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t ≤
      relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t
    exact le_refl _
  filter_upwards [(isOpen_setOf_relativeStackDimensionAt_le B S hS f hf h𝒯 h𝒳
    (relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t)).mem_nhds hmem] with t' ht'
  exact lt_of_le_of_lt ht' hy

/-- For a smooth 1-morphism `f : 𝒯 ⟶ 𝒳` of locally Noetherian algebraic stacks, the function
`t ↦ dim_t(𝒯_{f(t)})` of Stacks 0DRL is locally constant on `|𝒯|`. -/
@[stacks 0DRQ "part (2)", ega "IV 17.10.2" "special case"]
theorem isLocallyConstant_relativeStackDimensionAt_of_isSmooth
    (hfsm : AlgebraicStacks.IsSmooth B S hS f) :
    IsLocallyConstant (relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳) := by
  classical
  rw [IsLocallyConstant.iff_exists_open]
  intro t₀
  obtain ⟨V, hV, h, hsm, v₀, hv₀⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒯 t₀
  have hh := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS h hsm
  have hhf := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS h f hh hf
  have hdlc := isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack B S hS hV
    𝒯 h hsm hh
  have halc := isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack B S hS hV
    𝒳 (h ≫ f) (AlgebraicStacks.isSmooth_comp B S hS h f hsm hfsm) hhf
  obtain ⟨d₀, hd₀⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS V hV 𝒯 h hh v₀
  obtain ⟨m, hm⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v₀
  have hval : ∀ (v : Space.points B S hS V) (e : ℕ),
      relativeDimensionAt.{u, w} B S hS V hV 𝒯 h hh v = ((d₀ : ℕ) : WithBot ℕ∞) →
      relativeDimensionAt.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v = ((e : ℕ) : WithBot ℕ∞) →
      relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳
          (pointsMap B S hS (fibredCategory B S hS V).val
            (fibredCategory B S hS V).property 𝒯.val.property h.hom.hom
            (stackPointOfSpacePoint B S hS V v)) =
        dimensionSubNat ((e : ℕ) : WithBot ℕ∞) d₀ := by
    intro v e hvd hve
    rw [relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf h𝒯 h𝒳 _
      hV h hsm hh hhf v rfl d₀ hvd, hve]
  have hopen : ∀ O : Set (Space.points B S hS V), IsOpen O →
      IsOpen ((fun v => pointsMap B S hS (fibredCategory B S hS V).val
        (fibredCategory B S hS V).property 𝒯.val.property h.hom.hom
        (stackPointOfSpacePoint B S hS V v)) '' O) := by
    intro O hO
    have h1 := isOpenMap_spacePointMap_representing B S hS V (fibredCategory B S hS V)
      (reflEquivOfAlgebraicSpace.{u, w} B S hS V hV) O hO
    have h2 := AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS h hsm _ h1
    rwa [Set.image_image] at h2
  refine ⟨(fun v => pointsMap B S hS (fibredCategory B S hS V).val
      (fibredCategory B S hS V).property 𝒯.val.property h.hom.hom
      (stackPointOfSpacePoint B S hS V v)) ''
    ({v : Space.points B S hS V | relativeDimensionAt.{u, w} B S hS V hV 𝒯 h hh v =
        relativeDimensionAt.{u, w} B S hS V hV 𝒯 h hh v₀} ∩
      {v : Space.points B S hS V | relativeDimensionAt.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v =
        relativeDimensionAt.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v₀}),
    hopen _ ((hdlc.isOpen_fiber _).inter (halc.isOpen_fiber _)),
    ⟨v₀, ⟨rfl, rfl⟩, hv₀⟩, ?_⟩
  rintro _ ⟨v, ⟨hvD, hvA⟩, rfl⟩
  rw [hval v m (hvD.trans hd₀) (hvA.trans hm), ← hv₀, hval v₀ m hd₀ hm]

end Main

end AlgebraicGeometry.Stack

end
