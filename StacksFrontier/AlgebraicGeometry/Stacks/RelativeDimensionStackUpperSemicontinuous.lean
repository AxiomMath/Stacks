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
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackLocalConstancy
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackRepresentingChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionZeroLocusStack

/-!
# The relative dimension of a 1-morphism of algebraic stacks is upper semi-continuous

For a locally-of-finite-type 1-morphism `f : 𝒯 ⟶ 𝒳` of algebraic stacks the function
`t ↦ dim_t(𝒯_{f(t)})` of Stacks 0DRL is upper semi-continuous on `|𝒯|`, and is locally constant
when `f` is smooth. No Noetherian hypothesis is needed: the only object whose dimension
`AlgebraicGeometry.Stack.relativeStackDimension` takes is the fibre `𝒯 ×_𝒳 Spec k`, which is
locally Noetherian for every locally-of-finite-type `f`.

## Main results

* `AlgebraicGeometry.Stack.isOpen_setOf_relativeStackDimension_le`: every sublevel set of the
  relative dimension is open.
* `AlgebraicGeometry.Stack.upperSemicontinuous_relativeStackDimension`: the relative dimension is
  upper semi-continuous.
* `AlgebraicGeometry.Stack.isLocallyConstant_relativeStackDimension_of_isSmooth`: the relative
  dimension of a smooth 1-morphism is locally constant.

## Implementation notes

Upper semi-continuity is stated both as the openness of every sublevel set and as Mathlib's
`UpperSemicontinuous`; the two agree because the relative dimension of Stacks 0DRL takes only
integer values (`AlgebraicGeometry.Stack.exists_relativeStackDimension_eq_intCast`).

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

/-! ### The stack-target case -/

/-- Let `f : T ⟶ 𝒳` be a locally-of-finite-type 1-morphism from an algebraic space to an
algebraic stack and let `t₀ ∈ |T|`. There are algebraic spaces `Z` and `U`, a
smooth morphism `pr : Z ⟶ T` of algebraic spaces whose image on points contains `t₀`, and a
locally-of-finite-type morphism `g : Z ⟶ U` of algebraic spaces, such that the relative
dimension of Stacks 04NM of `g` at `z` is the relative dimension of Stacks 0DRG of `f` at
`pr(z)`; and `g` is smooth when `f` is. Here `U` is a smooth chart `bch` of `𝒳` through the image
of `t₀` and `Z` represents the 2-fibre product `W` of `bch` and `f`. -/
private theorem exists_chart_aux
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
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
  have hWfst : AlgebraicStacks.IsLocallyOfFiniteType B S hS W.fst :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS f bch W hW hf
  have hWsnd : AlgebraicStacks.IsSmooth B S hS W.snd :=
    AlgebraicStacks.isSmooth_baseChange B S hS bch f W.swap
      (Bicategory.isTwoFibreProduct_swap hW) hbsm
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
  let eZ' : StacksRepresentableCFG.EquivalenceOver
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p (presheafOfCategories (Z ⋙ typeToCat)).p :=
    StacksRepresentableCFG.EquivalenceOver.refl _
  let eU' : StacksRepresentableCFG.EquivalenceOver
      (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p (presheafOfCategories (U ⋙ typeToCat)).p :=
    StacksRepresentableCFG.EquivalenceOver.refl _
  let eT' : StacksRepresentableCFG.EquivalenceOver
      (algebraicSpaceStack.{u, w} B S hS T hT).val.val.p (presheafOfCategories (T ⋙ typeToCat)).p :=
    StacksRepresentableCFG.EquivalenceOver.refl _
  let g : Z ⟶ U := representingMap B S hS (fibredCategory B S hS Z)
    (algebraicSpaceStack.{u, w} B S hS U hU).val Z U eZ' eU' (c ≫ W.fst).hom
  let pr : Z ⟶ T := representingMap B S hS (fibredCategory B S hS Z)
    (algebraicSpaceStack.{u, w} B S hS T hT).val Z T eZ' eT' (c ≫ W.snd).hom
  have hprsm : Space.IsSmooth B S hS pr :=
    isSmooth_representingMap_of_isSmooth.{u, w} B S hS
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) Z T hZ hT eZ' eT' (c ≫ W.snd) hcsnd
  have hprpt : ∀ z : Space.points B S hS Z,
      stackPointOfSpacePoint B S hS T (Space.pointsMap B S hS Z pr z) =
        pointsMap B S hS (fibredCategory B S hS Z).val
          (fibredCategory B S hS Z).property
          (algebraicSpaceStack.{u, w} B S hS T hT).val.property (c ≫ W.snd).hom.hom
          (stackPointOfSpacePoint B S hS Z z) :=
    spacePointMap_representing_naturality B S hS Z T (fibredCategory B S hS Z)
      (algebraicSpaceStack.{u, w} B S hS T hT).val eZ' eT' (c ≫ W.snd).hom
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
    have hA := relativeStackDimension_eq_dimensionSubNat_relativeDimensionAt_of_representing.{u,
      w} B S hS W.pt Z hZ eZ (algebraicSpaceStack.{u, w} B S hS U hU) W.fst hWfst hcfst z
      _ rfl
    have hbc := relativeStackDimension_fst_eq_relativeStackDimension.{u, w} B S hS bch f
      W hW hf hWfst
      (spacePointMap B S hS Z W.pt.val
        (representingEquivalence B S hS Z W.pt.val eZ).functor z)
    obtain ⟨p, q, hp, hq⟩ := exists_admissible_fieldFibreStackDimensionAt.{u, w} B S hS f
      (stackPointOfSpacePoint B S hS T (Space.pointsMap B S hS Z pr z))
    have hsrc : relativeStackDimension.{u, w} B S hS f hf
        (stackPointOfSpacePoint B S hS T (Space.pointsMap B S hS Z pr z)) =
        dimensionSubNat (relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf
          (Space.pointsMap B S hS Z pr z)) 0 :=
      (relativeStackDimension_eq_fieldFibreStackDimensionAt_of_algebraicSpace.{u, w} B S hS
          T hT 𝒳 f hf _ p q hp hq).trans
        (fieldFibreStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt.{u, w} B S hS T hT
          𝒳 f hf (Space.pointsMap B S hS Z pr z) p q hp hq)
    rw [hA, hsnd z, hsrc] at hbc
    obtain ⟨m, hm⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS Z hZ
      (algebraicSpaceStack.{u, w} B S hS U hU) (c ≫ W.fst) hcfst z
    obtain ⟨n, hn⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS T hT 𝒳 f hf
      (Space.pointsMap B S hS Z pr z)
    rw [hm, hn] at hbc ⊢
    have h₁ : (m : ℤ) - ((0 : ℕ) : ℤ) ≤ (n : ℤ) - ((0 : ℕ) : ℤ) :=
      WithBotTop.coe_le_coe.mp hbc.le
    have h₂ : (n : ℤ) - ((0 : ℕ) : ℤ) ≤ (m : ℤ) - ((0 : ℕ) : ℤ) :=
      WithBotTop.coe_le_coe.mp hbc.ge
    rw [show m = n by omega]
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
  · exact (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (isAlgebraicStack_fibredCategory.{u, w} B S hS Z hZ)
      (algebraicSpaceStack.{u, w} B S hS U hU).property Z U hZ hU eZ' eU' (c ≫ W.fst).hom).mp
      (hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS _
        (isAlgebraicStack_fibredCategory.{u, w} B S hS Z hZ)
        (algebraicSpaceStack.{u, w} B S hS U hU).property (c ≫ W.fst).hom hcfst)
  · intro hfsm
    exact isSmooth_representingMap_of_isSmooth.{u, w} B S hS
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) Z U hZ hU eZ' eU' (c ≫ W.fst)
      (AlgebraicStacks.isSmooth_comp B S hS c W.fst hcsm
        (AlgebraicStacks.isSmooth_baseChange B S hS f bch W hW hfsm))
  · intro z d
    rw [← hkey z]
    exact (relativeDimensionAt_eq_iff_hasRelativeDimensionAt_representingMap.{u, w} B S hS Z hZ
      (algebraicSpaceStack.{u, w} B S hS U hU) (c ≫ W.fst) hcfst U hU eU' z d).symm

/-- Let `f : T ⟶ 𝒳` be a locally-of-finite-type 1-morphism from an algebraic space to an
algebraic stack and let `t₀ ∈ |T|`. There are algebraic spaces `Z` and `U`, a smooth morphism
`pr : Z ⟶ T` whose image on points contains `t₀`, and a locally-of-finite-type morphism
`g : Z ⟶ U`, smooth when `f` is, such that the relative dimension of Stacks 04NM of `g` at `z` is
the relative dimension of Stacks 0DRG of `f` at `pr(z)`. -/
private theorem exists_chart_hasRelativeDimensionAt_iff_relativeDimensionAt
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
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
  exact exists_chart_aux B S hS hT 𝒳 f hf hU bch hbsm
    (twoFibreProductSquareAlgebraicStacks B S hS bch f)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS bch f)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      bch.hom f.hom)
    t₀ u₀ hu₀

/-! ### Upper semi-continuity and local constancy -/

section Main

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
  (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)

/-- Let `f : 𝒯 ⟶ 𝒳` be a locally-of-finite-type 1-morphism of algebraic stacks over `S`. Then
every sublevel set of the function `t ↦ dim_t(𝒯_{f(t)})` of Stacks 0DRL is open in `|𝒯|`. -/
@[stacks 0DRQ "part (1), as openness of the sublevel sets"]
theorem isOpen_setOf_relativeStackDimension_le (c : EInt) :
    IsOpen {t : points B S hS 𝒯.val.val 𝒯.val.property |
      relativeStackDimension.{u, w} B S hS f hf t ≤ c} := by
  classical
  rw [isOpen_iff_forall_mem_open]
  intro t₀ ht₀
  obtain ⟨V, hV, h, hsm, v₀, hv₀⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒯 t₀
  have hh := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS h hsm
  have hhf := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS h f hh hf
  have hdlc := isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack B S hS hV
    𝒯 h hsm hh
  obtain ⟨d₀, hd₀⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS V hV 𝒯 h hh v₀
  obtain ⟨m, hm⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v₀
  have hval : ∀ (v : Space.points B S hS V) (e : ℕ),
      relativeDimensionAt.{u, w} B S hS V hV 𝒯 h hh v = ((d₀ : ℕ) : WithBot ℕ∞) →
      relativeDimensionAt.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v = ((e : ℕ) : WithBot ℕ∞) →
      relativeStackDimension.{u, w} B S hS f hf
          (pointsMap B S hS (fibredCategory B S hS V).val
            (fibredCategory B S hS V).property 𝒯.val.property h.hom.hom
            (stackPointOfSpacePoint B S hS V v)) =
        dimensionSubNat ((e : ℕ) : WithBot ℕ∞) d₀ := by
    intro v e hvd hve
    rw [relativeStackDimension_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf _
      hV h hsm hh hhf v rfl d₀ hvd, hve]
  have hopen : ∀ O : Set (Space.points B S hS V), IsOpen O →
      IsOpen ((fun v => pointsMap B S hS (fibredCategory B S hS V).val
        (fibredCategory B S hS V).property 𝒯.val.property h.hom.hom
        (stackPointOfSpacePoint B S hS V v)) '' O) := by
    intro O hO
    have h₁ := AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS h hsm _
      (isOpenMap_spacePointMap_representing B S hS V (fibredCategory B S hS V)
        (StacksRepresentableCFG.EquivalenceOver.refl _) O hO)
    rwa [Set.image_image] at h₁
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
    change relativeStackDimension.{u, w} B S hS f hf _ ≤ c
    rw [hval v e (hvD.trans hd₀) he]
    have hvA' : relativeDimensionAt.{u, w} B S hS V hV 𝒳 (h ≫ f) hhf v ≤
        ((m : ℕ) : WithBot ℕ∞) := hvA
    have hem : e ≤ m := by
      rw [he] at hvA'
      exact_mod_cast hvA'
    have h1 : dimensionSubNat ((e : ℕ∞) : WithBot ℕ∞) d₀ ≤
        dimensionSubNat ((m : ℕ∞) : WithBot ℕ∞) d₀ :=
      WithBotTop.coe_le_coe.mpr (by omega : (e : ℤ) - d₀ ≤ (m : ℤ) - d₀)
    have h2 : dimensionSubNat ((m : ℕ) : WithBot ℕ∞) d₀ ≤ c := by
      rw [← hval v₀ m hd₀ hm, hv₀]
      exact ht₀
    exact h1.trans h2
  · exact hopen _ ((hdlc.isOpen_fiber _).inter
      (isOpen_setOf_relativeDimensionAt_le_of_algebraicStackTarget B S hS 𝒳 _ hV (h ≫ f) hhf m))

/-- For a locally-of-finite-type 1-morphism `f : 𝒯 ⟶ 𝒳` of algebraic stacks, the function
`t ↦ dim_t(𝒯_{f(t)})` of Stacks 0DRL is upper semi-continuous on `|𝒯|`. -/
@[stacks 0DRQ "part (1)"]
theorem upperSemicontinuous_relativeStackDimension :
    UpperSemicontinuous (relativeStackDimension.{u, w} B S hS f hf) := by
  intro t y hy
  filter_upwards [(isOpen_setOf_relativeStackDimension_le B S hS f hf
    (relativeStackDimension.{u, w} B S hS f hf t)).mem_nhds (Set.mem_ofPred.2 le_rfl)] with t' ht'
  exact ht'.trans_lt hy

/-- For a smooth, locally-of-finite-type 1-morphism `f : 𝒯 ⟶ 𝒳` of algebraic stacks, the function
`t ↦ dim_t(𝒯_{f(t)})` of Stacks 0DRL is locally constant on `|𝒯|`. -/
@[stacks 0DRQ "part (2)", ega "IV 17.10.2" "more general"]
theorem isLocallyConstant_relativeStackDimension_of_isSmooth
    (hfsm : AlgebraicStacks.IsSmooth B S hS f) :
    IsLocallyConstant (relativeStackDimension.{u, w} B S hS f hf) := by
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
      relativeStackDimension.{u, w} B S hS f hf
          (pointsMap B S hS (fibredCategory B S hS V).val
            (fibredCategory B S hS V).property 𝒯.val.property h.hom.hom
            (stackPointOfSpacePoint B S hS V v)) =
        dimensionSubNat ((e : ℕ) : WithBot ℕ∞) d₀ := by
    intro v e hvd hve
    rw [relativeStackDimension_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf _
      hV h hsm hh hhf v rfl d₀ hvd, hve]
  have hopen : ∀ O : Set (Space.points B S hS V), IsOpen O →
      IsOpen ((fun v => pointsMap B S hS (fibredCategory B S hS V).val
        (fibredCategory B S hS V).property 𝒯.val.property h.hom.hom
        (stackPointOfSpacePoint B S hS V v)) '' O) := by
    intro O hO
    have h₁ := AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS h hsm _
      (isOpenMap_spacePointMap_representing B S hS V (fibredCategory B S hS V)
        (StacksRepresentableCFG.EquivalenceOver.refl _) O hO)
    rwa [Set.image_image] at h₁
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
