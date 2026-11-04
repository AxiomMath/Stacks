module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.AlgebraicGeometry.NagataValuativeCriterion.Basic

/-!
# Universal closedness tested on curves essentially of finite type

Over a base `S` that is locally Noetherian, universal closedness of a quasi-compact morphism
`f : X ⟶ Y` of schemes locally of finite type over `S` can be tested on one-dimensional normal
integral test schemes: for a normal integral `C` of finite type over `S` and a closed point
`c ∈ C` with `dim 𝒪_{C,c} = 1`, a morphism to `X` defined on `C \ {c}` must extend over
`Spec 𝒪_{C,c}` compatibly with a given morphism `C ⟶ Y`. This extension condition is
`Stacks.AlgebraicGeometry.NagataValuativeCriterion.HasEssentiallyFiniteTypeValuativeExtension`,
item (3) of Tag 0GWV. The local ring `𝒪_{C,c}` is then a discrete valuation ring, so the condition
is a restricted valuative criterion, in which only valuation rings *essentially of finite type over
the base* occur.

## Main results

* `AlgebraicGeometry.valuationRing_stalk_of_ringKrullDim_eq_one`: on a normal scheme locally of
  finite type over a locally Noetherian base, the local ring at a point of Krull dimension one is
  a valuation ring.
* `AlgebraicGeometry.isClosedMap_affineSpace_map`: a universally closed morphism stays closed
  after base change to affine space, which is the implication (1) ⟹ (2) of Tag 0GWV.
* `AlgebraicGeometry.hasEssentiallyFiniteTypeValuativeExtension_of_universallyClosed`: a
  universally closed morphism satisfies the extension condition, which is (1) ⟹ (3).
* `AlgebraicGeometry.HasEssentiallyFiniteTypeValuativeExtension.affineSpace_map`: the extension
  condition is inherited by the base change to affine space.
* `AlgebraicGeometry.isClosedMap_of_isClosedMap_affineSpace_map`: conversely, closedness of one
  base change to an *empty* affine space already gives closedness of the morphism.

## References

* [Stacks Project, Tag 0GWV](https://stacks.math.columbia.edu/tag/0GWV)
* [Stacks Project, Tag 05JY](https://stacks.math.columbia.edu/tag/05JY)
* [Stacks Project, Tag 01KF](https://stacks.math.columbia.edu/tag/01KF)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
-/

@[expose] public section

open Stacks.AlgebraicGeometry.NagataValuativeCriterion (HasEssentiallyFiniteTypeValuativeExtension)
open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}}

/-! ### The local ring of a one-dimensional point of a normal test scheme -/

/-- The local ring at a point of Krull dimension one of a normal scheme locally of finite type
over a locally Noetherian base is a valuation ring. -/
theorem valuationRing_stalk_of_ringKrullDim_eq_one {C : Scheme.{u}} (p : C ⟶ S)
    [LocallyOfFiniteType p] [IsLocallyNoetherian S] [IsNormal C] (c : C)
    (hdim : ringKrullDim (C.presheaf.stalk c) = 1) :
    ValuationRing (C.presheaf.stalk c) :=
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  Stacks.AlgebraicGeometry.NagataValuativeCriterion.valuationRing_stalk_of_ringKrullDim_eq_one
    C hdim

/-! ### Item (3) of Tag 0GWV -/

/-- **Tag 0GWV, (1) ⟹ (3).** A universally closed morphism over a locally Noetherian base
satisfies the one-dimensional finite-type extension test. -/
theorem hasEssentiallyFiniteTypeValuativeExtension_of_universallyClosed (hY : Y ⟶ S) (f : X ⟶ Y)
    [IsLocallyNoetherian S] [UniversallyClosed f] :
    HasEssentiallyFiniteTypeValuativeExtension f hY := by
  have hex : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ ‹UniversallyClosed f› :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
  intro C p hp hpq hC hCi c hc hdim U q a hq ha hdom A i g hg
  have := hp
  have := hC
  have := hdom
  let sq : ValuativeCommSq f :=
    { R := C.presheaf.stalk c
      commRing := inferInstance
      domain := hdom
      valuationRing := valuationRing_stalk_of_ringKrullDim_eq_one p c hdim
      K := FractionRing (C.presheaf.stalk c)
      field := inferInstance
      algebra := inferInstance
      isFractionRing := inferInstance
      i₁ := g ≫ a
      i₂ := C.fromSpecStalk c ≫ q
      commSq := ⟨by rw [Category.assoc, ha, ← Category.assoc, hg, Category.assoc]⟩ }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hex sq).exists_lift
  exact ⟨l, hl₂, hl₁⟩

/-! ### Item (2) of Tag 0GWV -/

namespace AffineSpace

/-- `AffineSpace.map n f` is quasi-compact when `f` is. -/
instance quasiCompact_map (n : Type u) (f : X ⟶ Y) [QuasiCompact f] :
    QuasiCompact (AffineSpace.map n f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_map (n := n) f).flip ‹_›

/-- `AffineSpace.map n f` is universally closed when `f` is. -/
instance universallyClosed_map (n : Type u) (f : X ⟶ Y) [UniversallyClosed f] :
    UniversallyClosed (AffineSpace.map n f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_map (n := n) f).flip ‹_›

end AffineSpace

/-- **Tag 0GWV, (1) ⟹ (2).** A universally closed morphism remains closed after base change to
affine space of any index type. -/
theorem isClosedMap_affineSpace_map (n : Type u) (f : X ⟶ Y) [UniversallyClosed f] :
    IsClosedMap (AffineSpace.map n f) :=
  (AffineSpace.map n f).isClosedMap

/-- Closedness of the base change of `f` to an empty affine space already gives closedness of
`f`. In particular the `n = 0` instance of item (2) of Tag 0GWV implies that `f` is closed. -/
theorem isClosedMap_of_isClosedMap_affineSpace_map (n : Type u) [IsEmpty n] (f : X ⟶ Y)
    (h : IsClosedMap (AffineSpace.map n f)) : IsClosedMap f := by
  have key : f = (inv (𝔸(n; X) ↘ X)) ≫ AffineSpace.map n f ≫ (𝔸(n; Y) ↘ Y) := by
    rw [AffineSpace.map_over, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [key]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp]
  exact ((𝔸(n; Y) ↘ Y).isClosedMap.comp h).comp (inv (𝔸(n; X) ↘ X)).isClosedMap

/-- The extension condition passes from `f` to its base change `𝔸(n; X) ⟶ 𝔸(n; Y)` to affine
space. -/
theorem HasEssentiallyFiniteTypeValuativeExtension.affineSpace_map (hY : Y ⟶ S) (f : X ⟶ Y)
    (n : Type u) (H : HasEssentiallyFiniteTypeValuativeExtension f hY) :
    HasEssentiallyFiniteTypeValuativeExtension (AffineSpace.map n f) (𝔸(n; Y) ↘ Y ≫ hY) := by
  intro C p hp hpq hC hCi c hc hdim U q a hq ha hdom A i g hg
  have hsq := AffineSpace.isPullback_map (n := n) f
  obtain ⟨l', hl'₁, hl'₂⟩ :=
    H C p hp hpq hC hCi c hc hdim (q ≫ (𝔸(n; Y) ↘ Y)) (a ≫ (𝔸(n; X) ↘ X))
      (by rw [Category.assoc]; exact hq)
      (by rw [Category.assoc, ← AffineSpace.map_over, ← Category.assoc, ha, Category.assoc])
      hdom g hg
  refine ⟨hsq.lift (C.fromSpecStalk c ≫ q) l' (by rw [Category.assoc]; exact hl'₁.symm), ?_, ?_⟩
  · exact hsq.lift_fst _ _ _
  · refine hsq.hom_ext ?_ ?_
    · rw [Category.assoc, hsq.lift_fst, ← Category.assoc, ← hg, Category.assoc, ← ha,
        Category.assoc]
    · rw [Category.assoc, hsq.lift_snd, hl'₂, Category.assoc]

end AlgebraicGeometry
