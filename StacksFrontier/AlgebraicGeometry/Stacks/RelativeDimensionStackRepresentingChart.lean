module

public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackRepresentable

/-!
# The relative dimension of a morphism of algebraic stacks with representable source

Let `𝒯` be an algebraic stack over `S` represented by an algebraic space `Z` through an
equivalence-over `eZ`, and let `F : 𝒯 ⟶ 𝒳` be a 1-morphism of algebraic stacks, locally of finite
type. The relative dimension of Stacks 0DRL of `F` is the relative dimension of Stacks 0DRG of the
composite `Z ⟶ 𝒯 ⟶ 𝒳`, where `Z ⟶ 𝒯` is étale, hence smooth of relative dimension `0` (Stacks
04SW, 04XX, 03XU, 04NV).

The relative dimension used here is `AlgebraicGeometry.Stack.relativeStackDimension`, which
asks no local Noetherianity of the source or the target: the fibre is locally Noetherian because
it is locally of finite type over the spectrum of a field.

## Main results

* `AlgebraicGeometry.Stack.relativeStackDimension_eq_fieldFibreStackDimensionAt_of_algebraicSpace`
  is **Stacks 0DRM** for a 1-morphism `f : T ⟶ 𝒳` from the algebraic stack of an algebraic
  space: the infimum of Stacks 0DRL is attained at every admissible pair of choices, so the value
  depends on neither.
* `Stack.relativeStackDimension_eq_dimensionSubNat_relativeDimensionAt_of_representing`
  computes the relative dimension of Stacks 0DRL as that of Stacks 0DRG for a source only
  *representable by* an algebraic space, rather than literally the algebraic stack of one. Its
  existential form, which asks only for
  `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace`, is
  `AlgebraicGeometry.Stack.exists_relativeStackDimension_eq_dimensionSubNat_relativeDimensionAt`.

## References

* [Stacks Project, Tag 03XU](https://stacks.math.columbia.edu/tag/03XU)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XX](https://stacks.math.columbia.edu/tag/04XX)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRM](https://stacks.math.columbia.edu/tag/0DRM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `f : T ⟶ 𝒳` be a 1-morphism, locally of finite type, from the algebraic stack of an
algebraic space to an algebraic stack, and let `t ∈ |T|`. Then the relative dimension of Stacks
0DRL at `t` is the value of the formula of Stacks 0DRL at *every* admissible pair of choices — a
field-valued point `p` of `𝒳` representing the image of `t` and a point `q` of
`T ×_𝒳 Spec κ(p)` above `t`. So that value depends on neither choice. -/
theorem relativeStackDimension_eq_fieldFibreStackDimensionAt_of_algebraicSpace
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : points B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property)
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒳.val.property f.hom.hom t)
    (hq : pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property
      (fibredCategory B S hS T).property
      (fieldFibreStackSquare B S hS f p).snd.hom.hom q = t) :
    relativeStackDimension.{u, w} B S hS f hf t =
      fieldFibreStackDimensionAt.{u, w} B S hS f hf p q := by
  classical
  obtain ⟨t₀, rfl⟩ := (spacePointMap_id_bijective B S hS T).surjective t
  refine le_antisymm (relativeStackDimension_le.{u, w} B S hS f hf _ p hp q hq) ?_
  refine le_sInf ?_
  rintro z ⟨p', q', hp', hq', rfl⟩
  exact le_of_eq
    ((fieldFibreStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt.{u, w} B S hS T hT 𝒳 f
        hf t₀ p q hp hq).trans
      (fieldFibreStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt.{u, w} B S hS T hT 𝒳 f
        hf t₀ p' q' hp' hq').symm)

/-! ### Reading the relative dimension on the chart of a representing equivalence -/

section RepresentingChart

variable (𝒯 : AlgebraicStacks.{u, w} B S hS)
  (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
  (eZ : StacksRepresentableCFG.EquivalenceOver 𝒯.val.val.p
    (presheafOfCategories (Z ⋙ typeToCat)).p)

/-- Let `F : 𝒯 ⟶ 𝒳` be a 1-morphism, locally of finite type, of algebraic stacks, and let `𝒯` be
represented by an algebraic space `Z` through the equivalence-over `eZ`. Then at the point
`t ∈ |𝒯|` named by `z ∈ |Z|`, the relative dimension of Stacks 0DRL of `F` is the relative
dimension of Stacks 0DRG of the composite `Z ⟶ 𝒯 ⟶ 𝒳`, read in `EInt` through the embedding of
Stacks 0AFN for a chart of relative dimension `0`. -/
theorem relativeStackDimension_eq_dimensionSubNat_relativeDimensionAt_of_representing
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (F : 𝒯 ⟶ 𝒳)
    (hF : AlgebraicStacks.IsLocallyOfFiniteType B S hS F)
    (hcF : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ ≫ F))
    (z : Space.points B S hS Z) (t : points B S hS 𝒯.val.val 𝒯.val.property)
    (ht : spacePointMap B S hS Z 𝒯.val
      (representingEquivalence B S hS Z 𝒯.val eZ).functor z = t) :
    relativeStackDimension.{u, w} B S hS F hF t =
      dimensionSubNat (relativeDimensionAt.{u, w} B S hS Z hZ 𝒳
        (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ ≫ F) hcF z) 0 :=
  relativeStackDimension_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS F hF t hZ
    (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ)
    (isSmooth_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ)
    (isLocallyOfFiniteType_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ) hcF z
    ((pointsMap_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ z).trans ht) 0
    (relativeDimensionAt_representingStackChart_eq_zero.{u, w} B S hS 𝒯 Z hZ eZ _ z)

end RepresentingChart

/-! ### The bridge in existential form -/

section RepresentableSource

variable (𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- For a locally-of-finite-type 1-morphism `F : 𝒯 ⟶ 𝒳` of algebraic stacks with `𝒯`
representable by an algebraic space, and for every `t ∈ |𝒯|`, there are an algebraic space `Z`, a
1-morphism `c : Z ⟶ 𝒯` of algebraic stacks and a point `z ∈ |Z|` above `t` for which the relative
dimension of Stacks 0DRL of `F` at `t` is the relative dimension of Stacks 0DRG of `c ≫ F` at
`z`. -/
theorem exists_relativeStackDimension_eq_dimensionSubNat_relativeDimensionAt
    (F : 𝒯 ⟶ 𝒳) (hF : AlgebraicStacks.IsLocallyOfFiniteType B S hS F)
    (h𝒯rep : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
      (c : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒯)
      (hcF : AlgebraicStacks.IsLocallyOfFiniteType B S hS (c ≫ F))
      (z : Space.points B S hS Z),
      pointsMap B S hS (fibredCategory B S hS Z).val (fibredCategory B S hS Z).property
            𝒯.val.property c.hom.hom (stackPointOfSpacePoint B S hS Z z) = t ∧
        relativeStackDimension.{u, w} B S hS F hF t =
          dimensionSubNat (relativeDimensionAt.{u, w} B S hS Z hZ 𝒳 (c ≫ F) hcF z) 0 := by
  classical
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := id h𝒯rep
  obtain ⟨z, hz⟩ := (bijective_spacePointMap_representing B S hS Z 𝒯.val eZ).surjective t
  refine ⟨Z, hZ, representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ,
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS _ F
      (isLocallyOfFiniteType_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ) hF, z,
    (pointsMap_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ z).trans hz, ?_⟩
  exact relativeStackDimension_eq_dimensionSubNat_relativeDimensionAt_of_representing.{u, w}
    B S hS 𝒯 Z hZ eZ 𝒳 F hF _ z t hz

end RepresentableSource

end AlgebraicGeometry.Stack

end
