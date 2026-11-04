module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackMorphism

/-!
# The relative dimension of a morphism from a stack representable by an algebraic space

For a 1-morphism `f : 𝒯 ⟶ 𝒳` of algebraic stacks, locally of finite type, the relative dimension
`dim_t(𝒯_x)` of Stacks 0DRL does not depend on the field-valued representative of `x` nor on the
point of the fibre above `t` used to compute it, when `𝒯` is the algebraic stack of an algebraic
space. When `𝒯` is only representable by an algebraic space `Z`, it is the relative dimension of
Stacks 0DRG of the composite `Z ⟶ 𝒯 ⟶ 𝒳`.

## Main definitions

* `AlgebraicGeometry.Stack.representingStackChart`: the 1-morphism `Z ⟶ 𝒯` of algebraic stacks
  carried by an equivalence representing `𝒯` by an algebraic space `Z`.

## Main results

In the namespace `AlgebraicGeometry.Stack`:

* `fieldFibreStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt`: for `f : T ⟶ 𝒳` from the
  algebraic stack of an algebraic space, every admissible pair of choices in the formula of
  Stacks 0DRL gives the relative dimension of Stacks 0DRG of `f` at `t`, read in `EInt`.
* `relativeStackDimensionAt_eq_fieldFibreStackDimensionAt_of_algebraicSpace`: for such an `f`, the
  relative dimension of Stacks 0DRL is attained at every admissible pair of choices.
* `relativeStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt_of_representing`: for a source
  represented by an algebraic space `Z`, the relative dimension of Stacks 0DRL is the relative
  dimension of Stacks 0DRG of the composite with `representingStackChart`.
* `exists_relativeStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt`: the same, for a source
  representable by an algebraic space.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRH](https://stacks.math.columbia.edu/tag/0DRH)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRM](https://stacks.math.columbia.edu/tag/0DRM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every admissible pair of choices in the formula of Stacks 0DRL gives the relative
dimension of Stacks 0DRG**, when the source of `f` is the algebraic stack of an algebraic
space `T`. The two values differ only by the embedding of `WithBot ℕ∞` in `EInt` that the
formula of Stacks 0AFN uses on a chart of relative dimension `0`. -/
theorem fieldFibreStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : Space.points B S hS T)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property)
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t))
    (hq : pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property
      (fibredCategory B S hS T).property
      (fieldFibreStackSquare B S hS f p).snd.hom.hom q = stackPointOfSpacePoint B S hS T t) :
    fieldFibreStackDimensionAt.{u, w} B S hS f hf p q =
      dimensionSubNat (relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t) 0 := by
  classical
  have hTrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT
  have hsq := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    (fieldValuedPointMorphism B S hS 𝒳.val p) f.hom
  have hZrep : IsRepresentableByAlgebraicSpace B S hS
      (fieldFibreStackSquare B S hS f p).pt.val :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS T) 𝒳.val (schemeFibredCategory B S hS p.base)
      f.hom (fieldValuedPointMorphism B S hS 𝒳.val p) _ hsq
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property hTrep
        f.hom)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS p.base)
  obtain ⟨W, hW, ⟨eW⟩⟩ := id hZrep
  obtain ⟨x, hx⟩ := (bijective_spacePointMap_representing B S hS W
    (fieldFibreStackSquare B S hS f p).pt.val eW).surjective q
  obtain ⟨q₀, hq₀⟩ := exists_point_fieldFibreSquare B S hS f.hom
    (stackPointOfSpacePoint B S hS T t) p hp
  have hL1 := dimensionAtPoint_eq_dimensionSubNat_zero_of_representing.{u, w} B S hS
    (fieldFibreStackSquare B S hS f p).pt
    (isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS f hf p) W hW eW x q hx
  have hrep : Space.dimensionAtPoint B S hS W hW x =
      representedDimensionAtPoint B S hS (fieldFibreStackSquare B S hS f p).pt.val hZrep q :=
    hx ▸ (representedDimensionAtPoint_eq B S hS
      (fieldFibreStackSquare B S hS f p).pt.val hZrep W hW eW x).symm
  have hfib : representedDimensionAtPoint B S hS
        (fieldFibreStackSquare B S hS f p).pt.val hZrep q =
      fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property hTrep p q₀ :=
    representedDimensionAtPoint_eq_fieldFibreDimensionAt_of_fst.{u, w} B S hS f
      hTrep hf p (P := (fieldFibreStackSquare B S hS f p).underlying.swap)
      (Bicategory.isTwoFibreProduct_swap hsq) hZrep q q₀ (hq.trans hq₀.symm)
  have hwd : relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t =
      fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property hTrep p q₀ :=
    relativeDimensionAt_eq_fieldFibreDimensionAt.{u, w} B S hS T hT 𝒳 f hf t p q₀ hp hq₀
  exact hL1.trans (by rw [hrep, hfib, hwd])

/-- Let `f : T ⟶ 𝒳` be a 1-morphism, locally of finite type, from the algebraic stack of an
algebraic space to a locally Noetherian algebraic stack, and let `t ∈ |T|`. Then the relative
dimension of Stacks 0DRL at `t` is the value of the formula of Stacks 0DRL at *every* admissible
pair of choices — a field-valued point `p` of `𝒳` representing the image of `t` and a point `q` of
`T ×_𝒳 Spec κ(p)` above `t`. So that value depends on neither choice. -/
@[stacks 0DRM "the case of a source representable by an algebraic space"]
theorem relativeStackDimensionAt_eq_fieldFibreStackDimensionAt_of_algebraicSpace
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS (algebraicSpaceStack.{u, w} B S hS T hT))
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
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
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t =
      fieldFibreStackDimensionAt.{u, w} B S hS f hf p q := by
  classical
  obtain ⟨t₀, rfl⟩ := (spacePointMap_id_bijective B S hS T).surjective t
  refine le_antisymm (relativeStackDimensionAt_le.{u, w} B S hS f hf h𝒯 h𝒳 _ p hp q hq)
    (le_sInf ?_)
  rintro z ⟨p', q', hp', hq', rfl⟩
  exact ((fieldFibreStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt.{u, w} B S hS T hT 𝒳
    f hf t₀ p q hp hq).trans
      (fieldFibreStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt.{u, w} B S hS T hT 𝒳 f
        hf t₀ p' q' hp' hq').symm).le

/-! ### The chart carried by a representing equivalence -/

section RepresentingChart

variable (𝒯 : AlgebraicStacks.{u, w} B S hS)
  (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
  (eZ : StacksRepresentableCFG.EquivalenceOver 𝒯.val.val.p
    (presheafOfCategories (Z ⋙ typeToCat)).p)

/-- **The chart of an algebraic stack carried by a representing equivalence.** For an algebraic
stack `𝒯` represented by an algebraic space `Z` through the equivalence-over `eZ`, this is the
1-morphism `Z ⟶ 𝒯` of algebraic stacks whose underlying based functor is the forward functor of
`eZ`. -/
noncomputable abbrev representingStackChart :
    algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒯 :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom
      (representingEquivalence B S hS Z 𝒯.val eZ).functor :
      fibredCategory B S hS Z ⟶ 𝒯.val)

/-- `AlgebraicGeometry.Stack.representingStackChart` is smooth and locally of finite type, and its
morphism of representing presheaves is étale. -/
private theorem isSmooth_and_isLocallyOfFiniteType_representingStackChart :
    AlgebraicStacks.IsSmooth B S hS (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ) ∧
      AlgebraicStacks.IsLocallyOfFiniteType B S hS
          (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ) ∧
        Space.IsEtale B S hS
          (representingMap B S hS (fibredCategory B S hS Z) 𝒯.val Z Z
            (StacksRepresentableCFG.EquivalenceOver.refl _) eZ
            (Bicategory.InducedBicategory.mkHom
              (representingEquivalence B S hS Z 𝒯.val eZ).functor)) := by
  classical
  let a : fibredCategory B S hS Z ⟶ 𝒯.val :=
    Bicategory.InducedBicategory.mkHom (representingEquivalence B S hS Z 𝒯.val eZ).functor
  let b : 𝒯.val ⟶ fibredCategory B S hS Z :=
    Bicategory.InducedBicategory.mkHom (representingEquivalence B S hS Z 𝒯.val eZ).inverse
  have θ : a ≫ b ≅ 𝟙 (fibredCategory B S hS Z) :=
    Bicategory.InducedBicategory.isoMk (representingEquivalence B S hS Z 𝒯.val eZ).unitIso
  have θ' : b ≫ a ≅ 𝟙 𝒯.val :=
    Bicategory.InducedBicategory.isoMk (representingEquivalence B S hS Z 𝒯.val eZ).counitIso
  have hetale := Space.isEtale_of_iso B S hS (representingIsoOfInverse B S hS Z Z
    (StacksRepresentableCFG.EquivalenceOver.refl _) eZ θ θ')
  have hsmr := Space.isSmooth_of_isEtale B S hS hZ hetale
  exact ⟨(hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (isAlgebraicStack_fibredCategory.{u, w} B S hS Z hZ) 𝒯.property Z Z hZ hZ
      (StacksRepresentableCFG.EquivalenceOver.refl _) eZ a).mpr hsmr,
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (isAlgebraicStack_fibredCategory.{u, w} B S hS Z hZ) 𝒯.property a).mpr
      ((hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
        (isAlgebraicStack_fibredCategory.{u, w} B S hS Z hZ) 𝒯.property Z Z hZ hZ
        (StacksRepresentableCFG.EquivalenceOver.refl _) eZ a).mpr
        (Space.isLocallyOfFiniteType_of_isSmooth B S hS hsmr)), hetale⟩

/-- The chart of a representing equivalence is a **smooth** 1-morphism of algebraic stacks. -/
theorem isSmooth_representingStackChart :
    AlgebraicStacks.IsSmooth B S hS (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ) :=
  (isSmooth_and_isLocallyOfFiniteType_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ).1

/-- The chart of a representing equivalence is **locally of finite type**. -/
theorem isLocallyOfFiniteType_representingStackChart :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ) :=
  (isSmooth_and_isLocallyOfFiniteType_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ).2.1

/-- The chart of a representing equivalence has **relative dimension `0`** of Stacks 0DRG at
every point. -/
theorem relativeDimensionAt_representingStackChart_eq_zero
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ))
    (z : Space.points B S hS Z) :
    relativeDimensionAt.{u, w} B S hS Z hZ 𝒯
        (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ) hc z =
      ((0 : ℕ) : WithBot ℕ∞) :=
  have he := (isSmooth_and_isLocallyOfFiniteType_representingStackChart.{u, w}
    B S hS 𝒯 Z hZ eZ).2.2
  (relativeDimensionAt_eq_iff_hasRelativeDimensionAt_representingMap.{u, w} B S hS Z hZ 𝒯
    (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ) hc Z hZ eZ z 0).mpr
    ((Space.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS _
      (Space.isLocallyOfFiniteType_of_isSmooth B S hS (Space.isSmooth_of_isEtale B S hS hZ he))).mp
      (Space.isLocallyQuasiFinite_of_isEtale' B S hS he) z)

/-- The point of `|𝒯|` that a point of `Z` names, read through the chart of the representing
equivalence: the two descriptions of it — as the image under the chart of the corresponding
point of the stack of `Z`, and as the image of the equivalence on points of Stacks 04XL — agree.
-/
theorem pointsMap_representingStackChart (z : Space.points B S hS Z) :
    pointsMap B S hS (fibredCategory B S hS Z).val (fibredCategory B S hS Z).property
        𝒯.val.property (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ).hom.hom
        (stackPointOfSpacePoint B S hS Z z) =
      spacePointMap B S hS Z 𝒯.val (representingEquivalence B S hS Z 𝒯.val eZ).functor z := by
  have hpt := congrFun (spacePointMap_comp B S hS Z (fibredCategory B S hS Z) 𝒯.val
    (BasedFunctor.id (fibredCategory B S hS Z).val)
    (representingEquivalence B S hS Z 𝒯.val eZ).functor) z
  rw [BasedFunctor.id_comp] at hpt
  exact hpt.symm

/-- Let `F : 𝒯 ⟶ 𝒳` be a 1-morphism, locally of finite
type, of locally Noetherian algebraic stacks, and let `𝒯` be represented by an algebraic space
`Z` through the equivalence-over `eZ`. Then at the point `t ∈ |𝒯|` named by `z ∈ |Z|`, the
relative dimension of Stacks 0DRL of `F` is the relative dimension of Stacks 0DRG of the
composite `Z ⟶ 𝒯 ⟶ 𝒳`, read in `EInt` through the embedding of Stacks 0AFN for a chart of
relative dimension `0`. -/
theorem relativeStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt_of_representing
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (F : 𝒯 ⟶ 𝒳)
    (hF : AlgebraicStacks.IsLocallyOfFiniteType B S hS F)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (hcF : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ ≫ F))
    (z : Space.points B S hS Z) (t : points B S hS 𝒯.val.val 𝒯.val.property)
    (ht : spacePointMap B S hS Z 𝒯.val
      (representingEquivalence B S hS Z 𝒯.val eZ).functor z = t) :
    relativeStackDimensionAt.{u, w} B S hS F hF h𝒯 h𝒳 t =
      dimensionSubNat (relativeDimensionAt.{u, w} B S hS Z hZ 𝒳
        (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ ≫ F) hcF z) 0 :=
  relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS F hF h𝒯 h𝒳 t hZ
    (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ)
    (isSmooth_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ)
    (isLocallyOfFiniteType_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ) hcF z
    ((pointsMap_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ z).trans ht) 0
    (relativeDimensionAt_representingStackChart_eq_zero.{u, w} B S hS 𝒯 Z hZ eZ _ z)

end RepresentingChart

/-! ### The bridge in existential form -/

section RepresentableSource

variable (𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- For a locally-of-finite-type 1-morphism `F : 𝒯 ⟶ 𝒳` of
locally Noetherian algebraic stacks with `𝒯` representable by an algebraic space, and for every
`t ∈ |𝒯|`, there are an algebraic space `Z`, a 1-morphism `c : Z ⟶ 𝒯` of algebraic stacks and a
point `z ∈ |Z|` above `t` for which the relative dimension of Stacks 0DRL of `F` at `t` is the
relative dimension of Stacks 0DRG of `c ≫ F` at `z`. -/
theorem exists_relativeStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt
    (F : 𝒯 ⟶ 𝒳) (hF : AlgebraicStacks.IsLocallyOfFiniteType B S hS F)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯rep : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
      (c : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒯)
      (hcF : AlgebraicStacks.IsLocallyOfFiniteType B S hS (c ≫ F))
      (z : Space.points B S hS Z),
      pointsMap B S hS (fibredCategory B S hS Z).val (fibredCategory B S hS Z).property
            𝒯.val.property c.hom.hom (stackPointOfSpacePoint B S hS Z z) = t ∧
        relativeStackDimensionAt.{u, w} B S hS F hF h𝒯 h𝒳 t =
          dimensionSubNat (relativeDimensionAt.{u, w} B S hS Z hZ 𝒳 (c ≫ F) hcF z) 0 := by
  classical
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := id h𝒯rep
  obtain ⟨z, hz⟩ := (bijective_spacePointMap_representing B S hS Z 𝒯.val eZ).surjective t
  refine ⟨Z, hZ, representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ,
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS _ F
      (isLocallyOfFiniteType_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ) hF, z,
    (pointsMap_representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ z).trans hz,
    relativeStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt_of_representing.{u, w}
      B S hS 𝒯 Z hZ eZ 𝒳 F hF h𝒯 h𝒳 _ z t hz⟩

end RepresentableSource

end AlgebraicGeometry.Stack

end
