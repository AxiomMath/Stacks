module

public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosureImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureChartCompactFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureQuotientChart
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteOverFieldPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapTransport
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstTwoFibreProduct

/-!
# The fibre of a quotient chart as `U ×_𝒳 Spec κ(u)`, from the chart's relation data

For a quotient chart `[U/R] ⟶ 𝒳` (`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid`)
and a point `u` of `U`, the fibre `F` of the target map over `Spec κ(u)` is the 2-fibre product
`U ×_𝒳 Spec κ(u)`, and if `Spec κ(u) ⟶ 𝒳` is quasi-compact then so is `F ⟶ U`. A
`ChartGroupoid` does not record that its arrow object `V` is `U ×_𝒳 U`, so this module takes that
identification as data: an equivalence `eR` over the site between the self-intersection
`U ×_{𝒳'} U` of a chart `U ⟶ 𝒳'` and the Yoneda image of `V`, under which `K.s` and `K.t` are the
source and target morphisms of Stacks 04T4 (4).

This is the step of the proof of **Stacks 0DU5** which forms the cartesian diagram `F = U ×_𝒳 u`
and reads quasi-compactness of `F ⟶ U` off quasi-compactness of `u ⟶ 𝒳`. The chart `[U/R] ⟶ 𝒳`
of Stacks 0DU3 carries no record of the fact that its arrow object `V` *is* `U ×_𝒳 U`; with the
record `eR` as data, this module produces the 2-fibre product square the quasi-compactness step
consumes.

## Implementation notes

Write `g : U ⟶ 𝒳'` for the chart and `v : Spec κ(u) ⟶ U` for the residue field point at the chart
point. The self-intersection `U ×_{𝒳'} U` is, on the nose, the apex of the canonical 2-fibre
product square of the cospan `(g, g)`, so `eR` says that apex is represented by `yoneda V`, with
the two projections inducing `yoneda.map K.t` and `yoneda.map K.s`. Cancelling the first factor of
the iterated 2-fibre product `(U ×_{𝒳'} U) ×_{U, pr₀} Spec κ(u)` — **Stacks 02XD**,
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare` — exhibits that apex as a
2-fibre product of the cospan `(g, v ≫ g)`, with its projection to `U` the outer projection
followed by `pr₁`.

The apex is represented by an algebraic space (**Stacks 0300**), and **Stacks 04SD** for
represented stacks, in the form
`AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProduct`, makes its representing
presheaf a fibre product of `yoneda.map (residuePointMap)` and `yoneda.map K.t`. The fibre product
of objects of the site along the same cospan is another
(`AlgebraicGeometry.Stack.isPullback_sitePullback`, Yoneda preserving fibre products), and its
apex is `AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.targetFibreObj` on the nose; so
the comparison of the two pullbacks transports the representing equivalence onto
`yoneda (targetFibreObj)`, and
`AlgebraicGeometry.Stack.representingMap_trans_equivalenceOverOfIso` then computes the induced
morphism of representing presheaves of the projection to `U` as
`yoneda.map (targetFibreToObjects)`.

Finally the cospan's second leg is moved from `v ≫ g` to the 1-morphism of a field-valued point:
the residue field point at the chart point is a field-valued point of the slice over `U`
(`AlgebraicGeometry.Stack.closedPointFieldValuedPoint`) whose 2-Yoneda lift is `v`
(`CategoryTheory.Functor.TwoYoneda.liftBased_overMap_iso`), and
`AlgebraicGeometry.Stack.fieldValuedPointMorphism_comp_iso` identifies its composite with `g` as
the 1-morphism of its image on `𝒳'`.

## Main results

* `AlgebraicGeometry.Stack.EtaleLocalStructure.exists_isTwoFibreProduct_targetFibre_of_relation`:
  the fibre of the target map over the chart point is a 2-fibre product `U ×_{𝒳'} Spec κ(u)`, in
  the shape the quasi-compactness step asks for.
* `AlgebraicGeometry.Stack.EtaleLocalStructure.exists_compactSpace_targetFibre_of_relation`: a
  point with a quasi-compact representative admits a quotient chart whose target map has compact
  fibre over the chart point, which is what the proof of Stacks 0DU5 consumes.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0DTK](https://stacks.math.columbia.edu/tag/0DTK)
* [Stacks Project, Tag 0DU3](https://stacks.math.columbia.edu/tag/0DU3)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fibre of the target map of a quotient chart over the chart point is `U ×_{𝒳'} Spec κ(u)`,
given the chart's relation data.** Let `K` be a quotient chart of an algebraic stack, let `z` be a
point of its object scheme, and let `hom : U ⟶ 𝒳'` be a 1-morphism whose self-intersection
`U ×_{𝒳'} U` is represented by `yoneda K.V` through `eR`, with `K.s` and `K.t` the source and
target morphisms of Stacks 04T4 (4). Then there are a field-valued point `p` of `𝒳'`, a 2-fibre
product square of the cospan `(hom, p)` and a representing equivalence of its apex by
`yoneda (targetFibreObj K z)` under which the projection to `U` induces
`yoneda.map (targetFibreToObjects K z)`; and `p` is the image of the residue field point at `z`.

See the module documentation for the proof. -/
theorem exists_isTwoFibreProduct_targetFibre_of_relation
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (K : ChartGroupoid B S hS 𝒳)
    (z : Space.points B S hS (yoneda.obj K.U))
    (hom : schemeStack.{u, w} B S hS K.U ⟶ 𝒴)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS K.U).val 𝒴.val
        hom.hom.hom).val.p
      (presheafOfCategories ((schemeSpace K.V :
        AlgebraicSpaces B S hS).obj ⋙ typeToCat)).p)
    (hs : yoneda.map K.s = SelfIntersection.relationSourceMap
      (U := schemeSpace K.U)
      (R := schemeSpace K.V)
      (representedChart B S hS K.U) eR)
    (ht : yoneda.map K.t = SelfIntersection.relationTargetMap
      (U := schemeSpace K.U)
      (R := schemeSpace K.V)
      (representedChart B S hS K.U) eR) :
    ∃ (p : FieldValuedPoint B S hS 𝒴.val.val)
      (g : schemeFibredCategory B S hS K.U ⟶ 𝒴.val)
      (Q : Bicategory.TwoCommSq g (fieldValuedPointMorphism B S hS 𝒴.val p))
      (_hQ : Bicategory.IsTwoFibreProduct Q)
      (eF : StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
        (presheafOfCategories
          (yoneda.obj (ChartGroupoid.targetFibreObj K z) ⋙ typeToCat)).p),
      pointClass B S hS 𝒴.val.val 𝒴.val.isFiberedInGroupoids p =
        AlgebraicStacks.pointsMap B S hS hom (pointClass B S hS
          (schemeStack.{u, w} B S hS K.U).val.val
          (schemeStack.{u, w} B S hS K.U).val.isFiberedInGroupoids
          (closedPointFieldValuedPoint B S hS K.U (Space.pointsToScheme B S hS K.U z)
            (BigFppfSite.residueField_spec_contains B K.contains_objects _))) ∧
      representingMap B S hS Q.pt (schemeFibredCategory B S hS K.U)
          (yoneda.obj (ChartGroupoid.targetFibreObj K z))
          (yoneda.obj K.U) eF (representedChart B S hS K.U) Q.fst
        = yoneda.map (ChartGroupoid.targetFibreToObjects K z) := by
  classical
  let g₀ : (schemeStack.{u, w} B S hS K.U).val ⟶ 𝒴.val := hom.hom
  let relSq := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g₀ g₀
  let v : schemeFibredCategory B S hS (ChartGroupoid.residuePointObj K z) ⟶
      schemeFibredCategory B S hS K.U :=
    schemeFibredCategoryMap B S hS (ChartGroupoid.residuePointMap K z)
  let C := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} relSq.fst v
  have hrelRep : IsRepresentableByAlgebraicSpace B S hS relSq.pt :=
    ⟨yoneda.obj K.V, isAlgebraicSpace_yoneda B S hS K.V, ⟨eR⟩⟩
  have hvRep : IsRepresentableByAlgebraicSpaces B S hS v.hom :=
    isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS _
  obtain ⟨T₁, hT₁, ⟨eT₁⟩⟩ : IsRepresentableByAlgebraicSpace B S hS C.pt :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
      (schemeFibredCategory B S hS K.U) relSq.pt
      (schemeFibredCategory B S hS (ChartGroupoid.residuePointObj K z))
      relSq.fst.hom v.hom hvRep hrelRep
  have : (twoFibreProductStructureFunctor B S hS relSq.pt
      (schemeFibredCategory B S hS (ChartGroupoid.residuePointObj K z))
      (schemeFibredCategory B S hS K.U) relSq.fst v).IsFibered := C.pt.property.isFibered
  -- the first projection of the relation square names the target morphism of the groupoid
  have hfst : representingMap B S hS relSq.pt (schemeFibredCategory B S hS K.U)
      (yoneda.obj K.V) (yoneda.obj K.U) eR (representedChart B S hS K.U) relSq.fst =
      SelfIntersection.relationTargetMap
        (U := schemeSpace K.U)
        (R := schemeSpace K.V)
        (representedChart B S hS K.U) eR := rfl
  -- the residue field point induces the morphism of the site it is
  have hsnd : representingMap B S hS
      (schemeFibredCategory B S hS (ChartGroupoid.residuePointObj K z))
      (schemeFibredCategory B S hS K.U)
      (yoneda.obj (ChartGroupoid.residuePointObj K z)) (yoneda.obj K.U)
      (representedChart B S hS (ChartGroupoid.residuePointObj K z))
      (representedChart B S hS K.U) v =
      yoneda.map (ChartGroupoid.residuePointMap K z) := by
    rw [show v = (schemeStackMap.{u, w} B S hS (ChartGroupoid.residuePointMap K z)).hom from rfl,
      representingMap_representedChart_eq_yoneda_map_siteMap, siteMap_schemeStackMap]
  -- Stacks 04SD: the representing presheaf of the iterated apex is a fibre product
  have hPB₁ := isPullback_representingMap_twoFibreProduct B S hS relSq.pt
    (schemeFibredCategory B S hS (ChartGroupoid.residuePointObj K z))
    (schemeFibredCategory B S hS K.U)
    (yoneda.obj K.V) (yoneda.obj (ChartGroupoid.residuePointObj K z)) (yoneda.obj K.U)
    eR (representedChart B S hS (ChartGroupoid.residuePointObj K z))
    (representedChart B S hS K.U) relSq.fst v T₁ eT₁
  rw [hfst, hsnd, ← ht] at hPB₁
  have hPB₂ : IsPullback
      (yoneda.map (sitePullbackFst B S hS (ChartGroupoid.residuePointMap K z) K.t))
      (yoneda.map (sitePullbackSnd B S hS (ChartGroupoid.residuePointMap K z) K.t))
      (yoneda.map (ChartGroupoid.residuePointMap K z)) (yoneda.map K.t) :=
    (isPullback_sitePullback B S hS (ChartGroupoid.residuePointMap K z) K.t).map yoneda
  let i : T₁ ≅ yoneda.obj (ChartGroupoid.targetFibreObj K z) := hPB₁.isoIsPullback _ _ hPB₂
  let eF : StacksRepresentableCFG.EquivalenceOver C.pt.val.p
      (presheafOfCategories
        (yoneda.obj (ChartGroupoid.targetFibreObj K z) ⋙ typeToCat)).p :=
    eT₁.trans (PresheafOfCategories.equivalenceOverOfIso i)
  -- the second projection of the relation square names the source morphism of the groupoid
  have hrelsnd : representingMap B S hS relSq.pt (schemeFibredCategory B S hS K.U)
      (yoneda.obj K.V) (yoneda.obj K.U) eR (representedChart B S hS K.U) relSq.snd =
      yoneda.map K.s := by
    rw [hs]; rfl
  -- the outer projection of the iterated apex names the second projection of the fibre
  have hCfst : representingMap B S hS C.pt relSq.pt
      (yoneda.obj (ChartGroupoid.targetFibreObj K z)) (yoneda.obj K.V) eF eR C.fst =
      yoneda.map (sitePullbackSnd B S hS (ChartGroupoid.residuePointMap K z) K.t) := by
    have h₁ := representingMap_trans_equivalenceOverOfIso B S hS
      (𝒜 := C.pt) (𝒞 := relSq.pt) T₁ (yoneda.obj (ChartGroupoid.targetFibreObj K z))
      (yoneda.obj K.V) eT₁ eR i C.fst
    have h₂ : i.hom ≫
        yoneda.map (sitePullbackSnd B S hS (ChartGroupoid.residuePointMap K z) K.t) =
        representingMap B S hS C.pt relSq.pt T₁ (yoneda.obj K.V) eT₁ eR C.fst :=
      IsPullback.isoIsPullback_hom_snd ..
    exact (cancel_epi i.hom).1 (h₁.symm.trans h₂.symm)
  have hfinal : representingMap B S hS C.pt (schemeFibredCategory B S hS K.U)
      (yoneda.obj (ChartGroupoid.targetFibreObj K z)) (yoneda.obj K.U) eF
      (representedChart B S hS K.U) (C.fst ≫ relSq.snd) =
      yoneda.map (ChartGroupoid.targetFibreToObjects K z) := by
    refine (representingMap_comp B S hS (𝒜 := C.pt) (ℬ := relSq.pt)
        (𝒞 := schemeFibredCategory B S hS K.U)
        (yoneda.obj (ChartGroupoid.targetFibreObj K z)) (yoneda.obj K.V) (yoneda.obj K.U)
        eF eR (representedChart B S hS K.U) C.fst relSq.snd).trans ?_
    rw [hCfst, hrelsnd]
    exact (yoneda.map_comp (sitePullbackSnd B S hS (ChartGroupoid.residuePointMap K z) K.t)
      K.s).symm
  -- the residue field point of the chart at `z`, and the 2-isomorphism moving the cospan's
  -- second leg onto its 1-morphism
  let q : FieldValuedPoint B S hS (schemeFibredCategory B S hS K.U).val :=
    closedPointFieldValuedPoint B S hS K.U (Space.pointsToScheme B S hS K.U z)
      (BigFppfSite.residueField_spec_contains B K.contains_objects _)
  let p : FieldValuedPoint B S hS 𝒴.val.val :=
    fieldValuedPointMap B S hS (schemeFibredCategory B S hS K.U).val g₀.hom q
  let θ₀ : fieldValuedPointMorphism B S hS (schemeFibredCategory B S hS K.U) q ≅ v :=
    Bicategory.InducedBicategory.isoMk
      (CategoryTheory.Functor.TwoYoneda.liftBased_overMap_iso
        (V := K.U) (Functor.Fiber.mk (a := q.obj) q.over)
        (schemeFibredCategory B S hS K.U).isFiberedInGroupoids)
  let θ : v ≫ g₀ ≅ fieldValuedPointMorphism B S hS 𝒴.val p :=
    Bicategory.whiskerRightIso θ₀.symm g₀ ≪≫
      Bicategory.InducedBicategory.isoMk (fieldValuedPointMorphism_comp_iso B S hS g₀.hom q)
  exact ⟨p, g₀, CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} g₀ g₀ v _ θ,
    CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1} g₀ g₀ v _ θ,
    eF, rfl, hfinal⟩

/-- **A quotient chart with compact fibre over its chart point, from the chart's relation data.**
Let `x` be a point of an algebraic stack `𝒳` with a quasi-compact field-valued representative,
let `m : 𝒴 ⟶ 𝒳` be a monomorphism of algebraic stacks, and let `K` be a quotient chart of `𝒳` with
a point `z` over `x`, together with a 1-morphism `hom : U ⟶ 𝒴` whose self-intersection is
represented by `yoneda K.V` through `eR`, with `K.s` and `K.t` the source and target morphisms,
such that `m ∘ hom` sends the residue field point at `z` to `x`. Then some quotient chart `K'` of
`𝒳` has a point `z'` over `x` at which the fibre of its target map over `Spec κ(z')` is compact.

This is the conclusion the proof of **Stacks 0DU5** consumes. The quasi-compact representative of
`x` lives on `𝒳`; the 2-fibre product square of
`AlgebraicGeometry.Stack.EtaleLocalStructure.exists_isTwoFibreProduct_targetFibre_of_relation`
lives on an algebraic stack `𝒴` admitting a monomorphism to `𝒳` — which is where the chart
construction of Stacks 0DU3 lands, the image open substack of the affine chart — and
`Stack.exists_chartGroupoid_compactSpace_targetFibre_of_isTwoFibreProduct_of_isMonomorphism`
is what moves quasi-compactness between the two and reads it off the fibre. -/
theorem exists_compactSpace_targetFibre_of_relation
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hqc : ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
      pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = x ∧
        IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p)
    {𝒴 : AlgebraicStacks.{u, w} B S hS} (m : 𝒴 ⟶ 𝒳)
    (hm : AlgebraicStacks.IsMonomorphism B S hS m)
    (K : ChartGroupoid B S hS 𝒳)
    (z : Space.points B S hS (yoneda.obj K.U))
    (hom : schemeStack.{u, w} B S hS K.U ⟶ 𝒴)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS K.U).val 𝒴.val
        hom.hom.hom).val.p
      (presheafOfCategories ((schemeSpace K.V :
        AlgebraicSpaces B S hS).obj ⋙ typeToCat)).p)
    (hs : yoneda.map K.s = SelfIntersection.relationSourceMap
      (U := schemeSpace K.U)
      (R := schemeSpace K.V)
      (representedChart B S hS K.U) eR)
    (ht : yoneda.map K.t = SelfIntersection.relationTargetMap
      (U := schemeSpace K.U)
      (R := schemeSpace K.V)
      (representedChart B S hS K.U) eR)
    (hzx : AlgebraicStacks.pointsMap B S hS K.map (K.point z) = x)
    (hqx : AlgebraicStacks.pointsMap B S hS m (AlgebraicStacks.pointsMap B S hS hom
      (pointClass B S hS (schemeStack.{u, w} B S hS K.U).val.val
        (schemeStack.{u, w} B S hS K.U).val.isFiberedInGroupoids
        (closedPointFieldValuedPoint B S hS K.U (Space.pointsToScheme B S hS K.U z)
          (BigFppfSite.residueField_spec_contains B K.contains_objects _)))) = x) :
    ∃ (K' : ChartGroupoid B S hS 𝒳) (z' : Space.points B S hS (yoneda.obj K'.U)),
      AlgebraicStacks.pointsMap B S hS K'.map (K'.point z') = x ∧
      CompactSpace ↑(pullback (K'.groupoid.objects.left.fromSpecResidueField
        (Space.pointsToScheme B S hS K'.U z')) K'.groupoid.target.left) := by
  obtain ⟨p, g, Q, hQ, eF, hp, hrep⟩ :=
    exists_isTwoFibreProduct_targetFibre_of_relation B S hS K z hom eR hs ht
  refine exists_chartGroupoid_compactSpace_targetFibre_of_isTwoFibreProduct_of_isMonomorphism
    B S hS 𝒳 x hqc ⟨𝒴, m, hm, K, z, p, g, Q, hQ, eF, hzx, ?_, hrep⟩
  rw [show pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids
      (fieldValuedPointMap B S hS 𝒴.val.val m.hom.hom p) =
      AlgebraicStacks.pointsMap B S hS m (pointClass B S hS 𝒴.val.val
        𝒴.val.isFiberedInGroupoids p) from rfl, hp]
  exact hqx

end AlgebraicGeometry.Stack.EtaleLocalStructure

end
