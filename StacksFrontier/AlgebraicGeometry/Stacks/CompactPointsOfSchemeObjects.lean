module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# Compactness of the space of points from finitely many objects over quasi-compact schemes

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`. An object `x` of `𝒳`
over a scheme `U` is, by the 2-Yoneda lemma (Stacks 004B), a 1-morphism from `U` to `𝒳`, and the
map it induces on points is continuous for the topology of Stacks 04Y8 (clause (1) of
Stacks 04XL). If `U` is quasi-compact the image is therefore compact. This file records the
consequence used to prove that a moduli stack is quasi-compact: if finitely many objects `xᵢ` of
`𝒳` over quasi-compact schemes `Uᵢ` are such that every field-valued point of `𝒳` maps to one of
them, the space of points of `𝒳` is compact.

## Main results

* `AlgebraicGeometry.Stack.isCompact_range_pointsMap_liftBased`: the image on points of the
  1-morphism attached to an object over a quasi-compact scheme is compact.
* `AlgebraicGeometry.Stack.pointClass_mem_range_pointsMap_liftBased`: a field-valued point with a
  morphism to that object lies in that image.
* `AlgebraicGeometry.Stack.compactSpace_points_of_forall_exists_hom`: the space of points is
  compact as soon as every field-valued point maps to one of finitely many objects over
  quasi-compact schemes.

## Implementation notes

The 1-morphism attached to `x` over `U` is `CategoryTheory.Functor.TwoYoneda.liftBased`, a
based functor out of the slice `AlgebraicGeometry.Stack.schemeFibredCategory` of the site over
`U`. Its points are compact because they are the continuous image of the points of the algebraic
space `U` represents (clause (1) of Stacks 03BX, `AlgebraicGeometry.Space.schemePointsHomeomorph`)
along the canonical map of the tautological chart followed by the equivalence of the two models
of `U` (`AlgebraicGeometry.Stack.schemeFibredCategoryEquivalence`), both surjective.

A field-valued point `p` with a morphism `φ : p.obj ⟶ x` is the image of the field-valued point
of the slice whose object is the base of `p` over `U` through the image of `φ`; the chosen lift
of `x` over that object receives a morphism from `p.obj`, the chosen arrow being strongly
cartesian, and a morphism of objects over field spectra is a common refinement (Stacks 04XF).

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04Y8](https://stacks.math.columbia.edu/tag/04Y8)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **The image on points of an object over a quasi-compact scheme is compact.** The object `x`
over `U` is the 1-morphism `CategoryTheory.Functor.TwoYoneda.liftBased` from the slice of the site
over `U`; its map on points is continuous (clause (1) of Stacks 04XL), and the points of the
slice are the continuous image of the points of `U`, a compact space. -/
theorem isCompact_range_pointsMap_liftBased (U : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)] (x : 𝒳.val.p.Fiber U) :
    @IsCompact _ (pointTopology B S hS 𝒳)
      (Set.range (pointsMap B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property 𝒳.property
        (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.property U x))) := by
  let 𝒰 := schemeFibredCategory B S hS U
  let 𝒴 := fibredCategory B S hS (yoneda.obj U)
  let : TopologicalSpace (Space.points B S hS (yoneda.obj U)) :=
    Space.pointTopology B S hS (yoneda.obj U)
  have hU : CompactSpace (Space.points B S hS (yoneda.obj U)) :=
    (Space.schemePointsHomeomorph B S hS U).symm.compactSpace
  let := pointTopology B S hS 𝒴
  let := pointTopology B S hS 𝒰
  let := pointTopology B S hS 𝒳
  let e := schemeFibredCategoryEquivalence B S hS U
  let a := spacePointMap B S hS (yoneda.obj U) 𝒴 (BasedFunctor.id 𝒴.val)
  let b := pointsMap B S hS 𝒴.val 𝒴.property 𝒰.property e.inverse
  let c := pointsMap B S hS 𝒰.val 𝒰.property 𝒳.property
    (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.property U x)
  have ha : Continuous a :=
    @continuous_spacePointMap B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝒴
      (BasedFunctor.id 𝒴.val)
  have hb := continuous_pointsMap B S hS 𝒴 𝒰 e.inverse
  have hc := continuous_pointsMap B S hS 𝒰 𝒳
    (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.property U x)
  have hsurj : Function.Surjective (b ∘ a) :=
    (pointsMap_surjective_of_basedEquivalence B S hS e.symm).comp
      (spacePointMap_id_bijective B S hS (yoneda.obj U)).2
  rw [← hsurj.range_comp c]
  exact isCompact_range (hc.comp (hb.comp ha))

/-- **A field-valued point mapping to an object `x` over `U` lies in the image of `x` on
points.** The field-valued point of the slice over `U` whose object is the base of `p`, over `U`
through the image of `φ`, is sent to the chosen lift of `x` along that morphism, which receives
a morphism from `p.obj` because the chosen arrow is strongly cartesian. -/
theorem pointClass_mem_range_pointsMap_liftBased (U : BigFppfOver B S hS)
    (x : 𝒳.val.p.Fiber U) (p : FieldValuedPoint B S hS 𝒳.val) (φ : p.obj ⟶ x.1) :
    pointClass B S hS 𝒳.val 𝒳.property p ∈
      Set.range (pointsMap B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property 𝒳.property
        (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.property U x)) := by
  let f : p.base ⟶ U := eqToHom p.over.symm ≫ 𝒳.val.p.map φ ≫ eqToHom x.2
  let q : FieldValuedPoint B S hS (schemeFibredCategory B S hS U).val :=
    { carrier := p.carrier
      base := p.base
      isSpec := p.isSpec
      obj := Over.mk f
      «over» := rfl }
  refine ⟨pointClass B S hS _ _ q, ?_⟩
  refine (pointsMap_class B S hS _ _ _ _ q).trans
    ((class_eq_class_iff_hasCommonExtension B S hS 𝒳.val 𝒳.property _ _).2 ?_)
  let L := Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.property U x (Over.mk f)
  have : 𝒳.val.p.IsHomLift (𝒳.val.p.map φ ≫ eqToHom x.2) φ :=
    IsHomLift.of_fac _ _ φ rfl x.2 (by simp)
  let m : p.obj ⟶ L.y := Functor.IsStronglyCartesian.map 𝒳.val.p (Over.mk f).hom L.φ
    (f' := 𝒳.val.p.map φ ≫ eqToHom x.2) (g := eqToHom p.over) (by simp [f]) φ
  exact ⟨p, ⟨m⟩, ⟨𝟙 _⟩⟩

/-- **The space of points is compact as soon as every field-valued point maps to one of finitely
many objects over quasi-compact schemes.** The space of points is then the union of finitely
many compact images, by `AlgebraicGeometry.Stack.isCompact_range_pointsMap_liftBased` and
`AlgebraicGeometry.Stack.pointClass_mem_range_pointsMap_liftBased`. -/
theorem compactSpace_points_of_forall_exists_hom {ι : Type*} [Finite ι]
    (U : ι → BigFppfOver B S hS) [∀ i, CompactSpace ((BigFppfOver.toScheme B S hS).obj (U i))]
    (x : ∀ i, 𝒳.val.p.Fiber (U i))
    (h : ∀ p : FieldValuedPoint B S hS 𝒳.val, ∃ i, Nonempty (p.obj ⟶ (x i).1)) :
    @CompactSpace (points B S hS 𝒳.val 𝒳.property) (pointTopology B S hS 𝒳) := by
  let := pointTopology B S hS 𝒳
  refine ⟨?_⟩
  have hcover : (Set.univ : Set (points B S hS 𝒳.val 𝒳.property)) =
      ⋃ i, Set.range (pointsMap B S hS (schemeFibredCategory B S hS (U i)).val
        (schemeFibredCategory B S hS (U i)).property 𝒳.property
        (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.property (U i) (x i))) := by
    refine (Set.eq_univ_of_forall fun ξ => ?_).symm
    induction ξ using Quotient.inductionOn with
    | h p =>
      obtain ⟨i, ⟨φ⟩⟩ := h p
      exact Set.mem_iUnion.2 ⟨i, pointClass_mem_range_pointsMap_liftBased B S hS 𝒳 (U i) (x i) p φ⟩
  rw [hcover]
  exact isCompact_iUnion fun i => isCompact_range_pointsMap_liftBased B S hS 𝒳 (U i) (x i)

end AlgebraicGeometry.Stack
