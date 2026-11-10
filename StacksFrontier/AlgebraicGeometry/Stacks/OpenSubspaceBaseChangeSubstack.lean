module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinOpenSubstack
import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget

/-!
# Open substacks from open-subspace base changes

Let `𝒳` be an algebraic stack over `S` and let `P` be a property of the objects of `𝒳` which is
inherited along morphisms. For every scheme-valued point `z` of `𝒳` with values in `V`, the base
change of the inclusion of the full subcategory cut out by `P` along `z` is the category of
elements of the subfunctor `AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor` of
`yoneda V`. If every such subfunctor is an **open subspace** of `V` (**Stacks 02YU**, part (2)),
then the full subcategory is an open substack of `𝒳` in the sense of **Stacks 04YM**.

## Main definitions

* `AlgebraicGeometry.Stack.openSubstackOfIsOpenSubspace`: the open substack cut out by such a
  property.

## Main results

* `AlgebraicGeometry.Stack.prop_of_hom_of_isFieldObject`: for such a property, an object over the
  spectrum of a field has the property as soon as some object over a nonempty scheme mapping to
  it does.
* `AlgebraicGeometry.Stack.prop_of_mem_pointSet_openSubstackOfIsOpenSubspace`: a field-valued
  point whose class lies in the point set of the open substack has its object in it.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) {P : ObjectProperty 𝒳.val.val.obj}
  (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
  (hopen : ∀ (V : BigFppfOver B S hS)
    (z : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj)
    (_hz : z ⋙ 𝒳.val.val.p = Over.map V.hom),
    Space.IsOpenSubspace B V.left.1 V.left.2 (fullSubcategoryBaseChangeSubfunctor 𝒳 hP z))

include hopen in
/-- If every base change subfunctor of `P` is an open subspace, the inclusion of the full
subcategory on `P` is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_isOpenSubspace :
    IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryBasedInclusion 𝒳 P) :=
  isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion 𝒳 hP
    (fun W y hy => (hopen W y hy).1)

include hopen in
/-- If every base change subfunctor of `P` is an open subspace, the full subcategory on `P` is an
algebraic stack. -/
theorem isAlgebraicStack_fullSubcategoryBased_of_isOpenSubspace :
    IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P) :=
  isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces.{u, w} B S hS
    (𝒳 := CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 P)
      (isFiberedInGroupoids_fullSubcategoryBased 𝒳 hP))
    (𝒴 := 𝒳.val)
    (Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedInclusion 𝒳 P))
    (isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_isOpenSubspace
      B S hS 𝒳 hP hopen)
    𝒳.property

/-- If every base change subfunctor of `P` is an open subspace, the inclusion of the full
subcategory on `P` is an open immersion of algebraic stacks. -/
theorem isOpenImmersion_fullSubcategoryInclusion_of_isOpenSubspace :
    AlgebraicStacks.IsOpenImmersion B S hS
      (fullSubcategoryInclusion 𝒳 P
        (isAlgebraicStack_fullSubcategoryBased_of_isOpenSubspace B S hS 𝒳 hP hopen)) := by
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  have hrep := isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_of_isOpenSubspace
    B S hS 𝒳 hP hopen
  refine ⟨hrep, ?_⟩
  refine hasRelativeProperty_of_exists_representing B S hS
    (Space.openImmersionProperty B S hS)
    (fullSubcategoryInclusion 𝒳 P
      (isAlgebraicStack_fullSubcategoryBased_of_isOpenSubspace B S hS 𝒳 hP hopen)).hom
    hrep (fun U y hy => ?_)
  refine ⟨(fullSubcategoryBaseChangeSubfunctor 𝒳 hP y).toFunctor, (hopen U y hy).1,
    nonempty_equivalenceOver_fullSubcategoryBaseChange 𝒳 hP y hy, ?_⟩
  exact isOpenImmersion_algebraicSpaceMap_of_isOpenSubspace B S hS U _ (hopen U y hy)

/-- For a property `P` of the objects of `𝒳` inherited along morphisms, whose base change
subfunctor at every scheme-valued point is an open subspace, the full subcategory on `P` as an
open substack of `𝒳` (Stacks 04YM). -/
def openSubstackOfIsOpenSubspace : OpenSubstack 𝒳 where
  property := P
  strictlyFull := ⟨fun e h => hP e.inv h⟩
  isAlgebraic := isAlgebraicStack_fullSubcategoryBased_of_isOpenSubspace B S hS 𝒳 hP hopen
  isOpenImmersion := isOpenImmersion_fullSubcategoryInclusion_of_isOpenSubspace B S hS 𝒳 hP hopen

/-- The property cutting out `openSubstackOfIsOpenSubspace` is `P`. -/
@[simp]
theorem openSubstackOfIsOpenSubspace_property :
    (openSubstackOfIsOpenSubspace B S hS 𝒳 hP hopen).property = P :=
  rfl

include hopen in
/-- Let `c` be an object of `𝒳` over the
spectrum of a field and let `m : r ⟶ c` be a morphism from an object over a nonempty scheme. If
`r` has the property `P` then so does `c`. -/
theorem prop_of_hom_of_isFieldObject {r c : 𝒳.val.val.obj}
    (hc : IsFieldObject B S hS (𝒳.val.val.p.obj c))
    (hr : Nonempty ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj r)))
    (m : r ⟶ c) (hPr : P r) : P c := by
  set p := 𝒳.val.val.p
  have hfib := 𝒳.val.property
  set V := p.obj c
  obtain ⟨z, hz, ξ, hξ⟩ := StacksRepresentableCFG.exists_pointOverMap_of_obj p hfib V c rfl
  have hT' : (Over.map V.hom).obj (Over.mk (𝟙 V.left)) = V := Functor.overMap_obj_mkId V
  let t : p.obj r ⟶ V := p.map m
  let a : BigFppfOver B V.left.1 V.left.2 := Over.mk t.left
  let ta : a ⟶ Over.mk (𝟙 V.left) := Over.homMk t.left (Category.comp_id _)
  have hlift : p.IsHomLift ((Over.map V.hom).map ta ≫ eqToHom hT') (z.map ta ≫ ξ.hom) := by
    have : p.IsHomLift ((Over.map V.hom).map ta) (z.map ta) :=
      Functor.isHomLift_map_of_comp_eq hz ((Over.map V.hom).map ta) ta
    have := hξ
    infer_instance
  let e : (Over.map V.hom).obj a ⟶ p.obj r := Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ _ = t.left ≫ V.hom
    rw [Category.id_comp, Over.w t])
  have he : (Over.map V.hom).map ta ≫ eqToHom hT' = e ≫ t := by
    ext
    simp [e, ta, a]
  have _ : p.IsHomLift t m := IsHomLift.map p m
  have _ : p.IsStronglyCartesian t m := hfib.isStronglyCartesian_homLift t m
  let k : z.obj a ⟶ r := Functor.IsStronglyCartesian.map p t m he (z.map ta ≫ ξ.hom)
  have hza : P (z.obj a) := hP k hPr
  let Sub := fullSubcategoryBaseChangeSubfunctor 𝒳 hP z
  obtain ⟨x⟩ := hr
  obtain ⟨q, -⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B V.left.1 V.left.2 a x
  let w : Space.points B V.left.1 V.left.2 Sub.toFunctor :=
    Space.pointsMap B V.left.1 V.left.2 (yoneda.obj a) (yonedaEquiv.symm ⟨ta, hza⟩)
      (q.class B V.left.1 V.left.2 (yoneda.obj a))
  have hsub : Subsingleton ((BigFppfOver.toScheme B V.left.1 V.left.2).obj
      (Over.mk (𝟙 V.left))) := by
    obtain ⟨k, hk, ⟨i⟩⟩ := hc
    let : Field k := hk
    exact i.hom.homeomorph.injective.subsingleton
  have hle : (⊤ : Subfunctor (yoneda.obj (Over.mk (𝟙 V.left)) :
      (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) ≤ Sub := by
    refine Space.le_of_range_pointsMap_ι_subset B V.left.1 V.left.2 (hopen V z hz) ?_
    rintro _ ⟨w', rfl⟩
    exact ⟨w, Space.injective_pointsToScheme B V.left.1 V.left.2 _ (Subsingleton.elim _ _)⟩
  exact hP ξ.inv (hle _ (Set.mem_univ (𝟙 (Over.mk (𝟙 V.left)))))

include hopen in
/-- If the class of a field-valued point lies in the point set of
`AlgebraicGeometry.Stack.openSubstackOfIsOpenSubspace`, then its object has the property `P`. -/
theorem prop_of_mem_pointSet_openSubstackOfIsOpenSubspace (q : FieldValuedPoint B S hS 𝒳.val.val)
    (hq : pointClass B S hS 𝒳.val.val 𝒳.val.property q ∈
      (openSubstackOfIsOpenSubspace B S hS 𝒳 hP hopen).pointSet B S hS) :
    P q.obj := by
  obtain ⟨q', hq', hcl⟩ := (OpenSubstack.mem_pointSet_iff B S hS _ _).1 hq
  obtain ⟨r, ⟨m'⟩, ⟨m⟩⟩ :=
    (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val 𝒳.val.property q' q).1 hcl
  refine prop_of_hom_of_isFieldObject B S hS 𝒳 hP hopen ?_ ?_ m (hP m' hq')
  · rw [q.over]
    exact ⟨q.carrier, q.field, ⟨q.isSpec⟩⟩
  · rw [r.over]
    exact ⟨r.isSpec.inv (Classical.arbitrary _)⟩

end AlgebraicGeometry.Stack

end
