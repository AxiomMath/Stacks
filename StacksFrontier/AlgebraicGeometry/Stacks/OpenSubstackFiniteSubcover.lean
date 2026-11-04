module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackUnion
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation

/-!
# Finite subcovers of a quasi-compact open substack

Let `𝒳` be an algebraic stack over `S`, let `𝒳' ⊆ 𝒳` be a quasi-compact open substack, and let
`𝒳ᵢ ⊆ 𝒳`, `i ∈ I`, be open substacks with `𝒳' ⊆ ⋃_{i ∈ I} 𝒳ᵢ`. Then `𝒳' ⊆ ⋃_{i ∈ I'} 𝒳ᵢ` for a
finite `I' ⊆ I`.

## Main definitions

* `AlgebraicGeometry.Stack.IsOpenSubstackCoverOn`: a family of open substacks of `𝒳` covers an
  open substack `𝒳'` when every object of `𝒳` lying in `𝒳'` restricts, over the members of some
  covering sieve of the fppf topology, into a member of the family.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.pointClass_mem_pointSet` and
  `AlgebraicGeometry.Stack.OpenSubstack.exists_fieldValuedPoint_of_mem_pointSet`: a point of
  `|𝒳|` lies in `|𝒳'|` exactly when some field-valued point representing it has its object in
  `𝒳'`.
* `AlgebraicGeometry.Stack.exists_mem_pointSet_of_isOpenSubstackCoverOn`: the point sets of a
  covering family of open substacks cover the point set of the open substack they cover.
* `AlgebraicGeometry.Stack.exists_finset_pointSet_subset_of_isQuasiCompactStack`: finitely many
  members of a covering family already contain the point set of a quasi-compact open substack.
* `AlgebraicGeometry.Stack.exists_finset_le_of_isQuasiCompactStack`: a quasi-compact open
  substack contained in the union of a family of open substacks is contained in the union of
  finitely many of them.

## Implementation notes

The union is `AlgebraicGeometry.Stack.OpenSubstack.iUnion`, and both the hypothesis and the
conclusion are stated with it, containment of open substacks being containment of their objects.

## References

* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 05UQ](https://stacks.math.columbia.edu/tag/05UQ)
* [Stacks Project, Tag 05UR](https://stacks.math.columbia.edu/tag/05UR)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Covering an open substack -/

/-- A family of open substacks of an algebraic stack `𝒳` *covers* an open substack `𝒳'` of `𝒳`
when every object of a fibre of `𝒳` lying in `𝒳'` restricts, over the members of some covering
sieve of the fppf topology, into one of the substacks, the substack being allowed to depend on
the member. -/
def IsOpenSubstackCoverOn (𝒳 : AlgebraicStacks.{u, w} B S hS) (𝒳' : OpenSubstack 𝒳)
    {I : Type*} (𝒰 : I → OpenSubstack 𝒳) : Prop :=
  haveI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  ∀ (T : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber T), 𝒳'.property x.1 →
    ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ T), R.arrows f →
      ∃ i, (𝒰 i).property (Functor.pullbackFiber 𝒳.val.val.p x f).1

/-! ### Points of an open substack -/

/-- A field-valued point of `𝒳` whose object lies in an open substack represents a point of the
point set of that substack. -/
theorem OpenSubstack.pointClass_mem_pointSet {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒳) (p : FieldValuedPoint B S hS 𝒳.val.val) (hp : W.property p.obj) :
    pointClass B S hS 𝒳.val.val 𝒳.val.property p ∈ W.pointSet B S hS :=
  ⟨pointClass B S hS _ _
    { carrier := p.carrier
      field := p.field
      base := p.base
      isSpec := p.isSpec
      obj := ⟨p.obj, hp⟩
      «over» := p.over }, rfl⟩

/-- Every point of the point set of an open substack is represented by a field-valued point of
`𝒳` whose object lies in the substack. -/
theorem OpenSubstack.exists_fieldValuedPoint_of_mem_pointSet
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (W : OpenSubstack 𝒳)
    {x : AlgebraicStacks.points B S hS 𝒳} (hx : x ∈ W.pointSet B S hS) :
    ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
      W.property p.obj ∧ pointClass B S hS 𝒳.val.val 𝒳.val.property p = x := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨q, hq⟩ := Quotient.exists_rep y
  refine ⟨fieldValuedPointMap B S hS (fullSubcategoryBased 𝒳 W.property)
    (fullSubcategoryBasedInclusion 𝒳 W.property) q, q.obj.property, ?_⟩
  rw [← hy, ← hq]
  rfl

/-- If a family of open substacks `𝒰` covers an open substack `𝒳'`, then every point of the
point set of `𝒳'` lies in the point set of some member of `𝒰`. -/
theorem exists_mem_pointSet_of_isOpenSubstackCoverOn {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (𝒳' : OpenSubstack 𝒳) {I : Type*} (𝒰 : I → OpenSubstack 𝒳)
    (hcover : IsOpenSubstackCoverOn B S hS 𝒳 𝒳' 𝒰)
    {x : AlgebraicStacks.points B S hS 𝒳} (hx : x ∈ 𝒳'.pointSet B S hS) :
    ∃ i, x ∈ (𝒰 i).pointSet B S hS := by
  have hfib : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨q, hq, rfl⟩ := 𝒳'.exists_fieldValuedPoint_of_mem_pointSet B S hS hx
  have hqField : IsFieldObject B S hS q.base := ⟨q.carrier, q.field, ⟨q.isSpec⟩⟩
  obtain ⟨R, hR, hmem⟩ := hcover q.base ⟨q.obj, q.over⟩ hq
  obtain ⟨V, g, hV, hgR⟩ := exists_isFieldObject_arrow_of_mem_topology B S hS hqField hR
  obtain ⟨i, hi⟩ := hmem g hgR
  obtain ⟨k, hk, ⟨e⟩⟩ := hV
  let _ : Field k := hk
  refine ⟨i, ?_⟩
  have hpull : pointClass B S hS 𝒳.val.val 𝒳.val.property
      { carrier := k
        field := hk
        base := V
        isSpec := e
        obj := (Functor.pullbackFiber 𝒳.val.val.p ⟨q.obj, q.over⟩ g).1
        «over» := Functor.IsPreFibered.pullbackObj_proj q.over g } =
      pointClass B S hS 𝒳.val.val 𝒳.val.property q :=
    (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val _ _ q).2
      ⟨_, ⟨𝟙 _⟩, ⟨Functor.IsPreFibered.pullbackMap q.over g⟩⟩
  rw [← hpull]
  exact (𝒰 i).pointClass_mem_pointSet B S hS _ hi

/-! ### The finite subcover -/

/-- If a quasi-compact open substack `𝒳'` of an algebraic stack `𝒳` is covered by a family of
open substacks `𝒳ᵢ`, then finitely many of the `𝒳ᵢ` already cover the point set of `𝒳'`. -/
@[stacks 05UR "the conclusion read on points: finitely many members of the family contain the \
point set of the quasi-compact open substack"]
theorem exists_finset_pointSet_subset_of_isQuasiCompactStack
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (𝒳' : OpenSubstack 𝒳)
    (hqc : IsQuasiCompactStack.{u, w} B S hS
      (fullSubcategoryAlgebraicStack 𝒳 𝒳'.property 𝒳'.isAlgebraic).val
      (fullSubcategoryAlgebraicStack 𝒳 𝒳'.property 𝒳'.isAlgebraic).property)
    {I : Type*} (𝒰 : I → OpenSubstack 𝒳)
    (hcover : IsOpenSubstackCoverOn B S hS 𝒳 𝒳' 𝒰) :
    ∃ J : Finset I, 𝒳'.pointSet B S hS ⊆ ⋃ i ∈ J, (𝒰 i).pointSet B S hS := by
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS
    (fullSubcategoryAlgebraicStack 𝒳 𝒳'.property 𝒳'.isAlgebraic).val
  let _ : CompactSpace (points B S hS
    (fullSubcategoryAlgebraicStack 𝒳 𝒳'.property 𝒳'.isAlgebraic).val.val
    (fullSubcategoryAlgebraicStack 𝒳 𝒳'.property 𝒳'.isAlgebraic).val.property) := hqc
  exact (isCompact_range (continuous_pointsMap B S hS
      (fullSubcategoryAlgebraicStack 𝒳 𝒳'.property 𝒳'.isAlgebraic).val 𝒳.val
      𝒳'.inclusion.hom.hom)).elim_finite_subcover (fun i => (𝒰 i).pointSet B S hS)
    (fun i => OpenSubstack.isOpen_pointSet B S hS (𝒰 i)) fun _ hx =>
      Set.mem_iUnion.2 (exists_mem_pointSet_of_isOpenSubstackCoverOn B S hS 𝒳' 𝒰 hcover hx)

/-- Let `𝒳` be an algebraic stack and `𝒳' ⊆ 𝒳` a quasi-compact open substack. Let `𝒳ᵢ ⊆ 𝒳`,
`i ∈ I`, be open substacks such that `𝒳' ⊆ ⋃_{i ∈ I} 𝒳ᵢ`, the union being
`AlgebraicGeometry.Stack.OpenSubstack.iUnion`. Then there is a finite subset `I' ⊆ I` such that
`𝒳' ⊆ ⋃_{i ∈ I'} 𝒳ᵢ`. -/
@[stacks 05UR]
theorem exists_finset_le_of_isQuasiCompactStack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (𝒳' : OpenSubstack 𝒳)
    (hqc : IsQuasiCompactStack.{u, w} B S hS
      (fullSubcategoryAlgebraicStack 𝒳 𝒳'.property 𝒳'.isAlgebraic).val
      (fullSubcategoryAlgebraicStack 𝒳 𝒳'.property 𝒳'.isAlgebraic).property)
    {I : Type*} (𝒰 : I → OpenSubstack 𝒳) (hle : 𝒳' ≤ OpenSubstack.iUnion 𝒰) :
    ∃ J : Finset I, 𝒳' ≤ OpenSubstack.iUnion (fun i : J => 𝒰 i) := by
  obtain ⟨J, hJ⟩ := exists_finset_pointSet_subset_of_isQuasiCompactStack B S hS 𝒳' hqc 𝒰
    fun T x hx => (OpenSubstack.isUnion_iUnion 𝒰).2 T x (hle _ hx)
  refine ⟨J, OpenSubstack.property_le_of_pointSet_subset B S hS ?_⟩
  rw [OpenSubstack.pointSet_iUnion]
  exact hJ.trans (Set.iUnion₂_subset fun i hi =>
    Set.subset_iUnion_of_subset (⟨i, hi⟩ : J) subset_rfl)

end AlgebraicGeometry.Stack

end
