module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.FiberPointSpecPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.IntegralTracePresheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceConstruction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GeometricPointSum

/-!
# The stalk of the integral trace map is the weighted sum over the geometric fibre

Let `f : X ⟶ Y` be a morphism of a big étale site which is locally of finite type and locally
quasi-finite as a morphism of schemes, let `w` be a weighting of it, and let `Z` be the constant
abelian sheaf with value `ULift ℤ`. The trace map `Tr : f_!Z ⟶ Z` of
`AlgebraicGeometry.SmallEtale.integralTrace` has, at a geometric point `s̄` of `Y`, the behaviour
Stacks 0GKG asks of it: read through the stalk decomposition `(f_!Z)_s̄ ≅ ⊕_{x̄ ↦ s̄} Z_x̄` of
Stacks 0F5F it is the sum over the geometric fibre of the weight of `x̄` times the identification
of `Z_x̄` with the coefficient group.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fiberPointChartEquiv` — the points of the geometric fibre lifting
  into the canonical open of a finite support, read as the `s̄`-points of that open over the
  chosen lift.
* `AlgebraicGeometry.SmallEtale.integralTraceStalkValueSummand` and
  `AlgebraicGeometry.SmallEtale.integralTraceStalkValue` — the weighted sum over the geometric
  fibre with values in the coefficient group, as a map out of the direct sum of the stalks.
* `AlgebraicGeometry.SmallEtale.integralTraceStalkMap` — **the weighted sum over the geometric
  fibre**, as a map from the direct sum of the stalks to the stalk of `Z` at `s̄`.
* `AlgebraicGeometry.SmallEtale.integralTraceFiberTerm` — the integer summand of that weighted
  sum attached to a supported section: the value of the section at the lift of a point of the
  geometric fibre times the weight of that point, and zero when the point does not lift.

## Main results

* `AlgebraicGeometry.SmallEtale.directSum_toAddMonoid_eq_finsum` and
  `AlgebraicGeometry.SmallEtale.finsum_subtype_eq_finsum` — a map out of a direct sum is the
  locally finite sum of its components, and a locally finite sum over a subtype is the sum over
  the whole type when the summand vanishes off the subtype.
* `AlgebraicGeometry.SmallEtale.fibreIntegral_eq_finsum_fiberPoints` — **the fibre integral at a
  geometric point is the weighted sum over the points of the geometric fibre which lift into the
  canonical open.**
* `AlgebraicGeometry.SmallEtale.etaleStalkLocallyConstantMapsAbIso_fiberStalkComponent` — the
  germ of a supported section at a point of the geometric fibre, read in the coefficient group,
  is the value of the section at the lift of that point.
* `AlgebraicGeometry.SmallEtale.integralTraceStalkValue_generator` and
  `AlgebraicGeometry.SmallEtale.integralTraceStalkValue_core` — the comparison on the generators
  of the double colimit, and its consequence for the whole stalk.
* `AlgebraicGeometry.SmallEtale.integralTrace_stalk` — **the stalk of the trace map is the
  weighted sum over the geometric fibre**, which is the characterisation of Stacks 0GKG.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 0F39](https://stacks.math.columbia.edu/tag/0F39)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v w

namespace AlgebraicGeometry.SmallEtale

/-! ### Sums over direct sums and subtypes -/

/-- A map out of a direct sum of abelian groups, evaluated at an element, is the locally finite
sum of the componentwise images. -/
public theorem directSum_toAddMonoid_eq_finsum {ι : Type*} [DecidableEq ι] {β : ι → Type*}
    [∀ i, AddCommGroup (β i)] {γ : Type*} [AddCommGroup γ] (φ : ∀ i, β i →+ γ) (x : ⨁ i, β i) :
    DirectSum.toAddMonoid φ x = ∑ᶠ i, φ i (x i) := by
  classical
  have hsub : Function.support (fun i => φ i (x i)) ⊆ (x.support : Set ι) := by
    intro i hi
    exact DFinsupp.mem_support_iff.2 fun h0 => hi (by simp [h0])
  rw [finsum_eq_sum_of_support_subset _ hsub]
  conv_lhs => rw [← DirectSum.sum_support_of x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => DirectSum.toAddMonoid_of φ i (x i)

/-- A locally finite sum over a subtype is the locally finite sum over the whole type, provided
the summand vanishes off the subtype. -/
public theorem finsum_subtype_eq_finsum {ι : Type*} {M : Type*} [AddCommMonoid M]
    (P : ι → Prop) (F : ι → M) (h : Function.support F ⊆ {i | P i}) :
    (∑ᶠ j : {i // P i}, F j.1) = ∑ᶠ i, F i := by
  have h1 : (∑ᶠ j : ({i | P i} : Set ι), F ↑j) = ∑ᶠ i ∈ ({i | P i} : Set ι), F i :=
    finsum_set_coe_eq_finsum_mem (f := F) _
  rwa [finsum_mem_def, Set.indicator_eq_self.2 h] at h1

/-! ### Composites of morphisms -/

/-- A morphism into a term of a diagram, followed by the colimit inclusion and a map induced on
colimits, is its composite with the component of the inducing transformation. -/
public theorem generator_comp_colim_map {J : Type*} [Category J] {A : Type*} [Category A]
    [HasColimitsOfShape J A] {F G : J ⥤ A} (α : F ⟶ G) (j : J) {S P T : A}
    (m : S ⟶ P) (e : P ⟶ F.obj j) (k : colim.obj G ⟶ T) {g : S ⟶ G.obj j}
    (hg : m ≫ e ≫ α.app j = g) :
    m ≫ e ≫ colimit.ι F j ≫ colim.map α ≫ k = g ≫ colimit.ι G j ≫ k := by
  subst hg
  simp

/-- If `m ≫ e ≫ n ≫ p = g`, then `m ≫ e ≫ n ≫ p ≫ k = g ≫ k`. -/
public theorem comp_assoc_four {A : Type*} [Category A] {S P Q R T : A}
    (m : S ⟶ P) (e : P ⟶ Q) (n : Q ⟶ R) (p : R ⟶ T) {T' : A} (k : T ⟶ T') {g : S ⟶ T}
    (hg : m ≫ e ≫ n ≫ p = g) :
    m ≫ e ≫ n ≫ p ≫ k = g ≫ k := by
  subst hg
  simp

/-- Two composites of abelian groups agree as soon as they agree on elements. -/
public theorem addCommGrpCat_comp_ext₃ {M N P Q R : AddCommGrpCat.{w}}
    (a₁ : M ⟶ N) (b₁ : N ⟶ P) (c₁ : P ⟶ R) (a₂ : M ⟶ Q) (b₂ : Q ⟶ R)
    (h : ∀ x, c₁ (b₁ (a₁ x)) = b₂ (a₂ x)) : a₁ ≫ b₁ ≫ c₁ = a₂ ≫ b₂ :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext h)

/-- A square commuting for the forward directions of two isomorphisms commutes for the backward
directions on the other diagonal. -/
public theorem iso_inv_comp_of_comp_hom {A : Type*} [Category A] {P Q R T : A}
    (α : P ≅ Q) (β : R ≅ T) (M : P ⟶ R) (N : Q ⟶ T) (h : M ≫ β.hom = α.hom ≫ N) :
    α.inv ≫ M = N ≫ β.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ### The fibre integral as a sum over the geometric fibre -/

section FibreSum

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (s : GeometricPoint Y.obj) (V : SmallEtale B Y.obj Y.property)
  (u : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B f V)

/-- The points of the geometric fibre which lift into the canonical open of a finite support,
read as the `s̄`-points of that open over the chosen lift of `s̄`, with the projection
`finiteSupportChartProj`. -/
public def fiberPointChartEquiv :
    {x : GeometricFiberPoint B f s // HasFiberLift B f s V u E x} ≃
      {q : s.source ⟶ (finiteSupportOpen B f V E).toScheme //
        q ≫ finiteSupportChartProj B f V E = u.1} :=
  fiberPointHasFiberLiftEquiv B f s V u E

/-- The `s̄`-point of the chart attached to a point of the geometric fibre, followed by the open
immersion, is the lift of that point to the base change. -/
public theorem fiberPointChartEquiv_comp_ι
    (x : {x : GeometricFiberPoint B f s // HasFiberLift B f s V u E x}) :
    (fiberPointChartEquiv B f s V u E x).1 ≫ (finiteSupportOpen B f V E).ι =
      fiberPointLift B f s V u x.1 :=
  fiberPointHasFiberLiftEquiv_apply_comp_ι B f s V u E x

/-- The `s̄`-point of the chart attached to a point of the geometric fibre, followed by the
structure map of the chart to `X`, is that point of the geometric fibre. -/
public theorem fiberPointChartEquiv_comp_toSource
    (x : {x : GeometricFiberPoint B f s // HasFiberLift B f s V u E x}) :
    (fiberPointChartEquiv B f s V u E x).1 ≫ finiteSupportChartToSource B f V E = x.1.1 := by
  rw [finiteSupportChartToSource, ← Category.assoc, fiberPointChartEquiv_comp_ι]
  exact fiberPointLift_comp_snd B f s V u x.1

/-- **The fibre integral at a geometric point is a sum over the geometric fibre.** The value of
the fibre integral of a locally constant section supported on a finite support, at the image of a
lift `ū` of `s̄` to `V`, is the sum over the points of the geometric fibre above `s̄` which lift
into the canonical open of the value of the section at that lift times the weight of the point. -/
public theorem fibreIntegral_eq_finsum_fiberPoints (w : X.obj → ℤ)
    {σ : (finiteSupportOpen B f V E).toScheme → ℤ} (hσ : IsLocallyConstant σ)
    (hsupp : ∀ p, σ p ≠ 0 → p ∈ (finiteSupportOpen B f V E).ι.base ⁻¹' E.1) :
    fibreIntegral (finiteSupportChartToSource B f V E)
        (finiteSupportChartProj B f V E) w hσ (u.1.base (default : ↥s.source)) =
      ∑ᶠ x : {x : GeometricFiberPoint B f s // HasFiberLift B f s V u E x},
        σ ((fiberPointChartEquiv B f s V u E x).1.base (default : ↥s.source)) *
          w (x.1.1.base (default : ↥s.source)) := by
  obtain ⟨Z, i, hi, hZ, hrange⟩ :=
    exists_isClosedImmersion_isFinite_range_finiteSupportChart B f V E
  have hpt : (default : ↥s.source) = IsLocalRing.closedPoint s.residueField :=
    Subsingleton.elim _ _
  have hfin : {p : (finiteSupportOpen B f V E).toScheme |
      (finiteSupportChartProj B f V E).base p =
          u.1.base (IsLocalRing.closedPoint s.residueField) ∧
        σ p * w (finiteSupportChartToSource B f V E p) ≠ 0}.Finite := by
    refine Set.Finite.subset (((i ≫ finiteSupportChartProj B f V E).finite_preimage_singleton
      (u.1.base (IsLocalRing.closedPoint s.residueField))).image i.base) ?_
    rintro p ⟨hp, hne⟩
    have hσp : σ p ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
    obtain ⟨z, rfl⟩ := hrange.ge (hsupp p hσp)
    exact ⟨z, hp, rfl⟩
  have hstep : fibreIntegral (finiteSupportChartToSource B f V E)
        (finiteSupportChartProj B f V E) w hσ (u.1.base (default : ↥s.source)) =
      ∑ᶠ q : {q : s.source ⟶ (finiteSupportOpen B f V E).toScheme //
          q ≫ finiteSupportChartProj B f V E = u.1},
        σ (q.1.base (IsLocalRing.closedPoint s.residueField)) *
          w (finiteSupportChartToSource B f V E
            (q.1.base (IsLocalRing.closedPoint s.residueField))) := by
    rw [fibreIntegral_eq_separableDegreeWeightedFiberSum_finiteSupportChart B f V E w hσ hsupp,
      hpt]
    exact separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_hom
      (finiteSupportChartProj B f V E)
      (fun p => σ p * w (finiteSupportChartToSource B f V E p)) u.1 hfin
  refine hstep.trans ((finsum_comp_equiv (fiberPointChartEquiv B f s V u E)).symm.trans
    (finsum_congr fun x => ?_))
  rw [← hpt]
  exact congrArg
    (fun z => σ ((fiberPointChartEquiv B f s V u E x).1.base (default : ↥s.source)) * w z)
    (congrArg (fun m : s.source ⟶ X.obj => m.base (default : ↥s.source))
      (fiberPointChartEquiv_comp_toSource B f s V u E x))

end FibreSum

/-! ### The weighted sum on the stalks over the geometric fibre -/

section StalkMap

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (w : X.obj → ℤ) (s : GeometricPoint Y.obj)

/-- The summand of the weighted sum over the geometric fibre indexed by a point `x̄` of the
fibre, with values in the coefficient group: the germ at `x̄` is read as its value in the
coefficient group and multiplied by the weight of `x̄`. -/
public def integralTraceStalkValueSummand (x : GeometricFiberPoint B f s) :
    ↥(etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
        (locallyConstantMapsAbSmallEtale.{u, v} B X.obj X.property TraceCoeff.{u, v})) →+
      TraceCoeff.{u, v} :=
  AddMonoidHom.mk'
    (fun z => w (x.1.base (default : ↥s.source)) •
      (etaleStalkLocallyConstantMapsAbIso.{u, v} B X.obj X.property
        (x.toGeometricPoint B f s) TraceCoeff.{u, v}).hom z)
    (fun a b => by rw [map_add, smul_add])

/-- The weighted sum over the geometric fibre, with values in the coefficient group. -/
public def integralTraceStalkValue :
    AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B f s
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})) ⟶
      AddCommGrpCat.of TraceCoeff.{u, v} :=
  letI := Classical.decEq (GeometricFiberPoint B f s)
  AddCommGrpCat.ofHom (DirectSum.toAddMonoid (integralTraceStalkValueSummand.{u, v} B f w s))

/-- **The weighted sum over the geometric fibre.** The summand indexed by a point `x̄` of the
geometric fibre above `s̄` reads the germ at `x̄` as its value in the coefficient group, multiplies
that value by the weight of `x̄`, and puts it back in the stalk of the constant sheaf at `s̄`. -/
public def integralTraceStalkMap :
    AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B f s
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})) ⟶
      etaleStalk B Y.obj Y.property s
        (locallyConstantMapsAbSmallEtale.{u, v} B Y.obj Y.property TraceCoeff.{u, v}) :=
  integralTraceStalkValue.{u, v} B f w s ≫
    (etaleStalkLocallyConstantMapsAbIso.{u, v} B Y.obj Y.property s TraceCoeff.{u, v}).inv

/-- The weighted sum over the geometric fibre is the coefficient-valued weighted sum followed by
the identification of the coefficient group with the stalk at `s̄`. -/
public theorem integralTraceStalkMap_eq :
    integralTraceStalkMap.{u, v} B f w s =
      integralTraceStalkValue.{u, v} B f w s ≫
        (etaleStalkLocallyConstantMapsAbIso.{u, v} B Y.obj Y.property s TraceCoeff.{u, v}).inv :=
  rfl

/-- The coefficient-valued weighted sum on the summand indexed by a point of the geometric
fibre. -/
public theorem integralTraceStalkValue_fiberStalkOf (x : GeometricFiberPoint B f s)
    (z : ↥(etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
      (locallyConstantMapsAbSmallEtale.{u, v} B X.obj X.property TraceCoeff.{u, v}))) :
    integralTraceStalkValue.{u, v} B f w s
        (fiberStalkOf.{u, v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) x z) =
      w (x.1.base (default : ↥s.source)) •
        (etaleStalkLocallyConstantMapsAbIso.{u, v} B X.obj X.property
          (x.toGeometricPoint B f s) TraceCoeff.{u, v}).hom z := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact DirectSum.toAddMonoid_of (integralTraceStalkValueSummand.{u, v} B f w s) x z

/-- The weighted sum over the geometric fibre on the summand indexed by a point of the fibre. -/
public theorem integralTraceStalkMap_fiberStalkOf (x : GeometricFiberPoint B f s)
    (z : ↥(etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
      (locallyConstantMapsAbSmallEtale.{u, v} B X.obj X.property TraceCoeff.{u, v}))) :
    integralTraceStalkMap.{u, v} B f w s
        (fiberStalkOf.{u, v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) x z) =
      w (x.1.base (default : ↥s.source)) •
        (etaleStalkLocallyConstantMapsAbIso.{u, v} B Y.obj Y.property s TraceCoeff.{u, v}).inv
          ((etaleStalkLocallyConstantMapsAbIso.{u, v} B X.obj X.property
            (x.toGeometricPoint B f s) TraceCoeff.{u, v}).hom z) := by
  show (etaleStalkLocallyConstantMapsAbIso.{u, v} B Y.obj Y.property s TraceCoeff.{u, v}).inv
      (integralTraceStalkValue.{u, v} B f w s
        (fiberStalkOf.{u, v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) x z)) = _
  rw [integralTraceStalkValue_fiberStalkOf.{u, v} B f w s x z, map_zsmul]

end StalkMap

/-! ### The germs of a supported section at the points of the geometric fibre -/

section Germ

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (w : X.obj → ℤ) (s : GeometricPoint Y.obj) (V : SmallEtale B Y.obj Y.property)
  (u : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B f V)

/-- The lift of a point of the geometric fibre into the canonical open of a finite support is the
`s̄`-point of the chart attached to it. -/
public theorem openObjectLift_base_eq_fiberPointChartEquiv (x : GeometricFiberPoint B f s)
    (h : HasFiberLift B f s V u E x) :
    (openObjectLift B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f V)
          (fiberPointElement B f s V u x) (finiteSupportOpen B f V E) h).1.base
        (default : ↥s.source) =
      (fiberPointChartEquiv B f s V u E ⟨x, h⟩).1.base (default : ↥s.source) := rfl

open Classical in
/-- **The germ of a supported section at a point of the geometric fibre, read in the coefficient
group, is the value of the section at the lift of that point** — and zero when the point does not
lift into the canonical open. -/
public theorem etaleStalkLocallyConstantMapsAbIso_fiberStalkComponent
    (a : integralTraceSections.{u, v} B f V E) (x : GeometricFiberPoint B f s) :
    (etaleStalkLocallyConstantMapsAbIso.{u, v} B X.obj X.property
          (x.toGeometricPoint B f s) TraceCoeff.{u, v}).hom
        (fiberStalkComponent.{u, max (u + 1) v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V u E a x) =
      if h : HasFiberLift B f s V u E x then
        ULift.up (integralTraceSectionFun.{u, v} B f V E a
          ((fiberPointChartEquiv B f s V u E ⟨x, h⟩).1.base (default : ↥s.source)))
      else 0 := by
  by_cases h : HasFiberLift B f s V u E x
  · rw [dif_pos h]
    refine Eq.trans (congrArg (fun z => (etaleStalkLocallyConstantMapsAbIso.{u, v} B X.obj
          X.property (x.toGeometricPoint B f s) TraceCoeff.{u, v}).hom z)
        (fiberStalkComponent_of_hasFiberLift.{u, max (u + 1) v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V u E a x h)) ?_
    exact etaleStalkLocallyConstantMapsAbIso_etaleGerm.{u, v} B X.obj X.property
      (x.toGeometricPoint B f s) TraceCoeff.{u, v} (finiteSupportOpenObject B f V E)
      (openObjectLift B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f V)
        (fiberPointElement B f s V u x) (finiteSupportOpen B f V E) h)
      (asLocallyConstant.{u, v} B X.obj X.property TraceCoeff.{u, v}
        (finiteSupportOpenObject B f V E) a.val)
  · rw [dif_neg h, fiberStalkComponent_of_not_hasFiberLift.{u, max (u + 1) v} B f s
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V u E a x h]
    exact map_zero _

open Classical in
/-- The integer summand of the weighted sum over the geometric fibre attached to a supported
section: the value of the section at the lift of a point of the geometric fibre times the weight
of that point, and zero when the point does not lift into the canonical open. -/
public def integralTraceFiberTerm (a : integralTraceSections.{u, v} B f V E)
    (x : GeometricFiberPoint B f s) : ℤ :=
  if h : HasFiberLift B f s V u E x then
    integralTraceSectionFun.{u, v} B f V E a
        ((fiberPointChartEquiv B f s V u E ⟨x, h⟩).1.base (default : ↥s.source)) *
      w (x.1.base (default : ↥s.source))
  else 0

/-- The integer summand at a point of the geometric fibre which lifts into the canonical open. -/
public theorem integralTraceFiberTerm_of_hasFiberLift
    (a : integralTraceSections.{u, v} B f V E) (x : GeometricFiberPoint B f s)
    (h : HasFiberLift B f s V u E x) :
    integralTraceFiberTerm.{u, v} B f w s V u E a x =
      integralTraceSectionFun.{u, v} B f V E a
          ((fiberPointChartEquiv B f s V u E ⟨x, h⟩).1.base (default : ↥s.source)) *
        w (x.1.base (default : ↥s.source)) :=
  dite_eq_left h

/-- The integer summand vanishes at a point of the geometric fibre which does not lift into the
canonical open. -/
public theorem integralTraceFiberTerm_of_not_hasFiberLift
    (a : integralTraceSections.{u, v} B f V E) (x : GeometricFiberPoint B f s)
    (h : ¬ HasFiberLift B f s V u E x) :
    integralTraceFiberTerm.{u, v} B f w s V u E a x = 0 :=
  dite_eq_right h

/-- The summand of the weighted sum over the geometric fibre, evaluated at the germ of a
supported section, is the integer summand lifted to the coefficient group. -/
public theorem integralTraceStalkValueSummand_fiberStalkComponent
    (a : integralTraceSections.{u, v} B f V E) (x : GeometricFiberPoint B f s) :
    integralTraceStalkValueSummand.{u, v} B f w s x
        (fiberStalkComponent.{u, max (u + 1) v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V u E a x) =
      ULift.up (integralTraceFiberTerm.{u, v} B f w s V u E a x) := by
  show w (x.1.base (default : ↥s.source)) •
      (etaleStalkLocallyConstantMapsAbIso.{u, v} B X.obj X.property
        (x.toGeometricPoint B f s) TraceCoeff.{u, v}).hom
        (fiberStalkComponent.{u, max (u + 1) v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V u E a x) = _
  rw [etaleStalkLocallyConstantMapsAbIso_fiberStalkComponent.{u, v} B f s V u E a x]
  by_cases h : HasFiberLift B f s V u E x
  · rw [dif_pos h, integralTraceFiberTerm_of_hasFiberLift.{u, v} B f w s V u E a x h]
    exact congrArg ULift.up (mul_comm _ _)
  · rw [dif_neg h, integralTraceFiberTerm_of_not_hasFiberLift.{u, v} B f w s V u E a x h,
      smul_zero]
    rfl

/-- The coefficient-valued weighted sum over the geometric fibre of the germ decomposition of a
supported section is the locally finite sum of the integer summands. -/
public theorem integralTraceStalkValue_fiberStalkSum
    (a : integralTraceSections.{u, v} B f V E) :
    integralTraceStalkValue.{u, v} B f w s
        (fiberStalkSum.{u, max (u + 1) v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V u E a) =
      ULift.up (∑ᶠ x : GeometricFiberPoint B f s,
        integralTraceFiberTerm.{u, v} B f w s V u E a x) := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  have h1 : integralTraceStalkValue.{u, v} B f w s
        (fiberStalkSum.{u, max (u + 1) v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V u E a) =
      ∑ᶠ x : GeometricFiberPoint B f s, integralTraceStalkValueSummand.{u, v} B f w s x
        (fiberStalkComponent.{u, max (u + 1) v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V u E a x) := by
    show DirectSum.toAddMonoid (integralTraceStalkValueSummand.{u, v} B f w s)
      (fiberStalkSum.{u, max (u + 1) v} B f s
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V u E a) = _
    exact directSum_toAddMonoid_eq_finsum _ _
  refine h1.trans ((finsum_congr (integralTraceStalkValueSummand_fiberStalkComponent.{u, v}
    B f w s V u E a)).trans ?_)
  exact (AddEquiv.map_finsum (AddEquiv.ulift.symm : ℤ ≃+ TraceCoeff.{u, v})
    (integralTraceFiberTerm.{u, v} B f w s V u E a)).symm

end Germ

/-! ### The stalk of the trace map -/

section Stalk

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {w : X.obj → ℤ} (hw : IsWeighting (B.inclusion.map f) w)

/-- **The comparison on a generator of the double colimit.** For a section `a` supported on a
finite support `E` over an étale neighbourhood `(V, ū)` of `s̄`, the value of the fibre integral at
the image of `ū` is the weighted sum of the germs of `a` at the points of the geometric fibre. -/
public theorem integralTraceStalkValue_generator (s : GeometricPoint Y.obj)
    (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B f V)
    (a : integralTraceSections.{u, v} B f V E) :
    integralTraceGenerator.{u, v} B f hw V E a (u.1.base (default : ↥s.source)) =
      integralTraceStalkValue.{u, v} B f w s
        (fiberStalkSum.{u, max (u + 1) v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V u E a) := by
  rw [integralTraceStalkValue_fiberStalkSum.{u, v} B f w s V u E a,
    integralTraceGenerator_apply.{u, v} B f hw V E a]
  refine congrArg ULift.up ?_
  rw [fibreIntegral_eq_finsum_fiberPoints B f s V u E w
    (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E a)
    (integralTraceSectionFun_support.{u, v} B f V E a)]
  refine Eq.trans (finsum_congr fun j => ?_)
    (finsum_subtype_eq_finsum (fun x => HasFiberLift B f s V u E x)
      (integralTraceFiberTerm.{u, v} B f w s V u E a) fun x hx => ?_)
  · exact (integralTraceFiberTerm_of_hasFiberLift.{u, v} B f w s V u E a j.1 j.2).symm
  · by_contra hc
    exact hx (integralTraceFiberTerm_of_not_hasFiberLift.{u, v} B f w s V u E a x hc)

/-- **The stalk of the trace map of presheaves, read in the coefficient group, is the weighted
sum over the geometric fibre.** The map induced on stalks at `s̄` by the trace map of presheaves,
followed by the identification of the stalk of the constant sheaf with the coefficient group, is
the stalk decomposition followed by the coefficient-valued weighted sum over the geometric
fibre. -/
public theorem integralTraceStalkValue_core (s : GeometricPoint Y.obj) :
    colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
          (integralTracePresheafMap.{u, v} B f hw)) ≫
        (etaleStalkLocallyConstantMapsAbIso.{u, v} B Y.obj Y.property s TraceCoeff.{u, v}).hom =
      (finiteSupportStalkIso.{u, max (u + 1) v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})
          (fun _ => inferInstance)).hom ≫
        integralTraceStalkValue.{u, v} B f w s := by
  apply colimit.hom_ext
  rintro ⟨U⟩
  apply (cancel_epi (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
    (fun _ => inferInstance)).2.obj_eq
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) U.1).symm)).1
  apply colimit.hom_ext
  intro E
  refine Eq.trans (generator_comp_colim_map
      (Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
        (integralTracePresheafMap.{u, v} B f hw)) (op U) _ _ _
      (integralTracePresheafMap_ι.{u, v} B f hw U.1 E))
    (Eq.trans ?_ (comp_assoc_four _ _ _ _ _
      (finiteSupportStalkToFiberStalks_generator.{u, max (u + 1) v} B f s
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})
        (fun _ => inferInstance) U E)).symm)
  refine addCommGrpCat_comp_ext₃ _ _ _ _ _ fun a => ?_
  exact (etaleStalkLocallyConstantMapsAbIso_etaleGerm.{u, v} B Y.obj Y.property s
      TraceCoeff.{u, v} U.1 U.2 (integralTraceGenerator.{u, v} B f hw U.1 E a)).trans
    (integralTraceStalkValue_generator.{u, v} B f hw s U.1 U.2 E a)

/-- **The stalk of the trace map is the weighted sum over the geometric fibre.** At a geometric
point `s̄` of `Y` the map `Tr : f_!Z ⟶ Z` induces on stalks, read through the decomposition
`(f_!Z)_s̄ ≅ ⊕_{x̄ ↦ s̄} Z_x̄` of Stacks 0F5F, the sum over the geometric fibre of the weight
of `x̄` times the identification of `Z_x̄` with the coefficient group. This is the behaviour
Stacks 0GKG asks of the trace map. -/
public theorem integralTrace_stalk (s : GeometricPoint Y.obj) :
    (fShriekStalkIso.{u, v} B f s
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})).inv ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
          (integralTrace.{u, v} B f hw).1) =
      integralTraceStalkMap.{u, v} B f w s := by
  have hS := iso_inv_comp_of_comp_hom
    (finiteSupportStalkIso.{u, max (u + 1) v} B f s
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})
      (fun _ => inferInstance))
    (etaleStalkLocallyConstantMapsAbIso.{u, v} B Y.obj Y.property s TraceCoeff.{u, v})
    _ _ (integralTraceStalkValue_core.{u, v} B f hw s)
  rw [← toSheafify_integralTrace.{u, v} B f hw] at hS
  refine Eq.trans ?_ hS
  rw [Functor.whiskerLeft_comp, colim.map_comp]
  rfl

end Stalk

end AlgebraicGeometry.SmallEtale

end
