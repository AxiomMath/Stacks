module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties

/-!
# A criterion for reasonableness in terms of generic points

Let `X` be an algebraic space over a scheme `S`. If every quasi-compact scheme étale over `X`
has finitely many irreducible components, and every point of `X` of codimension zero is
represented by a monomorphism from the spectrum of a field, then `X` is reasonable.

## Main results

* `AlgebraicGeometry.Space.isReasonableSpace_of_finite_irreducibleComponents_of_mono`
  is Stacks 0BB8.

## Implementation notes

Reasonableness is taken in the form `AlgebraicGeometry.Space.IsReasonableSpace`, condition (2)
of Stacks 03JT: every étale chart by an affine scheme has universally bounded fibres in the
sense of Stacks 03JL. So a chart `φ : h_U ⟶ X` with `U` affine is fixed and one integer is
produced bounding the degree of every field-valued fibre of `φ`.

The bound comes from the generic points of `U`. A point of `X` below a generic point of an
étale chart has codimension zero (Stacks 0BAQ), so the hypothesis supplies a monomorphic
field-valued representative of it; the fibre of `φ` over such a representative injects into the
generic points of `U`, because a monomorphism of algebraic spaces is injective on points
(Stacks 06RV), and is therefore a *finite* set. Being also étale over the spectrum of a field
it is finite locally free of some degree, and the supremum `n` of those finitely many degrees
is the bound sought.

That `n` bounds the degree over *every* field-valued point, not only over those coming from a
generic point, is where the degree stratification of Stacks 086T enters. Its chain of open
subspaces `X = X₀ ⊇ X₁ ⊇ …` is pulled back along `φ` to an open subscheme `V ⊆ U`. No generic
point of `U` lies in `V`, by the choice of `n`; since every point of a scheme is a
specialization of a generic point and `V` is open, `V` is empty; and a field-valued point of a
nonempty stratum would have a nonempty fibre, hence give a point of `V`. So the stratum
`X_{n+1}` has no points, no field-valued point of `X` factors through it, and every fibre of
`φ` is finite locally free of degree at most `n`.

## References

* [Stacks Project, Tag 0BB8](https://stacks.math.columbia.edu/tag/0BB8)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Two facts with no algebraic spaces in them -/

/-- In a quasi-sober space every point is a specialization of the generic point of some
irreducible component. -/
private theorem exists_mem_genericPoints_specializes {Y : Type*} [TopologicalSpace Y]
    [QuasiSober Y] (y : Y) : ∃ η ∈ genericPoints Y, η ⤳ y := by
  obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({y} : Set Y)) isIrreducible_singleton.closure
  refine ⟨(genericPoints.ofComponent ⟨C, hC⟩ : genericPoints Y).1,
    (genericPoints.ofComponent ⟨C, hC⟩).2, ?_⟩
  rw [specializes_iff_mem_closure, genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩]
  exact hyC (subset_closure (Set.mem_singleton y))

/-- An open subset of a quasi-sober space containing no generic point of an irreducible
component is empty. -/
private theorem eq_empty_of_forall_genericPoints_notMem {Y : Type*} [TopologicalSpace Y]
    [QuasiSober Y] {V : Set Y} (hV : IsOpen V) (h : ∀ η ∈ genericPoints Y, η ∉ V) :
    V = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
  obtain ⟨η, hη, hspec⟩ := exists_mem_genericPoints_specializes y
  exact hV.not_specializes (h η hη) hy hspec

/-- A finite étale morphism to the spectrum of a field is finite locally free of some degree:
its fibre degree is constant because the target has a single point. -/
@[ega "IV 18.2.7" "special case"]
private theorem exists_isFiniteLocallyFreeOfRank_of_etale_of_isFinite {k : Type u} [Field k]
    {A : Scheme.{u}} (f : A ⟶ Spec (.of k)) [_root_.AlgebraicGeometry.Etale f]
    [_root_.AlgebraicGeometry.IsFinite f] : ∃ r : ℕ, IsFiniteLocallyFreeOfRank f r := by
  have hlqf := _root_.AlgebraicGeometry.locallyQuasiFinite_of_etale f
  have : LocallyOfFiniteType f := hlqf.1
  have : LocallyQuasiFinite f := hlqf.2
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨s, hs, -⟩ := existsUnique_rank_of_bounded_fiber f
    (_root_.AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite f)
    (default : Spec (.of k))
  exact ⟨s, rank_of_constant_fiber_rank f s fun t ↦ by
    rwa [Subsingleton.elim t (default : Spec (.of k))]⟩

/-- A fibre which is finite locally free of degree at most `n` does not have degree at least
`n + 1`, the degree of a finite locally free morphism over a field being unique. -/
private theorem not_degreeGe_succ_of_isFiniteLocallyFreeOfRank_le {k : Type u} [Field k]
    {A : Scheme.{u}} (f : A ⟶ Spec (.of k)) {r n : ℕ} (hr : IsFiniteLocallyFreeOfRank f r)
    (hrn : r ≤ n) : ¬ DegreeGe f (n + 1) := by
  rintro (hnf | ⟨t, htn, ht⟩)
  · exact hnf ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).1
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (h := hr) f r)).1
  · have : r = t := finiteLocallyFree_rank_unique f r t hr ht
    omega

/-- Having degree at least `n + 1` forces the fibre to be nonempty: a morphism with empty
source is finite locally free of degree zero. -/
private theorem nonempty_of_degreeGe_succ {k : Type u} [Field k] {A : Scheme.{u}}
    (f : A ⟶ Spec (.of k)) {n : ℕ} (h : DegreeGe f (n + 1)) : Nonempty A := by
  by_contra hA
  have : IsEmpty A := not_nonempty_iff.mp hA
  exact not_degreeGe_succ_of_isFiniteLocallyFreeOfRank_le f
    (isFiniteLocallyFreeOfRank_zero_of_isEmpty f) n.zero_le h

/-! ### Reading an open set of points on the representing scheme -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private theorem mem_iff_pointsToScheme_mem {U : BigFppfOver B S hS}
    {W : Set (points B S hS (yoneda.obj U))}
    {V : Set ((BigFppfOver.toScheme B S hS).obj U)}
    (h : ∀ q : FieldValuedPoint B S hS (yoneda.obj U),
      q.class B S hS (yoneda.obj U) ∈ W ↔ schemePoint B S hS U q ∈ V)
    (z : points B S hS (yoneda.obj U)) :
    z ∈ W ↔ pointsToScheme B S hS U z ∈ V :=
  Quot.inductionOn z h

/-- A field-valued point factors through an open subspace exactly when the point it represents
lies in the point set of that subspace.

The point set of the tautological chart of a field-valued point is the single point it
represents, so the criterion of Stacks 03IE for that chart reduces to one membership. -/
private theorem exists_comp_ι_iff_class_mem_range
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (G : Subfunctor X) (hG : IsOpenSubspace B S hS G) (p : FieldValuedPoint B S hS X) :
    (∃ g, g ≫ G.ι = yonedaEquiv.symm p.value) ↔
      p.class B S hS X ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  rw [factorsThrough_openSubspace_iff_points B S hS hX
    (isAlgebraicSpace_yoneda B S hS _) G hG (yonedaEquiv.symm p.value)]
  refine ⟨fun h ↦ h ((range_pointsMap_yonedaEquiv_symm B S hS p).ge rfl), fun h y hy ↦ ?_⟩
  have hy' := (range_pointsMap_yonedaEquiv_symm B S hS p).subset hy
  rw [Set.mem_singleton_iff] at hy'
  exact hy' ▸ h

/-! ### The fibre of a chart over a monomorphic field-valued point -/

/-- Every point of the fibre of a chart `φ` over a field-valued point `p` of the target lies, in
the chart, above the point represented by `p`. -/
private theorem pointsMap_fst'_eq_class {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
    (hrep : yoneda.relativelyRepresentable φ) (p : FieldValuedPoint B S hS X)
    (z : points B S hS
      (yoneda.obj (hrep.pullback (yonedaEquiv.symm p.value)))) :
    pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS _
          (yoneda.map (hrep.fst' (yonedaEquiv.symm p.value))) z) =
      p.class B S hS X := by
  have hmem : pointsMap B S hS (yoneda.obj p.siteObject) (yonedaEquiv.symm p.value)
      (pointsMap B S hS _
        (yoneda.map (hrep.snd (yonedaEquiv.symm p.value))) z) ∈
      Set.range (pointsMap B S hS (yoneda.obj p.siteObject)
        (yonedaEquiv.symm p.value)) := Set.mem_range_self _
  rw [range_pointsMap_yonedaEquiv_symm, Set.mem_singleton_iff] at hmem
  rw [← pointsMap_comp_apply, (hrep.isPullback' (yonedaEquiv.symm p.value)).w,
    pointsMap_comp_apply]
  exact hmem

/-- Each point of the fibre of an étale chart over a monomorphic field-valued representative of
a point of codimension zero maps to a generic point of an irreducible component of the chart.

This is Stacks 0BAQ, condition (3), read at the point of the chart underlying the given point
of the fibre. -/
private theorem mem_genericPoints_of_mem_fibre {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
    (hφ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (p : FieldValuedPoint B S hS X)
    (hdim : localRingDimension B S hS (p.class B S hS X) = 0)
    (v : (BigFppfOver.toScheme B S hS).obj
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).pullback
        (yonedaEquiv.symm p.value))) :
    (BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).fst'
          (yonedaEquiv.symm p.value)) v ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj U) := by
  have hchart := chartPoint_pointsToScheme B S hS U φ
    (pointsMap B S hS _
      (yoneda.map ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).fst'
        (yonedaEquiv.symm p.value)))
      ((schemePointRepresentative B S hS
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).pullback
          (yonedaEquiv.symm p.value)) v).class B S hS (yoneda.obj _)))
  rw [pointsToScheme_pointsMap, pointsToScheme_class,
    schemePointRepresentative_point,
    pointsMap_fst'_eq_class B S hS
      (relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ) p] at hchart
  exact (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX
    (p.class B S hS X)).mp hdim U φ _
    ((isEtale_iff_presheaf_of_yoneda B S hS φ).mpr hφ) hchart

/-- A morphism of the site whose Yoneda image is a monomorphism is injective on the points of
the underlying schemes: the points of a represented presheaf are the points of the representing
scheme, and a monomorphism of presheaves is injective on points by Stacks 06RV. -/
private theorem injective_toScheme_map_of_mono_yoneda_map {V U : BigFppfOver B S hS}
    (j : V ⟶ U) (hj : Mono (yoneda.map j)) :
    Function.Injective ((BigFppfOver.toScheme B S hS).map j) := by
  have : Mono (yoneda.map j) := hj
  intro x y hxy
  obtain ⟨zx, hzx⟩ := surjective_pointsToScheme B S hS V x
  obtain ⟨zy, hzy⟩ := surjective_pointsToScheme B S hS V y
  have hkey : pointsMap B S hS (yoneda.obj V) (yoneda.map j) zx =
      pointsMap B S hS (yoneda.obj V) (yoneda.map j) zy := by
    refine injective_pointsToScheme B S hS U ?_
    rw [pointsToScheme_pointsMap, pointsToScheme_pointsMap, hzx, hzy]
    exact hxy
  rw [← hzx, ← hzy, pointsMap_injective_of_mono B S hS (yoneda.map j) hkey]

/-- **The fibre of an étale chart over a monomorphic point of codimension zero is finite locally
free.** Let `φ : h_U ⟶ X` be an étale chart of an algebraic space over `S` whose source has
only finitely many generic points, and let `p` be a field-valued point of `X` of codimension
zero whose associated morphism is a monomorphism. Then the fibre of `φ` over `p` is finite
locally free of some degree.

The fibre maps injectively into the generic points of `U`: its projection to `h_U` is a
monomorphism, being a base change of one, so it is injective on points, and each of its points
lands on a generic point by Stacks 0BAQ. So the fibre is a finite set, hence quasi-compact, and
being étale and locally quasi-finite over the spectrum of a field with quasi-compact source it
is finite, hence finite locally free of a degree. -/
private theorem exists_isFiniteLocallyFreeOfRank_snd_of_mono
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
    (hφ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hgenfin : (genericPoints ((BigFppfOver.toScheme B S hS).obj U)).Finite)
    (p : FieldValuedPoint B S hS X) (hmono : Mono (yonedaEquiv.symm p.value))
    (hdim : localRingDimension B S hS (p.class B S hS X) = 0) :
    ∃ r : ℕ, IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
        (yonedaEquiv.symm p.value))) r := by
  classical
  have hmono' : Mono (yonedaEquiv.symm p.value) := hmono
  have hpb : IsPullback
      (yoneda.map ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).fst'
        (yonedaEquiv.symm p.value)))
      (yoneda.map ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
        (yonedaEquiv.symm p.value))) φ (yonedaEquiv.symm p.value) :=
    (relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).isPullback' _
  have hmonoj : Mono (yoneda.map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).fst'
        (yonedaEquiv.symm p.value))) := hpb.mono_fst_of_mono
  have hinj := injective_toScheme_map_of_mono_yoneda_map B S hS
    ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).fst'
      (yonedaEquiv.symm p.value)) hmonoj
  have hgenf : Finite (genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :=
    hgenfin.to_subtype
  have hZfin : Finite ((BigFppfOver.toScheme B S hS).obj
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).pullback
        (yonedaEquiv.symm p.value))) :=
    Finite.of_injective
      (fun v ↦ (⟨_, mem_genericPoints_of_mem_fibre B S hS hX hφ p hdim v⟩ :
        genericPoints ((BigFppfOver.toScheme B S hS).obj U)))
      fun x y hxy ↦ hinj (congrArg Subtype.val hxy)
  have hetale : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
        (yonedaEquiv.symm p.value))) :=
    hφ.property_snd _
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
        (yonedaEquiv.symm p.value))) := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    intro W _
    exact (Set.toFinite (((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
        (yonedaEquiv.symm p.value))) ⁻¹' (W : Set _))).isCompact
  have hart : IsLocallyArtinian (Spec (CommRingCat.of p.carrier)) := inferInstance
  have hlqf : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
        (yonedaEquiv.symm p.value))) :=
    (_root_.AlgebraicGeometry.locallyQuasiFinite_of_etale _).2
  have hfin : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
        (yonedaEquiv.symm p.value))) :=
    @_root_.AlgebraicGeometry.IsFinite.of_locallyQuasiFinite _ _ _ hlqf hqc hart
  exact exists_isFiniteLocallyFreeOfRank_of_etale_of_isFinite (k := p.carrier) _

/-! ### From a universal degree bound to universally bounded fibres -/

/-- **The bound of Stacks 03JL from a bound on every field-valued fibre.** If no field-valued
fibre of a chart `φ : h_U ⟶ X` of an algebraic space over `S` has degree at least `n + 1`, then
the fibres of `φ` are universally bounded with bound `n`.

Stacks 03JL quantifies over a site object together with an isomorphism to a field spectrum,
whereas the degree condition is attached to a field-valued point in the sense of Stacks 03BU;
`AlgebraicGeometry.Space.exists_fieldValuedPoint_degreeGe_iff` passes between the two. -/
private theorem hasUniversallyBoundedFibers_of_forall_not_degreeGe_succ
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
    (hφ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) (n : ℕ)
    (hbound : ∀ p : FieldValuedPoint B S hS X,
      ¬ DegreeGe ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
          (yonedaEquiv.symm p.value))) (n + 1)) :
    HasUniversallyBoundedFibers B S hS U φ := by
  classical
  refine ⟨(n : ℤ), ?_⟩
  intro k _ A e ξ
  obtain ⟨p, -, hdeg⟩ := exists_fieldValuedPoint_degreeGe_iff B S hS hX φ k A e ξ
  have hnd : ¬ DegreeGe ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd ξ)) (n + 1) :=
    fun h ↦ hbound p ((hdeg (n + 1)).1 h)
  rw [degreeGe_iff, not_or, not_not, not_exists] at hnd
  obtain ⟨hfin, hno⟩ := hnd
  have hfin' : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd ξ)) := hfin
  have hetale : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd ξ)) :=
    hφ.property_snd _
  obtain ⟨r, hr⟩ := exists_isFiniteLocallyFreeOfRank_of_etale_of_isFinite
    (k := k) ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd ξ) ≫ e.hom)
  have hrank : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd ξ)) r :=
    ((IsFiniteLocallyFreeOfRank.property.{u} r).cancel_right_of_respectsIso
      ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd ξ)) e.hom).1 hr
  have hrn : r ≤ n := by
    by_contra hcon
    exact hno r ⟨by omega, hrank⟩
  exact ⟨(relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).pullback ξ,
    (relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd ξ,
    (relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).fst ξ, r,
    by exact_mod_cast hrn, hrank,
    (relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).isPullback ξ⟩

/-! ### Stacks 0BB8 -/

/-- **Stacks 0BB8.** An algebraic space over a scheme `S` is reasonable as soon as every
quasi-compact scheme étale over it has finitely many irreducible components and every one of
its points of codimension zero is represented by a monomorphism from the spectrum of a
field. -/
@[stacks 0BB8]
theorem isReasonableSpace_of_finite_irreducibleComponents_of_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hfinite : ∀ U : BigFppfOver B S hS,
      CompactSpace ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ f : yoneda.obj U ⟶ X,
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) f →
        (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)).Finite)
    (hgeneric : ∀ x : points B S hS X, localRingDimension B S hS x = 0 →
      ∃ p : FieldValuedPoint B S hS X,
        p.class B S hS X = x ∧ Mono (yonedaEquiv.symm p.value)) :
    IsReasonableSpace B S hS X := by
  classical
  intro U hU φ hφ
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hUcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
  have hgenfin : (genericPoints ((BigFppfOver.toScheme B S hS).obj U)).Finite :=
    genericPoints.finite (hfinite U hUcpt φ hφ)
  let _ : Fintype (genericPoints ((BigFppfOver.toScheme B S hS).obj U)) := hgenfin.fintype
  -- A monomorphic representative and the degree of the fibre above it, for each generic point.
  have hdata : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U),
      ∃ (p : FieldValuedPoint B S hS X) (r : ℕ),
        (∀ z : points B S hS (yoneda.obj U), pointsToScheme B S hS U z = η.1 →
            pointsMap B S hS (yoneda.obj U) φ z = p.class B S hS X) ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
            ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
              (yonedaEquiv.symm p.value))) r := by
    intro η
    obtain ⟨z₀, hz₀⟩ := surjective_pointsToScheme B S hS U η.1
    have hdim0 : localRingDimension B S hS
        (pointsMap B S hS (yoneda.obj U) φ z₀) = 0 := by
      refine (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX _).mpr
        ⟨U, φ, η.1, (isEtale_iff_presheaf_of_yoneda B S hS φ).mpr hφ, ?_, η.2⟩
      exact hz₀ ▸ chartPoint_pointsToScheme B S hS U φ z₀
    obtain ⟨p, hpc, hpm⟩ := hgeneric _ hdim0
    obtain ⟨r, hr⟩ := exists_isFiniteLocallyFreeOfRank_snd_of_mono B S hS hX hφ hgenfin p hpm
      (hpc ▸ hdim0)
    refine ⟨p, r, fun z hz ↦ ?_, hr⟩
    rw [injective_pointsToScheme B S hS U (hz.trans hz₀.symm), hpc]
  choose pη rη hpηz hrηrank using hdata
  obtain ⟨n, hnle⟩ : ∃ n : ℕ, ∀ η, rη η ≤ n :=
    ⟨Finset.univ.sup rη, fun η ↦ Finset.le_sup (Finset.mem_univ η)⟩
  -- The degree stratification of Stacks 086T for the chart.
  obtain ⟨Y, hY0, hYanti, hYopen, hYiff⟩ :=
    exists_antitone_isOpenSubspace_iff_fibre_degree_ge B S hS hX φ
      (isFlat_of_presheafEtale B S hS hφ)
      (isLocallyOfFinitePresentation_of_presheafEtale B S hS hφ)
      (isSeparated_of_scheme_isSeparated B S hS inferInstance φ)
      (isLocallyQuasiFinite_of_presheafEtale B S hS hφ)
  have hdegree : ∀ (d : ℕ) (p : FieldValuedPoint B S hS X),
      DegreeGe ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
            (yonedaEquiv.symm p.value))) d ↔
        p.class B S hS X ∈
          Set.range (pointsMap B S hS (Y d).toFunctor (Y d).ι) := fun d p ↦
    ((degreeGe_iff_presheaf B S hS
      (relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ)
      (yonedaEquiv.symm p.value) d).trans (hYiff d p).symm).trans
      (exists_comp_ι_iff_class_mem_range B S hS hX (Y d) (hYopen d) p)
  -- The open subset of the chart cut out by the stratum above the bound.
  obtain ⟨V, hVopen, hViff⟩ :=
    (isOpen_yoneda_iff_isSchemeOpen B S hS U
      (pointsMap B S hS (yoneda.obj U) φ ⁻¹'
        Set.range (pointsMap B S hS (Y (n + 1)).toFunctor (Y (n + 1)).ι))).mp
      ((isOpen_range_pointsMap_of_isOpenImmersion B S hS (Y (n + 1)).ι
        (hYopen (n + 1)).2).preimage (continuous_pointsMap B S hS φ))
  have hVmem := mem_iff_pointsToScheme_mem B S hS hViff
  -- No generic point of the chart lies in it.
  have hVempty : V = ∅ := by
    refine eq_empty_of_forall_genericPoints_notMem hVopen fun η hη hηV ↦ ?_
    obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS U η
    exact not_degreeGe_succ_of_isFiniteLocallyFreeOfRank_le _ (hrηrank ⟨η, hη⟩)
      (hnle ⟨η, hη⟩)
      ((hdegree (n + 1) (pη ⟨η, hη⟩)).2
        (hpηz ⟨η, hη⟩ z hz ▸ (hVmem z).2 (hz ▸ hηV)))
  -- Hence the stratum has no points at all.
  have hWempty : ∀ p : FieldValuedPoint B S hS X,
      ¬ DegreeGe ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
          (yonedaEquiv.symm p.value))) (n + 1) := by
    intro p hdeg
    obtain ⟨v⟩ := nonempty_of_degreeGe_succ (k := p.carrier) _ hdeg
    have hmem : pointsToScheme B S hS U
        (pointsMap B S hS _
          (yoneda.map ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).fst'
            (yonedaEquiv.symm p.value)))
          ((schemePointRepresentative B S hS
            ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).pullback
              (yonedaEquiv.symm p.value)) v).class B S hS (yoneda.obj _))) ∈ V := by
      refine (hVmem _).1 ?_
      rw [Set.mem_preimage, pointsMap_fst'_eq_class B S hS
        (relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ) p]
      exact (hdegree (n + 1) p).1 hdeg
    rw [hVempty] at hmem
    exact hmem
  exact hasUniversallyBoundedFibers_of_forall_not_degreeGe_succ B S hS hX hφ n hWempty

end AlgebraicGeometry.Space

end
