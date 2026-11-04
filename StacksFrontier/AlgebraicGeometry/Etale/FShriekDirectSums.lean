module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekComposition
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekSubsheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.CategoryTheory.Sites.DirectSumRecognition

/-!
# Direct sums and the proper-support direct image

Let `f : X ⟶ Y` be a morphism of schemes which is separated and locally of finite type. The
proper-support direct image `f_!` of abelian sheaves on the small étale sites commutes with
direct sums: it carries a direct sum of a family of abelian sheaves on the small étale site of
`X`, indexed by an arbitrary type, to the direct sum of their proper-support direct images.

## Main definitions

* `AlgebraicGeometry.SmallEtale.shriekLeg` and `AlgebraicGeometry.SmallEtale.shriekProj` — the
  coprojections of a direct sum and their retractions, carried through `f_!`.

## Main results

* `AlgebraicGeometry.SmallEtale.properSupportFunctor_preservesColimitsOfShape_discrete` —
  **`f_!` commutes with direct sums**, in the form that it preserves colimits of every discrete
  shape.
* `AlgebraicGeometry.SmallEtale.isCompact_of_isProperOver` — a closed subset proper over a
  quasi-compact base is quasi-compact.
* `AlgebraicGeometry.SmallEtale.exists_compact_opens_superset` — a quasi-compact subset of a
  scheme lies in a quasi-compact open.
* `AlgebraicGeometry.SmallEtale.exists_finset_eq_sum_of_properSupportSections` — a section with
  proper support over a quasi-compact test object is a finite sum of sections of the summands.
* `AlgebraicGeometry.SmallEtale.exists_sieve_eq_sum_shriekLeg` — the same, locally on an
  arbitrary test object.

## Implementation notes

"Commutes with direct sums" is `CategoryTheory.Limits.PreservesColimitsOfShape (Discrete ι)`:
a colimit cocone is sent to a colimit cocone, so the statement does not presuppose that the
direct sums exist. The index type and the coefficient universe are independent variables.

Sections over a quasi-compact object of the small étale site (Tag 090H,
`CategoryTheory.GrothendieckTopology.IsQuasiCompactObject`) commute with direct sums (Tag 0935
part (2)), used here in the elementwise form
`Stacks.Sites.DirectSumRecognition.exists_finset_sum_eq_of_isQuasiCompactObject`; the Stacks
proof cites Tag 09YQ instead. The Stacks proof reduces to a quasi-compact source by Tag 0F54
(`AlgebraicGeometry.SmallEtale.properSupportOpenCoverCocone_isColimit`); here a section with
support proper over a quasi-compact test object has quasi-compact support, contained in a single
quasi-compact open of `X ×_Y V`, and the comparison is made on the Zariski covering by that open
and the complement of the support.

## References

* [Stacks Project, Tag 0F56](https://stacks.math.columbia.edu/tag/0F56)
* [Stacks Project, Tag 0F54](https://stacks.math.columbia.edu/tag/0F54)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.DirectSumRecognition

universe u v w

namespace AlgebraicGeometry.SmallEtale

section Compactness

/-- A closed subset proper over a quasi-compact base is quasi-compact. -/
public theorem isCompact_of_isProperOver {A V : Scheme.{u}} (P : A ⟶ V) [CompactSpace V]
    (Z : Closeds A)
    (hZ : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ P)) :
    IsCompact (Z : Set A) := by
  have := hZ
  have hc : CompactSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    rw [← isCompact_univ_iff]
    have h := QuasiCompact.isCompact_preimage
      (f := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ P)
      (U := Set.univ) isOpen_univ (by rw [isCompact_univ_iff]; infer_instance)
    simpa using h
  have hr : IsCompact (Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.base) :=
    isCompact_range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.continuous
  rwa [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal] at hr

/-- A quasi-compact subset of a scheme lies in a quasi-compact open. -/
public theorem exists_compact_opens_superset {A : Scheme.{u}} (Z : Set A) (h : IsCompact Z) :
    ∃ W : A.Opens, Z ⊆ (W : Set A) ∧ IsCompact (W : Set A) := by
  classical
  have hopen : ∀ i, IsOpen (((A.affineCover.f i).opensRange : A.Opens) : Set A) :=
    fun i => (A.affineCover.f i).opensRange.isOpen
  have hcov : Z ⊆ ⋃ i, (((A.affineCover.f i).opensRange : A.Opens) : Set A) := fun x _ =>
    Set.mem_iUnion.mpr ⟨A.affineCover.idx x, A.affineCover.covers x⟩
  obtain ⟨t, ht⟩ := h.elim_finite_subcover _ hopen hcov
  refine ⟨⨆ i ∈ t, (A.affineCover.f i).opensRange, by simpa using ht, ?_⟩
  simp only [Opens.coe_iSup]
  exact t.finite_toSet.isCompact_biUnion fun i _ =>
    isCompact_range (A.affineCover.f i).continuous

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object of the small étale site cut out by a quasi-compact open is quasi-compact. -/
public theorem isQuasiCompactObject_openObject (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens)
    (hW : IsCompact (W : Set ((SmallEtale.toScheme B S hS).obj U))) :
    (SmallEtale.topology B S hS).IsQuasiCompactObject (openObject B S hS U W) :=
  isQuasiCompactObject_of_compactSpace B S hS _ (isCompact_iff_compactSpace.mp hW)

/-- A point lies in the image of the inclusion of a Zariski open iff it lies in that open. -/
private theorem mem_range_openObjectι_iff (U : SmallEtale B S hS)
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens) (x : U.obj.left.1) :
    x ∈ Set.range (B.inclusion.map (openObjectι B S hS U W).hom.left) ↔ x ∈ W := by
  rw [show ((B.inclusion.map (openObjectι B S hS U W).hom.left)) =
    (SmallEtale.toScheme B S hS).map (openObjectι B S hS U W) from rfl, openObjectι_range]
  rfl

/-- Two Zariski opens whose union is everything generate a covering sieve. -/
public theorem mem_topology_openObject_pair (U : SmallEtale B S hS)
    (W W' : ((SmallEtale.toScheme B S hS).obj U).Opens) (hWW' : W ⊔ W' = ⊤) :
    Sieve.generate (Presieve.ofArrows
        (fun b : Bool => openObject B S hS U (cond b W W'))
        (fun b => openObjectι B S hS U (cond b W W'))) ∈
      SmallEtale.topology B S hS U := by
  refine generate_ofArrows_mem_topology_of_jointlySurjective B S hS _ _ fun x => ?_
  have hx : x ∈ (W : Set ((SmallEtale.toScheme B S hS).obj U)) ∪
      (W' : Set ((SmallEtale.toScheme B S hS).obj U)) := by
    have : x ∈ ((W ⊔ W' : ((SmallEtale.toScheme B S hS).obj U).Opens) :
        Set ((SmallEtale.toScheme B S hS).obj U)) := by rw [hWW']; trivial
    simpa using this
  rcases hx with hx | hx
  · exact ⟨true, (mem_range_openObjectι_iff B S hS U W x).2 hx⟩
  · exact ⟨false, (mem_range_openObjectι_iff B S hS U W' x).2 hx⟩

end Compactness

section SectionDecomposition

section Site

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {ι : Type w}
  (D : Discrete ι ⥤ Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v}) (c : Cocone D)

/-- Restricting along a composite is restricting along each factor in turn. -/
private theorem map_comp_op_apply {C : Type*} [Category C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    {X Y Z : C} (g : Z ⟶ Y) (h : Y ⟶ X) (x : F.obj (op X)) :
    F.map (g ≫ h).op x = F.map g.op (F.map h.op x) := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- A section of a direct sum of abelian étale sheaves which vanishes outside a quasi-compact
open is a finite sum of sections of the summands, with coefficients read off by the projections
of the direct sum. -/
public theorem exists_finset_eq_sum_of_compact_opens (hc : IsColimit c)
    (U : SmallEtale B S hS) (s : c.pt.obj.obj (op U))
    (W : ((SmallEtale.toScheme B S hS).obj U).Opens)
    (hWc : IsCompact (W : Set ((SmallEtale.toScheme B S hS).obj U)))
    (hWZ : W ⊔ zeroOpen B S hS c.pt U s = ⊤) :
    ∃ T : Finset ι, s = ∑ k ∈ T, (leg D c k).hom.app (op U)
      ((projection D c hc k).hom.app (op U) s) := by
  classical
  have hR := mem_topology_openObject_pair B S hS U W (zeroOpen B S hS c.pt U s) hWZ
  obtain ⟨T, t, ht⟩ := exists_finset_sum_eq_of_isQuasiCompactObject
    (SmallEtale.topology B S hS) D c hc (openObject B S hS U W)
    (isQuasiCompactObject_openObject B S hS U W hWc)
    (c.pt.obj.map (openObjectι B S hS U W).op s)
  refine ⟨T, eq_sum_projection_of_locally D c hc s T hR ?_⟩
  rintro V' a ⟨Z', g, h, ⟨b⟩, rfl⟩
  rcases b with _ | _
  · refine ⟨fun _ => 0, ?_⟩
    change c.pt.obj.map (g ≫ openObjectι B S hS U (zeroOpen B S hS c.pt U s)).op s =
      ∑ k ∈ T, (leg D c k).hom.app (op V') 0
    have hzero : c.pt.obj.map
        (openObjectι B S hS U (zeroOpen B S hS c.pt U s)).op s = 0 :=
      (map_eq_zero_iff_le_zeroOpen B S hS c.pt U s _
        (openObjectι B S hS U (zeroOpen B S hS c.pt U s))).2
        (le_of_eq (openObjectι_opensRange B S hS U (zeroOpen B S hS c.pt U s)))
    rw [map_comp_op_apply, hzero, map_zero]
    exact (Finset.sum_eq_zero fun k _ => map_zero _).symm
  · refine ⟨fun k => (D.obj ⟨k⟩).obj.map g.op (t k), ?_⟩
    change c.pt.obj.map (g ≫ openObjectι B S hS U W).op s =
      ∑ k ∈ T, (leg D c k).hom.app (op V') ((D.obj ⟨k⟩).obj.map g.op (t k))
    rw [map_comp_op_apply, ht]
    exact map_sum_leg D c g.op T t

end Site

section ProperSupport

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] {ι : Type w}
  (D : Discrete ι ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
  (c : Cocone D)

/-- A section of a direct sum of abelian étale sheaves whose support is proper over a
quasi-compact test object is a finite sum of sections of the summands. -/
public theorem exists_finset_eq_sum_of_properSupportSections (hc : IsColimit c)
    (V : SmallEtale B Y.obj Y.property)
    (hV : CompactSpace ((SmallEtale.toScheme B Y.obj Y.property).obj V))
    (s : c.pt.obj.obj (op ((smallEtaleBaseChange B f).obj V)))
    (hs : properSupportSections B f c.pt V s) :
    ∃ T : Finset ι,
      s = ∑ k ∈ T, (leg D c k).hom.app (op ((smallEtaleBaseChange B f).obj V))
        ((projection D c hc k).hom.app (op ((smallEtaleBaseChange B f).obj V)) s) := by
  classical
  have := hasPullbacks_bigEtaleSite B
  have hq : LocallyOfFiniteType (B.inclusion.map (pullback.fst V.obj.hom f)) :=
    locallyOfFiniteType_baseChangeProjection B f V
  have hcs : CompactSpace (B.inclusion.obj V.obj.left) := hV
  have hsP : IsProperOver (B.inclusion.map (pullback.fst V.obj.hom f))
      (zeroOpen B X.obj X.property c.pt ((smallEtaleBaseChange B f).obj V) s).compl := hs
  have hZcompact : IsCompact ((zeroOpen B X.obj X.property c.pt
      ((smallEtaleBaseChange B f).obj V) s).compl :
        Set ((SmallEtale.toScheme B X.obj X.property).obj
          ((smallEtaleBaseChange B f).obj V))) :=
    isCompact_of_isProperOver (B.inclusion.map (pullback.fst V.obj.hom f)) _ hsP
  obtain ⟨W, hZW, hWc⟩ := exists_compact_opens_superset _ hZcompact
  refine exists_finset_eq_sum_of_compact_opens B X.obj X.property D c hc _ s W hWc ?_
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
  simp only [TopologicalSpace.Opens.coe_sup, Set.mem_union]
  exact or_iff_not_imp_right.2 fun hx => hZW hx

/-- Each component of a proper-support section again has proper support. -/
public theorem properSupportSections_projection (hc : IsColimit c)
    (V : SmallEtale B Y.obj Y.property)
    (s : c.pt.obj.obj (op ((smallEtaleBaseChange B f).obj V)))
    (hs : properSupportSections B f c.pt V s) (k : ι) :
    properSupportSections B f (D.obj ⟨k⟩) V
      ((projection D c hc k).hom.app (op ((smallEtaleBaseChange B f).obj V)) s) := by
  have := hasPullbacks_bigEtaleSite B
  have hq : LocallyOfFiniteType (B.inclusion.map (pullback.fst V.obj.hom f)) :=
    locallyOfFiniteType_baseChangeProjection B f V
  have hsP : IsProperOver (B.inclusion.map (pullback.fst V.obj.hom f))
      (zeroOpen B X.obj X.property c.pt ((smallEtaleBaseChange B f).obj V) s).compl := hs
  have hle : (zeroOpen B X.obj X.property (D.obj ⟨k⟩) ((smallEtaleBaseChange B f).obj V)
      ((projection D c hc k).hom.app (op ((smallEtaleBaseChange B f).obj V)) s)).compl ≤
      (zeroOpen B X.obj X.property c.pt ((smallEtaleBaseChange B f).obj V) s).compl :=
    supportSection_map_subset B X.obj X.property c.pt (D.obj ⟨k⟩) (projection D c hc k)
      ((smallEtaleBaseChange B f).obj V) s
  exact isProperOver_of_le (B.inclusion.map (pullback.fst V.obj.hom f)) hle hsP

end ProperSupport

end SectionDecomposition

section FunctorSections

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)]

/-- The inclusion of `f_! F` into `f_* F` is injective on sections. -/
public theorem injective_fShriekSubsheaf_arrow_app
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property) :
    Function.Injective ((fShriekSubsheaf B f F).val.arrow.hom.app (op V)) :=
  fun _ _ => Subtype.ext

/-- The map induced by `f_!` on sections is the given map of sheaves, read inside `f_* F`. -/
public theorem fShriekSubsheaf_arrow_properSupportFunctor_map
    (F H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) (φ : F ⟶ H)
    (V : SmallEtale B Y.obj Y.property)
    (x : ((properSupportFunctor B f).obj F).obj.obj (op V)) :
    (fShriekSubsheaf B f H).val.arrow.hom.app (op V)
        (((properSupportFunctor B f).map φ).hom.app (op V) x) =
      φ.hom.app (op ((smallEtaleBaseChange B f).obj V))
        ((fShriekSubsheaf B f F).val.arrow.hom.app (op V) x) := by
  have hmap : ((((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).map φ).hom.app (op V)) =
      φ.hom.app (op ((smallEtaleBaseChange B f).obj V)) :=
    Functor.sheafPushforwardContinuous_map_hom_app (smallEtaleBaseChange B f) AddCommGrpCat.{v}
      (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property) φ (op V)
  have key : (properSupportFunctor B f).map φ ≫ (fShriekSubsheaf B f H).val.arrow =
      (fShriekSubsheaf B f F).val.arrow ≫ (((smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).map φ) :=
    (SmallEtale.fShriekMap B f F H φ).property
  have h := congrArg (fun m : ((properSupportFunctor B f).obj F) ⟶
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj H =>
    ConcreteCategory.hom (m.hom.app (op V)) x) key
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, hmap] at h
  exact h

/-- `f_!` sends the zero map to the zero map. -/
public theorem properSupportFunctor_map_zero
    (F H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    (properSupportFunctor B f).map (0 : F ⟶ H) = 0 := by
  refine Sheaf.hom_ext ?_
  refine NatTrans.ext (funext fun V => ?_)
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  refine injective_fShriekSubsheaf_arrow_app B f H V.unop ?_
  rw [fShriekSubsheaf_arrow_properSupportFunctor_map B f F H 0 V.unop x]
  simp only [ObjectProperty.zero_hom, NatTrans.app_zero, AddCommGrpCat.hom_zero]
  rfl

section DirectSum

variable {ι : Type w}
  (D : Discrete ι ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
  (c : Cocone D)

/-- The coprojection of the `k`-th summand of a direct sum, carried through `f_!`. -/
public abbrev shriekLeg (k : ι) :
    (properSupportFunctor B f).obj (D.obj ⟨k⟩) ⟶ (properSupportFunctor B f).obj c.pt :=
  (properSupportFunctor B f).map (leg D c k)

/-- The projection of a direct sum onto its `k`-th summand, carried through `f_!`. -/
public abbrev shriekProj (hc : IsColimit c) (k : ι) :
    (properSupportFunctor B f).obj c.pt ⟶ (properSupportFunctor B f).obj (D.obj ⟨k⟩) :=
  (properSupportFunctor B f).map (projection D c hc k)

/-- `f_!` carries the retraction identity of the direct sum. -/
public theorem shriekLeg_comp_shriekProj_self (hc : IsColimit c) (k : ι) :
    shriekLeg B f D c k ≫ shriekProj B f D c hc k = 𝟙 _ := by
  rw [← Functor.map_comp, leg_comp_projection_self D c hc k, CategoryTheory.Functor.map_id]

/-- `f_!` carries the vanishing of the off-diagonal retractions of the direct sum. -/
public theorem shriekLeg_comp_shriekProj_ne (hc : IsColimit c) {k j : ι} (hkj : k ≠ j) :
    shriekLeg B f D c k ≫ shriekProj B f D c hc j = 0 := by
  rw [← Functor.map_comp, leg_comp_projection_ne D c hc hkj]
  exact properSupportFunctor_map_zero B f _ _

/-- A section of `f_!` of a direct sum, over a quasi-compact test object, is the finite sum of
its components. -/
public theorem eq_sum_shriekLeg_of_compactSpace (hc : IsColimit c)
    (V : SmallEtale B Y.obj Y.property)
    (hV : CompactSpace ((SmallEtale.toScheme B Y.obj Y.property).obj V))
    (x : ((properSupportFunctor B f).obj c.pt).obj.obj (op V)) :
    ∃ T : Finset ι, x = ∑ k ∈ T, (shriekLeg B f D c k).hom.app (op V)
      ((shriekProj B f D c hc k).hom.app (op V) x) := by
  have hs : properSupportSections B f c.pt V
      ((fShriekSubsheaf B f c.pt).val.arrow.hom.app (op V) x) :=
    (mem_range_fShriekSubsheaf_arrow_iff B f c.pt V _).1 ⟨x, rfl⟩
  obtain ⟨T, hT⟩ := exists_finset_eq_sum_of_properSupportSections B f D c hc V hV _ hs
  have hsum : (fShriekSubsheaf B f c.pt).val.arrow.hom.app (op V)
      (∑ k ∈ T, (shriekLeg B f D c k).hom.app (op V)
        ((shriekProj B f D c hc k).hom.app (op V) x)) =
      ∑ k ∈ T, (leg D c k).hom.app (op ((smallEtaleBaseChange B f).obj V))
        ((projection D c hc k).hom.app (op ((smallEtaleBaseChange B f).obj V))
          ((fShriekSubsheaf B f c.pt).val.arrow.hom.app (op V) x)) := by
    refine (map_sum (ConcreteCategory.hom
      ((fShriekSubsheaf B f c.pt).val.arrow.hom.app (op V)))
      (fun k => (shriekLeg B f D c k).hom.app (op V)
        ((shriekProj B f D c hc k).hom.app (op V) x)) T).trans
      (Finset.sum_congr rfl fun k _ => ?_)
    exact (fShriekSubsheaf_arrow_properSupportFunctor_map B f (D.obj ⟨k⟩) c.pt
      (leg D c k) V ((shriekProj B f D c hc k).hom.app (op V) x)).trans
      (congrArg (ConcreteCategory.hom ((leg D c k).hom.app
        (op ((smallEtaleBaseChange B f).obj V))))
        (fShriekSubsheaf_arrow_properSupportFunctor_map B f c.pt (D.obj ⟨k⟩)
          (projection D c hc k) V x))
  exact ⟨T, injective_fShriekSubsheaf_arrow_app B f c.pt V (hT.trans hsum.symm)⟩

/-- Restriction distributes over a finite sum of coprojections. -/
public theorem map_sum_shriekLeg {V V' : SmallEtale B Y.obj Y.property} (a : V' ⟶ V)
    (T : Finset ι)
    (υ : ∀ k : ι, ((properSupportFunctor B f).obj (D.obj ⟨k⟩)).obj.obj (op V)) :
    ((properSupportFunctor B f).obj c.pt).obj.map a.op
        (∑ k ∈ T, (shriekLeg B f D c k).hom.app (op V) (υ k)) =
      ∑ k ∈ T, (shriekLeg B f D c k).hom.app (op V')
        (((properSupportFunctor B f).obj (D.obj ⟨k⟩)).obj.map a.op (υ k)) := by
  refine (map_sum (ConcreteCategory.hom
    (((properSupportFunctor B f).obj c.pt).obj.map a.op))
    (fun k => (shriekLeg B f D c k).hom.app (op V) (υ k)) T).trans
    (Finset.sum_congr rfl fun k _ => ?_)
  exact (NatTrans.naturality_apply (shriekLeg B f D c k).hom a.op (υ k)).symm

/-- The finite-sum presentation of a section is inherited by its restrictions. -/
public theorem eq_sum_shriekLeg_restrict (hc : IsColimit c)
    {V V' : SmallEtale B Y.obj Y.property} (a : V' ⟶ V)
    (x : ((properSupportFunctor B f).obj c.pt).obj.obj (op V)) (T : Finset ι)
    (hx : x = ∑ k ∈ T, (shriekLeg B f D c k).hom.app (op V)
      ((shriekProj B f D c hc k).hom.app (op V) x)) :
    ((properSupportFunctor B f).obj c.pt).obj.map a.op x =
      ∑ k ∈ T, (shriekLeg B f D c k).hom.app (op V')
        ((shriekProj B f D c hc k).hom.app (op V')
          (((properSupportFunctor B f).obj c.pt).obj.map a.op x)) := by
  conv_lhs => rw [hx]
  rw [map_sum_shriekLeg B f D c a T fun k => (shriekProj B f D c hc k).hom.app (op V) x]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact (NatTrans.naturality_apply (shriekProj B f D c hc k).hom a.op x).symm

end DirectSum

end FunctorSections

section LocalFiniteness

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] {ι : Type w}
  (D : Discrete ι ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
  (c : Cocone D)

/-- Every section of `f_!` of a direct sum is, locally on an étale covering by quasi-compact
objects, a finite sum of its components. -/
public theorem exists_sieve_eq_sum_shriekLeg (hc : IsColimit c)
    (V : SmallEtale B Y.obj Y.property)
    (x : ((properSupportFunctor B f).obj c.pt).obj.obj (op V)) :
    ∃ R ∈ SmallEtale.topology B Y.obj Y.property V,
      ∀ ⦃V' : SmallEtale B Y.obj Y.property⦄ (a : V' ⟶ V), R a → ∃ T : Finset ι,
        ((properSupportFunctor B f).obj c.pt).obj.map a.op x =
          ∑ k ∈ T, (shriekLeg B f D c k).hom.app (op V')
            ((shriekProj B f D c hc k).hom.app (op V')
              (((properSupportFunctor B f).obj c.pt).obj.map a.op x)) := by
  classical
  refine ⟨Sieve.generate (Presieve.ofArrows
    (fun i : ((SmallEtale.toScheme B Y.obj Y.property).obj V).affineCover.I₀ =>
      openObject B Y.obj Y.property V
        (((SmallEtale.toScheme B Y.obj Y.property).obj V).affineCover.f i).opensRange)
    (fun i => openObjectι B Y.obj Y.property V
      (((SmallEtale.toScheme B Y.obj Y.property).obj V).affineCover.f i).opensRange)), ?_, ?_⟩
  · refine generate_ofArrows_mem_topology_of_jointlySurjective B Y.obj Y.property _ _ fun z => ?_
    refine ⟨((SmallEtale.toScheme B Y.obj Y.property).obj V).affineCover.idx z, ?_⟩
    exact (mem_range_openObjectι_iff B Y.obj Y.property V _ z).2
      (by simpa using ((SmallEtale.toScheme B Y.obj Y.property).obj V).affineCover.covers z)
  · rintro V' a ⟨Z', g, h, ⟨i⟩, rfl⟩
    have hcpt : CompactSpace ((SmallEtale.toScheme B _ _).obj
        (openObject B _ _ V (((SmallEtale.toScheme B _ _).obj V).affineCover.f i).opensRange)) :=
      isCompact_iff_compactSpace.mp (by
        simpa using isCompact_range
          (((SmallEtale.toScheme B _ _).obj V).affineCover.f i).continuous)
    obtain ⟨T, hy⟩ := eq_sum_shriekLeg_of_compactSpace B f D c hc _ hcpt
      (((properSupportFunctor B f).obj c.pt).obj.map
        (openObjectι B _ _ V
          (((SmallEtale.toScheme B _ _).obj V).affineCover.f i).opensRange).op x)
    refine ⟨T, ?_⟩
    rw [map_comp_op_apply]
    exact eq_sum_shriekLeg_restrict B f D c hc g _ T hy

end LocalFiniteness


section Main

/-- **Stacks 0F56.** Let `f : X ⟶ Y` be a morphism of schemes which is separated and locally of
finite type. Then the proper-support direct image `f_!` of abelian sheaves on the small étale
sites commutes with direct sums: it preserves colimits indexed by any discrete category, so it
carries a direct sum of an arbitrarily indexed family of abelian sheaves on the small étale
site of `X` to the direct sum of their proper-support direct images. -/
@[stacks 0F56]
public theorem properSupportFunctor_preservesColimitsOfShape_discrete
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
    (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) (properSupportFunctor.{u, v} B f) :=
  ⟨fun {D} => ⟨fun {c} hc => isColimit_of_retractions_of_locally_finite_sum
    ((properSupportFunctor B f).mapCocone c) (shriekProj B f D c hc)
    (shriekLeg_comp_shriekProj_self B f D c hc)
    (fun _ _ => shriekLeg_comp_shriekProj_ne B f D c hc)
    (exists_sieve_eq_sum_shriekLeg B f D c hc)⟩⟩

end Main

end AlgebraicGeometry.SmallEtale

end
