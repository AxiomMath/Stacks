module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.SchemeTheoreticUnion
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Contraction
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Intersection
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.PushoutSituation
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Pushout.Gluing
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionPushout
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfDimensionOnePointsFiniteComponents
public import StacksCore.Tactic.StacksAttribute

/-!
# The pushout contraction of a rational bridge

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge (Tag 0E3M). Write `X'` for
the scheme-theoretic closure of `X \ C` and `k' = Γ(C, 𝒪_C)`.

[Stacks, Tag 0E3M] asserts that the pushout
```
C ∩ X' ⟶ X'
  ↓         ↓ a
Spec k' ⟶   Y
```
exists, and that it receives a morphism `c : X ⟶ Y` restricting to `a` on `X'` and to the
canonical collapse `C ⟶ Spec k'` followed by `Spec k' ⟶ Y` on `C`. This file proves both.

## Main results

* `Stacks.Curves.nonempty_intersection_bridge` — `C ∩ X'` is nonempty.
* `Stacks.Curves.topologicalKrullDim_intersection_bridge_eq_zero` — `C ∩ X'` is
  zero-dimensional.
* `Stacks.Curves.exists_isAffineOpen_containing_intersection_bridge` — the points of `C ∩ X'` lie
  in a single affine open of `X'`.
* `Stacks.Curves.exists_contraction_pushoutScheme_bridge` — the contraction `c : X ⟶ Y` into the
  pushout itself.
* `Stacks.Curves.exists_pushout_contraction_bridge` — the pushout `Y` and the contraction
  `c : X ⟶ Y` exist.

## Implementation notes

The pushout is [Stacks, Tag 0E25], in the form
`AlgebraicGeometry.pushoutAlongClosedImmersionAndIntegral`, applied to the closed immersion
`C ∩ X' ⟶ X'` and the morphism `C ∩ X' ⟶ Spec k'`. Three things must be checked. First, the
latter morphism is integral: `C ∩ X'` is a zero-dimensional scheme proper over `k`, hence finite
over `k`, so it is finite over `Spec k'` by `AlgebraicGeometry.IsFinite.of_comp`. Second,
`C ∩ X'` must be nonempty for that dimension count — it is, because `X` is connected
(`H⁰(X, 𝒪_X) = k`) while `C` and `X'` are nonempty closed sets covering it, so they meet. Third,
the fibre condition of [Stacks, Tag 0ECI]: `Spec k'` has a single point, so what is needed is one
affine open of `X'` containing every point of `C ∩ X'`, and that is [Stacks, Tag 09NN] — the
intersection is finite, and the local rings of the one-dimensional Noetherian curve `X'` at its
closed points are Noetherian of Krull dimension at most one. This is exactly the appeal the source
makes to Section 0E35, where the same proposition is cited.

The contraction is the universal property of the scheme-theoretic union: `C` and `X'` cover `X`
scheme-theoretically because `X` is reduced, so `C ⊓ 𝒥 = ⊥` where `𝒥` cuts out `X'`, and the union
of two closed subschemes is the pushout over their intersection
(`AlgebraicGeometry.Scheme.IdealSheafData.isPushout_subscheme_inf`, [Stacks, Tag 0C4J]). The two
morphisms `C ⟶ Spec k' ⟶ Y` and `X' ⟶ Y` agree on `C ∩ X'` precisely because the first square is
commutative, so they descend to `c : X ⟶ Y`.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 09NN](https://stacks.math.columbia.edu/tag/09NN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The structure morphism of `Spec k'` over `Spec k`, for `k'` the global functions on a closed
subscheme `C` of a scheme over `k`. -/
abbrev bridgeSectionsStructureMap (C : X.IdealSheafData) :
    CommRingCat.of k ⟶ Γ(C.subscheme, ⊤) :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop

/-- The canonical collapse of a closed subscheme onto the spectrum of its global functions is a
morphism over the base. -/
theorem toSpecΓ_comp_bridgeSectionsStructureMap (C : X.IdealSheafData) :
    C.subscheme.toSpecΓ ≫ Spec.map (bridgeSectionsStructureMap C) =
      C.subschemeι ≫ (X ↘ Spec (.of k)) := by
  rw [bridgeSectionsStructureMap, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- A point whose image under a continuous injective map is closed is itself closed. -/
private theorem isClosed_singleton_of_injective_of_isClosed_singleton_apply
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} (hf : Continuous f)
    (hinj : Function.Injective f) {w : α} (h : IsClosed {f w}) : IsClosed {w} := by
  simpa only [← Set.image_singleton, hinj.preimage_image] using h.preimage hf

section Bridge

variable [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **The intersection of a rational bridge with the closure of its complement is nonempty.**
The bridge and that closure are nonempty closed subsets covering the connected space `X`, so they
meet. -/
theorem nonempty_intersection_bridge
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    Nonempty (intersectionWithComplementaryCurve C) := by
  have := hC.isIntegral
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  have hcompl : ((C.support : Set X))ᶜ ⊆ ((complementaryCurveIdeal C).support : Set X) := by
    show ((C.support.compl : X.Opens) : Set X) ⊆ _
    rw [← Scheme.Opens.range_ι]
    exact Scheme.Hom.range_subset_ker_support _
  have hne : ∀ I : X.IdealSheafData, Nonempty I.subscheme → (I.support : Set X).Nonempty :=
    fun I ⟨z⟩ => ⟨I.subschemeι.base z, by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩⟩
  obtain ⟨x, -, hx⟩ := isPreconnected_closed_iff.1 isPreconnected_univ _ _ C.support.isClosed
    (complementaryCurveIdeal C).support.isClosed (fun x _ => (em _).imp id (hcompl ·))
    (by rw [Set.univ_inter]; exact hne _ inferInstance)
    (by rw [Set.univ_inter]; exact hne _ hC.complementaryCurve_nonempty)
  have hxW : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X) := by
    simpa only [intersectionWithComplementaryCurveIdeal, Scheme.IdealSheafData.support_sup,
      TopologicalSpace.Closeds.coe_inf, Set.mem_inter_iff] using hx
  rw [← Scheme.IdealSheafData.range_subschemeι] at hxW
  obtain ⟨w, -⟩ := hxW
  exact ⟨w⟩

/-- **The intersection of a rational bridge with the closure of its complement is
zero-dimensional.**  It is a nonempty sober `T1` space: its points are nodes of `X`, hence
closed. -/
theorem topologicalKrullDim_intersection_bridge_eq_zero
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    topologicalKrullDim (intersectionWithComplementaryCurve C) = 0 := by
  have hne : Nonempty (intersectionWithComplementaryCurve C) := nonempty_intersection_bridge hC
  have : T1Space (intersectionWithComplementaryCurve C) := by
    refine ⟨fun w => ?_⟩
    exact isClosed_singleton_of_injective_of_isClosed_singleton_apply
      (intersectionWithComplementaryCurveIdeal C).subschemeι.continuous
      (intersectionWithComplementaryCurveIdeal C).subschemeι.isClosedEmbedding.injective
      (isNode_of_mem_intersection_bridge k X hdim hnodal C hC w).1
  refine le_antisymm
    Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space ?_
  obtain ⟨w⟩ := hne
  refine Order.krullDim_nonneg_iff.mpr ?_
  exact ⟨⟨closure {w}, (isIrreducible_singleton (x := w)).closure, isClosed_closure⟩⟩

/-- **The morphism collapsing `C ∩ X'` onto `Spec k'` is finite.**  The intersection is a
zero-dimensional scheme proper over `k`, hence finite over `k`, and `Spec k'` is separated over
`k`, so the first factor is finite as well. -/
theorem isFinite_intersection_toSpec_bridgeSections
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    IsFinite (Scheme.IdealSheafData.inclusion (I := C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subscheme.toSpecΓ) := by
  have hcomp : (Scheme.IdealSheafData.inclusion (I := C)
        (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subscheme.toSpecΓ) ≫
        Spec.map (bridgeSectionsStructureMap C) =
      (intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k)) := by
    rw [Category.assoc, toSpecΓ_comp_bridgeSectionsStructureMap, ← Category.assoc,
      Scheme.IdealSheafData.inclusion_subschemeι]
  have : IsFinite ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
      (X ↘ Spec (.of k))) :=
    isFinite_of_finiteType_of_dimension_zero k _
      (topologicalKrullDim_intersection_bridge_eq_zero hdim hnodal hC)
  have : IsFinite ((Scheme.IdealSheafData.inclusion (I := C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subscheme.toSpecΓ) ≫
      Spec.map (bridgeSectionsStructureMap (k := k) C)) := by rw [hcomp]; infer_instance
  exact IsFinite.of_comp (Scheme.IdealSheafData.inclusion (I := C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subscheme.toSpecΓ)
    (Spec.map (bridgeSectionsStructureMap (k := k) C))

/-- **The points at which a rational bridge meets the closure of its complement all lie in one
affine open of that closure.**  This is the appeal the source makes to [Stacks, Tag 09NN] through
Section 0E35: the intersection is finite, and the local rings of the one-dimensional Noetherian
curve `X'` at its closed points are Noetherian of Krull dimension at most one. -/
theorem exists_isAffineOpen_containing_intersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    ∃ U : (complementaryCurve C).Opens, IsAffineOpen U ∧
      ∀ w : intersectionWithComplementaryCurve C,
        (Scheme.IdealSheafData.inclusion (I := complementaryCurveIdeal C)
          (J := intersectionWithComplementaryCurveIdeal C) le_sup_right).base w ∈ U := by
  have : Finite (intersectionWithComplementaryCurve C) :=
    finite_intersectionWithComplementaryCurve_bridge hdim hnodal hC
  have hproper : IsProper (complementaryCurveι C ≫ (X ↘ Spec (.of k))) := inferInstance
  have : IsLocallyNoetherian (complementaryCurve C) :=
    LocallyOfFiniteType.isLocallyNoetherian (complementaryCurveι C ≫ (X ↘ Spec (.of k)))
  have : CompactSpace (complementaryCurve C) :=
    QuasiCompact.compactSpace_of_compactSpace (complementaryCurveι C ≫ (X ↘ Spec (.of k)))
  have : AlgebraicGeometry.IsNoetherian (complementaryCurve C) := ⟨⟩
  have : NoetherianSpace (complementaryCurve C) := inferInstance
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have : (complementaryCurve C).IsSeparated :=
    Scheme.IsSeparated.of_isSeparated (complementaryCurveι C)
  have hdimX' : topologicalKrullDim (complementaryCurve C) = 1 :=
    topologicalKrullDim_complementaryCurve_eq_one
      (equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim) hdim
      hnodal C hC.complementaryCurve_nonempty
  -- each intersection point is a closed point of `X'`
  have himg : ∀ w : intersectionWithComplementaryCurve C,
      (complementaryCurveι C).base ((Scheme.IdealSheafData.inclusion
          (I := complementaryCurveIdeal C)
          (J := intersectionWithComplementaryCurveIdeal C) le_sup_right).base w) =
        (intersectionWithComplementaryCurveIdeal C).subschemeι.base w := by
    intro w
    conv_rhs => rw [← Scheme.IdealSheafData.inclusion_subschemeι
      (le_sup_right : complementaryCurveIdeal C ≤ intersectionWithComplementaryCurveIdeal C)]
    rfl
  have hzclosed : ∀ w : intersectionWithComplementaryCurve C,
      IsClosed ({(Scheme.IdealSheafData.inclusion (I := complementaryCurveIdeal C)
        (J := intersectionWithComplementaryCurveIdeal C) le_sup_right).base w} :
          Set (complementaryCurve C)) := by
    intro w
    refine isClosed_singleton_of_injective_of_isClosed_singleton_apply
      (complementaryCurveι C).continuous (complementaryCurveι C).isClosedEmbedding.injective ?_
    rw [himg w]
    exact (isNode_of_mem_intersection_bridge k X hdim hnodal C hC w).1
  refine exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components
    (complementaryCurve C)
    (AlgebraicGeometry.finite_irreducibleComponents_of_isCompact (complementaryCurve C))
    (fun w : intersectionWithComplementaryCurve C =>
      (Scheme.IdealSheafData.inclusion (I := complementaryCurveIdeal C)
        (J := intersectionWithComplementaryCurveIdeal C) le_sup_right).base w)
    (fun _ => inferInstance) fun w => ?_
  rw [Ring.krullDimLE_iff, ← topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point
    (complementaryCurveι C ≫ (X ↘ Spec (.of k))) _ (hzclosed w), Nat.cast_one, ← hdimX']
  exact topologicalKrullDimAt_le_topologicalKrullDim _

/-- **The pushout situation of [Stacks, Tag 0E25] attached to a rational bridge.**  The closed
immersion is `C ∩ X' ⟶ X'`, the integral morphism is the collapse `C ∩ X' ⟶ Spec k'`, and the
fibre condition of [Stacks, Tag 0ECI] is
`Stacks.Curves.exists_isAffineOpen_containing_intersection_bridge`. -/
def bridgePushoutSituation
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
  haveI : IsFinite (Scheme.IdealSheafData.inclusion (I := C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subscheme.toSpecΓ) :=
    isFinite_intersection_toSpec_bridgeSections hdim hnodal hC
  { S := Spec (.of k)
    X := complementaryCurve C
    Y := Spec Γ(C.subscheme, ⊤)
    Z := intersectionWithComplementaryCurve C
    pX := complementaryCurveι C ≫ (X ↘ Spec (.of k))
    pY := Spec.map (bridgeSectionsStructureMap (k := k) C)
    pZ := (intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))
    i := Scheme.IdealSheafData.inclusion (I := complementaryCurveIdeal C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_right
    j := Scheme.IdealSheafData.inclusion (I := C)
      (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫ C.subscheme.toSpecΓ
    i_over := by
      rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    j_over := by
      rw [Category.assoc, toSpecΓ_comp_bridgeSectionsStructureMap, ← Category.assoc,
        Scheme.IdealSheafData.inclusion_subschemeι]
    fiber_preimage_subset_affine := fun _ => by
      obtain ⟨U, hUaff, hUmem⟩ :=
        exists_isAffineOpen_containing_intersection_bridge hdim hnodal hC
      exact ⟨U, hUaff, fun z _ => hUmem z⟩ }

/-- **The pushout of [Stacks, Tag 0E3M] carries a contraction of the rational bridge**, in the
form that names the pushout: it is the scheme `AlgebraicGeometry.pushoutScheme` of
`Stacks.Curves.bridgePushoutSituation`.  The contraction `c : X ⟶ Y` is the descent of
`X' ⟶ Y` and `C ⟶ Spec k' ⟶ Y` along the presentation of `X` as the scheme-theoretic union of
`C` and `X'` ([Stacks, Tag 0C4J]), which is a pushout over `C ∩ X'`. -/
theorem exists_contraction_pushoutScheme_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    ∃ c : X ⟶ pushoutScheme (bridgePushoutSituation hdim hnodal hC),
      IsContractionOfRationalBridge hC c := by
  let s : PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
    bridgePushoutSituation hdim hnodal hC
  set Y := pushoutScheme s with hYdef
  set a : complementaryCurve C ⟶ Y := pushoutInl s with hadef
  set b : Spec Γ(C.subscheme, ⊤) ⟶ Y := pushoutInr s with hbdef
  have hpo : IsPushout s.i s.j a b := (pushoutAlongClosedImmersionAndIntegral s).isPushout
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have hbot : C ⊓ complementaryCurveIdeal C = ⊥ := inf_complementaryCurveIdeal_eq_bot C
  have : IsIso (C ⊓ complementaryCurveIdeal C).subschemeι := hbot ▸ inferInstance
  set e : (C ⊓ complementaryCurveIdeal C).subscheme ≅ X :=
    asIso (C ⊓ complementaryCurveIdeal C).subschemeι with hedef
  set hpush := Scheme.IdealSheafData.isPushout_subscheme_inf C (complementaryCurveIdeal C)
    with hpushdef
  have hglue : Scheme.IdealSheafData.inclusion (I := C)
        (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫
        (C.subscheme.toSpecΓ ≫ b) =
      Scheme.IdealSheafData.inclusion (I := complementaryCurveIdeal C)
        (J := intersectionWithComplementaryCurveIdeal C) le_sup_right ≫ a := by
    rw [← Category.assoc]; exact hpo.w.symm
  set desc : (C ⊓ complementaryCurveIdeal C).subscheme ⟶ Y :=
    hpush.desc (C.subscheme.toSpecΓ ≫ b) a hglue with hdescdef
  have he_inv : (C ⊓ complementaryCurveIdeal C).subschemeι ≫ e.inv =
      𝟙 (C ⊓ complementaryCurveIdeal C).subscheme := e.hom_inv_id
  have hres : ∀ (I : X.IdealSheafData) (hI : C ⊓ complementaryCurveIdeal C ≤ I),
      I.subschemeι ≫ e.inv ≫ desc = Scheme.IdealSheafData.inclusion hI ≫ desc := fun I hI => by
    rw [← Scheme.IdealSheafData.inclusion_subschemeι hI, Category.assoc,
      ← Category.assoc ((C ⊓ complementaryCurveIdeal C).subschemeι), he_inv, Category.id_comp]
  refine ⟨e.inv ≫ desc, hbot, a, b, hpo, ?_, ?_⟩
  · rw [← Category.assoc]
    exact (hres _ inf_le_right).trans (hpush.inr_desc (C.subscheme.toSpecΓ ≫ b) a hglue)
  · rw [← Category.assoc]
    exact (hres _ inf_le_left).trans (hpush.inl_desc (C.subscheme.toSpecΓ ≫ b) a hglue)

/-- **The pushout of a rational bridge exists and carries a contraction of the bridge.**  The
pushout square
```
C ∩ X' ⟶ X'
  ↓        ↓ a
Spec k' ⟶  Y
```
is [Stacks, Tag 0E25] applied to `Stacks.Curves.bridgePushoutSituation`, and the contraction is
the one produced by `Stacks.Curves.exists_contraction_pushoutScheme_bridge`. -/
@[stacks 0E3M "the pushout Y along C ∩ X' ⟶ Spec k' exists and receives the contraction c : X ⟶ Y"]
theorem exists_pushout_contraction_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    ∃ (Y : Scheme.{u}) (c : X ⟶ Y), IsContractionOfRationalBridge hC c := by
  obtain ⟨c, hc⟩ := exists_contraction_pushoutScheme_bridge hdim hnodal hC
  exact ⟨_, c, hc⟩

end Bridge

end Stacks.Curves
