module

import all StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.CapLocallyFinite
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommutingEveryCap
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindBivariantIdentification
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindCapCommute
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RelativeCycleGysinIntegral

/-!
# The exterior product over a Dedekind base in its second variable

Instances for the base change of a morphism of test schemes, and the compatibility of the exterior
product over a Dedekind base, in its second variable, with restriction to an open subscheme, with
proper pushforward along a closed immersion or from a coproduct of closed subschemes, and with
locally finite sums of point cycles.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Properties of the base change of a morphism of test schemes -/

section TestBaseChangeInstances

variable {Y Z T T' : Scheme.{u}} (w : Y ⟶ Z) (g : T ⟶ Z) (v : T' ⟶ T) (m : T' ⟶ Z)

/-- The base change of a flat morphism of test schemes is flat. -/
instance flat_testBaseChangeMapOfEq [Flat v] (hm : v ≫ g = m) :
    Flat (testBaseChangeMapOfEq w g v m hm) :=
  MorphismProperty.of_isPullback (isPullback_testBaseChangeMapOfEq w g v m hm)
    (P := @Flat) inferInstance

/-- The base change of a morphism of test schemes locally of finite type is locally of finite
type. -/
instance locallyOfFiniteType_testBaseChangeMapOfEq [LocallyOfFiniteType v] (hm : v ≫ g = m) :
    LocallyOfFiniteType (testBaseChangeMapOfEq w g v m hm) :=
  MorphismProperty.of_isPullback (isPullback_testBaseChangeMapOfEq w g v m hm)
    (P := @LocallyOfFiniteType) inferInstance

/-- The base change of a morphism of test schemes surjective on stalks is surjective on
stalks. -/
instance surjectiveOnStalks_testBaseChangeMapOfEq [SurjectiveOnStalks v] (hm : v ≫ g = m) :
    SurjectiveOnStalks (testBaseChangeMapOfEq w g v m hm) :=
  MorphismProperty.of_isPullback (isPullback_testBaseChangeMapOfEq w g v m hm)
    (P := @SurjectiveOnStalks) inferInstance

end TestBaseChangeInstances

/-! ### The exterior product over a Dedekind base in its second variable -/

section SecondFactor

variable (C : ChowSituation.{u}) {X T T' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : T ⟶ C.S) [LocallyOfFiniteType g] (v : T' ⟶ T) (m : T' ⟶ C.S) [LocallyOfFiniteType m]
  (hm : v ≫ g = m)

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType m] in
/-- The product `closure {x} ×_S closure {v y}` pulls back along `1 × v : X ×_S T' ⟶ X ×_S T` to
`closure {x} ×_S closure {y}`, as soon as the reduced closure of `v y` pulls back along `v` to the
reduced closure of `y`. -/
theorem comap_exteriorProductIdeal_testBaseChangeMapOfEq (x : X) (y : T')
    (hy : (integralComponentAt (v.base y)).comap v = integralComponentAt y) :
    (exteriorProductIdeal f g x (v.base y)).comap (testBaseChangeMapOfEq f g v m hm) =
      exteriorProductIdeal f m x y := by
  simp only [exteriorProductIdeal, Scheme.IdealSheafData.comap_sup,
    ← Scheme.IdealSheafData.comap_comp, testBaseChangeMapOfEq_fst, testBaseChangeMapOfEq_snd]
  rw [Scheme.IdealSheafData.comap_comp _ (pullback.snd f m) v]
  rw [show Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({v.base y} : Set T)) =
    integralComponentAt (v.base y) from rfl, hy]
  rfl

/-- **The exterior product multiplicity along the base change of an open immersion in the second
factor.** -/
theorem exteriorProductWeight_testBaseChangeMapOfEq_of_isOpenImmersion [IsOpenImmersion v]
    (j : ℤ) (x : X) (y : T') (w : (pullback f m : Scheme.{u})) :
    exteriorProductWeight C f g j x (v.base y) ((testBaseChangeMapOfEq f g v m hm).base w) =
      exteriorProductWeight C f m j x y w := by
  unfold exteriorProductWeight
  rw [← closedSubschemeCycleCoeff_congr C (pullback.fst f m ≫ f)
    (comap_exteriorProductIdeal_testBaseChangeMapOfEq C f g v m hm x y
      (comap_integralComponentAt_of_isOpenImmersion v y)) j w]
  exact (closedSubschemeCycleCoeff_comap_of_isOpenImmersion C (pullback.fst f g ≫ f)
    (pullback.fst f m ≫ f) _ (by rw [testBaseChangeMapOfEq_fst_assoc]) _ j w).symm

/-- **The exterior product multiplicity along the base change of a closed immersion in the second
factor.** -/
theorem exteriorProductWeight_testBaseChangeMapOfEq_of_isClosedImmersion [IsClosedImmersion v]
    (j : ℤ) (x : X) (y : T') (w : (pullback f m : Scheme.{u})) :
    exteriorProductWeight C f g j x (v.base y) ((testBaseChangeMapOfEq f g v m hm).base w) =
      exteriorProductWeight C f m j x y w := by
  set B := testBaseChangeMapOfEq f g v m hm with hB
  have hsq := isPullback_testBaseChangeMapOfEq f g v m hm
  have hker : B.ker ≤ exteriorProductIdeal f g x (v.base y) := by
    have hfst : hsq.flip.isoPullback.hom ≫ pullback.fst (pullback.snd f g) v = B :=
      hsq.flip.isoPullback_hom_fst
    rw [← hfst, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    refine le_trans (Scheme.IdealSheafData.comap_mono _ ?_) le_sup_right
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    show closure ({v.base y} : Set T) ⊆ (v.ker.support : Set T)
    rw [Scheme.Hom.support_ker]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨y, rfl⟩)
  unfold exteriorProductWeight
  rw [← closedSubschemeCycleCoeff_congr C (pullback.fst f m ≫ f)
    (comap_exteriorProductIdeal_testBaseChangeMapOfEq C f g v m hm x y
      (comap_integralComponentAt_of_isClosedImmersion v y)) j w]
  have key : ∀ (q : (pullback f m : Scheme.{u}) ⟶ C.S) [LocallyOfFiniteType q],
      q = B ≫ pullback.fst f g ≫ f →
      closedSubschemeCycleCoeff C q ((exteriorProductIdeal f g x (v.base y)).comap B).subschemeι
          j w =
        closedSubschemeCycleCoeff C (B ≫ pullback.fst f g ≫ f)
          ((exteriorProductIdeal f g x (v.base y)).comap B).subschemeι j w := by
    intro q _ hq; subst hq; rfl
  rw [key _ (by rw [hB, testBaseChangeMapOfEq_fst_assoc])]
  exact closedSubschemeCycleCoeff_comap_of_isClosedImmersion C (pullback.fst f g ≫ f) B _ hker
    j w

omit [LocallyOfFiniteType g] in
include hm in
/-- Dominating an irreducible component of the base is read off the image in the base. -/
theorem dominatesBaseComponent_comp_iff (y : T') :
    DominatesBaseComponent C m y ↔ DominatesBaseComponent C g (v.base y) := by
  subst hm
  unfold DominatesBaseComponent
  rw [Scheme.Hom.comp_apply]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType m] in
/-- The second projection of the base change `1 × v`. -/
theorem snd_testBaseChangeMapOfEq_apply (w : (pullback f m : Scheme.{u})) :
    (pullback.snd f g).base ((testBaseChangeMapOfEq f g v m hm).base w) =
      v.base ((pullback.snd f m).base w) := by
  rw [← Scheme.Hom.comp_apply, testBaseChangeMapOfEq_snd, Scheme.Hom.comp_apply]

/-- A finite sum over a function supported on the range of an injective map `g` is the sum over
the source of `g`. -/
private theorem finsum_eq_finsum_comp_of_support_subset_range {α β M : Type*} [AddCommMonoid M]
    (F : α → M) {g : β → α} (hg : Function.Injective g) (hsupp : Function.support F ⊆ Set.range g) :
    ∑ᶠ q, F q = ∑ᶠ j, F (g j) := by
  rw [← finsum_mem_univ F, finsum_mem_inter_support_eq _ Set.univ (Set.range g)
    (by rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp]), finsum_mem_range hg]

/-- **The exterior product over a Dedekind base commutes with restriction to an open subscheme in
its second variable**: `(α × β)|_{X ×_S T'} = α × β|_{T'}` for an open immersion `T' ⟶ T`. -/
theorem cycleGroupRestrict_exteriorProductDedekindCycles [IsOpenImmersion v] (n k : ℤ)
    (a : CycleGroup C f n) (b : CycleGroup C g k) :
    cycleGroupRestrict C (pullback.fst f g ≫ f) (pullback.fst f m ≫ f)
        (testBaseChangeMapOfEq f g v m hm) (by rw [testBaseChangeMapOfEq_fst_assoc]) (n + k - 1)
        (exteriorProductDedekindCycles C f g n k a b) =
      exteriorProductDedekindCycles C f m n k a (cycleGroupRestrict C g m v hm k b) := by
  classical
  set B := testBaseChangeMapOfEq f g v m hm with hB
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun w ↦ ?_)
  show (exteriorProductDedekindCycles C f g n k a b).1 (B.base w) =
    (exteriorProductDedekindCycles C f m n k a (cycleGroupRestrict C g m v hm k b)).1 w
  rw [exteriorProductDedekindCycles_apply, exteriorProductDedekindCycles_apply]
  have hinj : Function.Injective (Prod.map (id : X → X) v.base) :=
    Function.injective_id.prodMap v.isOpenEmbedding.injective
  have hsupp : Function.support (exteriorProductDedekindTerm C f g n k a b (B.base w)) ⊆
      Set.range (Prod.map (id : X → X) v.base) := by
    intro q hq
    obtain ⟨-, h2⟩ := mem_closure_of_exteriorProductDedekindTerm_ne_zero C f g n k a b _ q hq
    rw [hB, snd_testBaseChangeMapOfEq_apply] at h2
    obtain ⟨y, hy⟩ : q.2 ∈ Set.range v.base :=
      (specializes_iff_mem_closure.mpr h2).mem_open v.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
    exact ⟨(q.1, y), Prod.ext rfl hy⟩
  rw [finsum_eq_finsum_comp_of_support_subset_range _ hinj hsupp]
  refine finsum_congr fun q ↦ ?_
  unfold exteriorProductDedekindTerm
  simp only [Prod.map_fst, Prod.map_snd, id]
  have hw := exteriorProductWeight_testBaseChangeMapOfEq_of_isOpenImmersion C f g v m hm
    (n + k - 1) q.1 q.2 w
  unfold exteriorProductWeight at hw
  rw [dominatesBaseComponent_comp_iff C g v m hm, cycleGroupRestrict_apply, hB, hw]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType m] in
/-- The range of the base change `1 × v` of a morphism `v` of the second factor is the inverse
image of the range of `v` under the second projection. -/
theorem mem_range_testBaseChangeMapOfEq {z : (pullback f g : Scheme.{u})} {y : T'}
    (hz : (pullback.snd f g).base z = v.base y) :
    ∃ w : (pullback f m : Scheme.{u}), (testBaseChangeMapOfEq f g v m hm).base w = z ∧
      (pullback.snd f m).base w = y := by
  have hsq := (isPullback_testBaseChangeMapOfEq f g v m hm).flip
  obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback z y hz
  refine ⟨hsq.isoPullback.inv.base t, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_fst]
    exact ht1
  · rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd]
    exact ht2

/-- **The exterior product over a Dedekind base commutes with pushforward along a closed
immersion in its second variable**: `(1 × v)_*(α × β) = α × v_*β`. -/
theorem properPushforward_exteriorProductDedekindCycles_of_isClosedImmersion
    [IsClosedImmersion v] (n k : ℤ) (a : CycleGroup C f n) (b : CycleGroup C m k) :
    properPushforward C (pullback.fst f m ≫ f) (pullback.fst f g ≫ f)
        (testBaseChangeMapOfEq f g v m hm) (by rw [testBaseChangeMapOfEq_fst_assoc]) (n + k - 1)
        (exteriorProductDedekindCycles C f m n k a b) =
      exteriorProductDedekindCycles C f g n k a (properPushforward C m g v hm k b) := by
  classical
  set B := testBaseChangeMapOfEq f g v m hm with hB
  have hinj : Function.Injective (Prod.map (id : X → X) v.base) :=
    Function.injective_id.prodMap v.isClosedEmbedding.injective
  -- a contributing pair has its second entry in the range of `v`
  have hsnd : ∀ (z : (pullback f g : Scheme.{u})) (q : X × T),
      exteriorProductDedekindTerm C f g n k a (properPushforward C m g v hm k b) z q ≠ 0 →
        q.2 ∈ Set.range v.base := by
    intro z q hq
    by_contra hr
    unfold exteriorProductDedekindTerm at hq
    rw [properPushforward_apply_of_notMem_range C m g v hm k b hr] at hq
    simp at hq
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  by_cases hz : z ∈ Set.range B.base
  · obtain ⟨w, rfl⟩ := hz
    rw [properPushforward_apply_image_of_isClosedImmersion, exteriorProductDedekindCycles_apply,
      exteriorProductDedekindCycles_apply]
    have hsupp : Function.support (exteriorProductDedekindTerm C f g n k a
        (properPushforward C m g v hm k b) (B.base w)) ⊆
        Set.range (Prod.map (id : X → X) v.base) := by
      intro q hq
      obtain ⟨y, hy⟩ := hsnd _ q hq
      exact ⟨(q.1, y), Prod.ext rfl hy⟩
    rw [finsum_eq_finsum_comp_of_support_subset_range _ hinj hsupp]
    refine finsum_congr fun q ↦ ?_
    unfold exteriorProductDedekindTerm
    simp only [Prod.map_fst, Prod.map_snd, id]
    have hw := exteriorProductWeight_testBaseChangeMapOfEq_of_isClosedImmersion C f g v m hm
      (n + k - 1) q.1 q.2 w
    unfold exteriorProductWeight at hw
    rw [dominatesBaseComponent_comp_iff C g v m hm,
      properPushforward_apply_image_of_isClosedImmersion, hB, hw]
  · rw [properPushforward_apply_of_notMem_range C _ _ B _ _ _ hz,
      exteriorProductDedekindCycles_apply]
    symm
    refine finsum_eq_zero_of_forall_eq_zero fun q ↦ ?_
    by_contra hq
    obtain ⟨y, hy⟩ := hsnd z q hq
    obtain ⟨-, h2⟩ := mem_closure_of_exteriorProductDedekindTerm_ne_zero C f g n k a _ z q hq
    rw [← hy] at h2
    have hcl : (pullback.snd f g).base z ∈ Set.range v.base :=
      closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_range_self y))
        v.isClosedEmbedding.isClosed_range h2
    obtain ⟨y', hy'⟩ := hcl
    obtain ⟨w, hw, -⟩ := mem_range_testBaseChangeMapOfEq C f g v m hm hy'.symm
    exact hz ⟨w, hw⟩

omit [LocallyOfFiniteType f] in
/-- The base changes of the summand inclusions of a coproduct cover the base change of the
coproduct. -/
theorem exists_mem_range_testBaseChangeMapOfEq_sigmaι {I : Type u} (Z : I → Scheme.{u})
    (h : (∐ Z : Scheme.{u}) ⟶ C.S) [LocallyOfFiniteType h]
    [∀ i, LocallyOfFiniteType (Sigma.ι Z i ≫ h)] (x : (pullback f h : Scheme.{u})) :
    ∃ i, x ∈ Set.range (testBaseChangeMapOfEq f h (Sigma.ι Z i) (Sigma.ι Z i ≫ h) rfl) := by
  obtain ⟨i, t, ht⟩ := exists_mem_range_sigmaι Z ((pullback.snd f h).base x)
  obtain ⟨w, hw, -⟩ := mem_range_testBaseChangeMapOfEq C f h (Sigma.ι Z i) (Sigma.ι Z i ≫ h) rfl
    ht.symm
  exact ⟨i, w, hw⟩

omit [LocallyOfFiniteType f] in
/-- The base changes of the summand inclusions of a coproduct have pairwise disjoint ranges. -/
theorem pairwise_disjoint_range_testBaseChangeMapOfEq_sigmaι {I : Type u} (Z : I → Scheme.{u})
    (h : (∐ Z : Scheme.{u}) ⟶ C.S) [LocallyOfFiniteType h]
    [∀ i, LocallyOfFiniteType (Sigma.ι Z i ≫ h)] :
    Pairwise fun i l ↦
      Disjoint (Set.range (testBaseChangeMapOfEq f h (Sigma.ι Z i) (Sigma.ι Z i ≫ h) rfl))
        (Set.range (testBaseChangeMapOfEq f h (Sigma.ι Z l) (Sigma.ι Z l ≫ h) rfl)) := by
  intro i l hil
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  refine Set.disjoint_left.mp (pairwise_disjoint_range_sigmaι Z hil)
    ⟨(pullback.snd f (Sigma.ι Z i ≫ h)).base a, rfl⟩
    ⟨(pullback.snd f (Sigma.ι Z l ≫ h)).base b, ?_⟩
  have h1 := snd_testBaseChangeMapOfEq_apply C f h (Sigma.ι Z l) _ rfl b
  have h2 := snd_testBaseChangeMapOfEq_apply C f h (Sigma.ι Z i) _ rfl a
  rw [hb] at h1
  exact h1.symm.trans h2

end SecondFactor

/-! ### Proper pushforward along a morphism which is a closed immersion on each piece -/

/-- **Proper pushforward along a morphism which is a closed immersion on each piece of a
decomposition into open and closed subschemes.** Let `π : W ⟶ T` be proper and surjective on
stalks, and let `W` be covered by pairwise disjoint open immersions `eᵢ` with `eᵢ ≫ π` a closed
immersion. Then the coefficient at `y` of `π_*γ` is the sum over the pieces of the coefficients
of the pushforwards of the restrictions of `γ`: each point of `W` over `y` lies on exactly one
piece, and on it is the only point over `y`. -/
theorem properPushforward_apply_eq_finsum_of_pieces (C : ChowSituation.{u}) {W T : Scheme.{u}}
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sT : T ⟶ C.S) [LocallyOfFiniteType sT]
    (π : W ⟶ T) [IsProper π] [SurjectiveOnStalks π] (hπ : π ≫ sT = sW) {I : Type*}
    {P : I → Scheme.{u}} (e : ∀ i, P i ⟶ W) [∀ i, IsOpenImmersion (e i)]
    [∀ i, IsClosedImmersion (e i ≫ π)] (hcover : ∀ x : W, ∃ i, x ∈ Set.range (e i))
    (hdisjoint : Pairwise fun i l ↦ Disjoint (Set.range (e i)) (Set.range (e l))) (k : ℤ)
    (γ : CycleGroup C sW k) (y : T) :
    (properPushforward C sW sT π hπ k γ).1 y = ∑ᶠ i, (properPushforward C (e i ≫ sW) sT (e i ≫ π)
      (by rw [Category.assoc, hπ]) k (cycleGroupRestrict C sW (e i ≫ sW) (e i) rfl k γ)).1 y := by
  classical
  subst hπ
  have hres : ∀ x : W, Function.Bijective ((π.residueFieldMap x).hom) := fun x ↦
    bijective_residueFieldMap_of_surjective_stalkMap π x (π.stalkMap_surjective x)
  have hterm : ∀ x : W, γ.1 x *
      (if relativeDimension C.dimensionFunction (π ≫ sT) x =
          relativeDimension C.dimensionFunction sT (π.base x) then (π.residueDegree x : ℤ)
        else 0) = γ.1 x := by
    intro x
    rw [relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction π sT x
      (hres x), residueDegree_eq_one_of_bijective_residueFieldMap π x (hres x)]
    simp
  rw [properPushforward_apply, finsum_mem_congr rfl fun x _ ↦ hterm x]
  choose idx hidx using hcover
  set F : I → ℤ := fun i ↦ (properPushforward C (e i ≫ π ≫ sT) sT (e i ≫ π)
    (by rw [Category.assoc]) k (cycleGroupRestrict C (π ≫ sT) (e i ≫ π ≫ sT) (e i) rfl k γ)).1 y
    with hF
  have hFval : ∀ i (a : P i), (e i ≫ π).base a = y → F i = γ.1 ((e i).base a) := by
    intro i a ha
    have hpre : (e i ≫ π).base ⁻¹' {y} = {a} := by
      ext a'
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h ↦ (e i ≫ π).isClosedEmbedding.injective (h.trans ha.symm), fun h ↦ h ▸ ha⟩
    rw [hF]
    dsimp only
    rw [properPushforward_apply_of_isClosedImmersion, hpre, finsum_mem_singleton,
      cycleGroupRestrict_apply]
  have hidx_eq : ∀ x i, x ∈ Set.range (e i) → idx x = i := by
    intro x i hx
    by_contra hne
    exact Set.disjoint_left.mp (hdisjoint hne) (hidx x) hx
  have hclaim : ∀ i (a a' : P i), π.base ((e i).base a) = y → π.base ((e i).base a') = y →
      (e i).base a = (e i).base a' := by
    intro i a a' ha ha'
    have hy : (e i ≫ π).base a = (e i ≫ π).base a' := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ha, ha']
    rw [(e i ≫ π).isClosedEmbedding.injective hy]
  have hinj : Set.InjOn idx (π.base ⁻¹' {y}) := by
    intro x hx x' hx' h
    have hx2 : x ∈ Set.range (e (idx x')) := h ▸ hidx x
    obtain ⟨a, ha⟩ := hx2
    obtain ⟨a', ha'⟩ := hidx x'
    have hx1 : π.base x = y := hx
    have hx1' : π.base x' = y := hx'
    exact ha.symm.trans ((hclaim _ a a' (by rw [ha]; exact hx1) (by rw [ha']; exact hx1')).trans
      ha')
  have hsupp : Function.support F ⊆ idx '' (π.base ⁻¹' {y}) := by
    intro i hi
    by_contra hni
    refine hi ?_
    have hpre : (e i ≫ π).base ⁻¹' {y} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun a ha ↦ hni ⟨(e i).base a, ?_, ?_⟩
      · simpa [Scheme.Hom.comp_apply] using ha
      · exact hidx_eq _ i ⟨a, rfl⟩
    rw [hF]
    dsimp only
    rw [properPushforward_apply_of_isClosedImmersion, hpre, finsum_mem_empty]
  rw [finsum_mem_congr rfl fun x hx ↦ ?_, ← finsum_mem_image hinj,
    ← finsum_mem_univ F, finsum_mem_inter_support_eq F _ Set.univ
      (by rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp])]
  have key : ∀ i (a : P i), (e i).base a = x → γ.1 x = F i := by
    intro i a ha
    rw [hFval i a (by rw [Scheme.Hom.comp_apply, ha]; exact hx), ha]
  obtain ⟨a, ha⟩ := hidx x
  exact key _ a ha
/-! ### The exterior product with a locally finite sum of point cycles in the second variable -/

section PointSum

variable (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (u : U ⟶ C.S) [LocallyOfFiniteType u] (n k : ℤ)

/-- **The exterior product is additive over a cycle written as a sum of its point parts.** Let
`b` be a `k`-cycle supported on the image of an injective `pt : I → U`, and let `βᵢ` be the
cycle which is `b` at `pt i` and zero elsewhere. Then `a × b` is, coefficientwise, the sum of
the `a × βᵢ`. -/
theorem exteriorProductDedekindCycles_apply_eq_finsum_of_points (a : CycleGroup C sX n)
    (b : CycleGroup C u k) {I : Type*} (pt : I → U) (hpt : Function.Injective pt)
    (hb : Function.support (b.1 : U → ℤ) ⊆ Set.range pt) (β : I → CycleGroup C u k)
    (hβ : ∀ i y, (β i).1 y = open Classical in if y = pt i then b.1 (pt i) else 0)
    (z : (pullback sX u : Scheme.{u})) :
    (exteriorProductDedekindCycles C sX u n k a b).1 z =
      ∑ᶠ i, (exteriorProductDedekindCycles C sX u n k a (β i)).1 z := by
  classical
  set F := exteriorProductDedekindTerm C sX u n k a b z with hF
  -- each part is the sum over the first factor at the point `pt i`
  have hpart : ∀ i, (exteriorProductDedekindCycles C sX u n k a (β i)).1 z =
      ∑ᶠ x, F (x, pt i) := by
    intro i
    rw [exteriorProductDedekindCycles_apply]
    have hinj : Function.Injective fun x : X ↦ (x, pt i) := fun x x' h ↦ (Prod.ext_iff.1 h).1
    have hsupp : Function.support (exteriorProductDedekindTerm C sX u n k a (β i) z) ⊆
        Set.range fun x : X ↦ (x, pt i) := by
      intro q hq
      refine ⟨q.1, Prod.ext rfl ?_⟩
      by_contra hne
      refine hq ?_
      unfold exteriorProductDedekindTerm
      rw [hβ, if_neg (Ne.symm hne)]
      simp
    rw [finsum_eq_finsum_comp_of_support_subset_range _ hinj hsupp]
    refine finsum_congr fun x ↦ ?_
    rw [hF]
    unfold exteriorProductDedekindTerm
    rw [hβ, if_pos rfl]
  simp_rw [hpart]
  rw [exteriorProductDedekindCycles_apply, ← hF]
  have hinj : Function.Injective fun q : I × X ↦ (q.2, pt q.1) := by
    intro q q' h
    have h1 := (Prod.ext_iff.1 h).1
    have h2 := hpt (Prod.ext_iff.1 h).2
    exact Prod.ext h2 h1
  have hsupp : Function.support F ⊆ Set.range fun q : I × X ↦ (q.2, pt q.1) := by
    intro q hq
    have hbq : b.1 q.2 ≠ 0 := by
      intro h0
      refine hq ?_
      rw [hF]
      unfold exteriorProductDedekindTerm
      simp [h0]
    obtain ⟨i, hi⟩ := hb hbq
    exact ⟨(i, q.1), Prod.ext rfl hi⟩
  rw [finsum_eq_finsum_comp_of_support_subset_range F hinj hsupp]
  refine finsum_curry (fun q : I × X ↦ F (q.2, pt q.1)) ?_
  refine ((exteriorProductDedekindTerm_support_finite C sX u n k a b z).preimage
    hinj.injOn).subset fun q hq ↦ hq

/-- **The exterior product over a Dedekind base commutes with pushforward from a coproduct of
closed subschemes in its second variable.** Let `vᵢ : Zᵢ ⟶ U` be closed immersions with
`π = ∐ vᵢ` proper, and let `γ` be a cycle on `∐ Zᵢ`. Then `(1 × π)_*(a × γ)` is, coefficientwise,
the sum over `i` of `a × vᵢ_*(γ|_{Zᵢ})`: on the piece `X ×_S Zᵢ` the morphism `1 × π` is the
closed immersion `1 × vᵢ`. -/
theorem properPushforward_exteriorProductDedekindCycles_sigmaDesc_apply {I : Type u}
    (Z : I → Scheme.{u}) (v : ∀ i, Z i ⟶ U) [∀ i, IsClosedImmersion (v i)]
    [IsProper (Sigma.desc v)] (a : CycleGroup C sX n) (γ : CycleGroup C (Sigma.desc v ≫ u) k)
    (z : (pullback sX u : Scheme.{u})) :
    (properPushforward C (pullback.fst sX (Sigma.desc v ≫ u) ≫ sX) (pullback.fst sX u ≫ sX)
        (testBaseChangeMapOfEq sX u (Sigma.desc v) (Sigma.desc v ≫ u) rfl)
        (by rw [testBaseChangeMapOfEq_fst_assoc]) (n + k - 1)
        (exteriorProductDedekindCycles C sX (Sigma.desc v ≫ u) n k a γ)).1 z =
      ∑ᶠ i, (exteriorProductDedekindCycles C sX u n k a
        (properPushforward C (Sigma.ι Z i ≫ Sigma.desc v ≫ u) u (v i)
          (by rw [← Category.assoc, Sigma.ι_desc]) k
          (cycleGroupRestrict C (Sigma.desc v ≫ u) (Sigma.ι Z i ≫ Sigma.desc v ≫ u) (Sigma.ι Z i)
            rfl k γ))).1 z := by
  set π := Sigma.desc v with hπdef
  set π' := testBaseChangeMapOfEq sX u π (π ≫ u) rfl with hπ'
  have hvi : ∀ i, v i ≫ u = Sigma.ι Z i ≫ π ≫ u := fun i ↦ by
    rw [← Category.assoc, hπdef, Sigma.ι_desc]
  set B := fun i ↦ testBaseChangeMapOfEq sX (π ≫ u) (Sigma.ι Z i) (Sigma.ι Z i ≫ π ≫ u) rfl
    with hB
  have hBC : ∀ i, B i ≫ π' = testBaseChangeMapOfEq sX u (v i) (Sigma.ι Z i ≫ π ≫ u) (hvi i) := by
    intro i
    refine pullback.hom_ext ?_ ?_
    · simp [hB, hπ']
    · simp [hB, hπ', hπdef]
  have _ : ∀ i, SurjectiveOnStalks (v i) := fun i ↦ inferInstance
  have _ : SurjectiveOnStalks π := surjectiveOnStalks_sigmaDesc Z v
  have _ : ∀ i, IsClosedImmersion (B i ≫ π') := fun i ↦ by rw [hBC i]; infer_instance
  have hcover := exists_mem_range_testBaseChangeMapOfEq_sigmaι C sX Z (π ≫ u)
  have hdisjoint := pairwise_disjoint_range_testBaseChangeMapOfEq_sigmaι C sX Z (π ≫ u)
  rw [properPushforward_apply_eq_finsum_of_pieces C _ _ π' _ B hcover hdisjoint]
  refine finsum_congr fun i ↦ ?_
  rw [← properPushforward_exteriorProductDedekindCycles_of_isClosedImmersion C sX u (v i)
    (Sigma.ι Z i ≫ π ≫ u) (hvi i) n k a]
  have hs : B i ≫ pullback.fst sX (π ≫ u) ≫ sX =
      pullback.fst sX (Sigma.ι Z i ≫ π ≫ u) ≫ sX := by
    rw [hB]
    exact testBaseChangeMapOfEq_fst_assoc _ _ _ _ _ _
  have hR2 := cycleGroupRestrict_exteriorProductDedekindCycles C sX (π ≫ u)
    (Sigma.ι Z i) (Sigma.ι Z i ≫ π ≫ u) rfl n k a γ
  have hc : (cycleGroupRestrict C (pullback.fst sX (π ≫ u) ≫ sX)
      (B i ≫ pullback.fst sX (π ≫ u) ≫ sX) (B i) rfl (n + k - 1)
      (exteriorProductDedekindCycles C sX (π ≫ u) n k a γ)).1 =
      (exteriorProductDedekindCycles C sX (Sigma.ι Z i ≫ π ≫ u) n k a
        (cycleGroupRestrict C (π ≫ u) (Sigma.ι Z i ≫ π ≫ u) (Sigma.ι Z i) rfl k γ)).1 := by
    refine Function.locallyFinsuppWithin.ext fun w ↦ ?_
    have h := congrArg (fun c ↦ c.1 w) hR2
    simp only [cycleGroupRestrict_apply] at h
    rw [cycleGroupRestrict_apply]
    exact h
  have hq' : (B i ≫ π') ≫ pullback.fst sX u ≫ sX =
      pullback.fst sX (Sigma.ι Z i ≫ π ≫ u) ≫ sX := by
    rw [hBC i]
    exact testBaseChangeMapOfEq_fst_assoc _ _ _ _ _ _
  rw [properPushforward_val_congr C hs rfl (B i ≫ π') _ hq' _ _ hc]
  simp only [hBC i]
  rfl

end PointSum

end Stacks.Chow

end
