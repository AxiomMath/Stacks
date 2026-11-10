module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrierCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.OpenRestrictionFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSumGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SchemeSizeBounds

/-!
# A Chow cohomology class is detected on integral spaces

In the situation of Stacks 0EDT let `X/B` be good and let `c ∈ A^p(X)`. **Stacks 0ERS** says
that `c` is zero if and only if `c ∩ [Y] = 0` in `CH_*(Y)` for every integral algebraic space `Y`
locally of finite type over `X`.

The forward implication is the vanishing of the zero class. For the converse let `X' ⟶ X` be a
test space and `α = ∑ n_i [Y_i] ∈ Z_k(X')`, the `Y_i ⊆ X'` a locally finite family of integral
closed subspaces. Then `α` is the pushforward of the cycle `α' = ∑ n_i [Y_i]` on the disjoint
union `X'' = ∐ Y_i` along the proper morphism `X'' ⟶ X'`, so by the first axiom of a bivariant
class it suffices that `c ∩ α' = 0` in `CH_{k-p}(X'')`. The pieces `Y_i` of `X''` are open and
closed, and a cycle on `X''` whose restriction to every piece is rationally equivalent to zero is
itself rationally equivalent to zero (the injectivity half of `CH(X'') = ∏ CH(Y_i)`). The
restriction to a piece is flat pullback along an open immersion, with which capping with `c`
commutes, and `α'` restricts to `n_i [Y_i]`, so `c ∩ α'` restricts to `n_i (c ∩ [Y_i]) = 0`.

## Main definitions

* `AlgebraicGeometry.Space.ChowCohomologyClass.CapsFundamentalClassesToZero`: the condition
  `c ∩ [Y] = 0` for every good integral algebraic space `Y` over `X`.

## Main results

* `AlgebraicGeometry.Space.isIntegralSpace_of_iso`: integrality is invariant under isomorphism.
* `AlgebraicGeometry.Space.properCyclePushforward_integralClosedSubspaceCycle_of_isClosedImmersion`:
  the pushforward of `[V]` along a closed immersion is the cycle of the image of `V`.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_of_forall_cycleGroupRestrict`:
  on a space decomposed into open and closed subspaces, a cycle whose restriction to every piece
  is rationally equivalent to zero is rationally equivalent to zero.
* `AlgebraicGeometry.Space.ChowCohomologyClass.eq_zero_iff_capsFundamentalClassesToZero`:
  **Stacks 0ERS**.

## Implementation notes

The class `c` is an element of `AlgebraicGeometry.Space.ChowCohomologyClass`, the group
`A^p(X) = A^p(X ⟶ X)` over the Chow groups `AlgebraicGeometry.Space.chowGroupCanonical` of
Stacks 0EQ6, in which the fibre product `Y ×_X X` of a test space is `Y` itself. An integral
algebraic space `Y` locally of finite type over `X` is a good test space `g : Y ⟶ X` over the base
with `Y` integral, and `[Y] ∈ Z_k(Y)` is the cycle of `Y` as an integral closed subspace of
itself, `AlgebraicGeometry.Space.IntegralClosedSubspace.top`; it is zero unless `k` is the
δ-dimension of `Y`, so quantifying over all `k` is quantifying over the class `[Y] ∈ CH_*(Y)`.

The disjoint union `∐ Y_i` is `AlgebraicGeometry.Space.closedSubspacesCoproduct`, indexed by a
set of points of an atlas of `X'`, one over the generic point of each member of the support, so
that the index type is small enough for the disjoint union of atlases to exist in the site.

## References

* [Stacks Project, Tag 0ERS](https://stacks.math.columbia.edu/tag/0ERS)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0ERK](https://stacks.math.columbia.edu/tag/0ERK)
* [Stacks Project, Tag 0ES2](https://stacks.math.columbia.edu/tag/0ES2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Integrality along an isomorphism -/

section Integral

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Integrality is invariant under isomorphism.** An algebraic space isomorphic to an integral
one is integral: reducedness is read on an étale atlas, which composes with the isomorphism,
decency is invariant, and the spaces of points are homeomorphic. -/
theorem isIntegralSpace_of_iso (e : X ≅ Y) (h : IsIntegralSpace B S hS X) :
    IsIntegralSpace B S hS Y := by
  refine ⟨?_, isDecentSpace_of_iso B S hS e h.2.1,
    (pointsHomeomorphOfIso B S hS e).irreducibleSpace_iff.1 h.2.2⟩
  obtain ⟨U, a, haSurjective, haEtale, hP⟩ := h.1
  exact ⟨U, a ≫ e.hom, MorphismProperty.RespectsIso.postcomp _ e.hom a haSurjective,
    MorphismProperty.RespectsIso.postcomp _ e.hom a haEtale, hP⟩

end Integral

/-! ### The cycle of an integral closed subspace along a closed immersion -/

section ClosedImmersion

variable (D : BaseSpaceDimensionSituation.{u})
  {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
  (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

include hX in
/-- The δ-dimension of the closure of the image of an integral closed subspace along a closed
immersion over the base is its δ-dimension: the generic point goes to the generic point, and an
immersion does not change the dimension function. -/
theorem deltaDimension_closureImage_of_isClosedImmersion {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsClosedImmersion D.site D.base D.base_mem f)
    (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) f V) = deltaDimension D sX V := by
  change D.deltaValue sY (IntegralClosedSubspace.ambientGenericPoint D.site D.base D.base_mem _) =
    D.deltaValue sX (V.ambientGenericPoint D.site D.base D.base_mem)
  rw [IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem hX.1
    hY.1, ← D.deltaValue_comp_of_isLocallyQuasiFinite hX.1 hY.1 f sY
      (isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem f
        (isImmersion_of_isClosedImmersion D.site D.base D.base_mem hf)) hY.2.2, hfB]

/-- **Pushforward of the cycle of an integral closed subspace along a closed immersion.** For a
closed immersion `f : X ⟶ Y` over the base, `f_*[V]_k = [f(V)]_k`: the degree of Stacks 0EP1 of a
closed immersion is `1` and it does not change δ-dimensions. -/
theorem properCyclePushforward_integralClosedSubspaceCycle_of_isClosedImmersion {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (hf : IsClosedImmersion D.site D.base D.base_mem f)
    (V : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ) :
    properCyclePushforward D sX hX sY hY hfB
        (isQuasiCompact_of_isClosedImmersion' D.site D.base D.base_mem hf) k
        (integralClosedSubspaceCycle D sX V k) =
      integralClosedSubspaceCycle D sY (IntegralClosedSubspace.closureImage D.site D.base
        D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) f V) k := by
  classical
  have hdim := deltaDimension_closureImage_of_isClosedImmersion D sX hX sY hY hfB hf V
  have hdeg : properCycleDegree D sX hX sY hY f V = 1 := by
    rw [properCycleDegree, ite_eq_left hdim]
    have hone : functionFieldDegree D sX hX sY hY f V = 1 :=
      IntegralClosedSubspace.degreeOverClosureImage_eq_one_of_isClosedImmersion D.site D.base
        D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) (D.isDecentSpace_of_isGood sX hX) hf V
    rw [hone, Nat.cast_one]
  refine Subtype.ext (funext fun T => ?_)
  rw [properPushforward_apply, finsum_eq_single _ V fun Z hZ => by
    rw [integralClosedSubspaceCycle_coe,
      integralClosedSubspaceCycleCoeff_of_ne D sX V k hZ, zero_mul]]
  simp only [integralClosedSubspaceCycle_coe, integralClosedSubspaceCycleCoeff, properCycleMult,
    hdeg, hdim]
  by_cases hT : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) f V = T
  · subst hT
    simp
  · simp [hT, Ne.symm hT]

end ClosedImmersion

/-! ### Rational equivalence on a space decomposed into open and closed subspaces -/

section Clopen

variable (D : BaseSpaceDimensionSituation.{u})
  {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space) (hY : D.IsGood sY)
  {I : Type u} (R : I → Subfunctor Y)
  (hRo : ∀ i, IsOpenSubspace D.site D.base D.base_mem (R i))
  (hRc : ∀ i, IsClosedSubspace D.site D.base D.base_mem (R i))
  (hdisj : ∀ i j, i ≠ j → Disjoint (subspacePointSet D.site D.base D.base_mem Y (R i))
    (subspacePointSet D.site D.base D.base_mem Y (R j)))
  (hcov : ∀ p, ∃ i, p ∈ subspacePointSet D.site D.base D.base_mem Y (R i))

include hY hRo hRc hdisj hcov in
/-- A family of open and closed subspaces with disjoint covering point sets is a decomposition
into open and closed subspaces. -/
theorem isClopenSubspaceDecomposition_ι :
    IsClopenSubspaceDecomposition D sY fun i => (R i).ι where
  isGood := hY
  isGoodPiece i := isGood_ι_of_isClosedSubspace D sY hY (R i) (hRc i)
  isOpenImmersion i := (hRo i).2
  disjoint i j hij := hdisj i j hij
  iUnion_pieceRange_eq_univ :=
    Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 (hcov p)

include hRo hdisj hcov in
/-- The point sets of a family of open subspaces with disjoint covering point sets form a
locally finite family: each point has the piece containing it as a neighbourhood, which meets no
other piece. -/
theorem locallyFinite_subspacePointSet_of_disjoint {J : Type*} (e : J → I)
    (he : Function.Injective e) :
    LocallyFinite fun j => subspacePointSet D.site D.base D.base_mem Y (R (e j)) := by
  intro p
  obtain ⟨i, hi⟩ := hcov p
  refine ⟨subspacePointSet D.site D.base D.base_mem Y (R i),
    (isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem _ (hRo i).2).mem_nhds hi,
    Set.Subsingleton.finite fun j hj j' hj' => he ?_⟩
  obtain ⟨q, hqj, hqi⟩ := hj
  obtain ⟨q', hqj', hqi'⟩ := hj'
  have key : ∀ {j q}, q ∈ subspacePointSet D.site D.base D.base_mem Y (R (e j)) →
      q ∈ subspacePointSet D.site D.base D.base_mem Y (R i) → e j = i := fun hqj hqi => by
    by_contra hne
    exact (hdisj _ _ hne).le_bot ⟨hqj, hqi⟩
  rw [key hqj hqi, key hqj' hqi']

include hRo hRc hdisj hcov in
/-- **A cycle on a space decomposed into open and closed subspaces is rationally equivalent to
zero as soon as its restriction to every piece is.** This is the injectivity half of
`CH_k(Y) = ∏ CH_k(Y_i)` (Stacks 0ES2): the cycle is the locally finite sum of the pushforwards of
its restrictions, each of which is rationally equivalent to zero within its piece, and the pieces
form a locally finite family. -/
theorem isRationallyEquivalentToZeroCanonical_of_forall_cycleGroupRestrict (k : ℤ)
    (β : CycleGroup D sY k)
    (hβ : ∀ i, IsRationallyEquivalentToZeroCanonical.{u + 1} D ((R i).ι ≫ sY)
      (isGood_ι_of_isClosedSubspace D sY hY (R i) (hRc i)) k
      (cycleGroupRestrict D sY hY ((R i).ι ≫ sY)
        (isGood_ι_of_isClosedSubspace D sY hY (R i) (hRc i)) (hRo i).2 rfl k β)) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D sY hY k β := by
  classical
  have h := isClopenSubspaceDecomposition_ι D sY hY R hRo hRc hdisj hcov
  have hYdec := D.isDecentSpace_of_isGood sY hY
  let res : ∀ i, CycleGroup D ((R i).ι ≫ sY) k := fun i =>
    cycleGroupRestrict D sY hY ((R i).ι ≫ sY)
      (isGood_ι_of_isClosedSubspace D sY hY (R i) (hRc i)) (hRo i).2 rfl k β
  let γ : ULift.{u + 1} I → CycleGroup D sY k := fun j =>
    cycleGroupClosedPushforward D hY.1 (hRc j.down).1 hYdec (hRc j.down).2 sY hY.2.2
      ((R j.down).ι ≫ sY) rfl k (res j.down)
  refine isRationallyEquivalentToZeroCanonical_finsum.{u + 1} D sY hY k γ
    (fun j => subspacePointSet D.site D.base D.base_mem Y (R j.down))
    (locallyFinite_subspacePointSet_of_disjoint D R hRo hdisj hcov ULift.down
      ULift.down_injective) (fun j => ?_) (fun Z => ?_)
  · exact exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward
      D sY hY (R j.down) (hRc j.down) k (hβ j.down)
  · -- `Z` lies in the piece of its index, and only that summand contributes
    set i₀ := h.index Z
    have hZ := h.pieceClosureImage_pieceSubspace Z
    set V := h.pieceSubspace Z
    have hpush : IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 (hRc i₀).1
        hYdec (hRc i₀).2 V = Z := by
      rwa [← IntegralClosedSubspace.closureImage_eq_pushforward]
    rw [finsum_eq_single _ (ULift.up i₀)]
    · change β.1 Z = cycleClosedPushforward D hY.1 (hRc i₀).1 hYdec (hRc i₀).2 (res i₀).1 Z
      rw [← hpush, cycleClosedPushforward_apply_pushforward, cycleGroupRestrict_apply,
        IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem hY.1
          (hRc i₀).1 hYdec (hRc i₀).2]
    · intro j hj
      change cycleClosedPushforward D hY.1 (hRc j.down).1 hYdec (hRc j.down).2
        (res j.down).1 Z = 0
      refine cycleClosedPushforward_apply_of_forall_ne D hY.1 (hRc j.down).1 hYdec
        (hRc j.down).2 _ Z fun V' hV' => hj ?_
      have hsubj : subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆
          pieceRange D (fun i => (R i).ι) j.down := by
        rw [← hV', IntegralClosedSubspace.subspacePointSet_pushforward]
        exact Set.image_subset_range _ _
      exact congrArg ULift.up (h.index_eq Z hsubj).symm

end Clopen

/-! ### Stacks 0ERS -/

section Vanishing

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
  (hX : D.IsGood sX) {p : ℤ}

/-- **The condition of Stacks 0ERS.** A class `c ∈ A^p(X)` caps the fundamental class of every
integral algebraic space locally of finite type over `X` to zero: for every good test space
`g : Y ⟶ X` with `Y` integral and every degree `k`, `c ∩ [Y]_k = 0` in `CH_{k-p}(Y)`, where
`[Y]_k` is the cycle of `Y` as an integral closed subspace of itself (zero unless `k` is the
δ-dimension of `Y`). -/
def ChowCohomologyClass.CapsFundamentalClassesToZero (c : ChowCohomologyClass D sX hX p) :
    Prop :=
  ∀ ⦃Y : D.Ambient⦄ (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hint : IsIntegralSpace D.site D.base D.base_mem Y) (k l : ℤ) (hkl : l + p = k),
    c.cap g hY k l hkl (chowClassCanonical.{u + 1} D (g ≫ sX) hY k
      (integralClosedSubspaceCycle D (g ≫ sX)
        (IntegralClosedSubspace.top D.site D.base D.base_mem hY.1 hint) k)) = 0

/-- The support of a cycle is indexed by a type of the working universe of cardinality below the
cutoff of the site: one point of an atlas over the generic point of each member. -/
theorem exists_index_support {Y : D.Ambient} (sY : Y ⟶ D.space) (hY : D.IsGood sY) {k : ℤ}
    (α : CycleGroup D sY k) :
    ∃ (I : Type u) (W : I → IntegralClosedSubspace D.site D.base D.base_mem Y),
      #I < D.site.cutoff ∧ Function.Injective W ∧ (∀ i, α.1 (W i) ≠ 0) ∧
        ∀ Z, α.1 Z ≠ 0 → ∃ i, W i = Z := by
  classical
  obtain ⟨U, a, hasurj, -⟩ := hY.1.exists_atlas
  have hsurj : Function.Surjective (pointsMap D.site D.base D.base_mem _ a) :=
    isSurjective_of_presheafSurjective D.site D.base D.base_mem a hasurj
  let s := {Z : IntegralClosedSubspace D.site D.base D.base_mem Y | α.1 Z ≠ 0}
  let f : s → (BigFppfOver.toScheme D.site D.base D.base_mem).obj U := fun Z =>
    pointsEquivScheme D.site D.base D.base_mem U
      (Function.surjInv hsurj (Z.1.ambientGenericPoint D.site D.base D.base_mem))
  have hf : Function.Injective f := by
    intro Z Z' hZZ'
    have h1 := congrArg (pointsMap D.site D.base D.base_mem _ a)
      ((pointsEquivScheme D.site D.base D.base_mem U).injective hZZ')
    rw [Function.surjInv_eq hsurj, Function.surjInv_eq hsurj] at h1
    exact Subtype.ext (IntegralClosedSubspace.injective_ambientGenericPoint D.site D.base
      D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) h1)
  let e := Equiv.ofInjective f hf
  refine ⟨Set.range f, fun i => (e.symm i).1,
    (Cardinal.mk_set_le _).trans_lt (mk_points_lt_cutoff D.site D.base D.base_mem U),
    fun i j hij => e.symm.injective (Subtype.ext hij), fun i => (e.symm i).2,
    fun Z hZ => ⟨e ⟨Z, hZ⟩, by simp⟩⟩

include hX in
/-- **Stacks 0ERS, the forward implication.** The zero class caps every fundamental class to
zero. -/
theorem ChowCohomologyClass.zero_capsFundamentalClassesToZero :
    (0 : ChowCohomologyClass D sX hX p).CapsFundamentalClassesToZero D sX hX :=
  fun _ _ _ _ _ _ _ => rfl

/-- **Stacks 0ERS, the content of the converse.** If `c ∈ A^p(X)` caps the fundamental class of
every good integral space over `X` to zero, then it caps every cycle on every good test space to
zero. -/
theorem ChowCohomologyClass.cap_chowClassCanonical_eq_zero (c : ChowCohomologyClass D sX hX p)
    (hc : c.CapsFundamentalClassesToZero D sX hX) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (k l : ℤ) (hkl : l + p = k) (α : CycleGroup D (g ≫ sX) k) :
    c.cap g hY k l hkl (chowClassCanonical.{u + 1} D (g ≫ sX) hY k α) = 0 := by
  classical
  -- the support of `α`, and the disjoint union of its members
  obtain ⟨I, W, hIcard, hWinj, hWne, hWsupp⟩ := exists_index_support D (g ≫ sX) hY α
  have hWfin : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem Y
      (W i).subspace := by
    have h0 := α.2.1.comp_injective hWinj
    refine h0.subset fun i => ?_
    simp only [Function.comp_apply, ite_eq_right (hWne i), subset_rfl]
  let Z : I → Subfunctor Y := fun i => (W i).subspace
  have hZ : ∀ i, IsClosedSubspace D.site D.base D.base_mem (Z i) := fun i =>
    (W i).isClosedSubspace
  let P := closedSubspacesCoproduct Z hZ
  let d : P.obj ⟶ Y := closedSubspacesCoproductDesc Z hZ hY.1
  have hPalg : IsAlgebraicSpace D.site D.base D.base_mem P.obj :=
    isAlgebraicSpace_closedSubspacesCoproduct Z hZ hY.1 hIcard
  have hd : IsProper D.site D.base D.base_mem d :=
    isProper_closedSubspacesCoproductDesc hY.1 hIcard hWfin
  have hP : D.IsGood ((d ≫ g) ≫ sX) := by
    rw [Category.assoc]
    exact ⟨hPalg, isQuasiSeparated_comp D.site D.base D.base_mem hPalg hY.1 d (g ≫ sX)
      (isQuasiSeparated_of_isSeparated D.site D.base D.base_mem hd.1) hY.2.1,
      isLocallyOfFiniteType_comp D.site D.base D.base_mem hPalg hY.1 D.isAlgebraicSpace d
        (g ≫ sX) hd.2.1.1 hY.2.2⟩
  -- the pieces of the disjoint union
  let ι : ∀ i, (Z i).toFunctor ⟶ P.obj := fun i => (closedSubspacesCoproductι Z hZ i).hom
  have hmono : ∀ i, Mono (ι i) := fun i => mono_closedSubspacesCoproductι Z hZ i
  let R : I → Subfunctor P.obj := fun i => Subfunctor.range (ι i)
  have hRo : ∀ i, IsOpenSubspace D.site D.base D.base_mem (R i) := fun i =>
    isOpenSubspace_range_cofan_inj _ (isColimitClosedSubspacesCoproduct Z hZ) i (hZ i).1
  have hRc : ∀ i, IsClosedSubspace D.site D.base D.base_mem (R i) := fun i =>
    isClosedSubspace_range_cofan_inj _ (isColimitClosedSubspacesCoproduct Z hZ) i (hZ i).1
  have hrange : ∀ i, subspacePointSet D.site D.base D.base_mem P.obj (R i) =
      Set.range (pointsMap D.site D.base D.base_mem _ (ι i)) := by
    intro i
    have := hmono i
    ext q
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨z, rfl⟩ := pointsMap_surjective_of_isIso D.site D.base D.base_mem
        (Subfunctor.toRange (ι i)) r
      exact ⟨z, by rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨pointsMap D.site D.base D.base_mem _ (Subfunctor.toRange (ι i)) z,
        by rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]⟩
  have hdisj : ∀ i j, i ≠ j → Disjoint (subspacePointSet D.site D.base D.base_mem P.obj (R i))
      (subspacePointSet D.site D.base D.base_mem P.obj (R j)) := fun i j hij => by
    rw [hrange, hrange]
    exact disjoint_range_pointsMap_closedSubspacesCoproductι (Z := Z) (hZ := hZ) hij
  have hcov : ∀ q, ∃ i, q ∈ subspacePointSet D.site D.base D.base_mem P.obj (R i) := fun q => by
    obtain ⟨i, hi⟩ := exists_mem_range_pointsMap_closedSubspacesCoproductι hY.1 hIcard q
    exact ⟨i, (hrange i).symm ▸ hi⟩
  -- each piece is integral, being isomorphic to a member
  have hint : ∀ i, IsIntegralSpace D.site D.base D.base_mem (R i).toFunctor := fun i => by
    have := hmono i
    exact isIntegralSpace_of_iso D.site D.base D.base_mem (asIso (Subfunctor.toRange (ι i)))
      (W i).isIntegralSpace
  let U : I → IntegralClosedSubspace D.site D.base D.base_mem P.obj := fun i =>
    ⟨R i, hRc i, hint i⟩
  have hUfin : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem P.obj
      (U i).subspace :=
    locallyFinite_subspacePointSet_of_disjoint D R hRo hdisj hcov id Function.injective_id
  have htop : ∀ i, (U i).whole D.site D.base D.base_mem =
      IntegralClosedSubspace.top D.site D.base D.base_mem (hRc i).1 (hint i) := fun i =>
    IntegralClosedSubspace.eq_of_subspacePointSet_eq D (hRc i).1
      ((IntegralClosedSubspace.subspacePointSet_whole D.site D.base D.base_mem (U i)).trans
        (IntegralClosedSubspace.range_pointsMap_top D.site D.base D.base_mem _ _).symm)
  -- the cycle `α' = ∑ n_i [Y_i]` on the disjoint union
  let cI : ∀ i, CycleGroup D ((U i).subspace.ι ≫ (d ≫ g) ≫ sX) k := fun i =>
    α.1 (W i) • integralClosedSubspaceCycle D ((U i).subspace.ι ≫ (d ≫ g) ≫ sX)
      ((U i).whole D.site D.base D.base_mem) k
  let α' : CycleGroup D ((d ≫ g) ≫ sX) k := cycleFamilySum D ((d ≫ g) ≫ sX) hP U hUfin k cI
  -- `α'` pushes forward to `α`
  have hfac : ∀ i, ∃ _ : IsIso (Subfunctor.toRange (ι i)),
      (U i).subspace.ι ≫ d = inv (Subfunctor.toRange (ι i)) ≫ (W i).subspace.ι := fun i => by
    have := hmono i
    refine ⟨inferInstance, ?_⟩
    have hRι : (R i).ι = inv (Subfunctor.toRange (ι i)) ≫ ι i :=
      (IsIso.eq_inv_comp _).2 (Subfunctor.toRange_ι _)
    change (R i).ι ≫ d = _
    rw [hRι, Category.assoc]
    exact congrArg _ (closedSubspacesCoproductι_desc Z hZ hY.1 i)
  have hUd : ∀ i, IsClosedImmersion D.site D.base D.base_mem ((U i).subspace.ι ≫ d) := fun i => by
    obtain ⟨_, hf⟩ := hfac i
    rw [hf]
    exact MorphismProperty.RespectsIso.precomp _ _ _ (W i).isClosedSubspace.2
  have hclos : ∀ i, IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood (g ≫ sX) hY) ((U i).subspace.ι ≫ d)
      ((U i).whole D.site D.base D.base_mem) = W i := fun i => by
    have := hmono i
    refine IntegralClosedSubspace.eq_of_subspacePointSet_eq D hY.1 ?_
    rw [IntegralClosedSubspace.subspacePointSet_closureImage,
      IntegralClosedSubspace.subspacePointSet_whole, Set.image_univ]
    have hr : Set.range (pointsMap D.site D.base D.base_mem _ ((U i).subspace.ι ≫ d)) =
        subspacePointSet D.site D.base D.base_mem Y (W i).subspace := by
      obtain ⟨_, hf⟩ := hfac i
      rw [hf, pointsMap_comp, Set.range_comp,
        (pointsMap_surjective_of_isIso D.site D.base D.base_mem _).range_eq, Set.image_univ]
    rw [hr]
    exact (isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1
      (W i)).closure_eq
  have hpush : properCyclePushforward D ((d ≫ g) ≫ sX) hP (g ≫ sX) hY
      (Category.assoc d g sX).symm hd.2.1.2 k α' = α := by
    have key : ∀ i, properCyclePushforward D ((d ≫ g) ≫ sX) hP (g ≫ sX) hY
        (Category.assoc d g sX).symm hd.2.1.2 k
          (integralClosedSubspacePushforward D ((d ≫ g) ≫ sX) hP (U i) k (cI i)) =
        α.1 (W i) • integralClosedSubspaceCycle D (g ≫ sX) (W i) k := fun i => by
      rw [← properCyclePushforward_ι_eq_integralClosedSubspacePushforward,
        properCyclePushforward_comp D _ _ _ _ hP hY rfl (Category.assoc d g sX).symm
          (isProper_integralClosedSubspace_ι D hP.1 (U i)) hd, map_zsmul]
      congr 1
      rw [← hclos i]
      exact properCyclePushforward_integralClosedSubspaceCycle_of_isClosedImmersion D _
        (isGood_integralClosedSubspace D _ hP (U i)) (g ≫ sX) hY _ (hUd i) _ k
    refine Subtype.ext (funext fun T => ?_)
    rw [properCyclePushforward_cycleFamilySum_apply, finsum_congr fun i => by rw [key i]]
    have hz : ∀ i T, T ≠ W i →
        α.1 (W i) * integralClosedSubspaceCycleCoeff D (g ≫ sX) (W i) k T = 0 := fun i T h => by
      rw [integralClosedSubspaceCycleCoeff_of_ne D _ _ k h, mul_zero]
    by_cases hT : α.1 T = 0
    · rw [hT]
      exact finsum_eq_zero_of_forall_eq_zero fun i => hz i T fun h => hWne i (h ▸ hT)
    · obtain ⟨i₀, rfl⟩ := hWsupp T hT
      refine (finsum_eq_single _ i₀ fun i hi => hz i _ fun h => hi (hWinj h).symm).trans ?_
      show α.1 (W i₀) * integralClosedSubspaceCycleCoeff D (g ≫ sX) (W i₀) k (W i₀) = α.1 (W i₀)
      rw [integralClosedSubspaceCycleCoeff_self D _ _ k (α.2.2 _ (hWne i₀)), mul_one]
  -- the restriction of `α'` to the `i`-th piece is `n_i [Y_i]`
  have hres : ∀ i, cycleGroupRestrict D ((d ≫ g) ≫ sX) hP ((R i).ι ≫ (d ≫ g) ≫ sX)
      (isGood_ι_of_isClosedSubspace D _ hP (R i) (hRc i)) (hRo i).2 rfl k α' =
      α.1 (W i) • integralClosedSubspaceCycle D ((R i).ι ≫ (d ≫ g) ≫ sX)
        (IntegralClosedSubspace.top D.site D.base D.base_mem (hRc i).1 (hint i)) k := by
    intro i
    have hPdec := D.isDecentSpace_of_isGood _ hP
    refine Subtype.ext (funext fun V => ?_)
    rw [cycleGroupRestrict_apply, IntegralClosedSubspace.closureImage_eq_pushforward
      D.site D.base D.base_mem hP.1 (hRc i).1 hPdec (hRc i).2 V]
    change ∑ᶠ j, (integralClosedSubspacePushforward D ((d ≫ g) ≫ sX) hP (U j) k (cI j)).1
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hP.1 (U i).isClosedSubspace.1
          hPdec (U i).isClosedSubspace.2 V) = _
    rw [finsum_eq_single _ i, integralClosedSubspacePushforward_apply_pushforward, ← htop i]
    · intro j hj
      by_contra hne
      have hsub := subspacePointSet_subset_of_pushforward_ne_zero D _ hP (U j) k (cI j) _ hne
      obtain ⟨q, hq⟩ := (isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base
        D.base_mem (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hP.1
          (U i).isClosedSubspace.1 hPdec (U i).isClosedSubspace.2 V)).1
      have hqi : q ∈ subspacePointSet D.site D.base D.base_mem P.obj (R i) := by
        have hq' := hq
        change q ∈ subspacePointSet D.site D.base D.base_mem P.obj _ at hq'
        rw [IntegralClosedSubspace.subspacePointSet_pushforward] at hq'
        obtain ⟨v, -, rfl⟩ := hq'
        exact ⟨v, rfl⟩
      exact (hdisj i j (Ne.symm hj)).le_bot ⟨hqi, hsub hq⟩
  -- the first axiom along the proper morphism `d`
  obtain ⟨β, hβ1, hβ2⟩ := c.proper_naturality g hY d hP hd k l hkl α'
  rw [hpush] at hβ2
  rw [hβ2, chowClassCanonical_eq_zero_iff]
  refine isRationallyEquivalentToZeroCanonical_properCyclePushforward.{u + 1} D _ hP _ hY _ hd l
    β ?_
  -- `β` restricts to zero on every piece, by the second axiom along the inclusions of the pieces
  refine isRationallyEquivalentToZeroCanonical_of_forall_cycleGroupRestrict D _ hP R hRo hRc
    hdisj hcov l β fun i => ?_
  have hEt := isEtale_of_isOpenImmersion D.site D.base D.base_mem (hRo i).2
  have hfl := isFlat_of_isEtale D.site D.base D.base_mem hEt
  have hr0 := hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem (R i).ι hPalg hEt
  have hRg : D.IsGood (((R i).ι ≫ d ≫ g) ≫ sX) :=
    isGood_ι_of_isClosedSubspace D _ hP (R i) (hRc i)
  have hflat := c.flat_naturality (d ≫ g) hP (R i).ι hRg 0 hfl hr0 k l hkl k l (by simp)
    (by simp) (chowClassCanonical.{u + 1} D _ hP k α')
  rw [hβ1, flatPullbackChowMapCanonical_chowClassCanonical,
    flatPullbackChowMapCanonical_chowClassCanonical] at hflat
  have hα'res : flatPullbackMap D (((R i).ι ≫ d ≫ g) ≫ sX) hRg ((d ≫ g) ≫ sX) hP (R i).ι
      (Category.assoc (R i).ι (d ≫ g) sX).symm 0 hfl hr0 k k (by simp) α' =
      α.1 (W i) • integralClosedSubspaceCycle D (((R i).ι ≫ d ≫ g) ≫ sX)
        (IntegralClosedSubspace.top D.site D.base D.base_mem (hRc i).1 (hint i)) k :=
    (Subtype.ext (flatPullbackMap_eq_cycleGroupRestrict D _ hP _ hRg (hRo i).2 rfl k k
      (by simp) α')).trans (hres i)
  rw [hα'res, map_zsmul, map_zsmul, hc _ hRg (hint i) k l hkl, smul_zero] at hflat
  have h0 := (chowClassCanonical_eq_zero_iff.{u + 1} D _ hRg l _).1 hflat.symm
  rwa [Subtype.ext (flatPullbackMap_eq_cycleGroupRestrict D _ hP _ hRg (hRo i).2 rfl l l
    (by simp) β)] at h0

/-- **Stacks 0ERS.** In Situation 0EDT let `X/B` be good and let `c ∈ A^p(X)`. Then `c` is zero if
and only if `c ∩ [Y] = 0` in `CH_*(Y)` for every integral algebraic space `Y` locally of finite
type over `X`. -/
@[stacks 0ERS]
theorem ChowCohomologyClass.eq_zero_iff_capsFundamentalClassesToZero
    (c : ChowCohomologyClass D sX hX p) : c = 0 ↔ c.CapsFundamentalClassesToZero D sX hX := by
  refine ⟨fun h => h ▸ ChowCohomologyClass.zero_capsFundamentalClassesToZero D sX hX,
    fun hc => ChowCohomologyClass.ext fun {Y} g hY k l hkl x => ?_⟩
  rw [ChowCohomologyClass.zero_cap]
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  exact c.cap_chowClassCanonical_eq_zero D sX hX hc g hY k l hkl α

end Vanishing

end AlgebraicGeometry.Space

end
