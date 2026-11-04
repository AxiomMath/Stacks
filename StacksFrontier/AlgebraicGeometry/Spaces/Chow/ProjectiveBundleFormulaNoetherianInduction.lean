module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaLocallyFiniteSums
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# Surjectivity of the projective bundle formula by noetherian induction

Let `π : P → X` be proper and flat of relative dimension `n` between good algebraic spaces over
the base, and `ℒ` invertible on `P`. This file proves the surjectivity half of Stacks 0ERV for
`(π, ℒ)` from its surjectivity over a nonempty open of every integral space mapping to `X`
(`AlgebraicGeometry.Space.HasGenericallySurjectiveBundleFormula`), following the source's proof,
which argues as in Stacks 0ERG.

* *Reduction to `X` integral.* Write `β = ∑ m_W [W]`. The closures `Z_W` of the images of the `W`
  form a locally finite family since `π` is quasi-compact. If over each `Z_W` the class of the lift
  of `[W]` to `π^{-1}(Z_W)` is `∑_i c₁^i ∩ π_{Z_W}^*α_{W,i}`, then
  `α_i = ∑_W m_W (Z_W → X)_*α_{W,i}` works: the map commutes with locally finite sums of cycles
  and with pushforward along `Z_W → X`, and the locally finite sum of rational equivalences
  carried by the `π^{-1}(Z_W)` is a rational equivalence (Stacks 0EQ8).
* *Induction on `dim_δ(X)`.* For `X` integral, over a nonempty open `U ⊆ X` the restriction
  `β|_{π^{-1}(U)}` is in the image; by Stacks 0EP9 the `α_i` on `U` extend to `X`; by the
  localization sequence (Stacks 0EQ7) the difference comes from a cycle on `π^{-1}(X ∖ U)`, and
  `dim_δ(X ∖ U) < dim_δ(X)`.

## Main definitions

* `AlgebraicGeometry.Space.closedBaseChangeBundleFormulaMap`: the map of the projective bundle
  formula for the base change `π^{-1}(Z) → Z` to a closed subspace `Z ⊆ X`.
* `AlgebraicGeometry.Space.HasGenericallySurjectiveBundleFormula`: over every integral good
  space `T → X` there is a nonempty open `U ⊆ T` over which the base change of `(π, ℒ)` has a
  surjective projective bundle formula.

## Main results

* `AlgebraicGeometry.Space.surjective_bundleFormulaMap_of_forall_integralClosedSubspace`: the
  reduction to an integral base.
* `AlgebraicGeometry.Space.surjective_bundleFormulaMap_of_isOpenImmersion_of_closedComplement`:
  the localization step.
* `AlgebraicGeometry.Space.HasGenericallySurjectiveBundleFormula.closedSubspace`: the hypothesis
  passes to closed subspaces of the base.
* `AlgebraicGeometry.Space.bundleFormulaSurjective_of_hasGenericallySurjectiveBundleFormula`:
  **the surjectivity half of Stacks 0ERV**, by noetherian induction.

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0ERG](https://stacks.math.columbia.edu/tag/0ERG)
* [Stacks Project, Tag 0EQ7](https://stacks.math.columbia.edu/tag/0EQ7)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EP9](https://stacks.math.columbia.edu/tag/0EP9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Linear

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- The cycle-level map of the projective bundle formula is additive in the family. -/
theorem bundleFormulaCycle_sub (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (α α' : ∀ i, CycleGroup D sX (d i)) :
    bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd (fun i => α i - α' i) =
      bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α -
        bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α' := by
  simp only [bundleFormulaCycle, map_sub, Finset.sum_sub_distrib]

/-- The cycle-level map of the projective bundle formula commutes with integer multiples. -/
theorem bundleFormulaCycle_zsmul (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (m : ℤ) (α : ∀ i, CycleGroup D sX (d i)) :
    bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd (fun i => m • α i) =
      m • bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α := by
  simp only [bundleFormulaCycle, map_zsmul, Finset.smul_sum]

/-- The image under the map of the projective bundle formula of a family carried by a set is
carried by its inverse image. -/
theorem subspacePointSet_subset_of_bundleFormulaCycle_ne_zero (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (α : ∀ i, CycleGroup D sX (d i))
    (S : Set (points D.site D.base D.base_mem X))
    (hS : ∀ (i : Fin (n + 1)) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ S)
    (A : IntegralClosedSubspace D.site D.base D.base_mem P)
    (hA : (bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α).1 A ≠ 0) :
    subspacePointSet D.site D.base D.base_mem P A.subspace ⊆
      pointsMap D.site D.base D.base_mem P π ⁻¹' S := by
  unfold bundleFormulaCycle at hA
  rw [cycleGroup_finset_sum_apply] at hA
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
  exact subspacePointSet_subset_of_firstChernCapPowCycleMap_flatPullbackMap_ne_zero D sX hX sP hP
    π hπB n hflat hrel L hL i (d i) N (hd i) (α i) S (hS i) A hi

end Linear

section Closed

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The map of the projective bundle formula for the base change `π^{-1}(Z) → Z`** to a closed
subspace `Z ⊆ X`, with `ℒ` restricted to `π^{-1}(Z)`. -/
abbrev closedBaseChangeBundleFormulaMap (Z : Subfunctor X)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) :
    (∀ i, chowGroupCanonical.{u + 1} D (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ)
      (d i)) →+
      chowGroupCanonical.{u + 1} D ((Z.preimage π).ι ≫ sP)
        (isGood_ι_of_isClosedSubspace D sP hP _
          (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ)) N :=
  bundleFormulaMap D (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ)
    ((Z.preimage π).ι ≫ sP)
    (isGood_ι_of_isClosedSubspace D sP hP _
      (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
    (Z.fromPreimage π) (fromPreimage_comp_structureMorphism D sP sX π hπB Z) n
    (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
      hflat hrel).1
    (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
      hflat hrel).2
    (closedSubspaceModuleRestrict D sP hP L
      ⟨Z.preimage π, isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ⟩)
    (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1
      (Z.preimage π) (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ)) L hL)
    N d hd

/-- If the map of the projective bundle formula over a closed subspace `Z ⊆ X` hits the class of
`γ`, then `γ` agrees up to principal divisors carried by `|π^{-1}(Z)|` with the image of a
pushed-forward family. -/
private theorem exists_isRationallyEquivalentToZeroWithinCanonical_of_surjective_closedBaseChange
    (Z : Subfunctor X) (hZ : IsClosedSubspace D.site D.base D.base_mem Z) (N : ℤ)
    (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ))
    (hsurj : Function.Surjective (closedBaseChangeBundleFormulaMap D sX hX sP hP π hπB n hflat
      hrel L hL Z hZ N d hd))
    (γ : CycleGroup D ((Z.preimage π).ι ≫ sP) N) :
    ∃ α : ∀ i, CycleGroup D (Z.ι ≫ sX) (d i),
      IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sP hP N
        (bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd
            (fun i => cycleGroupClosedPushforward D hX.1 hZ.1 (D.isDecentSpace_of_isGood sX hX)
              hZ.2 sX hX.2.2 (Z.ι ≫ sX) rfl (d i) (α i)) -
          cycleGroupClosedPushforward D hP.1
            (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ).1
            (D.isDecentSpace_of_isGood sP hP)
            (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ).2 sP hP.2.2
            ((Z.preimage π).ι ≫ sP) rfl N γ)
        (subspacePointSet D.site D.base D.base_mem P (Z.preimage π)) := by
  obtain ⟨a, ha⟩ := hsurj (chowClassCanonical.{u + 1} D _ (isGood_ι_of_isClosedSubspace D sP hP _
    (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ)) N γ)
  choose α hα using fun i => QuotientAddGroup.mk_surjective (a i)
  have haα : a = fun i => chowClassCanonical.{u + 1} D _
      (isGood_ι_of_isClosedSubspace D sX hX _ hZ) (d i) (α i) := funext fun i => (hα i).symm
  rw [haα, closedBaseChangeBundleFormulaMap, bundleFormulaMap_chowClassCanonical,
    chowClassCanonical_eq_iff_rationallyEquivalentCanonical] at ha
  exact ⟨α, isRationallyEquivalentToZeroWithinCanonical_bundleFormulaCycle_closedPushforward_sub
    D sX hX sP hP π hπB n hflat hrel Z hZ L hL N d hd α _ ha⟩

end Closed

/-! ### The reduction to an integral base -/

section Reduction

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

include hp in
/-- **The surjectivity half of Stacks 0ERV, the reduction to an integral base.** If over every
integral closed subspace `Z ⊆ X` the map of the projective bundle formula for
`(π^{-1}(Z) → Z, ℒ|_{π^{-1}(Z)})` is surjective, so is the map for `(π, ℒ)`. -/
theorem surjective_bundleFormulaMap_of_forall_integralClosedSubspace (N : ℤ)
    (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ))
    (hZ : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      Function.Surjective (closedBaseChangeBundleFormulaMap D sX hX sP hP π hπB n hflat hrel L hL
        Z.subspace Z.isClosedSubspace N d hd)) :
    Function.Surjective (bundleFormulaMap D sX hX sP hP π hπB n hflat hrel L hL N d hd) := by
  classical
  intro b
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk_surjective b
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hPdec := D.isDecentSpace_of_isGood sP hP
  let I := {W : IntegralClosedSubspace D.site D.base D.base_mem P // β.1 W ≠ 0}
  let ZW : I → IntegralClosedSubspace D.site D.base D.base_mem X := fun W =>
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec π W.1
  have hPc : ∀ W : I, IsClosedSubspace D.site D.base D.base_mem ((ZW W).subspace.preimage π) :=
    fun W => isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π _
      (ZW W).isClosedSubspace
  have hPgood : ∀ W : I, D.IsGood (((ZW W).subspace.preimage π).ι ≫ sP) := fun W =>
    isGood_ι_of_isClosedSubspace D sP hP _ (hPc W)
  have hPpts : ∀ W : I, subspacePointSet D.site D.base D.base_mem P
      ((ZW W).subspace.preimage π) = pointsMap D.site D.base D.base_mem P π ⁻¹'
        subspacePointSet D.site D.base D.base_mem X (ZW W).subspace := fun W =>
    subspacePointSet_preimage D.site D.base D.base_mem π _
  have hsubW : ∀ W : I, subspacePointSet D.site D.base D.base_mem P W.1.subspace ⊆
      Set.range (pointsMap D.site D.base D.base_mem _ ((ZW W).subspace.preimage π).ι) := by
    intro W x hx
    change x ∈ subspacePointSet D.site D.base D.base_mem P ((ZW W).subspace.preimage π)
    rw [hPpts W, Set.mem_preimage, IntegralClosedSubspace.subspacePointSet_closureImage]
    exact subset_closure ⟨x, hx, rfl⟩
  choose W' hW' using fun W : I => IntegralClosedSubspace.exists_pushforward_eq D.site D.base
    D.base_mem hP.1 (hPc W).1 hPdec (D.isDecentSpace_of_isGood _ (hPgood W)) (hPc W).2 W.1
    (hsubW W)
  have hW'dim : ∀ W : I, deltaDimension D (((ZW W).subspace.preimage π).ι ≫ sP) (W' W) = N :=
    fun W => by
      rw [← IntegralClosedSubspace.deltaDimension_pushforward D sP hP.2.2 hP.1 (hPc W).1 hPdec
        (hPc W).2 (W' W), hW' W]
      exact β.2.2 W.1 W.2
  choose αW hαW using fun W : I =>
    exists_isRationallyEquivalentToZeroWithinCanonical_of_surjective_closedBaseChange D sX hX sP
      hP π hπB n hflat hrel L hL (ZW W).subspace (ZW W).isClosedSubspace N d hd (hZ (ZW W))
      (integralCycle D _ N (W' W) (hW'dim W))
  set G : I → CycleGroup D sP N := fun W =>
    bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd
      (fun i => cycleGroupClosedPushforward D hX.1 (ZW W).isClosedSubspace.1 hXdec
        (ZW W).isClosedSubspace.2 sX hX.2.2 ((ZW W).subspace.ι ≫ sX) rfl (d i) (αW W i)) with hG
  have hRW : ∀ W : I, IsCanonicallyRationallyEquivalentToZeroWithin.{u, u + 1} D sP hP N
      (G W - integralCycle D sP N W.1 (β.2.2 W.1 W.2))
      (subspacePointSet D.site D.base D.base_mem P ((ZW W).subspace.preimage π)) := by
    intro W
    refine IsRationallyEquivalentToZeroWithinCanonical.isCanonicallyRationallyEquivalentToZeroWithin
      ?_
    convert hαW W using 2
    refine Subtype.ext ?_
    rw [cycleGroupClosedPushforward_integralCycle_coe D _ (hPgood W) sP hP (hPc W).2 rfl N (W' W)
      (hW'dim W), hW' W]
    rfl
  let γ : ∀ i : Fin (n + 1), I → CycleGroup D sX (d i) := fun i W => β.1 W.1 •
    cycleGroupClosedPushforward D hX.1 (ZW W).isClosedSubspace.1 hXdec (ZW W).isClosedSubspace.2
      sX hX.2.2 ((ZW W).subspace.ι ≫ sX) rfl (d i) (αW W i)
  have hγT : ∀ (i : Fin (n + 1)) (W : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (γ i W).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
        subspacePointSet D.site D.base D.base_mem X (ZW W).subspace := by
    intro i W Z hZne
    have hne : (cycleGroupClosedPushforward D hX.1 (ZW W).isClosedSubspace.1 hXdec
        (ZW W).isClosedSubspace.2 sX hX.2.2 ((ZW W).subspace.ι ≫ sX) rfl (d i) (αW W i)).1 Z ≠ 0 :=
      by
        intro h0
        apply hZne
        simp only [γ, AddSubgroup.coe_zsmul, Pi.smul_apply, h0, smul_zero]
    by_cases hT : ∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
        (ZW W).isClosedSubspace.1 hXdec (ZW W).isClosedSubspace.2 T0 = Z
    · obtain ⟨T0, rfl⟩ := hT
      rw [IntegralClosedSubspace.subspacePointSet_pushforward]
      rintro _ ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    · exact absurd (cycleClosedPushforward_apply_of_forall_ne D hX.1 _ hXdec _ _ Z
        fun T0 hT0 => hT ⟨T0, hT0⟩) hne
  have hβlf : LocallyFinite fun W : I => subspacePointSet D.site D.base D.base_mem P W.1.subspace :=
    by
      have h := β.2.1.comp_injective (Subtype.val_injective (p := fun W => β.1 W ≠ 0))
      refine h.subset fun W => ?_
      simp only [Function.comp_apply, if_neg W.2, subset_refl]
  have hlf : LocallyFinite fun W : I => subspacePointSet D.site D.base D.base_mem X
      (ZW W).subspace := by
    have h := (locallyFinite_closure_image_pointsMap D sP hP sX hX hπB hp.2.1.2
      (fun W : I => subspacePointSet D.site D.base D.base_mem P W.1.subspace)
      (fun W => isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hP.1 W.1)
      hβlf).1
    refine h.subset fun W => ?_
    rw [IntegralClosedSubspace.subspacePointSet_closureImage]
  let α : ∀ i, CycleGroup D sX (d i) := fun i =>
    locallyFiniteCycleSum D sX (d i) _ hlf (γ i) (hγT i)
  refine ⟨fun i => chowClassCanonical.{u + 1} D sX hX (d i) (α i), ?_⟩
  rw [bundleFormulaMap_chowClassCanonical]
  change _ = chowClassCanonical.{u + 1} D sP hP N β
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  unfold RationallyEquivalentCanonical
  have hfam : LocallyFinite fun W : I => subspacePointSet D.site D.base D.base_mem P
      ((ZW W).subspace.preimage π) := by
    have h := hlf.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem π)
    refine h.subset fun W => ?_
    rw [hPpts W]
  have hrat := isCycleFamilySumWithin_finsum D sP hP N _ hfam
    (fun W => β.1 W.1 • (G W - integralCycle D sP N W.1 (β.2.2 W.1 W.2)))
    (fun W => (hRW W).zsmul neg_mem_canonicalPrincipalDivisors (β.1 W.1))
    (α := bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α - β) (fun A => ?_)
  · exact IsCanonicallyRationallyEquivalentToZeroWithin.isRationallyEquivalentToZeroCanonical hrat
  have hsum := bundleFormulaCycle_apply_of_locallyFinite D sX hX sP hP π hπB n hflat hrel L hL _
    hlf N d hd γ hγT α (fun i Z => locallyFiniteCycleSum_apply D sX (d i) _ hlf (γ i) (hγT i) Z) A
  have hγW : ∀ W : I, bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd
      (fun i => γ i W) = β.1 W.1 • G W := fun W =>
    bundleFormulaCycle_zsmul D sX hX sP hP π hπB n hflat hrel L hL N d hd (β.1 W.1) _
  have hT' : LocallyFinite fun W : I => pointsMap D.site D.base D.base_mem P π ⁻¹'
      subspacePointSet D.site D.base D.base_mem X (ZW W).subspace :=
    hlf.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem π)
  have hfin₁ : (Function.support fun W : I => (β.1 W.1 • G W).1 A).Finite :=
    finite_support_locallyFiniteCycleCoeff D sP N _ hT' (fun W => β.1 W.1 • G W)
      (fun W Z hZ => by
        rw [← hγW W] at hZ
        exact subspacePointSet_subset_of_bundleFormulaCycle_ne_zero D sX hX sP hP π hπB n hflat hrel
          L hL N d hd _ _ (fun i => hγT i W) Z hZ) A
  have hβA : β.1 A = ∑ᶠ W : I, β.1 W.1 * integralCycleCoeff D W.1 A := by
    by_cases hA : β.1 A = 0
    · rw [hA]
      refine (finsum_eq_zero_of_forall_eq_zero fun W => ?_).symm
      have hWA : A ≠ W.1 := fun h => W.2 (h ▸ hA)
      rw [integralCycleCoeff_eq_zero D W.1 hWA, mul_zero]
    · rw [finsum_eq_single _ ⟨A, hA⟩ (fun W hW => by
        have hWA : A ≠ W.1 := fun h => hW (Subtype.ext h.symm)
        rw [integralCycleCoeff_eq_zero D W.1 hWA, mul_zero]),
        integralCycleCoeff_self, mul_one]
  have hfin₂ : (Function.support fun W : I => β.1 W.1 * integralCycleCoeff D W.1 A).Finite := by
    refine Set.Subsingleton.finite fun W₁ hW₁ W₂ hW₂ => Subtype.ext ?_
    have key : ∀ W : I, W ∈ Function.support (fun W : I => β.1 W.1 * integralCycleCoeff D W.1 A) →
        W.1 = A := fun W hW => by
      by_contra hWA
      exact hW (show β.1 W.1 * integralCycleCoeff D W.1 A = 0 by
        rw [integralCycleCoeff_eq_zero D W.1 (Ne.symm hWA), mul_zero])
    rw [key W₁ hW₁, key W₂ hW₂]
  rw [AddSubgroupClass.coe_sub, Pi.sub_apply, hsum, hβA,
    finsum_congr fun W => congrArg (fun c : CycleGroup D sP N => c.1 A) (hγW W),
    ← finsum_sub_distrib hfin₁ hfin₂]
  refine finsum_congr fun W => ?_
  simp only [AddSubgroup.coe_zsmul, AddSubgroupClass.coe_sub, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, integralCycle_coe, mul_sub]

end Reduction

/-! ### The localization step -/

section Localization

variable (D : BaseSpaceDimensionSituation.{u})
    {X P U PU : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (sU : U ⟶ D.space) (hU : D.IsGood sU) (sPU : PU ⟶ D.space) (hPU : D.IsGood sPU)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjB : j ≫ sX = sU)
    {j' : PU ⟶ P} {πU : PU ⟶ U} (hj'B : j' ≫ sP = sPU) (hπUB : πU ≫ sU = sPU)
    (sq : IsPullback j' πU π j)

include hj hjB hj'B sq in
/-- **The surjectivity half of Stacks 0ERV, the localization step.** Let `j : U → X` be an open
immersion with base change `j' : P_U → P`, `π_U : P_U → U`, and let `Y ⊆ X` be a closed subspace
with `|Y| = |X| ∖ |U|`. If the maps of the projective bundle formula for `(π_U, j'^*ℒ)` and for
`(π^{-1}(Y) → Y, ℒ|_{π^{-1}(Y)})` are surjective, so is the map for `(π, ℒ)`: by Stacks 0EP9 and
the compatibility with restriction a class on `P` agrees with an image up to a class pushed from
`π^{-1}(Y)` (Stacks 0EQ7), which is an image pushed from `Y`. -/
theorem surjective_bundleFormulaMap_of_isOpenImmersion_of_closedComplement (N : ℤ)
    (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ))
    (hsurjU : Function.Surjective (bundleFormulaMap D sU hU sPU hPU πU hπUB n
      (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB hπB
        sq.flip n hflat hrel).2.1
      (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB hπB
        sq.flip n hflat hrel).2.2
      ((modulePullback D.site D.base D.base_mem
        (ObjectProperty.homMk j' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨P, hP.1⟩)).obj L)
      (modulePullbackInvertible
        (ObjectProperty.homMk j' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨P, hP.1⟩) L hL) N d hd))
    (Y : Subfunctor X) (hYc : IsClosedSubspace D.site D.base D.base_mem Y)
    (hYpts : Set.range (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι) =
      (Set.range (pointsMap D.site D.base D.base_mem U j))ᶜ)
    (hY : Function.Surjective (closedBaseChangeBundleFormulaMap D sX hX sP hP π hπB n hflat hrel
      L hL Y hYc N d hd)) :
    Function.Surjective (bundleFormulaMap D sX hX sP hP π hπB n hflat hrel L hL N d hd) := by
  intro b
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk_surjective b
  have hj' := isOpenImmersion_baseChange_of_isPullback D sX hX sP hP sU hU sPU hPU π hj sq
  obtain ⟨aU, haU⟩ := hsurjU (chowClassCanonical.{u + 1} D sPU hPU N
    (cycleGroupRestrict D sP hP sPU hPU hj' hj'B N β))
  choose αU hαU using fun i => QuotientAddGroup.mk_surjective (aU i)
  choose α hα using fun i => cycleGroupRestrict_surjective D sX hX sU hU hj hjB (d i) (αU i)
  have haU' : aU = fun i => chowClassCanonical.{u + 1} D sU hU (d i)
      (cycleGroupRestrict D sX hX sU hU hj hjB (d i) (α i)) :=
    funext fun i => by rw [hα i]; exact (hαU i).symm
  rw [haU', bundleFormulaMap_chowClassCanonical,
    ← chowClassCanonical_cycleGroupRestrict_bundleFormulaCycle D sX hX sP hP sU hU sPU hPU π hπB n
      hflat hrel hj hjB hj'B hπUB sq L hL,
    chowClassCanonical_eq_iff_rationallyEquivalentCanonical] at haU
  have hloc : IsCanonicallyRationallyEquivalentToZeroWithin.{u, u + 1} D sPU hPU N
      (cycleGroupRestrict D sP hP sPU hPU hj' hj'B N
          (bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α) -
        cycleGroupRestrict D sP hP sPU hPU hj' hj'B N β) Set.univ :=
    ((isRationallyEquivalentToZeroWithinCanonical_univ_iff D sPU hPU N _).2
      haU).isCanonicallyRationallyEquivalentToZeroWithin
  have hYP := isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Y hYc
  have hcomp : Set.range (pointsMap D.site D.base D.base_mem _ (Y.preimage π).ι) =
      (Set.range (pointsMap D.site D.base D.base_mem _ j'))ᶜ := by
    have h₁ := subspacePointSet_preimage D.site D.base D.base_mem π Y
    have h₂ := preimage_image_pointsMap_of_isPullback D.site D.base D.base_mem sq.flip Set.univ
    simp only [Set.image_univ, Set.preimage_univ] at h₂
    change subspacePointSet D.site D.base D.base_mem P (Y.preimage π) = _
    rw [h₁, ← h₂, subspacePointSet, hYpts, Set.preimage_compl]
  obtain ⟨γ, hγ⟩ :=
    exists_isCanonicallyRationallyEquivalentToZeroWithin_sub_add_cycleGroupClosedPushforward.{u,
      u + 1} D sP hP ((Y.preimage π).ι ≫ sP) (isGood_ι_of_isClosedSubspace D sP hP _ hYP) sPU hPU
      hYP.2 rfl hj' hj'B hcomp N (bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α)
      β hloc
  obtain ⟨α', hα'⟩ :=
    exists_isRationallyEquivalentToZeroWithinCanonical_of_surjective_closedBaseChange D sX hX sP
      hP π hπB n hflat hrel L hL Y hYc N d hd hY γ
  refine ⟨fun i => chowClassCanonical.{u + 1} D sX hX (d i) (α i -
    cycleGroupClosedPushforward D hX.1 hYc.1 (D.isDecentSpace_of_isGood sX hX) hYc.2 sX hX.2.2
      (Y.ι ≫ sX) rfl (d i) (α' i)), ?_⟩
  rw [bundleFormulaMap_chowClassCanonical]
  change _ = chowClassCanonical.{u + 1} D sP hP N β
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  unfold RationallyEquivalentCanonical
  rw [bundleFormulaCycle_sub]
  have key : ∀ A B C : CycleGroup D sP N, (A - B) - β = (A - (β + C)) - (B - C) := fun A B C => by
    abel
  rw [key _ _ (cycleGroupClosedPushforward D hP.1 hYP.1 (D.isDecentSpace_of_isGood sP hP) hYP.2 sP
    hP.2.2 ((Y.preimage π).ι ≫ sP) rfl N γ)]
  exact (rationalEquivalencesCanonical.{u + 1} D sP hP N).sub_mem
    (IsCanonicallyRationallyEquivalentToZeroWithin.isRationallyEquivalentToZeroCanonical hγ)
    hα'.isRationallyEquivalentToZeroCanonical

end Localization

/-! ### The hypothesis over integral spaces mapping to the base -/

section Generic

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The projective bundle formula holds generically**: for every integral good space `T` with a
morphism `g : T → X` over the base there is a nonempty open `j : U → T` and a base change
`j' : P_U → P`, `π_U : P_U → U` of `π` along `j ≫ g` over which the map of the projective bundle
formula for `(π_U, j'^*ℒ)` is surjective in every degree. For the projective bundle of a finite
locally free module this holds over an open where the module is free. -/
def HasGenericallySurjectiveBundleFormula : Prop :=
  ∀ ⦃T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u⦄ (sT : T ⟶ D.space)
    (_ : D.IsGood sT) (g : T ⟶ X), g ≫ sX = sT → IsIntegralSpace D.site D.base D.base_mem T →
    ∃ (U PU : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) (sU : U ⟶ D.space)
      (hU : D.IsGood sU) (sPU : PU ⟶ D.space) (hPU : D.IsGood sPU) (j : U ⟶ T)
      (_ : IsOpenImmersion D.site D.base D.base_mem j) (_ : j ≫ sT = sU)
      (_ : Nonempty (points D.site D.base D.base_mem U)) (j' : PU ⟶ P) (πU : PU ⟶ U)
      (_ : j' ≫ sP = sPU) (hπUB : πU ≫ sU = sPU) (sq : IsPullback j' πU π (j ≫ g)),
      BundleFormulaSurjective D sU hU sPU hPU πU hπUB n
        (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB hπB
          sq.flip n hflat hrel).2.1
        (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB hπB
          sq.flip n hflat hrel).2.2
        ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk j' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨P, hP.1⟩)).obj L)
        (modulePullbackInvertible
          (ObjectProperty.homMk j' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨P, hP.1⟩) L hL)

include hp in
/-- **The hypothesis passes to closed subspaces of the base**: a base change of
`π^{-1}(Z) → Z` along `j ≫ g : U → Z` is one of `π` along `j ≫ g ≫ (Z → X)`, and the two
pullbacks of `ℒ` agree. -/
theorem HasGenericallySurjectiveBundleFormula.closedSubspace
    (h : HasGenericallySurjectiveBundleFormula D sX hX sP hP π hπB n hflat hrel L hL)
    (Z : Subfunctor X) (hZ : IsClosedSubspace D.site D.base D.base_mem Z) :
    HasGenericallySurjectiveBundleFormula D (Z.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Z hZ) ((Z.preimage π).ι ≫ sP)
      (isGood_ι_of_isClosedSubspace D sP hP _
        (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
      (Z.fromPreimage π) (fromPreimage_comp_structureMorphism D sP sX π hπB Z) n
      (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
        hflat hrel).1
      (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
        hflat hrel).2
      (closedSubspaceModuleRestrict D sP hP L
        ⟨Z.preimage π, isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ⟩)
      (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1
        (Z.preimage π) (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
        L hL) := by
  intro T sT hT g hgB hint
  obtain ⟨U, PU, sU, hU, sPU, hPU, j, hj, hjB, hne, j', πU, hj'B, hπUB, sq, hsurj⟩ :=
    h sT hT (g ≫ Z.ι) (by rw [Category.assoc, hgB]) hint
  have hc := isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ
  have t : IsPullback (Z.preimage π).ι (Z.fromPreimage π) π Z.ι :=
    (Subfunctor.isPullback_preimage π Z).flip
  have hw : j' ≫ π = (πU ≫ j ≫ g) ≫ Z.ι := by
    rw [sq.w]
    simp only [Category.assoc]
  set j'' : PU ⟶ (Z.preimage π).toFunctor := t.lift j' (πU ≫ j ≫ g) hw with hj''
  have h1 : j'' ≫ (Z.preimage π).ι = j' := t.lift_fst _ _ _
  have h2 : j'' ≫ Z.fromPreimage π = πU ≫ j ≫ g := t.lift_snd _ _ _
  have sq' : IsPullback j'' πU (Z.fromPreimage π) (j ≫ g) :=
    IsPullback.of_right (by rw [h1, Category.assoc]; exact sq) h2 t
  have hj''B : j'' ≫ (Z.preimage π).ι ≫ sP = sPU := by rw [← Category.assoc, h1, hj'B]
  refine ⟨U, PU, sU, hU, sPU, hPU, j, hj, hjB, hne, j'', πU, hj''B, hπUB, sq', ?_⟩
  have hprop : IsProper D.site D.base D.base_mem πU :=
    isProper_of_isPullback D.site D.base D.base_mem hPU.1 hP.1 hU.1 hX.1 sq hp
  have hmod : (modulePullback D.site D.base D.base_mem
        (ObjectProperty.homMk j' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨P, hP.1⟩)).obj L =
      (modulePullback D.site D.base D.base_mem
        ((ObjectProperty.homMk j'' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨(Z.preimage π).toFunctor, hc.1⟩) ≫
          closedSubspaceHom D.site D.base D.base_mem hP.1 (Z.preimage π) hc)).obj L := by
    rw [← h1]
    rfl
  exact BundleFormulaSurjective.of_iso D sU hU sPU hPU sPU hPU πU hπUB πU hπUB n _ _ hprop _ _
    hprop _ _ _ _ (𝟙 PU) (Category.id_comp _) (Category.id_comp _)
    ((modulePullbackIdIso D.site D.base D.base_mem ⟨PU, hPU.1⟩).app _ ≪≫ eqToIso hmod ≪≫
      ((modulePullbackCompIso D.site D.base D.base_mem
        (ObjectProperty.homMk j'' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨(Z.preimage π).toFunctor, hc.1⟩)
        (closedSubspaceHom D.site D.base D.base_mem hP.1 (Z.preimage π) hc)).app L).symm) hsurj

end Generic

/-! ### The noetherian induction -/

section Induction

variable (D : BaseSpaceDimensionSituation.{u}) (n : ℕ) (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ))

/-- **The surjectivity half of Stacks 0ERV over a base of bounded dimension**, by induction on
`m` with `δ_X ≤ N - n - 1 + m`: for `m = 0` there are no nonzero `N`-cycles on `P`, and the
induction step is the reduction to integral closed subspaces `Z ⊆ X`, the localization step at a
nonempty open of `Z` over which the formula holds, and the induction hypothesis on its closed
complement, on which `δ` drops since the generic point of `Z` lies in the open. -/
theorem surjective_bundleFormulaMap_of_forall_deltaValue_le_add (m : ℕ) :
    ∀ ⦃X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u⦄ (sX : X ⟶ D.space)
      (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP) (π : P ⟶ X) (hπB : π ≫ sX = sP)
      (hflat : IsFlat D.site D.base D.base_mem π)
      (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
      (_ : IsProper D.site D.base D.base_mem π)
      (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
      (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L),
      HasGenericallySurjectiveBundleFormula D sX hX sP hP π hπB n hflat hrel L hL →
      (∀ x, D.deltaValue sX x ≤ N - n - 1 + m) →
      Function.Surjective (bundleFormulaMap D sX hX sP hP π hπB n hflat hrel L hL N d hd) := by
  induction m with
  | zero =>
    intro X P sX hX sP hP π hπB hflat hrel _ L hL _ hδ b
    obtain ⟨β, rfl⟩ := QuotientAddGroup.mk_surjective b
    have h0 := eq_zero_of_forall_deltaValue_le D sP hP sX hX π hπB n hrel (d := N - n - 1)
      (k := N - n) (fun x => by simpa using hδ x) (by omega) (cycleGroupCast D sP (by ring) β)
    have hβ : β = 0 := Subtype.ext (by
      have := congrArg Subtype.val h0
      rwa [cycleGroupCast_coe] at this)
    refine ⟨0, ?_⟩
    rw [map_zero, hβ]
    rfl
  | succ m ih =>
    intro X P sX hX sP hP π hπB hflat hrel hp L hL hgen hδ
    refine surjective_bundleFormulaMap_of_forall_integralClosedSubspace D sX hX sP hP π hπB n
      hflat hrel hp L hL N d hd fun Z => ?_
    have hZgood := isGood_ι_of_isClosedSubspace D sX hX Z.subspace Z.isClosedSubspace
    have hpZ := isProper_fromPreimage_of_isClosedSubspace D sX hX sP hP π hp Z.subspace
      Z.isClosedSubspace
    have hZgen := hgen.closedSubspace D sX hX sP hP π hπB n hflat hrel hp L hL Z.subspace
      Z.isClosedSubspace
    obtain ⟨U, PU, sU, hU, sPU, hPU, j, hj, hjB, hne, j', πU, hj'B, hπUB, sq, hsurj⟩ :=
      hZgen (Z.subspace.ι ≫ sX) hZgood (𝟙 _) (Category.id_comp _) Z.isIntegralSpace
    have sq' : IsPullback j' πU (Z.subspace.fromPreimage π) j := by
      simpa only [Category.comp_id] using sq
    set F : Set (points D.site D.base D.base_mem Z.subspace.toFunctor) :=
      (Set.range (pointsMap D.site D.base D.base_mem _ j))ᶜ with hF
    have hFc : IsClosed F :=
      (isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem j hj).isClosed_compl
    obtain ⟨Y, hYc, hYpts⟩ : ∃ Y : Subfunctor Z.subspace.toFunctor,
        IsClosedSubspace D.site D.base D.base_mem Y ∧
          Set.range (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι) = F :=
      ⟨_, isClosedSubspace_reducedClosedSubspace D.site D.base D.base_mem _ hZgood.1 F hFc,
        range_pointsMap_ι_reducedClosedSubspace D.site D.base D.base_mem _ hZgood.1 F hFc⟩
    have hδZ : ∀ z, D.deltaValue (Z.subspace.ι ≫ sX) z ≤ N - n - 1 + ((m + 1 : ℕ) : ℤ) :=
      fun z => by
        rw [D.deltaValue_comp_of_isLocallyQuasiFinite Z.isClosedSubspace.1 hX.1 Z.subspace.ι sX
          (isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem Z.subspace.ι
            (isImmersion_of_isClosedImmersion D.site D.base D.base_mem Z.isClosedSubspace.2))
          hX.2.2]
        exact hδ _
    obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η
        (Set.univ : Set (points D.site D.base D.base_mem Z.subspace.toFunctor)) := by
      have := quasiSober_points_of_isGood D _ hZgood
      have := Z.isIntegralSpace.2.2
      exact ⟨_root_.genericPoint _, _root_.genericPoint_spec _⟩
    have hηU : η ∈ Set.range (pointsMap D.site D.base D.base_mem _ j) := by
      obtain ⟨u₀⟩ := hne
      exact (hη.mem_open_set_iff
        (isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem j hj)).2
        ⟨_, Set.mem_univ _, u₀, rfl⟩
    have hδY : ∀ y, D.deltaValue (Y.ι ≫ Z.subspace.ι ≫ sX) y ≤ N - n - 1 + m := by
      intro y
      rw [D.deltaValue_comp_of_isLocallyQuasiFinite hYc.1 hZgood.1 Y.ι (Z.subspace.ι ≫ sX)
        (isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem Y.ι
          (isImmersion_of_isClosedImmersion D.site D.base D.base_mem hYc.2)) hZgood.2.2]
      have hyF : pointsMap D.site D.base D.base_mem _ Y.ι y ∈ F := by
        rw [← hYpts]
        exact ⟨y, rfl⟩
      have hne' : pointsMap D.site D.base D.base_mem _ Y.ι y ≠ η := fun h => hyF (h ▸ hηU)
      have h1 := deltaValue_lt_of_isGenericPoint D _ hZgood hη _ hne'
      have h2 := hδZ η
      push_cast at h2
      omega
    have hZc := isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z.subspace
      Z.isClosedSubspace
    refine surjective_bundleFormulaMap_of_isOpenImmersion_of_closedComplement D _ hZgood
      ((Z.subspace.preimage π).ι ≫ sP) (isGood_ι_of_isClosedSubspace D sP hP _ hZc) sU hU
      sPU hPU (Z.subspace.fromPreimage π)
      (fromPreimage_comp_structureMorphism D sP sX π hπB Z.subspace) n
      (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z.subspace
        Z.isClosedSubspace n hflat hrel).1
      (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z.subspace
        Z.isClosedSubspace n hflat hrel).2
      (closedSubspaceModuleRestrict D sP hP L ⟨Z.subspace.preimage π, hZc⟩)
      (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1
        (Z.subspace.preimage π) hZc) L hL)
      hj hjB hj'B hπUB sq' N d hd (hsurj N d hd) Y hYc hYpts ?_
    exact ih _ _ _ _ _ _ _ _
      (isProper_fromPreimage_of_isClosedSubspace D _ hZgood ((Z.subspace.preimage π).ι ≫ sP)
        (isGood_ι_of_isClosedSubspace D sP hP _ hZc) _ hpZ Y hYc) _ _
      (hZgen.closedSubspace D _ hZgood ((Z.subspace.preimage π).ι ≫ sP)
        (isGood_ι_of_isClosedSubspace D sP hP _ hZc) _ _ n _ _ hpZ _ _ Y hYc) hδY

end Induction

/-! ### The surjectivity half of Stacks 0ERV -/

section Main

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

include hp in
/-- **The surjectivity half of Stacks 0ERV, by noetherian induction.** Let `π : P → X` be proper
and flat of relative dimension `n` between good algebraic spaces over the base, and `ℒ`
invertible on `P`. If the projective bundle formula is surjective over a nonempty open of every
integral good space mapping to `X`, then
`(α_i) ↦ ∑_{i ≤ n} c₁(ℒ)^i ∩ π^*α_i : ⊕_i CH_{d i}(X) → CH_N(P)` is surjective in every degree. -/
theorem bundleFormulaSurjective_of_hasGenericallySurjectiveBundleFormula
    (h : HasGenericallySurjectiveBundleFormula D sX hX sP hP π hπB n hflat hrel L hL) :
    BundleFormulaSurjective D sX hX sP hP π hπB n hflat hrel L hL := by
  intro N d hd
  refine surjective_bundleFormulaMap_of_forall_integralClosedSubspace D sX hX sP hP π hπB n
    hflat hrel hp L hL N d hd fun Z => ?_
  have hZgood := isGood_ι_of_isClosedSubspace D sX hX Z.subspace Z.isClosedSubspace
  set dZ := D.deltaValue (Z.subspace.ι ≫ sX) (Z.genericPoint D.site D.base D.base_mem)
  refine surjective_bundleFormulaMap_of_forall_deltaValue_le_add D n N d hd
    (dZ - (N - n - 1)).toNat _ _ _ _ _ _ _ _
    (isProper_fromPreimage_of_isClosedSubspace D sX hX sP hP π hp Z.subspace Z.isClosedSubspace)
    _ _ (h.closedSubspace D sX hX sP hP π hπB n hflat hrel hp L hL Z.subspace Z.isClosedSubspace)
    fun z => ?_
  have hle : D.deltaValue (Z.subspace.ι ≫ sX) z ≤ dZ := by
    by_cases hz : z = Z.genericPoint D.site D.base D.base_mem
    · rw [hz]
    · exact (deltaValue_lt_of_isGenericPoint D _ hZgood
        (Z.closure_singleton_genericPoint D.site D.base D.base_mem) z hz).le
  omega

end Main

end AlgebraicGeometry.Space

end
