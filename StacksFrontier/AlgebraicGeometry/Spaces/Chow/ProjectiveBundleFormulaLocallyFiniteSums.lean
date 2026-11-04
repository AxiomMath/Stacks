module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaCycleLevel

/-!
# The map of the projective bundle formula and locally finite sums of cycles

The cap product `c₁(ℒ) ∩ -` of Stacks 0EQJ, its powers, and flat pullback are computed
coefficientwise by locally finite sums, so they commute with locally finite sums of cycles: if
`γ = ∑_w δ_w` coefficientwise, the `δ_w` being carried by the members `T_w` of a locally finite
family of subsets, then `c₁(ℒ) ∩ γ = ∑_w c₁(ℒ) ∩ δ_w` coefficientwise, and `c₁(ℒ) ∩ δ_w` is carried
by `T_w`. Hence the map `(α_i) ↦ ∑_i c₁(ℒ)^i ∩ π^*α_i` of the projective bundle formula commutes
with locally finite sums. This is the reassembly step of the reduction to an integral base in the
proof of Stacks 0ERV (Remark 0EQ8).

## Main results

* `AlgebraicGeometry.Space.firstChernCapCycleMap_apply_of_locallyFinite`: the cap product of a
  locally finite sum.
* `AlgebraicGeometry.Space.firstChernCapPowCycleMapOfRule_apply_of_locallyFinite`: its powers.
* `AlgebraicGeometry.Space.bundleFormulaCycle_apply_of_locallyFinite`: the map of the projective
  bundle formula on a locally finite sum.

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Coeff

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)

/-- The coefficients of a finite sum of cycles are the sums of the coefficients. -/
theorem cycleGroup_finset_sum_apply {ι : Type*} (k : ℤ) (s : Finset ι) (f : ι → CycleGroup D sX k)
    (A : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (∑ i ∈ s, f i).1 A = ∑ i ∈ s, (f i).1 A := by
  have h := map_sum (AddSubgroup.subtype (cyclesOfDimension D sX k)) f s
  exact (congrFun h A).trans (Finset.sum_apply _ _ _)

end Coeff

section Cap

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- The cap product of a cycle carried by a set is carried by that set: the component cycle of
`V` is carried by `V`. -/
theorem subspacePointSet_subset_of_firstChernCapCycleMap_ne_zero (k : ℤ)
    (chern : FirstChernComponentCycleRule D sX k) (δ : CycleGroup D sX (k + 1))
    (S : Set (points D.site D.base D.base_mem X))
    (hS : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X, δ.1 Z ≠ 0 →
      subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ S)
    (A : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hA : (firstChernCapCycleMap D sX hX k chern δ).1 A ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X A.subspace ⊆ S := by
  by_contra hcon
  refine hA ?_
  rw [firstChernCapCycleMap_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun V => ?_
  by_cases h1 : δ.1 V = 0
  · rw [h1, zero_mul]
  by_cases h2 : (firstChernComponentCycle D sX hX k chern V).1 A = 0
  · rw [h2, mul_zero]
  exact absurd ((subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chern V A
    h2).trans (hS V h1)) hcon

variable {I : Type*} (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)

include hT in
/-- At a fixed integral closed subspace `A ⊆ X` only finitely many pairs `(V, w)` contribute to
the coefficient of `c₁ ∩ ∑_w δ_w`: a nonzero component cycle of `V` at `A` puts the generic point
of `A` in `|V|`, and a nonzero coefficient of `δ_w` at `V` puts `|V|` in `T_w`. -/
theorem finite_support_mul_firstChernComponentCycle_of_locallyFinite (k : ℤ)
    (chern : FirstChernComponentCycleRule D sX k) (δ : I → CycleGroup D sX (k + 1))
    (hδT : ∀ (w : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X), (δ w).1 Z ≠ 0 →
      subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T w)
    (A : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (Function.support fun s : IntegralClosedSubspace D.site D.base D.base_mem X × I =>
      (δ s.2).1 s.1 * (firstChernComponentCycle D sX hX k chern s.1).1 A).Finite := by
  classical
  set ξ : points D.site D.base D.base_mem X :=
    pointsMap D.site D.base D.base_mem A.subspace.toFunctor A.subspace.ι
      (A.genericPoint D.site D.base D.base_mem) with hξ
  have hξA : ξ ∈ subspacePointSet D.site D.base D.base_mem X A.subspace := ⟨_, rfl⟩
  obtain ⟨V₀, hV₀, hV₀fin⟩ := hT ξ
  choose U hU hUfin using fun w : I => (δ w).2.1 ξ
  refine (hV₀fin.biUnion fun w _ => (hUfin w).image fun V =>
    ((V, w) : IntegralClosedSubspace D.site D.base D.base_mem X × I)).subset ?_
  rintro ⟨V, w⟩ hVw
  have hterm : (δ w).1 V * (firstChernComponentCycle D sX hX k chern V).1 A ≠ 0 := hVw
  have hpw : (δ w).1 V ≠ 0 := left_ne_zero_of_mul hterm
  have hmV : (firstChernComponentCycle D sX hX k chern V).1 A ≠ 0 := right_ne_zero_of_mul hterm
  have hξV : ξ ∈ subspacePointSet D.site D.base D.base_mem X V.subspace :=
    subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chern V A hmV hξA
  have hwF : w ∈ {w : I | (T w ∩ V₀).Nonempty} := ⟨ξ, hδT w V hpw hξV, mem_of_mem_nhds hV₀⟩
  refine Set.mem_biUnion hwF ⟨V, ⟨ξ, ?_, mem_of_mem_nhds (hU w)⟩, rfl⟩
  simp only [Set.mem_ite_empty_left]
  exact ⟨hpw, hξV⟩

include hT in
/-- **The cap product of a locally finite sum is the locally finite sum of the cap products**,
coefficientwise. -/
theorem firstChernCapCycleMap_apply_of_locallyFinite (k : ℤ)
    (chern : FirstChernComponentCycleRule D sX k) (δ : I → CycleGroup D sX (k + 1))
    (hδT : ∀ (w : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X), (δ w).1 Z ≠ 0 →
      subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T w)
    (γ : CycleGroup D sX (k + 1))
    (hγ : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X, γ.1 Z = ∑ᶠ w : I, (δ w).1 Z)
    (A : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (firstChernCapCycleMap D sX hX k chern γ).1 A =
      ∑ᶠ w : I, (firstChernCapCycleMap D sX hX k chern (δ w)).1 A := by
  rw [firstChernCapCycleMap_apply]
  calc (∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
        γ.1 V * (firstChernComponentCycle D sX hX k chern V).1 A)
      = ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X, ∑ᶠ w : I,
          (δ w).1 V * (firstChernComponentCycle D sX hX k chern V).1 A :=
        finsum_congr fun V => by rw [hγ V, finsum_mul]
    _ = ∑ᶠ w : I, ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
          (δ w).1 V * (firstChernComponentCycle D sX hX k chern V).1 A :=
        Stacks.Chow.finsum_finsum_comm_of_finite_support _
          (finite_support_mul_firstChernComponentCycle_of_locallyFinite D sX hX T hT k chern δ hδT
            A)
    _ = ∑ᶠ w : I, (firstChernCapCycleMap D sX hX k chern (δ w)).1 A :=
        finsum_congr fun w => (firstChernCapCycleMap_apply D sX hX k chern (δ w) A).symm

/-- A cycle carried by a set stays carried by it after a cast of the dimension. -/
private theorem subset_of_cycleGroupCast_ne_zero {a b : ℤ} (h : a = b)
    (δ : CycleGroup D sX a) (S : Set (points D.site D.base D.base_mem X))
    (hS : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X, δ.1 Z ≠ 0 →
      subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ S) :
    ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X, (cycleGroupCast D sX h δ).1 Z ≠ 0 →
      subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ S :=
  hS

/-- The powers of the cap product of a cycle carried by a set are carried by that set. -/
theorem subspacePointSet_subset_of_firstChernCapPowCycleMapOfRule_ne_zero
    (R : ∀ m : ℤ, FirstChernComponentCycleRule D sX m) (s : ℕ) :
    ∀ (m : ℤ) (δ : CycleGroup D sX (m + s)) (S : Set (points D.site D.base D.base_mem X)),
      (∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X, δ.1 Z ≠ 0 →
        subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ S) →
      ∀ A : IntegralClosedSubspace D.site D.base D.base_mem X,
        (firstChernCapPowCycleMapOfRule D sX hX R s m δ).1 A ≠ 0 →
          subspacePointSet D.site D.base D.base_mem X A.subspace ⊆ S := by
  induction s with
  | zero =>
    intro m δ S hS A hA
    exact hS A hA
  | succ s ih =>
    intro m δ S hS A hA
    simp only [firstChernCapPowCycleMapOfRule, AddMonoidHom.coe_comp, Function.comp_apply] at hA
    exact subspacePointSet_subset_of_firstChernCapCycleMap_ne_zero D sX hX m (R m) _ S
      (fun Z hZ => ih (m + 1) _ S (subset_of_cycleGroupCast_ne_zero D sX _ _ S hS) Z hZ)
      A hA

include hT in
/-- **The powers of the cap product commute with locally finite sums**, coefficientwise. -/
theorem firstChernCapPowCycleMapOfRule_apply_of_locallyFinite
    (R : ∀ m : ℤ, FirstChernComponentCycleRule D sX m) (s : ℕ) :
    ∀ (m : ℤ) (δ : I → CycleGroup D sX (m + s)),
      (∀ (w : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X), (δ w).1 Z ≠ 0 →
        subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T w) →
      ∀ γ : CycleGroup D sX (m + s),
        (∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X, γ.1 Z = ∑ᶠ w : I, (δ w).1 Z) →
        ∀ A : IntegralClosedSubspace D.site D.base D.base_mem X,
          (firstChernCapPowCycleMapOfRule D sX hX R s m γ).1 A =
            ∑ᶠ w : I, (firstChernCapPowCycleMapOfRule D sX hX R s m (δ w)).1 A := by
  induction s with
  | zero =>
    intro m δ _ γ hγ A
    exact hγ A
  | succ s ih =>
    intro m δ hδT γ hγ A
    simp only [firstChernCapPowCycleMapOfRule, AddMonoidHom.coe_comp, Function.comp_apply]
    refine firstChernCapCycleMap_apply_of_locallyFinite D sX hX T hT m (R m) _ ?_ _ ?_ A
    · intro w Z hZ
      exact subspacePointSet_subset_of_firstChernCapPowCycleMapOfRule_ne_zero D sX hX R s (m + 1) _
        (T w) (subset_of_cycleGroupCast_ne_zero D sX _ _ (T w) (hδT w)) Z hZ
    · intro Z
      refine ih (m + 1) _ (fun w => subset_of_cycleGroupCast_ne_zero D sX _ _ (T w) (hδT w)) _
        (fun Z' => ?_) Z
      rw [cycleGroupCast_coe, hγ Z']
      exact finsum_congr fun w => (congrFun (cycleGroupCast_coe D sX _ (δ w)) Z').symm

end Cap

section Pullback

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- The flat pullback of a cycle carried by a set is carried by its inverse image. -/
theorem subspacePointSet_subset_of_flatPullbackMap_ne_zero (m m' : ℤ) (h : m + (r : ℤ) = m')
    (γ : CycleGroup D sY m) (S : Set (points D.site D.base D.base_mem Y))
    (hS : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y, γ.1 Z ≠ 0 →
      subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ S)
    (A : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hA : (flatPullbackMap D sX hX sY hY f hbase r hflat hr m m' h γ).1 A ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X A.subspace ⊆
      pointsMap D.site D.base D.base_mem X f ⁻¹' S := by
  obtain ⟨W, hγW, hmult⟩ := exists_ne_zero_of_flatPullbackCoeff_ne_zero D sX hX sY hY f hbase r
    hflat hr m γ A (by rwa [flatPullbackMap_apply] at hA)
  exact (subspacePointSet_subset_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W A
    hmult).trans (Set.preimage_mono (hS W hγW))

variable {I : Type*} (T : I → Set (points D.site D.base D.base_mem Y)) (hT : LocallyFinite T)

include hT in
/-- **Flat pullback commutes with locally finite sums**, coefficientwise, in arbitrary degrees. -/
theorem flatPullbackMap_apply_of_locallyFinite (m m' : ℤ) (h : m + (r : ℤ) = m')
    (δ : I → CycleGroup D sY m)
    (hδT : ∀ (w : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem Y), (δ w).1 Z ≠ 0 →
      subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T w)
    (γ : CycleGroup D sY m)
    (hγ : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y, γ.1 Z = ∑ᶠ w : I, (δ w).1 Z)
    (A : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr m m' h γ).1 A =
      ∑ᶠ w : I, (flatPullbackMap D sX hX sY hY f hbase r hflat hr m m' h (δ w)).1 A := by
  have hγ' : γ = locallyFiniteCycleSum D sY m T hT δ hδT :=
    Subtype.ext (funext fun Z =>
      (hγ Z).trans (locallyFiniteCycleSum_apply D sY m T hT δ hδT Z).symm)
  subst hγ' h
  exact flatPullbackMap_coe_locallyFiniteCycleSum D sX hX sY hY f hbase r hflat hr m _ rfl T hT δ
    hδT A

end Pullback

section Formula

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    {I : Type*} (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)

/-- The summand `c₁(ℒ)^s ∩ π^*γ` of a cycle `γ` carried by a set is carried by its inverse
image. -/
theorem subspacePointSet_subset_of_firstChernCapPowCycleMap_flatPullbackMap_ne_zero (s : ℕ)
    (m N : ℤ) (h : m + (n : ℤ) = N + s) (γ : CycleGroup D sX m)
    (S : Set (points D.site D.base D.base_mem X))
    (hS : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X, γ.1 Z ≠ 0 →
      subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ S)
    (A : IntegralClosedSubspace D.site D.base D.base_mem P)
    (hA : (firstChernCapPowCycleMap D sP hP L hL s N
      (flatPullbackMap D sP hP sX hX π hπB n hflat hrel m (N + s) h γ)).1 A ≠ 0) :
    subspacePointSet D.site D.base D.base_mem P A.subspace ⊆
      pointsMap D.site D.base D.base_mem P π ⁻¹' S := by
  rw [← firstChernCapPowCycleMapOfRule_canonicalFirstChernRule D sP hP L hL s] at hA
  exact subspacePointSet_subset_of_firstChernCapPowCycleMapOfRule_ne_zero D sP hP _ s N _ _
    (subspacePointSet_subset_of_flatPullbackMap_ne_zero D sP hP sX hX π hπB n hflat hrel m
      (N + s) h γ S hS) A hA

include hT in
/-- **The map of the projective bundle formula commutes with locally finite sums**: if each
`α_i = ∑_w γ_{i,w}` coefficientwise, `γ_{i,w}` carried by the member `T_w` of a locally finite
family, then `∑_i c₁(ℒ)^i ∩ π^*α_i = ∑_w ∑_i c₁(ℒ)^i ∩ π^*γ_{i,w}` coefficientwise. -/
theorem bundleFormulaCycle_apply_of_locallyFinite (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (γ : ∀ i, I → CycleGroup D sX (d i))
    (hγT : ∀ (i : Fin (n + 1)) (w : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (γ i w).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T w)
    (α : ∀ i, CycleGroup D sX (d i))
    (hα : ∀ (i : Fin (n + 1)) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z = ∑ᶠ w : I, (γ i w).1 Z)
    (A : IntegralClosedSubspace D.site D.base D.base_mem P) :
    (bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α).1 A =
      ∑ᶠ w : I, (bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd
        (fun i => γ i w)).1 A := by
  have hT' : LocallyFinite fun w : I => pointsMap D.site D.base D.base_mem P π ⁻¹' T w :=
    hT.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem π)
  have hterm : ∀ i : Fin (n + 1),
      (firstChernCapPowCycleMap D sP hP L hL i N
        (flatPullbackMap D sP hP sX hX π hπB n hflat hrel (d i) (N + (i : ℕ)) (hd i) (α i))).1 A =
      ∑ᶠ w : I, (firstChernCapPowCycleMap D sP hP L hL i N
        (flatPullbackMap D sP hP sX hX π hπB n hflat hrel (d i) (N + (i : ℕ)) (hd i)
          (γ i w))).1 A := by
    intro i
    simp only [← firstChernCapPowCycleMapOfRule_canonicalFirstChernRule D sP hP L hL i]
    exact firstChernCapPowCycleMapOfRule_apply_of_locallyFinite D sP hP _ hT' _ i N _
      (fun w Z hZ => subspacePointSet_subset_of_flatPullbackMap_ne_zero D sP hP sX hX π hπB n hflat
        hrel (d i) (N + (i : ℕ)) (hd i) (γ i w) (T w) (hγT i w) Z hZ) _
      (flatPullbackMap_apply_of_locallyFinite D sP hP sX hX π hπB n hflat hrel T hT (d i)
        (N + (i : ℕ)) (hd i) (γ i) (hγT i) (α i) (hα i)) A
  have hfin : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
      (Function.support fun w : I => (firstChernCapPowCycleMap D sP hP L hL i N
        (flatPullbackMap D sP hP sX hX π hπB n hflat hrel (d i) (N + (i : ℕ)) (hd i)
          (γ i w))).1 A).Finite := fun i _ =>
    finite_support_locallyFiniteCycleCoeff D sP N _ hT' _
      (fun w Z hZ => subspacePointSet_subset_of_firstChernCapPowCycleMap_flatPullbackMap_ne_zero D
        sX hX sP hP π hπB n hflat hrel L hL i (d i) N (hd i) (γ i w) (T w) (hγT i w) Z hZ) A
  unfold bundleFormulaCycle
  rw [cycleGroup_finset_sum_apply, Finset.sum_congr rfl fun i _ => hterm i,
    ← finsum_sum_comm _ _ hfin]
  exact finsum_congr fun w => (cycleGroup_finset_sum_apply D sP N _ _ A).symm

end Formula

end AlgebraicGeometry.Space

end
