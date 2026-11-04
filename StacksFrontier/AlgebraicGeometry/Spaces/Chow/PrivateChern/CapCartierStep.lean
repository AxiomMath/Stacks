module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.CapChain
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.TopSegreSupportedInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinClosedSubspaceIntersectionAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinMemberRuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinOfClosedSubspaceNonContainment
import all StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinOfClosedSubspaceNonContainment

/-!
# The cap product with `c₁(ℒ)` of the cycle of a closed subspace cut by a regular section

In Situation 0EDT let `X/B` be good, `ℒ` an invertible `𝒪_X`-module with a global section `σ`,
`E = Z(σ)` its vanishing locus and `i : E → X` the closed immersion. For a closed subspace
`C ⊆ X` with `dim_δ(C) ≤ m + 1` on which `E ∩ C` is an effective Cartier divisor,

`c₁(ℒ) ∩ [C]_{m+1} ∼_rat i_*(i^*[C]_{m+1}) = i_*[E ∩ C]_m`   on `|C|`,

the cap product being the one of Stacks 0EQJ at the canonical choices.

## Main results

* `rationallyEquivalentOn_firstChernCapCycleMap_restrictedSectionChernRule`: the cap products at
  the canonical rule and at the rule of the restricted section are rationally equivalent on any
  set containing the components of the cycle, when no component lies in `E`.
* `rationallyEquivalentOn_firstChernCapCycleMap_closedSubspaceCycle`:
  `c₁(ℒ) ∩ [C]_{m+1} ∼_rat i_*(i^*[C]_{m+1})` on `|C|`.
* `rationallyEquivalentOn_firstChernCapCycleMap_closedSubspaceCycle_inf`:
  `c₁(ℒ) ∩ [C]_{m+1} ∼_rat [C ∩ E]_m` on `|C|`.
* `deltaDimensionSubspace_inf_vanishingLocus_le`: cutting a closed subspace by an effective
  Cartier divisor `Z(σ) ∩ C` lowers its δ-dimension by one.
* `rationallyEquivalentOn_iteratedFirstChernCapCycle_closedSubspaceCycle_chain`:
  for closed subspaces `C_0 ⊆ ⋯ ⊆ C_d` with `C_{j-1} = C_j ∩ Z(σ_j)` cut out by regular sections,
  `c₁(ℒ)^d ∩ [C_d] ∼_rat [C_0]` on `|C_d|`.
* `rationallyEquivalentOn_topSegreCycle_flatPullbackMap_integralCycle_of_chain`:
  for `π : P ⟶ U` proper and flat of relative dimension `d` and an integral `Z' ⊆ U`, a chain
  starting at `C_d = π^{-1}(Z')` and ending at a `C_0` with `π_*[C_0] = [Z']` gives
  `π_*(c₁(ℒ)^d ∩ π^*[Z']) ∼_rat [Z']` on `|Z'|`.
* `rationallyEquivalentOn_topSegreCycle_flatPullbackMap_integralCycle_of_regularChain`:
  the same with the δ-dimension bounds derived (flatness for `C_d`, the dimension drop below).

## References

* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (hLs : IsInvertibleSheaf D sX hX L) (σ : L.sections) (m : ℤ)

/-- The canonical rule and the rule of a restricted section give rationally equivalent cap
products, on any set `S` containing the components of a `(m+1)`-cycle `β` none of which lies
in the vanishing locus `E = Z(σ)`. -/
theorem rationallyEquivalentOn_firstChernCapCycleMap_restrictedSectionChernRule
    (β : CycleGroup D sX (m + 1)) (S : Set (points D.site D.base D.base_mem X))
    (hβ : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X, β.1 T ≠ 0 →
      ¬ T.subspace ≤ (vanishingLocus D sX hX L σ).1 ∧
        subspacePointSet D.site D.base D.base_mem X T.subspace ⊆ S) :
    RationallyEquivalentOn.{u + 1} D sX hX m S
      (firstChernCapCycleMap D sX hX m (canonicalFirstChernRule D sX hX L hL m) β)
      (firstChernCapCycleMap D sX hX m (restrictedSectionChernRule D sX hX L σ hLs m
        (canonicalFirstChernRule D sX hX L hL m)) β) := by
  refine (rationallyEquivalentOn_iff_zero.{u + 1} D sX hX _).2
    (rationallyEquivalentOn_of_withinCanonical D
      (isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_sub D sX hX m _ _ β S
        fun T hT hβT _ => ⟨?_, (hβ T hβT).2⟩))
  have hTE := (hβ T hβT).1
  rw [show restrictedSectionChernRule D sX hX L σ hLs m (canonicalFirstChernRule D sX hX L hL m)
      T hT = _ from dif_neg hTE]
  exact isPrincipalDivisorCycleOfGood_canonicalDivisorCycleAt_sub D _ _ T.isIntegralSpace _ _ _ _
    _ _ _

include hLs in
/-- `c₁(ℒ) ∩ [C]_{m+1} ∼_rat i_*(i^*[C]_{m+1})` on `|C|` for a closed subspace `C ⊆ X` with
`dim_δ(C) ≤ m + 1` on which `E ∩ C` is an effective Cartier divisor. -/
theorem rationallyEquivalentOn_firstChernCapCycleMap_closedSubspaceCycle
    (C : ClosedSubspaces D.site D.base D.base_mem X)
    (hCdim : deltaDimensionSubspace D sX hX C.1 C.2 ≤ ((m + 1 : ℤ) : EInt))
    (hCart : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨C.1.toFunctor, C.2.1⟩
      (interOnClosedSubspace D sX hX L σ C)) :
    RationallyEquivalentOn.{u + 1} D sX hX m (subspacePointSet D.site D.base D.base_mem X C.1)
      (firstChernCapCycleMap D sX hX m (canonicalFirstChernRule D sX hX L hL m)
        (closedSubspaceCycle D sX hX C.1 C.2 (m + 1) hCdim))
      (cycleGroupClosedPushforward D hX.1 (vanishingLocus D sX hX L σ).2.1
        (D.isDecentSpace_of_isGood sX hX) (vanishingLocus D sX hX L σ).2.2 sX hX.2.2
        ((vanishingLocus D sX hX L σ).1.ι ≫ sX) rfl m
        (gysinCycleMap D sX (vanishingLocus D sX hX L σ) (isGood_vanishingLocus D sX hX L σ) m
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L σ)
            (isGood_vanishingLocus D sX hX L σ) m (canonicalFirstChernRule D sX hX L hL m))
          (closedSubspaceCycle D sX hX C.1 C.2 (m + 1) hCdim))) := by
  rw [cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap D sX hX L σ hLs m]
  refine rationallyEquivalentOn_firstChernCapCycleMap_restrictedSectionChernRule D sX hX L hL hLs
    σ m _ _ fun T hT => ⟨?_, ?_⟩
  · exact not_le_vanishingLocus_of_cycleCoeffOfClosedSubspace_ne_zero D sX hX L σ (m + 1) C hCdim
      hCart _ T hT
  · exact subspacePointSet_subset_of_closedSubspaceCycle_ne_zero D sX hX C.1 C.2 (m + 1) hCdim T hT

/-- Two closed subspaces given by equal subfunctors have the same cycle coefficients, whatever
the degrees and bounds used to form them as long as the degrees agree. -/
theorem closedSubspaceCycle_coe_congr {Y Y' : Subfunctor X}
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (hY' : IsClosedSubspace D.site D.base D.base_mem Y') (h : Y = Y') {a b : ℤ} (hab : a = b)
    (ha : deltaDimensionSubspace D sX hX Y hY ≤ (a : EInt))
    (hb : deltaDimensionSubspace D sX hX Y' hY' ≤ (b : EInt)) :
    (closedSubspaceCycle D sX hX Y hY a ha).1 = (closedSubspaceCycle D sX hX Y' hY' b hb).1 := by
  subst h hab
  rfl

/-- Two closed subspaces given by equal subfunctors have the same δ-dimension. -/
theorem deltaDimensionSubspace_congr {Y Y' : Subfunctor X}
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (hY' : IsClosedSubspace D.site D.base D.base_mem Y') (h : Y = Y') :
    deltaDimensionSubspace D sX hX Y hY = deltaDimensionSubspace D sX hX Y' hY' := by
  subst h
  rfl

include hLs in
/-- `c₁(ℒ) ∩ [C]_{m+1} ∼_rat [C ∩ E]_m` on `|C|`, for `E = Z(σ)` and a closed subspace
`C ⊆ X` with `dim_δ(C) ≤ m + 1` on which `E ∩ C` is an effective Cartier divisor, the right-hand
side being the cycle of Stacks 0EE9 of the scheme-theoretic intersection `C ∩ E` in `X`. -/
theorem rationallyEquivalentOn_firstChernCapCycleMap_closedSubspaceCycle_inf
    (C : ClosedSubspaces D.site D.base D.base_mem X)
    (hCdim : deltaDimensionSubspace D sX hX C.1 C.2 ≤ ((m + 1 : ℤ) : EInt))
    (hCart : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨C.1.toFunctor, C.2.1⟩
      (interOnClosedSubspace D sX hX L σ C))
    (hinf : deltaDimensionSubspace D sX hX (C.1 ⊓ (vanishingLocus D sX hX L σ).1)
      (inf_isClosedSubspace D.site D.base D.base_mem X hX.1 C (vanishingLocus D sX hX L σ)) ≤
        (m : EInt)) :
    RationallyEquivalentOn.{u + 1} D sX hX m (subspacePointSet D.site D.base D.base_mem X C.1)
      (firstChernCapCycleMap D sX hX m (canonicalFirstChernRule D sX hX L hL m)
        (closedSubspaceCycle D sX hX C.1 C.2 (m + 1) hCdim))
      (closedSubspaceCycle D sX hX (C.1 ⊓ (vanishingLocus D sX hX L σ).1)
        (inf_isClosedSubspace D.site D.base D.base_mem X hX.1 C (vanishingLocus D sX hX L σ))
        m hinf) := by
  convert rationallyEquivalentOn_firstChernCapCycleMap_closedSubspaceCycle D sX hX L hL hLs σ m C
    hCdim hCart using 1
  refine Subtype.ext ?_
  show _ = cycleClosedPushforward D hX.1 (vanishingLocus D sX hX L σ).2.1
    (D.isDecentSpace_of_isGood sX hX) (vanishingLocus D sX hX L σ).2.2
    (gysinCycleMap D sX (vanishingLocus D sX hX L σ) (isGood_vanishingLocus D sX hX L σ) m
      (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L σ)
        (isGood_vanishingLocus D sX hX L σ) m (canonicalFirstChernRule D sX hX L hL m))
      (closedSubspaceCycle D sX hX C.1 C.2 (m + 1) hCdim)).1
  rw [gysinCycleMap_closedSubspaceCycle_coe_eq D sX hX L σ m C hLs _ hCdim hCart]
  exact (cycleClosedPushforward_cycleCoeffOfClosedSubspace_preimage_eq_inf D sX hX C m
    (vanishingLocus D sX hX L σ)).symm

/-- For a closed subspace `C ⊆ X` with `dim_δ(C) ≤ m + 1` on which `Z(σ) ∩ C` is an effective
Cartier divisor, `dim_δ(C ∩ Z(σ)) ≤ m`. -/
theorem deltaDimensionSubspace_inf_vanishingLocus_le
    (C : ClosedSubspaces D.site D.base D.base_mem X)
    (hCdim : deltaDimensionSubspace D sX hX C.1 C.2 ≤ ((m + 1 : ℤ) : EInt))
    (hCart : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨C.1.toFunctor, C.2.1⟩
      (interOnClosedSubspace D sX hX L σ C)) :
    deltaDimensionSubspace D sX hX (C.1 ⊓ (vanishingLocus D sX hX L σ).1)
      (inf_isClosedSubspace D.site D.base D.base_mem X hX.1 C (vanishingLocus D sX hX L σ)) ≤
        (m : EInt) := by
  set T := subspacePointSet D.site D.base D.base_mem X C.1
  set E := vanishingLocus D sX hX L σ
  have hTcl : IsClosed T := isClosed_subspacePointSet_of_isClosedSubspace D hX.1 C.1 C.2
  have hEcl : IsClosed (subspacePointSet D.site D.base D.base_mem X E.1) :=
    isClosed_subspacePointSet_of_isClosedSubspace D hX.1 _ E.2
  have hbound := (deltaDimensionClosed_le_coe_iff D sX hX T hTcl (m + 1)).1 hCdim
  refine (deltaDimensionClosed_le_coe_iff D sX hX _ _ m).2 fun t ht => ?_
  have htT : t ∈ T := subspacePointSet_mono_of_le D inf_le_left ht
  have htE : t ∈ subspacePointSet D.site D.base D.base_mem X E.1 :=
    subspacePointSet_mono_of_le D inf_le_right ht
  have hg : Topology.IsClosedEmbedding
      (pointsMap D.site D.base D.base_mem C.1.toFunctor C.1.ι) :=
    isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1 C.2.2
  have hcompl : subspacePointSet D.site D.base D.base_mem C.1.toFunctor
      (openComplement D.site D.base D.base_mem (interOnClosedSubspace D sX hX L σ C).1) =
      (subspacePointSet D.site D.base D.base_mem C.1.toFunctor
        (interOnClosedSubspace D sX hX L σ C).1)ᶜ :=
    range_pointsMap_ι_openComplement D.site D.base D.base_mem _
  have hinter : subspacePointSet D.site D.base D.base_mem C.1.toFunctor
      (interOnClosedSubspace D sX hX L σ C).1 =
      pointsMap D.site D.base D.base_mem C.1.toFunctor C.1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X E.1 :=
    subspacePointSet_preimage D.site D.base D.base_mem C.1.ι E.1
  have hdense : Dense (pointsMap D.site D.base D.base_mem C.1.toFunctor C.1.ι ⁻¹'
      (subspacePointSet D.site D.base D.base_mem X E.1)ᶜ) := by
    have h : Dense (subspacePointSet D.site D.base D.base_mem C.1.toFunctor
        (openComplement D.site D.base D.base_mem (interOnClosedSubspace D sX hX L σ C).1)) :=
      dense_subspacePointSet_of_isSchemeTheoreticallyDense D.site D.base D.base_mem
        (X := ⟨C.1.toFunctor, C.2.1⟩)
        (openComplement D.site D.base D.base_mem (interOnClosedSubspace D sX hX L σ C).1)
        (isSchemeTheoreticallyDense_openComplement_of_isEffectiveCartierDivisor D.site D.base
          D.base_mem ⟨C.1.toFunctor, C.2.1⟩ (interOnClosedSubspace D sX hX L σ C) hCart)
    rwa [hcompl, hinter, ← Set.preimage_compl] at h
  have hN := isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hX.1
    D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian
  have hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D sX hX
  have hTsober : QuasiSober (Set.range (pointsMap D.site D.base D.base_mem C.1.toFunctor C.1.ι)) :=
    hTcl.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨K, hK, htK⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({(⟨t, htT⟩ : Set.range (pointsMap D.site D.base D.base_mem C.1.toFunctor C.1.ι))} :
      Set (Set.range (pointsMap D.site D.base D.base_mem C.1.toFunctor C.1.ι)))
    isIrreducible_singleton
  have hKcl : IsClosed K := isClosed_of_mem_irreducibleComponents K hK
  set η' := hK.1.genericPoint
  have hη'K : closure ({η'} : Set (Set.range (pointsMap D.site D.base D.base_mem
      C.1.toFunctor C.1.ι))) = K := (hK.1.isGenericPoint_genericPoint_closure).trans
    hKcl.closure_eq
  have hηcl : closure ({η'.1} : Set (points D.site D.base D.base_mem X)) = Subtype.val '' K := by
    rw [← hη'K, ← Set.image_singleton, hTcl.isClosedEmbedding_subtypeVal.closure_image_eq]
  have hηE : η'.1 ∉ subspacePointSet D.site D.base D.base_mem X E.1 :=
    notMem_of_dense_preimage_compl hg (locallyFinite_irreducibleComponents_of_isClosed
      D.site D.base D.base_mem X hX.1 hN _ hTcl) hEcl hdense (C := ⟨K, hK⟩) hηcl
  have hspec : η'.1 ⤳ t := by
    rw [specializes_iff_mem_closure, hηcl]
    exact ⟨⟨t, htT⟩, htK rfl, rfl⟩
  have hne : η'.1 ≠ t := fun h => hηE (h ▸ htE)
  have hlt := lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hX.1
    (isDecentSpace_of_isGood D sX hX) D.isAlgebraicSpace
    (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
      D.isAlgebraicSpace D.quasiSeparated)
    D.locallyNoetherian D.universallyCatenary D.delta sX hX.2.2 hspec hne
  have hη := hbound η'.1 η'.2
  omega

include hLs in
/-- Iterated cap products along a chain of closed subspaces cut out by regular sections. Let
`σ_1, σ_2, …` be global sections of `ℒ` and `C_0, …, C_d` closed subspaces of `X` with
`C_{j-1} = C_j ∩ Z(σ_j)`, `dim_δ(C_j) ≤ k + j`, and `Z(σ_j) ∩ C_j` an effective Cartier divisor
on `C_j`. Then `c₁(ℒ)^d ∩ [C_d]_{k+d} ∼_rat [C_0]_k` on `|C_d|`, the cap products being those of
Stacks 0EQJ at the canonical choices. -/
theorem rationallyEquivalentOn_iteratedFirstChernCapCycle_closedSubspaceCycle_chain
    (σ : ℕ → L.sections) (k : ℤ) (C : ℕ → ClosedSubspaces D.site D.base D.base_mem X) :
    ∀ (d : ℕ) (hdim : ∀ j ≤ d,
        deltaDimensionSubspace D sX hX (C j).1 (C j).2 ≤ ((k + j : ℤ) : EInt))
      (_ : ∀ j < d, (C j).1 = (C (j + 1)).1 ⊓ (vanishingLocus D sX hX L (σ (j + 1))).1)
      (_ : ∀ j < d, IsEffectiveCartierDivisor D.site D.base D.base_mem
        ⟨(C (j + 1)).1.toFunctor, (C (j + 1)).2.1⟩
        (interOnClosedSubspace D sX hX L (σ (j + 1)) (C (j + 1)))),
      RationallyEquivalentOn.{u + 1} D sX hX k
        (subspacePointSet D.site D.base D.base_mem X (C d).1)
        (iteratedFirstChernCapCycle D sX hX d (fun _ => L) (fun _ => hL) k
          (closedSubspaceCycle D sX hX (C d).1 (C d).2 (k + d) (hdim d le_rfl)))
        (closedSubspaceCycle D sX hX (C 0).1 (C 0).2 k (by simpa using hdim 0 (Nat.zero_le d)))
  | 0, hdim, _, _ => by
    have h0 : iteratedFirstChernCapCycle D sX hX 0 (fun _ => L) (fun _ => hL) k
        (closedSubspaceCycle D sX hX (C 0).1 (C 0).2 (k + ((0 : ℕ) : ℤ)) (hdim 0 le_rfl)) =
        closedSubspaceCycle D sX hX (C 0).1 (C 0).2 k (by simpa using hdim 0 (Nat.zero_le 0)) :=
      Subtype.ext ((iteratedFirstChernCapCycle_zero D sX hX _ _ k _).trans
        (closedSubspaceCycle_coe_congr D sX hX _ _ rfl (by simp) _ _))
    rw [h0]
    exact rationallyEquivalentOn_refl.{u + 1} D sX hX k _ _
  | d + 1, hdim, hC, hCart => by
    have IH := rationallyEquivalentOn_iteratedFirstChernCapCycle_closedSubspaceCycle_chain σ k C d
      (fun j hj => hdim j (Nat.le_succ_of_le hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj))
      (fun j hj => hCart j (Nat.lt_succ_of_lt hj))
    rw [iteratedFirstChernCapCycle_succ]
    have hk : k + ((d + 1 : ℕ) : ℤ) = (k + d : ℤ) + 1 := by push_cast; ring
    have hd1 : deltaDimensionSubspace D sX hX (C (d + 1)).1 (C (d + 1)).2 ≤
        (((k + d : ℤ) + 1 : ℤ) : EInt) := by
      have := hdim (d + 1) le_rfl
      rwa [hk] at this
    have hcast : cycleGroupCast D sX hk
        (closedSubspaceCycle D sX hX (C (d + 1)).1 (C (d + 1)).2 (k + ((d + 1 : ℕ) : ℤ))
          (hdim (d + 1) le_rfl)) =
        closedSubspaceCycle D sX hX (C (d + 1)).1 (C (d + 1)).2 ((k + d : ℤ) + 1) hd1 :=
      Subtype.ext ((cycleGroupCast_coe D sX _ _).trans
        (closedSubspaceCycle_coe_congr D sX hX _ _ rfl hk _ _))
    rw [hcast]
    have hinf : deltaDimensionSubspace D sX hX
        ((C (d + 1)).1 ⊓ (vanishingLocus D sX hX L (σ (d + 1))).1)
        (inf_isClosedSubspace D.site D.base D.base_mem X hX.1 (C (d + 1))
          (vanishingLocus D sX hX L (σ (d + 1)))) ≤ ((k + d : ℤ) : EInt) :=
      (deltaDimensionSubspace_congr D sX hX _ _ (hC d (Nat.lt_succ_self d)).symm).le.trans
        (hdim d (Nat.le_succ d))
    have hstep := rationallyEquivalentOn_firstChernCapCycleMap_closedSubspaceCycle_inf D sX hX L hL
      hLs (σ (d + 1)) (k + d) (C (d + 1)) hd1 (hCart d (Nat.lt_succ_self d)) hinf
    have heq : closedSubspaceCycle D sX hX
        ((C (d + 1)).1 ⊓ (vanishingLocus D sX hX L (σ (d + 1))).1)
        (inf_isClosedSubspace D.site D.base D.base_mem X hX.1 (C (d + 1))
          (vanishingLocus D sX hX L (σ (d + 1)))) (k + d) hinf =
        closedSubspaceCycle D sX hX (C d).1 (C d).2 (k + d) (hdim d (Nat.le_succ d)) :=
      Subtype.ext (closedSubspaceCycle_coe_congr D sX hX _ _ (hC d (Nat.lt_succ_self d)).symm rfl
        _ _)
    rw [heq] at hstep
    have hsub : subspacePointSet D.site D.base D.base_mem X (C d).1 ⊆
        subspacePointSet D.site D.base D.base_mem X (C (d + 1)).1 := by
      rw [hC d (Nat.lt_succ_self d)]
      exact subspacePointSet_mono_of_le D inf_le_left
    exact RationallyEquivalentOn.trans
      (rationallyEquivalentOn_iteratedFirstChernCapCycle_of_rationallyEquivalentOn.{u + 1} D sX hX
        d (Fin.init fun _ => L) (fun _ => hL)
        (fun _ T k' α hα => rationallyEquivalentOn_firstChernCapCycleMap D sX hX L hL T k' α hα)
        _ k hstep)
      (RationallyEquivalentOn.mono hsub IH)

/-- The top Segre operation on an integral cycle, from a chain of sections. Let
`π : P ⟶ U` be a proper flat morphism of good algebraic spaces of relative dimension `d`, `ℒ`
invertible on `P` with global sections `σ_1, σ_2, …`, and `Z' ⊆ U` integral of δ-dimension `k`.
Suppose `C_d = π^{-1}(Z')`, `C_{j-1} = C_j ∩ Z(σ_j)` with `Z(σ_j) ∩ C_j` an effective Cartier
divisor on `C_j` and `dim_δ(C_j) ≤ k + j`, and `π_*[C_0]_k = [Z']`. Then
`π_*(c₁(ℒ)^d ∩ π^*[Z']) ∼_rat [Z']` on `|Z'|`. -/
theorem rationallyEquivalentOn_topSegreCycle_flatPullbackMap_integralCycle_of_chain
    {P U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sP : P ⟶ D.space)
    (hP : D.IsGood sP) (sU : U ⟶ D.space) (hU : D.IsGood sU) {π : P ⟶ U} (hπ : π ≫ sU = sP)
    (hπp : IsProper D.site D.base D.base_mem π) (d : ℕ)
    (hπf : IsFlat D.site D.base D.base_mem π)
    (hπd : HasRelativeDimension d D.site D.base D.base_mem π)
    (N : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hN : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (hNs : IsInvertibleSheaf D sP hP N) (τ : ℕ → N.sections) (k : ℤ)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem U) (hZ' : deltaDimension D sU Z' = k)
    (C : ℕ → ClosedSubspaces D.site D.base D.base_mem P) (hCd : (C d).1 = Z'.subspace.preimage π)
    (hdim : ∀ j ≤ d, deltaDimensionSubspace D sP hP (C j).1 (C j).2 ≤ ((k + j : ℤ) : EInt))
    (hC : ∀ j < d, (C j).1 = (C (j + 1)).1 ⊓ (vanishingLocus D sP hP N (τ (j + 1))).1)
    (hCart : ∀ j < d, IsEffectiveCartierDivisor D.site D.base D.base_mem
      ⟨(C (j + 1)).1.toFunctor, (C (j + 1)).2.1⟩
      (interOnClosedSubspace D sP hP N (τ (j + 1)) (C (j + 1))))
    (h0 : properCyclePushforward D sP hP sU hU hπ hπp.2.1.2 k
        (closedSubspaceCycle D sP hP (C 0).1 (C 0).2 k (by simpa using hdim 0 (Nat.zero_le d))) =
      integralCycle D sU k Z' hZ') :
    RationallyEquivalentOn.{u + 1} D sU hU k
      (subspacePointSet D.site D.base D.base_mem U Z'.subspace)
      (topSegreCycle D sP hP sU hU hπ hπp.2.1.2 N hN d k (k + d) rfl
        (flatPullbackMap D sP hP sU hU π hπ d hπf hπd k (k + d) rfl (integralCycle D sU k Z' hZ')))
      (integralCycle D sU k Z' hZ') := by
  have hpull : cycleGroupCast D sP rfl
      (flatPullbackMap D sP hP sU hU π hπ d hπf hπd k (k + d) rfl (integralCycle D sU k Z' hZ')) =
      closedSubspaceCycle D sP hP (C d).1 (C d).2 (k + d) (hdim d le_rfl) := by
    refine Subtype.ext (funext fun T => ?_)
    rw [cycleGroupCast_coe, flatPullbackMap_integralCycle]
    exact congrFun (closedSubspaceCycle_coe_congr D sP hP _ _ hCd.symm (by rw [hZ']) _ _) T
  have hchain := rationallyEquivalentOn_iteratedFirstChernCapCycle_closedSubspaceCycle_chain D sP hP
    N hN hNs τ k C d hdim hC hCart
  have hpush := rationallyEquivalentOn_properCyclePushforward.{u + 1} D sP hP sU hU hπ hπp k _ _
    ((rationallyEquivalentOn_iff_zero.{u + 1} D sP hP _).1 hchain)
  rw [map_sub, h0] at hpush
  have hsub : closure (pointsMap D.site D.base D.base_mem P π ''
      subspacePointSet D.site D.base D.base_mem P (C d).1) ⊆
      subspacePointSet D.site D.base D.base_mem U Z'.subspace := by
    refine closure_minimal ?_ (isClosed_range_pointsMap_integralClosedSubspace D.site D.base
      D.base_mem hU.1 Z')
    rw [hCd, subspacePointSet_preimage]
    exact Set.image_preimage_subset _ _
  have key := (rationallyEquivalentOn_iff_zero.{u + 1} D sU hU _).2 hpush
  show RationallyEquivalentOn.{u + 1} D sU hU k _
    (properCyclePushforward D sP hP sU hU hπ hπp.2.1.2 k
      (iteratedFirstChernCapCycle D sP hP d (fun _ => N) (fun _ => hN) k
        (cycleGroupCast D sP rfl (flatPullbackMap D sP hP sU hU π hπ d hπf hπd k (k + d) rfl
          (integralCycle D sU k Z' hZ'))))) _
  rw [hpull]
  exact RationallyEquivalentOn.mono hsub key

/-- The top Segre operation on an integral cycle, from a chain of regular sections: the statement
of `rationallyEquivalentOn_topSegreCycle_flatPullbackMap_integralCycle_of_chain` with no
δ-dimension bounds assumed. -/
theorem rationallyEquivalentOn_topSegreCycle_flatPullbackMap_integralCycle_of_regularChain
    {P U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sP : P ⟶ D.space)
    (hP : D.IsGood sP) (sU : U ⟶ D.space) (hU : D.IsGood sU) {π : P ⟶ U} (hπ : π ≫ sU = sP)
    (hπp : IsProper D.site D.base D.base_mem π) (d : ℕ)
    (hπf : IsFlat D.site D.base D.base_mem π)
    (hπd : HasRelativeDimension d D.site D.base D.base_mem π)
    (N : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hN : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (hNs : IsInvertibleSheaf D sP hP N) (τ : ℕ → N.sections) (k : ℤ)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem U) (hZ' : deltaDimension D sU Z' = k)
    (C : ℕ → ClosedSubspaces D.site D.base D.base_mem P) (hCd : (C d).1 = Z'.subspace.preimage π)
    (hC : ∀ j < d, (C j).1 = (C (j + 1)).1 ⊓ (vanishingLocus D sP hP N (τ (j + 1))).1)
    (hCart : ∀ j < d, IsEffectiveCartierDivisor D.site D.base D.base_mem
      ⟨(C (j + 1)).1.toFunctor, (C (j + 1)).2.1⟩
      (interOnClosedSubspace D sP hP N (τ (j + 1)) (C (j + 1))))
    (h0 : ∀ h0dim : deltaDimensionSubspace D sP hP (C 0).1 (C 0).2 ≤ (k : EInt),
      properCyclePushforward D sP hP sU hU hπ hπp.2.1.2 k
        (closedSubspaceCycle D sP hP (C 0).1 (C 0).2 k h0dim) = integralCycle D sU k Z' hZ') :
    RationallyEquivalentOn.{u + 1} D sU hU k
      (subspacePointSet D.site D.base D.base_mem U Z'.subspace)
      (topSegreCycle D sP hP sU hU hπ hπp.2.1.2 N hN d k (k + d) rfl
        (flatPullbackMap D sP hP sU hU π hπ d hπf hπd k (k + d) rfl (integralCycle D sU k Z' hZ')))
      (integralCycle D sU k Z' hZ') := by
  have htop : deltaDimensionSubspace D sP hP (C d).1 (C d).2 ≤ ((k + d : ℤ) : EInt) := by
    rw [deltaDimensionSubspace_congr D sP hP _ _ hCd, ← hZ']
    exact deltaDimensionSubspace_preimage_integralClosedSubspace_le D sP hP sU hU π hπ d hπf hπd Z'
  have haux : ∀ i, i ≤ d →
      deltaDimensionSubspace D sP hP (C (d - i)).1 (C (d - i)).2 ≤ ((k + (d - i : ℕ) : ℤ) : EInt)
  · intro i
    induction i with
    | zero => intro _; simpa using htop
    | succ i ih =>
      intro hi
      have hj : d - (i + 1) < d := by omega
      have hj1 : d - (i + 1) + 1 = d - i := by omega
      have hprev := ih (Nat.le_of_succ_le hi)
      rw [← hj1] at hprev
      have hdrop := deltaDimensionSubspace_inf_vanishingLocus_le D sP hP N (τ (d - (i + 1) + 1))
        (k + (d - (i + 1) : ℕ)) (C (d - (i + 1) + 1))
        (by rw [show (k + ((d - (i + 1) : ℕ) : ℤ) + 1 : ℤ) = k + ((d - (i + 1) + 1 : ℕ) : ℤ) by
          push_cast; ring]; exact hprev)
        (hCart _ hj)
      rwa [← deltaDimensionSubspace_congr D sP hP _ _ (hC _ hj)] at hdrop
  have hdim : ∀ j ≤ d, deltaDimensionSubspace D sP hP (C j).1 (C j).2 ≤ ((k + j : ℤ) : EInt) := by
    intro j hj
    have := haux (d - j) (Nat.sub_le d j)
    rwa [show d - (d - j) = j by omega] at this
  exact rationallyEquivalentOn_topSegreCycle_flatPullbackMap_integralCycle_of_chain D sP hP sU hU hπ
    hπp d hπf hπd N hN hNs τ k Z' hZ' C hCd hdim hC hCart (h0 _)

end AlgebraicGeometry.Space.PrivateChern

end
