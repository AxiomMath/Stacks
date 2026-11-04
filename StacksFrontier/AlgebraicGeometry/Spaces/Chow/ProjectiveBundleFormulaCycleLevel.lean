module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineBundleSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatProperTopPowerOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSurjectiveAffineFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaIsoTransport

/-!
# The map of the projective bundle formula on cycles, along closed and open subspaces

Let `π : P → X` be proper and flat of relative dimension `n` between good algebraic spaces over
the base, and `ℒ` invertible on `P`. On cycles the map of Stacks 0ERV is
`(α_i) ↦ ∑_i c₁(ℒ)^i ∩ π^*α_i` (`AlgebraicGeometry.Space.bundleFormulaCycle`); its class is the
map `AlgebraicGeometry.Space.bundleFormulaMap` on the Chow groups. This file proves the two
compatibilities the proof of the surjectivity half of Stacks 0ERV uses.

* *Closed subspaces of the base.* For a closed subspace `i : Z → X` with inverse image
  `i' : P_Z = π^{-1}(Z) → P` and `ℒ_Z = ℒ|_{P_Z}`, if the map for `(P_Z → Z, ℒ_Z)` sends `α` to a
  cycle rationally equivalent to `β`, then the map for `(π, ℒ)` sends `i_*α` to a cycle rationally
  equivalent to `i'_*β` through principal divisors carried by `|P_Z|`. On cycles
  `i'_*(c₁(ℒ_Z)^s ∩ π_Z^*α) = c₁(ℒ)^s ∩ π^*(i_*α)` holds exactly once the cap products on `P_Z` are
  taken at the rule transported from `P` (Stacks 0EPD for the closed immersion, and the exact
  compatibility of the cap products), and the transported rule agrees with the canonical rule of
  `ℒ_Z` up to rational equivalence (Stacks 0EQT for a closed immersion).
* *Open subspaces of the base.* For an open immersion `j : U → X` with base change
  `j' : P_U → P`, `π_U : P_U → U`, the restriction to `P_U` of the map for `(π, ℒ)` is the map for
  `(π_U, j'^*ℒ)` on restrictions, up to rational equivalence (Stacks 0EQR, and
  `j'^*π^* = π_U^*j^*`).

## Main definitions

* `AlgebraicGeometry.Space.bundleFormulaCycle`: `(α_i) ↦ ∑_i c₁(ℒ)^i ∩ π^*α_i` on cycles.
* `AlgebraicGeometry.Space.bundleFormulaCycleOfRule`: the same with the cap products at a family
  of component rules.

## Main results

* `AlgebraicGeometry.Space.bundleFormulaMap_chowClassCanonical`: the class of the cycle-level
  map is the map on Chow groups.
* `Space.isRationallyEquivalentToZeroWithinCanonical_bundleFormulaCycle_closedPushforward_sub`:
  the closed subspace compatibility.
* `AlgebraicGeometry.Space.chowClassCanonical_cycleGroupRestrict_bundleFormulaCycle`: the open
  subspace compatibility, as an equality of Chow classes on `P_U`.

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Canonical sums of principal divisors -/

section Canonical

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ}

/-- A rational equivalence to zero at the canonical embeddings of Stacks 0ENK within a carrier is
a sum of canonical principal divisors within that carrier: a principal divisor of a unit `f` read
at the canonical embeddings is the canonical principal divisor of `f`. -/
theorem IsRationallyEquivalentToZeroWithinCanonical.isCanonicallyRationallyEquivalentToZeroWithin
    {α : CycleGroup D sX k} {T : Set (points D.site D.base D.base_mem X)}
    (h : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k α T := by
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, hsum⟩ := h
  refine ⟨J, W, hWfin, c, hsub, fun j => ?_, hsum⟩
  obtain ⟨f, hf, heq⟩ := hprin j
  have hk : deltaDimensionClosed D ((W j).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (W j))
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX (W j), hdim j]
  exact ⟨hk, hf.unit, Subtype.ext heq⟩

end Canonical

/-! ### The map on cycles -/

section Cycle

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)

/-- The map `(α_i) ↦ ∑_i c₁^i ∩ π^*α_i` of the projective bundle formula on cycles, the cap
products being taken at a family of component rules `R`. -/
def bundleFormulaCycleOfRule (R : ∀ m : ℤ, FirstChernComponentCycleRule D sP m) (N : ℤ)
    (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ))
    (α : ∀ i, CycleGroup D sX (d i)) : CycleGroup D sP N :=
  ∑ i : Fin (n + 1), firstChernCapPowCycleMapOfRule D sP hP R i N
    (flatPullbackMap D sP hP sX hX π hπB n hflat hrel (d i) (N + (i : ℕ)) (hd i) (α i))

variable (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The map of the projective bundle formula on cycles**: `(α_i) ↦ ∑_i c₁(ℒ)^i ∩ π^*α_i`,
from `∏_i Z_{d i}(X)` to `Z_N(P)`, `d i + n = N + i`. -/
def bundleFormulaCycle (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ))
    (α : ∀ i, CycleGroup D sX (d i)) : CycleGroup D sP N :=
  ∑ i : Fin (n + 1), firstChernCapPowCycleMap D sP hP L hL i N
    (flatPullbackMap D sP hP sX hX π hπB n hflat hrel (d i) (N + (i : ℕ)) (hd i) (α i))

/-- At the canonical rules the map is `AlgebraicGeometry.Space.bundleFormulaCycle`. -/
theorem bundleFormulaCycleOfRule_canonicalFirstChernRule (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (α : ∀ i, CycleGroup D sX (d i)) :
    bundleFormulaCycleOfRule D sX hX sP hP π hπB n hflat hrel
        (fun m => canonicalFirstChernRule D sP hP L hL m) N d hd α =
      bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α :=
  Finset.sum_congr rfl fun i _ =>
    firstChernCapPowCycleMapOfRule_canonicalFirstChernRule D sP hP L hL i N _

/-- **The class of the cycle-level map is the map of the projective bundle formula on Chow
groups.** -/
theorem bundleFormulaMap_chowClassCanonical (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (α : ∀ i, CycleGroup D sX (d i)) :
    bundleFormulaMap D sX hX sP hP π hπB n hflat hrel L hL N d hd
        (fun i => chowClassCanonical.{u + 1} D sX hX (d i) (α i)) =
      chowClassCanonical.{u + 1} D sP hP N
        (bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α) := by
  simp only [bundleFormulaMap, ProjectiveBundleRelation.bundleSum_apply, bundleFormulaCycle,
    map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (chowClassCanonical.{u + 1} D sP hP N) (congrArg _ (Subtype.ext rfl))

/-- Rules agreeing with the canonical one up to rational equivalence give a map agreeing with
`AlgebraicGeometry.Space.bundleFormulaCycle` up to rational equivalence. -/
theorem isRationallyEquivalentToZeroCanonical_bundleFormulaCycleOfRule_sub
    (R : ∀ m : ℤ, FirstChernComponentCycleRule D sP m)
    (hR : ∀ (m : ℤ) (β : CycleGroup D sP (m + 1)),
      IsRationallyEquivalentToZeroCanonical.{u + 1} D sP hP m
        (firstChernCapCycleMap D sP hP m (R m) β -
          firstChernCapCycleMap D sP hP m (canonicalFirstChernRule D sP hP L hL m) β))
    (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ))
    (α : ∀ i, CycleGroup D sX (d i)) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D sP hP N
      (bundleFormulaCycleOfRule D sX hX sP hP π hπB n hflat hrel R N d hd α -
        bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α) := by
  unfold bundleFormulaCycleOfRule bundleFormulaCycle
  rw [← Finset.sum_sub_distrib]
  exact (rationalEquivalencesCanonical.{u + 1} D sP hP N).sum_mem fun i _ =>
    isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMapOfRule_sub D sP hP L hL R hR i N _

end Cycle

/-! ### Closed subspaces of the base -/

section Closed

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (Z : Subfunctor X) (hZ : IsClosedSubspace D.site D.base D.base_mem Z)

/-- `π^*(i_*β) = i'_*(π_Z^*β)` for the inclusion `i` of a closed subspace `Z ⊆ X`, in arbitrary
degrees `m + n = m'`. -/
theorem flatPullbackMap_cycleGroupClosedPushforward_of_eq (m m' : ℤ) (h : m + (n : ℤ) = m')
    (β : CycleGroup D (Z.ι ≫ sX) m) :
    flatPullbackMap D sP hP sX hX π hπB n hflat hrel m m' h
        (cycleGroupClosedPushforward D hX.1 hZ.1 (D.isDecentSpace_of_isGood sX hX) hZ.2 sX hX.2.2
          (Z.ι ≫ sX) rfl m β) =
      cycleGroupClosedPushforward D hP.1
        (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ).1
        (D.isDecentSpace_of_isGood sP hP)
        (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ).2 sP hP.2.2
        ((Z.preimage π).ι ≫ sP) rfl m'
        (flatPullbackMap D ((Z.preimage π).ι ≫ sP)
          (isGood_ι_of_isClosedSubspace D sP hP _
            (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
          (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ) (Z.fromPreimage π)
          (fromPreimage_comp_structureMorphism D sP sX π hπB Z) n
          (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
            hflat hrel).1
          (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
            hflat hrel).2 m m' h β) := by
  subst h
  exact flatPullbackMap_cycleGroupClosedPushforward D sP hP sX hX π hπB n hflat hrel Z hZ m β

/-- **Exact compatibility with pushforward along a closed subspace of the base**:
`i'_*(∑_i c₁^i ∩ π_Z^*α_i) = ∑_i c₁^i ∩ π^*(i_*α_i)`, the cap products on `π^{-1}(Z)` at the
transported rules. -/
theorem cycleGroupClosedPushforward_bundleFormulaCycleOfRule
    (R : ∀ m : ℤ, FirstChernComponentCycleRule D sP m) (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (α : ∀ i, CycleGroup D (Z.ι ≫ sX) (d i)) :
    cycleGroupClosedPushforward D hP.1
        (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ).1
        (D.isDecentSpace_of_isGood sP hP)
        (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ).2 sP hP.2.2
        ((Z.preimage π).ι ≫ sP) rfl N
        (bundleFormulaCycleOfRule D (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ)
          ((Z.preimage π).ι ≫ sP)
          (isGood_ι_of_isClosedSubspace D sP hP _
            (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
          (Z.fromPreimage π) (fromPreimage_comp_structureMorphism D sP sX π hπB Z) n
          (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
            hflat hrel).1
          (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
            hflat hrel).2
          (fun m => closedSubspaceChernRule D sP hP (Z.preimage π)
            (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ) m (R m))
          N d hd α) =
      bundleFormulaCycleOfRule D sX hX sP hP π hπB n hflat hrel R N d hd
        (fun i => cycleGroupClosedPushforward D hX.1 hZ.1 (D.isDecentSpace_of_isGood sX hX) hZ.2
          sX hX.2.2 (Z.ι ≫ sX) rfl (d i) (α i)) := by
  simp only [bundleFormulaCycleOfRule, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cycleGroupClosedPushforward_firstChernCapPowCycleMapOfRule D sP hP (Z.preimage π)
      (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ) R i N,
    flatPullbackMap_cycleGroupClosedPushforward_of_eq D sX hX sP hP π hπB n hflat hrel Z hZ]

variable (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The projective bundle formula along a closed subspace `i : Z → X` of the base.** If the map
for `(π_Z : π^{-1}(Z) → Z, ℒ|_{π^{-1}(Z)})` sends `α` to a cycle rationally equivalent to `β`,
then the map for `(π, ℒ)` sends `i_*α` to a cycle rationally equivalent to `i'_*β`, through
principal divisors carried by `|π^{-1}(Z)|`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_bundleFormulaCycle_closedPushforward_sub
    (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ))
    (α : ∀ i, CycleGroup D (Z.ι ≫ sX) (d i)) (β : CycleGroup D ((Z.preimage π).ι ≫ sP) N)
    (h : IsRationallyEquivalentToZeroCanonical.{u + 1} D ((Z.preimage π).ι ≫ sP)
      (isGood_ι_of_isClosedSubspace D sP hP _
        (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ)) N
      (bundleFormulaCycle D (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ)
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
            (Z.preimage π) (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
            L hL) N d hd α - β)) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sP hP N
      (bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd
          (fun i => cycleGroupClosedPushforward D hX.1 hZ.1 (D.isDecentSpace_of_isGood sX hX) hZ.2
            sX hX.2.2 (Z.ι ≫ sX) rfl (d i) (α i)) -
        cycleGroupClosedPushforward D hP.1
          (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ).1
          (D.isDecentSpace_of_isGood sP hP)
          (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ).2 sP hP.2.2
          ((Z.preimage π).ι ≫ sP) rfl N β)
      (subspacePointSet D.site D.base D.base_mem P (Z.preimage π)) := by
  have hc := isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ
  rw [← bundleFormulaCycleOfRule_canonicalFirstChernRule,
    ← cycleGroupClosedPushforward_bundleFormulaCycleOfRule D sX hX sP hP π hπB n hflat hrel Z hZ,
    ← map_sub]
  refine isRationallyEquivalentToZeroWithinCanonical_cycleGroupClosedPushforward D sP hP
    (Z.preimage π) hc N ?_
  have h1 := isRationallyEquivalentToZeroCanonical_bundleFormulaCycleOfRule_sub D (Z.ι ≫ sX)
    (isGood_ι_of_isClosedSubspace D sX hX Z hZ) ((Z.preimage π).ι ≫ sP)
    (isGood_ι_of_isClosedSubspace D sP hP _ hc) (Z.fromPreimage π)
    (fromPreimage_comp_structureMorphism D sP sX π hπB Z) n
    (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
      hflat hrel).1
    (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
      hflat hrel).2
    (closedSubspaceModuleRestrict D sP hP L ⟨Z.preimage π, hc⟩)
    (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1
      (Z.preimage π) hc) L hL)
    (fun m => closedSubspaceChernRule D sP hP (Z.preimage π) hc m
      (canonicalFirstChernRule D sP hP L hL m))
    (fun m β' =>
      isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_closedSubspaceChernRule_sub
        D sP hP L hL ⟨Z.preimage π, hc⟩ m β') N d hd α
  have h2 := isRationallyEquivalentToZeroCanonical_add.{u + 1} D _ _ N h1 h
  rwa [sub_add_sub_cancel] at h2

end Closed

/-! ### Open subspaces of the base -/

section Open

variable (D : BaseSpaceDimensionSituation.{u})
    {X P U PU : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (sU : U ⟶ D.space) (hU : D.IsGood sU) (sPU : PU ⟶ D.space) (hPU : D.IsGood sPU)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjB : j ≫ sX = sU)
    {j' : PU ⟶ P} {πU : PU ⟶ U} (hj'B : j' ≫ sP = sPU) (hπUB : πU ≫ sU = sPU)
    (sq : IsPullback j' πU π j)

include hX hU hP hPU hj sq in
/-- The base change `j' : P_U → P` of an open immersion `j : U → X` is an open immersion. -/
theorem isOpenImmersion_baseChange_of_isPullback : IsOpenImmersion D.site D.base D.base_mem j' :=
  isOpenImmersion_of_isPullback D.site D.base D.base_mem
    (isPullback_homMk D.site D.base D.base_mem hU.1 hP.1 hX.1 hPU.1 sq.flip) hj

/-- Along an open immersion, the flat pullback of cycles is the restriction of cycles. -/
private theorem flatPullbackMap_eq_cycleGroupRestrict_of_isOpenImmersion
    (hf : IsFlat D.site D.base D.base_mem j)
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem j)
    (m : ℤ) (α : CycleGroup D sX m) :
    flatPullbackMap D sU hU sX hX j hjB 0 hf hr m m (by simp) α =
      cycleGroupRestrict D sX hX sU hU hj hjB m α :=
  Subtype.ext (flatPullbackMap_eq_cycleGroupRestrict D sX hX sU hU hj hjB m m (by simp) α)

include hj sq in
/-- `j'^*π^*α = π_U^*(α|_U)` for the base change `j' : P_U → P`, `π_U : P_U → U` of an open
immersion `j : U → X`. -/
theorem flatPullbackMap_flatPullbackMap_eq_cycleGroupRestrict (m m' : ℤ) (h : m + (n : ℤ) = m')
    (α : CycleGroup D sX m) :
    flatPullbackMap D sPU hPU sP hP j' hj'B 0
        (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sP hP sU hU sX hX hj'B hjB sq 0
          (isFlat_and_hasRelativeDimension_zero_of_isOpenImmersion' D sX hX hj).1
          (isFlat_and_hasRelativeDimension_zero_of_isOpenImmersion' D sX hX hj).2).2.1
        (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sP hP sU hU sX hX hj'B hjB sq 0
          (isFlat_and_hasRelativeDimension_zero_of_isOpenImmersion' D sX hX hj).1
          (isFlat_and_hasRelativeDimension_zero_of_isOpenImmersion' D sX hX hj).2).2.2
        m' m' (by simp) (flatPullbackMap D sP hP sX hX π hπB n hflat hrel m m' h α) =
      flatPullbackMap D sPU hPU sU hU πU hπUB n
        (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB hπB
          sq.flip n hflat hrel).2.1
        (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB hπB
          sq.flip n hflat hrel).2.2 m m' h (cycleGroupRestrict D sX hX sU hU hj hjB m α) := by
  subst h
  have hjf := isFlat_and_hasRelativeDimension_zero_of_isOpenImmersion' D sX hX hj
  have hj'f := isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sP hP sU hU sX hX hj'B hjB
    sq 0 hjf.1 hjf.2
  have hπUf := isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB hπB
    sq.flip n hflat hrel
  rw [← flatPullbackMap_eq_cycleGroupRestrict_of_isOpenImmersion D sX hX sU hU hj hjB hjf.1 hjf.2]
  refine Subtype.ext ?_
  have h1 := congrArg (fun φ => (φ α).1)
    (flatPullbackMap_comp D sPU hPU sP hP sX hX j' π hj'B hπB 0 n hj'f.2.1 hj'f.2.2 hflat hrel m
      (m + n) (by push_cast; ring))
  have h2 := congrArg (fun φ => (φ α).1)
    (flatPullbackMap_comp D sPU hPU sU hU sX hX πU j hπUB hjB n 0 hπUf.2.1 hπUf.2.2 hjf.1 hjf.2 m
      (m + n) (by push_cast; ring))
  simp only [AddMonoidHom.comp_apply] at h1 h2
  refine (Eq.trans ?_ h1.symm).trans ((flatPullbackMap_coe_congr D sPU hPU sX hX sq.w _ _
    (by omega) _ _ _ _ m (m + n) m (m + n) _ _ _ _ rfl).trans (Eq.trans h2 ?_))
  · exact coe_flatPullbackMap_congr D sP hP sPU hPU j' hj'B 0 hj'f.2.1 hj'f.2.2 (by simp) rfl _ _
      _ _ rfl
  · exact coe_flatPullbackMap_congr D sU hU sPU hPU πU hπUB n hπUf.2.1 hπUf.2.2 (by simp) rfl _ _
      _ _ rfl

variable (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

include hj sq in
/-- **The projective bundle formula along an open subspace `j : U → X` of the base**: the
restriction to `P_U` of `∑_i c₁(ℒ)^i ∩ π^*α_i` has the class of
`∑_i c₁(j'^*ℒ)^i ∩ π_U^*(α_i|_U)` (Stacks 0EQR and `j'^*π^* = π_U^*j^*`). -/
theorem chowClassCanonical_cycleGroupRestrict_bundleFormulaCycle (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (α : ∀ i, CycleGroup D sX (d i)) :
    chowClassCanonical.{u + 1} D sPU hPU N
        (cycleGroupRestrict D sP hP sPU hPU
          (isOpenImmersion_baseChange_of_isPullback D sX hX sP hP sU hU sPU hPU π hj sq) hj'B N
          (bundleFormulaCycle D sX hX sP hP π hπB n hflat hrel L hL N d hd α)) =
      chowClassCanonical.{u + 1} D sPU hPU N
        (bundleFormulaCycle D sU hU sPU hPU πU hπUB n
          (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB hπB
            sq.flip n hflat hrel).2.1
          (isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sU hU sP hP sX hX hπUB hπB
            sq.flip n hflat hrel).2.2
          ((modulePullback D.site D.base D.base_mem
            (ObjectProperty.homMk j' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨P, hP.1⟩)).obj L)
          (modulePullbackInvertible
            (ObjectProperty.homMk j' : (⟨PU, hPU.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨P, hP.1⟩) L hL) N d hd
          (fun i => cycleGroupRestrict D sX hX sU hU hj hjB (d i) (α i))) := by
  have hj' := isOpenImmersion_baseChange_of_isPullback D sX hX sP hP sU hU sPU hPU π hj sq
  have hjf := isFlat_and_hasRelativeDimension_zero_of_isOpenImmersion' D sX hX hj
  have hj'f := isFlat_and_hasRelativeDimension_of_isPullback D sPU hPU sP hP sU hU sX hX hj'B hjB
    sq 0 hjf.1 hjf.2
  rw [← flatPullbackMap_eq_cycleGroupRestrict_of_isOpenImmersion D sP hP sPU hPU hj' hj'B
    hj'f.2.1 hj'f.2.2 N]
  simp only [bundleFormulaCycle, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap_modulePullback
      D sPU hPU sP hP j' hj'B 0
      hj'f.2.1 hj'f.2.2 L hL i N N (by simp) (by simp),
    flatPullbackMap_flatPullbackMap_eq_cycleGroupRestrict D sX hX sP hP sU hU sPU hPU π hπB n hflat
      hrel hj hjB hj'B hπUB sq]

end Open

end AlgebraicGeometry.Space

end
