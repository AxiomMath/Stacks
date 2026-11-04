module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineBundleSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalLocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaVanishingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatProperTopPowerOpen

/-!
# Surjectivity of the projective bundle formula from a divisor with affine complement

Let `π : P → X` be proper and flat of relative dimension `m + 1`, `ℒ` invertible on `P` with a
section `s` whose zero scheme `D = Z(s)` is a relative effective Cartier divisor on `P/X`, and
let `j : U → P` be an open immersion onto the complement of `D` such that flat pullback along
`p = π ∘ j : U → X` is surjective up to rational equivalence (Stacks 0ERG; for the projective
completion `P = 𝐏(ℰ ⊕ 𝒪)` this is the vector bundle `U = 𝐕(ℰ)`). If the map of the projective
bundle formula is surjective for `(π_D, ℒ|_D)`, it is surjective for `(π, ℒ)`.

This is the inductive step of the proof of Stacks 02TX on the strata of a projective space,
arranged as a projective completion. Given `β ∈ CH_N(P)`: by Stacks 0ERG `β|_U = p^*α₀`; by the
localization sequence (Stacks 0EQ7) `β = π^*α₀ + i_*γ`; by the hypothesis on `D`,
`γ = ∑_i c₁(ℒ|_D)^i ∩ π_D^*α_{i+1}`; and
`i_*(c₁(ℒ|_D)^i ∩ π_D^*α) = c₁(ℒ)^i ∩ i_*π_D^*α = c₁(ℒ)^{i+1} ∩ π^*α` (Stacks 0ERE).

## Main results

* `AlgebraicGeometry.Space.chowClassCanonical_firstChernCapPowCycleMap_succ_flatPullbackMap`:
  `c₁(ℒ)^{i+1} ∩ π^*α = i_*(c₁(ℒ|_D)^i ∩ π_D^*α)` in `CH_N(P)`.
* `AlgebraicGeometry.Space.BundleFormulaSurjective.of_vanishingLocus`

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 0ERE](https://stacks.math.columbia.edu/tag/0ERE)
* [Stacks Project, Tag 0EQ7](https://stacks.math.columbia.edu/tag/0EQ7)
* [Stacks Project, Tag 0ERG](https://stacks.math.columbia.edu/tag/0ERG)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section Divisor

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (m : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension (m + 1) D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (s : L.sections)
    (hE : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨X, hX.1⟩) (vanishingLocus D sP hP L s))

/-- **`c₁(ℒ)^{i+1} ∩ π^*α = i_*(c₁(ℒ|_D)^i ∩ π_D^*α)`** in `CH_N(P)`, for the vanishing locus
`i : D = Z(s) → P` (Stacks 0ERE and the exact compatibility of the cap products along `i`). -/
theorem chowClassCanonical_firstChernCapPowCycleMap_succ_flatPullbackMap (i : ℕ) (a N : ℤ)
    (h : a + ((m + 1 : ℕ) : ℤ) = N + ((i + 1 : ℕ) : ℤ)) (h' : a + (m : ℤ) = N + (i : ℤ))
    (α : CycleGroup D sX a) :
    chowClassCanonical.{u + 1} D sP hP N
        (firstChernCapPowCycleMap D sP hP L hL (i + 1) N
          (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel a (N + (i + 1 : ℕ)) h α)) =
      chowClassCanonical.{u + 1} D sP hP N
        (closedSubspaceCyclePushforward D sP hP (vanishingLocus D sP hP L s) N
          (firstChernCapPowCycleMap D ((vanishingLocus D sP hP L s).1.ι ≫ sP)
            (isGood_vanishingLocus D sP hP L s)
            (closedSubspaceModuleRestrict D sP hP L (vanishingLocus D sP hP L s))
            (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1
              (vanishingLocus D sP hP L s).1 (vanishingLocus D sP hP L s).2) L hL) i N
            (flatPullbackMap D ((vanishingLocus D sP hP L s).1.ι ≫ sP)
              (isGood_vanishingLocus D sP hP L s) sX hX ((vanishingLocus D sP hP L s).1.ι ≫ π)
              (comp_structureMorphism_eq D ((vanishingLocus D sP hP L s).1.ι ≫ sP) sP sX
                (vanishingLocus D sP hP L s).1.ι π rfl hπB) m hE.2
              (hasRelativeDimension_ι_comp D sP hP sX hX π hπB m hrel _ hE) a (N + i) h' α))) := by
  set E := vanishingLocus D sP hP L s
  have hEg := isGood_vanishingLocus D sP hP L s
  have hEB := comp_structureMorphism_eq D (E.1.ι ≫ sP) sP sX E.1.ι π rfl hπB
  have hErel := hasRelativeDimension_ι_comp D sP hP sX hX π hπB m hrel _ hE
  have hLi : IsInvertibleSheaf D sP hP L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  set α' : CycleGroup D sX (a - 1 + 1) := cycleGroupCast D sX (by ring) α
  have h0ERE := chowClassCanonical_firstChernCapCycleMap_flatPullbackMap.{u + 1, u} D sP hP sX hX π
    hπB m hflat hrel L hLi s hE (a - 1) α'
  set y := flatPullbackMap D (E.1.ι ≫ sP) hEg sX hX (E.1.ι ≫ π) hEB m hE.2 hErel a (N + i) h' α
  set α₀ : CycleGroup D sP (N + (i : ℤ) + ((1 : ℕ) : ℤ)) := cycleGroupCast D sP
    (by push_cast at h ⊢; omega)
    (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel a (N + (i + 1 : ℕ)) h α)
  have hcomp := firstChernCapPowCycleMap_firstChernCapPowCycleMap D sP hP L hL i 1 N α₀
  have hcast : firstChernCapPowCycleMap D sP hP L hL (i + 1) N
      (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel a (N + (i + 1 : ℕ)) h α) =
      firstChernCapPowCycleMap D sP hP L hL (i + 1) N
        (cycleGroupCast D sP (by push_cast; ring) α₀) :=
    congrArg _ (Subtype.ext rfl)
  have hpow : chowClassCanonical.{u + 1} D sP hP N
      (firstChernCapPowCycleMap D sP hP L hL (i + 1) N
        (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel a (N + (i + 1 : ℕ)) h α)) =
      chowClassCanonical.{u + 1} D sP hP N
        (firstChernCapPowCycleMap D sP hP L hL i N
          (cycleGroupClosedPushforward D hP.1 E.2.1 (D.isDecentSpace_of_isGood sP hP) E.2.2 sP
            hP.2.2 (E.1.ι ≫ sP) rfl (N + i) y)) := by
    rw [hcast, ← hcomp, ← firstChernCapPowChowMap_chowClassCanonical D sP hP L hL i N,
      ← firstChernCapPowChowMap_chowClassCanonical D sP hP L hL i N]
    congr 1
    have h1 := chowClassCanonical_eq_of_coe_eq D sP hP (show a - 1 + m + 1 = N + i by omega)
      (firstChernCapCycleMap D sP hP (a - 1 + m + 1)
        (canonicalFirstChernRule D sP hP L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hLi) (a - 1 + m + 1))
        (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel (a - 1 + 1) (a - 1 + m + 1 + 1)
          (by push_cast; ring) α'))
      (firstChernCapPowCycleMap D sP hP L hL 1 (N + i) α₀)
      (by
        simp only [firstChernCapPowCycleMap, AddMonoidHom.coe_comp, Function.comp_apply]
        refine coe_firstChernCapCycleMap_canonicalFirstChernRule_congr D sP hP L hL (by omega) _ _
          ?_
        simp only [cycleGroupCast_coe]
        exact coe_flatPullbackMap_congr D sX hX sP hP π hπB (m + 1) hflat hrel (by ring)
          (by push_cast at h ⊢; omega) (by push_cast; ring) h α' α rfl)
    have h2 := chowClassCanonical_eq_of_coe_eq D sP hP (show a - 1 + m + 1 = N + i by omega)
      (closedSubspaceCyclePushforward D sP hP E (a - 1 + m + 1)
        (flatPullbackMap D (E.1.ι ≫ sP) hEg sX hX (E.1.ι ≫ π) hEB m hE.2 hErel (a - 1 + 1)
          (a - 1 + m + 1) (by ring) α'))
      (cycleGroupClosedPushforward D hP.1 E.2.1 (D.isDecentSpace_of_isGood sP hP) E.2.2 sP
        hP.2.2 (E.1.ι ≫ sP) rfl (N + i) y)
      (coe_cycleGroupClosedPushforward_congr D sP hP E.1 E.2 (by omega) _ _
        (coe_flatPullbackMap_congr D sX hX (E.1.ι ≫ sP) hEg (E.1.ι ≫ π) hEB m hE.2 hErel
          (by ring) (by omega) _ _ _ _ rfl))
    rw [← h1, ← h2, h0ERE]
  have hpush := cycleGroupClosedPushforward_firstChernCapPowCycleMapOfRule D sP hP E.1 E.2
    (fun m => canonicalFirstChernRule D sP hP L hL m) i N y
  rw [hpow, ← firstChernCapPowCycleMapOfRule_canonicalFirstChernRule D sP hP L hL i, ← hpush,
    chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  unfold RationallyEquivalentCanonical
  rw [← map_sub]
  refine (isRationallyEquivalentToZeroWithinCanonical_cycleGroupClosedPushforward D sP hP E.1 E.2
    N ?_).isRationallyEquivalentToZeroCanonical
  exact isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMapOfRule_sub D _ _
    (closedSubspaceModuleRestrict D sP hP L E)
    (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1 E.1 E.2) L hL) _
    (fun m β' =>
      isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_closedSubspaceChernRule_sub
        D sP hP L hL E m β') i N y

/-- Canonical rational equivalence to zero within a carrier is transported along the
identifications of cycle groups of equal degrees. -/
theorem IsCanonicallyRationallyEquivalentToZeroWithin.cycleGroupCast' {a b : ℤ} (h : a = b)
    {α : CycleGroup D sP a} {T : Set (points D.site D.base D.base_mem P)}
    (hα : IsCanonicallyRationallyEquivalentToZeroWithin.{u, u} D sP hP a α T) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, u} D sP hP b (cycleGroupCast D sP h α) T := by
  subst h
  exact hα

variable {U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sU : U ⟶ D.space)
    (hU : D.IsGood sU) {j : U ⟶ P} (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (hjB : j ≫ sP = sU)
    (hcompl : Set.range (pointsMap D.site D.base D.base_mem _ (vanishingLocus D sP hP L s).1.ι) =
      (Set.range (pointsMap D.site D.base D.base_mem U j))ᶜ)
    (q : U ⟶ X) (hqB : q ≫ sX = sU) (hjq : j ≫ π = q)
    (hqflat : IsFlat D.site D.base D.base_mem q)
    (hqrel : HasRelativeDimension (m + 1) D.site D.base D.base_mem q)

include hjq in
/-- The restriction to `U` of `π^*α` is `q^*α`. -/
theorem coe_cycleGroupRestrict_flatPullbackMap (a N : ℤ) (h : a + ((m + 1 : ℕ) : ℤ) = N)
    (α : CycleGroup D sX a) :
    (cycleGroupRestrict D sP hP sU hU hj hjB N
        (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel a N h α)).1 =
      (flatPullbackMap D sU hU sX hX q hqB (m + 1) hqflat hqrel a N h α).1 := by
  have hj0 := isFlat_and_hasRelativeDimension_zero_of_isOpenImmersion' D sP hP hj
  rw [← flatPullbackMap_eq_cycleGroupRestrict D sP hP sU hU hj hjB N N (by simp)]
  have h1 := congrArg (fun ψ => (ψ α).1)
    (flatPullbackMap_comp D sU hU sP hP sX hX j π hjB hπB 0 (m + 1) hj0.1 hj0.2 hflat hrel a N
      (by push_cast at h ⊢; omega))
  refine (Eq.trans ?_ h1.symm).trans (flatPullbackMap_coe_congr D sU hU sX hX hjq _ _
    (by omega) _ _ _ _ a N a N _ _ _ _ rfl)
  exact coe_flatPullbackMap_congr D sP hP sU hU j hjB 0 hj0.1 hj0.2 h.symm rfl
    (by simp) (by push_cast at h ⊢; omega) _ _
    (coe_flatPullbackMap_congr D sX hX sP hP π hπB (m + 1) hflat hrel rfl h.symm h rfl α α rfl)

include hj hjB hcompl hjq in
/-- **The surjectivity half of Stacks 0ERV from the one on a relative effective Cartier divisor
`Z(s)` whose complement is an affine-space fibration over the base.** -/
theorem BundleFormulaSurjective.of_vanishingLocus
    (hsurjq : ∀ k : ℤ, IsFlatPullbackSurjective D sU hU sX hX q hqB (m + 1) hqflat hqrel k)
    (hD : BundleFormulaSurjective D sX hX ((vanishingLocus D sP hP L s).1.ι ≫ sP)
      (isGood_vanishingLocus D sP hP L s) ((vanishingLocus D sP hP L s).1.ι ≫ π)
      (comp_structureMorphism_eq D ((vanishingLocus D sP hP L s).1.ι ≫ sP) sP sX
        (vanishingLocus D sP hP L s).1.ι π rfl hπB) m hE.2
      (hasRelativeDimension_ι_comp D sP hP sX hX π hπB m hrel _ hE)
      (closedSubspaceModuleRestrict D sP hP L (vanishingLocus D sP hP L s))
      (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1
        (vanishingLocus D sP hP L s).1 (vanishingLocus D sP hP L s).2) L hL)) :
    BundleFormulaSurjective D sX hX sP hP π hπB (m + 1) hflat hrel L hL := by
  intro N d hd b
  set E := vanishingLocus D sP hP L s
  have hEg := isGood_vanishingLocus D sP hP L s
  have hιp : IsProper D.site D.base D.base_mem E.1.ι :=
    isProper_of_isClosedImmersion D.site D.base D.base_mem E.2.1 hP.1 _ E.2.2
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk_surjective b
  have hd0 : d 0 + ((m + 1 : ℕ) : ℤ) = N := by have := hd 0; simpa using this
  have hd' (i : Fin (m + 1)) : d i.succ + m = N + i := by
    have := hd i.succ; simp at this; omega
  -- the degree-zero part, from the complement
  obtain ⟨a₀, ha₀⟩ := hsurjq (d 0) (cycleGroupCast D sU hd0.symm
    (cycleGroupRestrict D sP hP sU hU hj hjB N β))
  set A := flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel (d 0) N hd0 a₀
  have hloc : IsCanonicallyRationallyEquivalentToZeroWithin.{u, u} D sU hU N
      (cycleGroupRestrict D sP hP sU hU hj hjB N A - cycleGroupRestrict D sP hP sU hU hj hjB N β)
      Set.univ := by
    have h := IsCanonicallyRationallyEquivalentToZeroWithin.cycleGroupCast' D sU hU hd0 ha₀
    convert h using 1
    refine Subtype.ext ?_
    rw [map_sub]
    change (cycleGroupRestrict D sP hP sU hU hj hjB N A).1 -
        (cycleGroupRestrict D sP hP sU hU hj hjB N β).1 = _ - _
    rw [coe_cycleGroupRestrict_flatPullbackMap D sX hX sP hP π hπB m hflat hrel sU hU hj hjB q hqB
      hjq hqflat hqrel (d 0) N hd0 a₀]
    rfl
  obtain ⟨γ, hγ⟩ :=
    exists_isCanonicallyRationallyEquivalentToZeroWithin_sub_add_cycleGroupClosedPushforward
      D sP hP (E.1.ι ≫ sP) hEg sU hU E.2.2 rfl hj hjB hcompl N A β hloc
  -- the higher parts, from the divisor
  obtain ⟨b', hb'⟩ := hD N (fun i => d i.succ)
    hd'
    (chowClassCanonical.{u + 1} D (E.1.ι ≫ sP) hEg N (-γ))
  choose βs hβs using fun i => QuotientAddGroup.mk_surjective (b' i)
  have hb'eq : b' = fun i => chowClassCanonical.{u + 1} D sX hX (d i.succ) (βs i) :=
    funext fun i => (hβs i).symm
  subst hb'eq
  refine ⟨Fin.cons (chowClassCanonical.{u + 1} D sX hX (d 0) a₀)
    (fun i => chowClassCanonical.{u + 1} D sX hX (d i.succ) (βs i)), ?_⟩
  set ιCH := chowGroupCanonicalProperPushforward.{u + 1} D (E.1.ι ≫ sP) hEg sP hP (p := E.1.ι) rfl
    hιp N
  have hsum : ∑ i : Fin (m + 1), bundleFormulaCap D sP hP L hL ((i.succ : Fin (m + 2)) : ℕ)
      (N + ((i.succ : Fin (m + 2)) : ℕ)) N rfl
      (bundleFormulaPull D sX hX sP hP π hπB (m + 1) hflat hrel (d i.succ)
        (N + ((i.succ : Fin (m + 2)) : ℕ)) (hd i.succ)
        (chowClassCanonical.{u + 1} D sX hX (d i.succ) (βs i))) =
      ιCH (chowClassCanonical.{u + 1} D (E.1.ι ≫ sP) hEg N (-γ)) := by
    rw [← hb']
    simp only [bundleFormulaMap, ProjectiveBundleRelation.bundleSum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change chowClassCanonical.{u + 1} D sP hP N _ = ιCH (chowClassCanonical.{u + 1} D _ hEg N _)
    rw [chowGroupCanonicalProperPushforward_chowClassCanonical,
      properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sP hP E.1 E.2]
    have hc := chowClassCanonical_firstChernCapPowCycleMap_succ_flatPullbackMap D sX hX sP hP π hπB
      m hflat hrel L hL s hE i (d i.succ) N (hd i.succ)
      (hd' i) (βs i)
    exact (congrArg (chowClassCanonical.{u + 1} D sP hP N)
      (congrArg _ (Subtype.ext rfl))).trans
      (hc.trans (congrArg (chowClassCanonical.{u + 1} D sP hP N)
        (Subtype.ext (coe_cycleGroupClosedPushforward_congr D sP hP E.1 E.2 rfl _ _
          (congrArg Subtype.val (congrArg _ (Subtype.ext rfl)))))))
  simp only [bundleFormulaMap, ProjectiveBundleRelation.bundleSum_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hsum]
  have h0 : bundleFormulaCap D sP hP L hL ((0 : Fin (m + 2)) : ℕ) (N + ((0 : Fin (m + 2)) : ℕ))
      N rfl (bundleFormulaPull D sX hX sP hP π hπB (m + 1) hflat hrel (d 0)
        (N + ((0 : Fin (m + 2)) : ℕ)) (hd 0) (chowClassCanonical.{u + 1} D sX hX (d 0) a₀)) =
      chowClassCanonical.{u + 1} D sP hP N A :=
    congrArg (chowClassCanonical.{u + 1} D sP hP N) (Subtype.ext
      (coe_flatPullbackMap_congr D sX hX sP hP π hπB (m + 1) hflat hrel rfl (by simp) (hd 0) hd0
        a₀ a₀ rfl))
  rw [h0, chowGroupCanonicalProperPushforward_chowClassCanonical,
    properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sP hP E.1 E.2, map_neg, map_neg,
    ← sub_eq_add_neg, sub_eq_iff_eq_add]
  change chowClassCanonical.{u + 1} D sP hP N A = chowClassCanonical.{u + 1} D sP hP N β +
    chowClassCanonical.{u + 1} D sP hP N (cycleGroupClosedPushforward D hP.1 E.2.1
      (D.isDecentSpace_of_isGood sP hP) E.2.2 sP hP.2.2 (E.1.ι ≫ sP) rfl N γ)
  rw [← map_add, chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  exact hγ.isRationallyEquivalentToZeroWithinCanonical.uliftIndex.{u + 1, u}
    |>.isRationallyEquivalentToZeroCanonical

end Divisor

end AlgebraicGeometry.Space

end
