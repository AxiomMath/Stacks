module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaVanishingLocusSurjective

/-!
# Injectivity of flat pullback to the complement of a divisor in a projective bundle

Let `π : P → X` be proper and flat of relative dimension `m + 1`, `ℒ` invertible on `P` with a
section `s` whose zero scheme `D = Z(s)` is a relative effective Cartier divisor on `P/X`, and
let `j : U → P` be an open immersion onto the complement of `D`, with `q = π ∘ j : U → X`. If the
map of the projective bundle formula is surjective for `(π_D, ℒ|_D)` and injective for `(π, ℒ)`,
then the flat pullback `q^* : CH_k(X) → CH_{k+m+1}(U)` is injective.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `IsRationallyEquivalentToZeroCanonical.isCanonicallyRationallyEquivalentToZeroWithin_univ`:
  a cycle rationally equivalent to zero at the canonical embeddings is a locally finite sum of
  canonical principal divisors.
* `sum_bundleFormulaCap_succ_bundleFormulaPull_eq_pushforward`: the pushforward along `i : D → P`
  of the bundle formula map of `(π_D, ℒ|_D)` is the sum of the summands of index `≥ 1` of the one
  of `(π, ℒ)`.
* `injective_flatPullbackChowMapCanonical_of_vanishingLocus`: the injectivity of `q^*`.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0ERE](https://stacks.math.columbia.edu/tag/0ERE)
* [Stacks Project, Tag 0EQ7](https://stacks.math.columbia.edu/tag/0EQ7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Canonical

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ}

/-- **A cycle rationally equivalent to zero is a locally finite sum of canonical principal
divisors.** -/
theorem IsRationallyEquivalentToZeroCanonical.isCanonicallyRationallyEquivalentToZeroWithin_univ
    {α : CycleGroup D sX k} (h : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k α Set.univ := by
  obtain ⟨J, W, hWfin, c, hdim, hprin, rfl⟩ := h
  refine ⟨J, W, hWfin, c, fun _ => Set.subset_univ _, fun j => ?_, rfl⟩
  have hk : deltaDimensionClosed D ((W j).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (W j))
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX (W j), hdim j]
  obtain ⟨f, ⟨g, rfl⟩, heq⟩ := hprin j
  exact ⟨hk, g, Subtype.ext heq⟩

end Canonical

section Divisor

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (m : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension (m + 1) D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (s : L.sections)
    (hE : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk π : (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨X, hX.1⟩) (vanishingLocus D sP hP L s))

/-- The degree bookkeeping for the summands of index `i + 1` in the projective bundle formula. -/
private theorem degree_succ_eq {m : ℕ} {N : ℤ} {d : Fin (m + 2) → ℤ}
    (hd : ∀ i, d i + ((m + 1 : ℕ) : ℤ) = N + (i : ℕ)) (i : Fin (m + 1)) :
    d i.succ + (m : ℤ) = N + (i : ℕ) := by
  have := hd i.succ
  simp only [Fin.val_succ] at this
  push_cast at this
  omega

/-- **The pushforward along `i : D = Z(s) → P` of the map of the projective bundle formula of
`(π_D, ℒ|_D)`** is the sum `∑_i c₁(ℒ)^{i+1} ∩ π^*β_i` of the summands of index `≥ 1` of the map
for `(π, ℒ)` (Stacks 0ERE). -/
theorem sum_bundleFormulaCap_succ_bundleFormulaPull_eq_pushforward (N : ℤ)
    (d : Fin (m + 2) → ℤ) (hd : ∀ i, d i + ((m + 1 : ℕ) : ℤ) = N + (i : ℕ))
    (b : ∀ i : Fin (m + 1), chowGroupCanonical.{u + 1} D sX hX (d i.succ)) :
    ∑ i : Fin (m + 1), bundleFormulaCap D sP hP L hL ((i.succ : Fin (m + 2)) : ℕ)
        (N + ((i.succ : Fin (m + 2)) : ℕ)) N rfl
        (bundleFormulaPull D sX hX sP hP π hπB (m + 1) hflat hrel (d i.succ)
          (N + ((i.succ : Fin (m + 2)) : ℕ)) (hd i.succ) (b i)) =
      chowGroupCanonicalProperPushforward.{u + 1} D ((vanishingLocus D sP hP L s).1.ι ≫ sP)
        (isGood_vanishingLocus D sP hP L s) sP hP (p := (vanishingLocus D sP hP L s).1.ι) rfl
        (isProper_of_isClosedImmersion D.site D.base D.base_mem
          (vanishingLocus D sP hP L s).2.1 hP.1 _ (vanishingLocus D sP hP L s).2.2) N
        (bundleFormulaMap D sX hX ((vanishingLocus D sP hP L s).1.ι ≫ sP)
          (isGood_vanishingLocus D sP hP L s) ((vanishingLocus D sP hP L s).1.ι ≫ π)
          (comp_structureMorphism_eq D ((vanishingLocus D sP hP L s).1.ι ≫ sP) sP sX
            (vanishingLocus D sP hP L s).1.ι π rfl hπB) m hE.2
          (hasRelativeDimension_ι_comp D sP hP sX hX π hπB m hrel _ hE)
          (closedSubspaceModuleRestrict D sP hP L (vanishingLocus D sP hP L s))
          (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1
            (vanishingLocus D sP hP L s).1 (vanishingLocus D sP hP L s).2) L hL) N
          (fun i => d i.succ)
          (fun i => by
            have := hd i.succ; simp only [Fin.val_succ] at this; push_cast at this ⊢; omega)
          b) := by
  set E := vanishingLocus D sP hP L s
  have hEg := isGood_vanishingLocus D sP hP L s
  choose βs hβs using fun i => QuotientAddGroup.mk_surjective (b i)
  have hb : b = fun i => chowClassCanonical.{u + 1} D sX hX (d i.succ) (βs i) :=
    funext fun i => (hβs i).symm
  subst hb
  simp only [bundleFormulaMap, ProjectiveBundleRelation.bundleSum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show chowClassCanonical.{u + 1} D sP hP N _ =
    chowGroupCanonicalProperPushforward.{u + 1} D _ hEg sP hP rfl _ N
      (chowClassCanonical.{u + 1} D _ hEg N _)
  rw [chowGroupCanonicalProperPushforward_chowClassCanonical,
    properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sP hP E.1 E.2]
  have hc := chowClassCanonical_firstChernCapPowCycleMap_succ_flatPullbackMap D sX hX sP hP π hπB
    m hflat hrel L hL s hE i (d i.succ) N (hd i.succ)
    (degree_succ_eq hd i) (βs i)
  exact (congrArg (chowClassCanonical.{u + 1} D sP hP N)
    (congrArg _ (Subtype.ext rfl))).trans (hc.trans (congrArg (chowClassCanonical.{u + 1} D sP hP N)
      (Subtype.ext (coe_cycleGroupClosedPushforward_congr D sP hP E.1 E.2 rfl _ _
        (congrArg Subtype.val (congrArg _ (Subtype.ext rfl)))))))

variable {U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sU : U ⟶ D.space)
    (hU : D.IsGood sU) {j : U ⟶ P} (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (hjB : j ≫ sP = sU)
    (hcompl : Set.range (pointsMap D.site D.base D.base_mem _ (vanishingLocus D sP hP L s).1.ι) =
      (Set.range (pointsMap D.site D.base D.base_mem U j))ᶜ)
    (q : U ⟶ X) (hqB : q ≫ sX = sU) (hjq : j ≫ π = q)
    (hqflat : IsFlat D.site D.base D.base_mem q)
    (hqrel : HasRelativeDimension (m + 1) D.site D.base D.base_mem q)

include hj hjB hcompl hjq in
/-- **Flat pullback to the complement of the divisor is injective** (the injectivity argument of
Stacks 0ERW). If the map of the projective bundle formula is surjective for `(π_D, ℒ|_D)` and
injective for `(π, ℒ)` in every degree, then `q^* : CH_k(X) → CH_{k+m+1}(U)` is injective. -/
theorem injective_flatPullbackChowMapCanonical_of_vanishingLocus
    (hD : BundleFormulaSurjective D sX hX ((vanishingLocus D sP hP L s).1.ι ≫ sP)
      (isGood_vanishingLocus D sP hP L s) ((vanishingLocus D sP hP L s).1.ι ≫ π)
      (comp_structureMorphism_eq D ((vanishingLocus D sP hP L s).1.ι ≫ sP) sP sX
        (vanishingLocus D sP hP L s).1.ι π rfl hπB) m hE.2
      (hasRelativeDimension_ι_comp D sP hP sX hX π hπB m hrel _ hE)
      (closedSubspaceModuleRestrict D sP hP L (vanishingLocus D sP hP L s))
      (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1
        (vanishingLocus D sP hP L s).1 (vanishingLocus D sP hP L s).2) L hL))
    (hinj : ∀ (N : ℤ) (d : Fin (m + 2) → ℤ) (hd : ∀ i, d i + ((m + 1 : ℕ) : ℤ) = N + (i : ℕ)),
      Function.Injective (bundleFormulaMap D sX hX sP hP π hπB (m + 1) hflat hrel L hL N d hd))
    (k : ℤ) :
    Function.Injective (flatPullbackChowMapCanonical.{u + 1} D sU hU sX hX q hqB (m + 1) hqflat
      hqrel k (k + ((m + 1 : ℕ) : ℤ)) rfl) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  set E := vanishingLocus D sP hP L s
  have hEg := isGood_vanishingLocus D sP hP L s
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective a
  set N : ℤ := k + ((m + 1 : ℕ) : ℤ) with hN
  have hqα : IsRationallyEquivalentToZeroCanonical.{u + 1} D sU hU N
      (flatPullbackMap D sU hU sX hX q hqB (m + 1) hqflat hqrel k N rfl α) :=
    (chowClassCanonical_eq_zero_iff.{u + 1} D sU hU N _).1 ha
  set A := flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel k N rfl α
  have hloc : IsCanonicallyRationallyEquivalentToZeroWithin.{u, u + 1} D sU hU N
      (cycleGroupRestrict D sP hP sU hU hj hjB N A - cycleGroupRestrict D sP hP sU hU hj hjB N 0)
      Set.univ := by
    convert hqα.isCanonicallyRationallyEquivalentToZeroWithin_univ using 1
    refine Subtype.ext ?_
    rw [map_zero, sub_zero]
    exact coe_cycleGroupRestrict_flatPullbackMap D sX hX sP hP π hπB m hflat hrel sU hU hj hjB q
      hqB hjq hqflat hqrel k N rfl α
  obtain ⟨γ, hγ⟩ :=
    exists_isCanonicallyRationallyEquivalentToZeroWithin_sub_add_cycleGroupClosedPushforward.{u,
      u + 1}
      D sP hP (E.1.ι ≫ sP) hEg sU hU E.2.2 rfl hj hjB hcompl N A 0 hloc
  set d : Fin (m + 2) → ℤ := fun i => k + (i : ℕ)
  have hd : ∀ i, d i + ((m + 1 : ℕ) : ℤ) = N + (i : ℕ) := fun i => by
    simp only [d, hN]
    ring
  obtain ⟨b, hb⟩ := hD N (fun i => d i.succ)
    (fun i => degree_succ_eq hd i)
    (chowClassCanonical.{u + 1} D (E.1.ι ≫ sP) hEg N γ)
  have hsum := sum_bundleFormulaCap_succ_bundleFormulaPull_eq_pushforward D sX hX sP hP π hπB m
    hflat hrel L hL s hE N d hd b
  rw [hb, chowGroupCanonicalProperPushforward_chowClassCanonical,
    properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sP hP E.1 E.2] at hsum
  have hd0 : k = d 0 := by simp [d]
  have h0 : bundleFormulaCap D sP hP L hL ((0 : Fin (m + 2)) : ℕ) (N + ((0 : Fin (m + 2)) : ℕ)) N
      rfl (bundleFormulaPull D sX hX sP hP π hπB (m + 1) hflat hrel (d 0)
        (N + ((0 : Fin (m + 2)) : ℕ)) (hd 0)
        (chowGroupCanonicalCast.{u + 1} D sX hX hd0 (chowClassCanonical.{u + 1} D sX hX k α))) =
      chowClassCanonical.{u + 1} D sP hP N A := by
    rw [chowGroupCanonicalCast_chowClassCanonical]
    exact congrArg (chowClassCanonical.{u + 1} D sP hP N) (Subtype.ext
      (coe_flatPullbackMap_congr D sX hX sP hP π hπB (m + 1) hflat hrel hd0.symm (by simp [hN])
        (hd 0) rfl _ α rfl))
  have hA : chowClassCanonical.{u + 1} D sP hP N A =
      chowClassCanonical.{u + 1} D sP hP N (cycleGroupClosedPushforward D hP.1 E.2.1
        (D.isDecentSpace_of_isGood sP hP) E.2.2 sP hP.2.2 (E.1.ι ≫ sP) rfl N γ) := by
    rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
    have h := (hγ.isRationallyEquivalentToZeroWithinCanonical).isRationallyEquivalentToZeroCanonical
    rwa [zero_add] at h
  have hzero := hinj N d hd (a₁ := Fin.cons
      (chowGroupCanonicalCast.{u + 1} D sX hX hd0 (chowClassCanonical.{u + 1} D sX hX k α))
      fun i => -b i) (a₂ := 0) (by
    rw [map_zero]
    simp only [bundleFormulaMap, ProjectiveBundleRelation.bundleSum_apply]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, map_neg, Finset.sum_neg_distrib]
    rw [h0, hsum, hA, add_neg_cancel])
  have h0α := congrFun hzero 0
  simp only [Fin.cons_zero, Pi.zero_apply, chowGroupCanonicalCast_chowClassCanonical,
    chowClassCanonical_eq_zero_iff] at h0α
  exact (chowClassCanonical_eq_zero_iff.{u + 1} D sX hX k α).2
    (isRationallyEquivalentToZeroCanonical_cycleGroupCast D sX hX hd0.symm h0α)

end Divisor

end AlgebraicGeometry.Space

end
