module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatProperTopPowerReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RelativeEffectiveCartierFlatPullback

/-!
# The projective bundle formula from a relative effective Cartier divisor

Let `π : P → X` be proper and flat of relative dimension `m + 1`, `ℒ` invertible on `P` with a
global section `s` whose zero scheme `D = Z(s)` is a relative effective Cartier divisor on `P/X`
(Stacks 0EPP), so that `π_D : D → X` is flat of relative dimension `m`. For the projective
completion `P = 𝐏(ℰ ⊕ 𝒪)` and the section `s` of `𝒪_P(1)` given by the summand `𝒪`, `D` is the
hyperplane at infinity `𝐏(ℰ)`.

By Stacks 0ERE, `c₁(ℒ) ∩ π^*α = i_*(π_D^*α)`. This file deduces the top power of Stacks 0ERU for
`(π, ℒ)` from the one for `(π_D, ℒ|_D)`: `c₁(ℒ)^{m+1} ∩ π^*α = c₁(ℒ)^m ∩ i_*π_D^*α
= i_*(c₁(ℒ|_D)^m ∩ π_D^*α)`, and `π_* i_* = π_{D,*}`.

## Main results

* `AlgebraicGeometry.Space.BundleTopPowerIdentity.of_vanishingLocus`

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0ERE](https://stacks.math.columbia.edu/tag/0ERE)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section Congr

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- The cap product at the canonical rule only depends on the underlying cycle and the degree. -/
theorem coe_firstChernCapCycleMap_canonicalFirstChernRule_congr
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    {a b : ℤ} (h : a = b) (β : CycleGroup D sX (a + 1)) (β' : CycleGroup D sX (b + 1))
    (hβ : β.1 = β'.1) :
    (firstChernCapCycleMap D sX hX a (canonicalFirstChernRule D sX hX L hL a) β).1 =
      (firstChernCapCycleMap D sX hX b (canonicalFirstChernRule D sX hX L hL b) β').1 := by
  subst h
  rw [Subtype.ext hβ]

/-- Pushforward along a closed subspace only depends on the underlying cycle. -/
theorem coe_cycleGroupClosedPushforward_congr (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) {a b : ℤ} (h : a = b)
    (β : CycleGroup D (Y.ι ≫ sX) a) (β' : CycleGroup D (Y.ι ≫ sX) b) (hβ : β.1 = β'.1) :
    (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl a β).1 =
      (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl b β').1 := by
  subst h
  rw [Subtype.ext hβ]

/-- The class map commutes with the identifications of cycle groups of equal degrees. -/
theorem chowClassCanonical_eq_of_coe_eq {a b : ℤ} (h : a = b) (x : CycleGroup D sX a)
    (y : CycleGroup D sX b) (hxy : x.1 = y.1) :
    chowGroupCanonicalCast.{u + 1} D sX hX h (chowClassCanonical.{u + 1} D sX hX a x) =
      chowClassCanonical.{u + 1} D sX hX b y := by
  subst h
  rw [Subtype.ext hxy]
  rfl

end Congr

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

include hX hp in
/-- The restriction of `π` to the vanishing locus is proper. -/
theorem isProper_vanishingLocus_ι_comp :
    IsProper D.site D.base D.base_mem ((vanishingLocus D sP hP L s).1.ι ≫ π) :=
  isProper_comp D.site D.base D.base_mem (vanishingLocus D sP hP L s).2.1 hP.1 hX.1 _ π
    (isProper_of_isClosedImmersion D.site D.base D.base_mem (vanishingLocus D sP hP L s).2.1 hP.1
      _ (vanishingLocus D sP hP L s).2.2) hp

/-- **The top power of Stacks 0ERU from the one on a relative effective Cartier divisor `Z(s)`.**
If `π_{D,*}(c₁(ℒ|_D)^m ∩ π_D^*α) = α` in the Chow group for the vanishing locus `D = Z(s)`, then
`π_*(c₁(ℒ)^{m+1} ∩ π^*α) = α`. -/
theorem BundleTopPowerIdentity.of_vanishingLocus
    (hD : BundleTopPowerIdentity D sX hX ((vanishingLocus D sP hP L s).1.ι ≫ sP)
      (isGood_vanishingLocus D sP hP L s) ((vanishingLocus D sP hP L s).1.ι ≫ π)
      (comp_structureMorphism_eq D ((vanishingLocus D sP hP L s).1.ι ≫ sP) sP sX
        (vanishingLocus D sP hP L s).1.ι π rfl hπB) m hE.2
      (hasRelativeDimension_ι_comp D sP hP sX hX π hπB m hrel _ hE)
      (isProper_vanishingLocus_ι_comp D sX hX sP hP π hp L s)
      (closedSubspaceModuleRestrict D sP hP L (vanishingLocus D sP hP L s))
      (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1
        (vanishingLocus D sP hP L s).1 (vanishingLocus D sP hP L s).2) L hL)) :
    BundleTopPowerIdentity D sX hX sP hP π hπB (m + 1) hflat hrel hp L hL := by
  intro k α
  set E := vanishingLocus D sP hP L s
  have hEg := isGood_vanishingLocus D sP hP L s
  have hEB := comp_structureMorphism_eq D ((vanishingLocus D sP hP L s).1.ι ≫ sP) sP sX
    (vanishingLocus D sP hP L s).1.ι π rfl hπB
  have hErel := hasRelativeDimension_ι_comp D sP hP sX hX π hπB m hrel _ hE
  have hEp := isProper_vanishingLocus_ι_comp D sX hX sP hP π hp L s
  have hιp : IsProper D.site D.base D.base_mem E.1.ι :=
    isProper_of_isClosedImmersion D.site D.base D.base_mem E.2.1 hP.1 _ E.2.2
  have hLi : IsInvertibleSheaf D sP hP L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  -- the degree `k = (k - 1) + 1` of Stacks 0ERE
  set α' : CycleGroup D sX (k - 1 + 1) := cycleGroupCast D sX (by ring) α
  -- Stacks 0ERE: `c₁(ℒ) ∩ π^*α = i_*(π_D^*α)`
  have h0ERE := chowClassCanonical_firstChernCapCycleMap_flatPullbackMap.{u + 1, u} D sP hP sX hX
    π hπB m hflat hrel L hLi s hE (k - 1) α'
  -- the cycle `π_D^*α` in degree `k + m`
  set y := flatPullbackMap D (E.1.ι ≫ sP) hEg sX hX (E.1.ι ≫ π) hEB m hE.2 hErel k (k + m) rfl α
  -- the cap power on `P` applied to `i_* y`
  have hpow : chowClassCanonical.{u + 1} D sP hP k
      (firstChernCapPowCycleMap D sP hP L hL (m + 1) k
        (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel k (k + (m + 1 : ℕ)) rfl α)) =
      chowClassCanonical.{u + 1} D sP hP k
        (firstChernCapPowCycleMap D sP hP L hL m k
          (cycleGroupClosedPushforward D hP.1 E.2.1 (D.isDecentSpace_of_isGood sP hP) E.2.2 sP
            hP.2.2 (E.1.ι ≫ sP) rfl (k + m) y)) := by
    set α₀ : CycleGroup D sP (k + (m : ℤ) + ((1 : ℕ) : ℤ)) := cycleGroupCast D sP
      (by push_cast; ring)
      (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel k (k + (m + 1 : ℕ)) rfl α)
    have hcomp := firstChernCapPowCycleMap_firstChernCapPowCycleMap D sP hP L hL m 1 k α₀
    have hcast : firstChernCapPowCycleMap D sP hP L hL (m + 1) k
        (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel k (k + (m + 1 : ℕ)) rfl α) =
        firstChernCapPowCycleMap D sP hP L hL (m + 1) k
          (cycleGroupCast D sP (by push_cast; ring) α₀) :=
      congrArg _ (Subtype.ext rfl)
    rw [hcast, ← hcomp, ← firstChernCapPowChowMap_chowClassCanonical D sP hP L hL m k,
      ← firstChernCapPowChowMap_chowClassCanonical D sP hP L hL m k]
    congr 1
    -- the single cap product, compared through Stacks 0ERE
    have h1 := chowClassCanonical_eq_of_coe_eq D sP hP (show k - 1 + m + 1 = k + m by ring)
      (firstChernCapCycleMap D sP hP (k - 1 + m + 1)
        (canonicalFirstChernRule D sP hP L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hLi) (k - 1 + m + 1))
        (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel (k - 1 + 1) (k - 1 + m + 1 + 1)
          (by push_cast; ring) α'))
      (firstChernCapPowCycleMap D sP hP L hL 1 (k + m)
        (cycleGroupCast D sP (by push_cast; ring)
          (flatPullbackMap D sP hP sX hX π hπB (m + 1) hflat hrel k (k + (m + 1 : ℕ)) rfl α)))
      (by
        simp only [firstChernCapPowCycleMap, AddMonoidHom.coe_comp, Function.comp_apply]
        refine coe_firstChernCapCycleMap_canonicalFirstChernRule_congr D sP hP L hL (by ring) _ _ ?_
        simp only [cycleGroupCast_coe]
        exact coe_flatPullbackMap_congr D sX hX sP hP π hπB (m + 1) hflat hrel (by ring)
          (by push_cast; ring) _ _ _ _ rfl)
    have h2 := chowClassCanonical_eq_of_coe_eq D sP hP (show k - 1 + m + 1 = k + m by ring)
      (closedSubspaceCyclePushforward D sP hP E (k - 1 + m + 1)
        (flatPullbackMap D (E.1.ι ≫ sP) hEg sX hX (E.1.ι ≫ π) hEB m hE.2 hErel (k - 1 + 1)
          (k - 1 + m + 1) (by ring) α'))
      (cycleGroupClosedPushforward D hP.1 E.2.1 (D.isDecentSpace_of_isGood sP hP) E.2.2 sP
        hP.2.2 (E.1.ι ≫ sP) rfl (k + m) y)
      (coe_cycleGroupClosedPushforward_congr D sP hP E.1 E.2 (by ring) _ _
        (coe_flatPullbackMap_congr D sX hX (E.1.ι ≫ sP) hEg (E.1.ι ≫ π) hEB m hE.2 hErel
          (by ring) (by ring) _ _ _ _ rfl))
    rw [← h1, ← h2, h0ERE]
  -- the cap powers along `i`, and `π_* i_* = π_{D,*}`
  have hpush := cycleGroupClosedPushforward_firstChernCapPowCycleMapOfRule D sP hP E.1 E.2
    (fun m => canonicalFirstChernRule D sP hP L hL m) m k y
  rw [← chowGroupCanonicalProperPushforward_chowClassCanonical.{u + 1} D sP hP sX hX hπB hp, hpow,
    chowGroupCanonicalProperPushforward_chowClassCanonical,
    ← firstChernCapPowCycleMapOfRule_canonicalFirstChernRule D sP hP L hL m, ← hpush,
    ← properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sP hP E.1 E.2,
    properCyclePushforward_comp D _ sP sX _ hP hX rfl hπB hιp hp]
  refine Eq.trans ?_ (hD k α)
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  unfold RationallyEquivalentCanonical
  rw [← map_sub]
  refine isRationallyEquivalentToZeroCanonical_properCyclePushforward D _ hEg sX hX hEB hEp k _ ?_
  exact isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMapOfRule_sub D _ _
    (closedSubspaceModuleRestrict D sP hP L E)
    (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1 E.1 E.2) L hL) _
    (fun m β' =>
      isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_closedSubspaceChernRule_sub
        D sP hP L hL E m β') m k y

end Divisor

end AlgebraicGeometry.Space

end
