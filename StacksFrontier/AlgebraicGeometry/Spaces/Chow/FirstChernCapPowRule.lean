module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceDescentCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChernRuleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaCanonical

/-!
# Powers of the cap product for an arbitrary component rule, and closed subspaces

All declarations below live in the namespace `AlgebraicGeometry.Space`.

The cap product `c₁(ℒ) ∩ -` of Stacks 0EQJ is built from a component rule
(`FirstChernComponentCycleRule`): the cycle `c₁(ℒ|_W) ∩ [W]` chosen at each integral closed
subspace `W`. The canonical rule (`canonicalFirstChernRule`) is the Weil divisor of the canonical
meromorphic section. Along the inclusion `i : Y → X` of a closed subspace, the cap product on `X`
at the canonical rule commutes **exactly**, at the level of cycles, with the cap product on `Y` at
the transported rule (`closedSubspaceChernRule`), and the transported rule agrees with the
canonical rule of `ℒ|_Y` up to rational equivalence (Stacks 0EQT for a closed immersion,
`exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum`).

This file iterates both facts to the `s`-fold cap product.

## Main definitions

* `firstChernCapPowCycleMapOfRule`: the `s`-fold cap product `Z_{m+s}(X) → Z_m(X)` for a family
  of component rules.

## Main results

* `firstChernCapPowCycleMapOfRule_canonicalFirstChernRule`: at the canonical rules it is
  `firstChernCapPowCycleMap`.
* `cycleGroupClosedPushforward_firstChernCapPowCycleMapOfRule`: exact compatibility with
  pushforward along a closed subspace, at the transported rules.
* `isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMapOfRule_sub`: a family of rules
  each agreeing with the canonical one up to rational equivalence gives powers agreeing with the
  canonical powers up to rational equivalence.
* `isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_closedSubspaceChernRule_sub`: the
  transported canonical rule agrees with the canonical rule of `ℒ|_Y` up to rational
  equivalence.

## References

* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section Rule

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- **The `s`-fold cap product `Z_{m+s}(X) → Z_m(X)` for a family of component rules**: the
composite of `s` cap products of Stacks 0EQJ, the one into `Z_m` at the rule `R m`. -/
def firstChernCapPowCycleMapOfRule (R : ∀ m : ℤ, FirstChernComponentCycleRule D sX m) :
    (s : ℕ) → (m : ℤ) → CycleGroup D sX (m + s) →+ CycleGroup D sX m
  | 0, m => cycleGroupCast D sX (by simp)
  | s + 1, m => (firstChernCapCycleMap D sX hX m (R m)).comp
      ((firstChernCapPowCycleMapOfRule R s (m + 1)).comp (cycleGroupCast D sX (by push_cast; ring)))

/-- At the canonical rules the powers are those of
`AlgebraicGeometry.Space.firstChernCapPowCycleMap`. -/
theorem firstChernCapPowCycleMapOfRule_canonicalFirstChernRule
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) (s : ℕ) :
    ∀ (m : ℤ) (α : CycleGroup D sX (m + s)),
      firstChernCapPowCycleMapOfRule D sX hX (fun m => canonicalFirstChernRule D sX hX L hL m) s
          m α =
        firstChernCapPowCycleMap D sX hX L hL s m α := by
  induction s with
  | zero => intro m α; rfl
  | succ s ih =>
    intro m α
    simp only [firstChernCapPowCycleMapOfRule, firstChernCapPowCycleMap, AddMonoidHom.coe_comp,
      Function.comp_apply]
    rw [ih]

/-- **The powers of the cap product agree with the canonical powers up to rational equivalence**
for a family of rules each of which agrees with the canonical rule up to rational equivalence;
and they preserve rational equivalence. -/
theorem isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMapOfRule_sub
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (R : ∀ m : ℤ, FirstChernComponentCycleRule D sX m)
    (hR : ∀ (m : ℤ) (β : CycleGroup D sX (m + 1)),
      IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX m
        (firstChernCapCycleMap D sX hX m (R m) β -
          firstChernCapCycleMap D sX hX m (canonicalFirstChernRule D sX hX L hL m) β))
    (s : ℕ) :
    ∀ (m : ℤ) (α : CycleGroup D sX (m + s)),
      IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX m
        (firstChernCapPowCycleMapOfRule D sX hX R s m α -
          firstChernCapPowCycleMap D sX hX L hL s m α) := by
  induction s with
  | zero =>
    intro m α
    have h0 : firstChernCapPowCycleMapOfRule D sX hX R 0 m α =
        firstChernCapPowCycleMap D sX hX L hL 0 m α := rfl
    rw [h0, sub_self]
    exact isRationallyEquivalentToZeroCanonical_zero.{u + 1} D sX hX m
  | succ s ih =>
    intro m α
    simp only [firstChernCapPowCycleMapOfRule, firstChernCapPowCycleMap, AddMonoidHom.coe_comp,
      Function.comp_apply]
    set β := cycleGroupCast D sX (show m + ((s + 1 : ℕ) : ℤ) = m + 1 + s by push_cast; ring) α
    have h1 := hR m (firstChernCapPowCycleMapOfRule D sX hX R s (m + 1) β)
    have h2 := isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_canonicalFirstChernRule
      D sX hX m L hL (ih (m + 1) β)
    rw [map_sub] at h2
    have h := isRationallyEquivalentToZeroCanonical_add.{u + 1} D sX hX m h1 h2
    rwa [sub_add_sub_cancel] at h

/-- The powers of the cap product at a family of rules agreeing with the canonical one up to
rational equivalence preserve rational equivalence. -/
theorem isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMapOfRule
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (R : ∀ m : ℤ, FirstChernComponentCycleRule D sX m)
    (hR : ∀ (m : ℤ) (β : CycleGroup D sX (m + 1)),
      IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX m
        (firstChernCapCycleMap D sX hX m (R m) β -
          firstChernCapCycleMap D sX hX m (canonicalFirstChernRule D sX hX L hL m) β))
    (s : ℕ) (m : ℤ) {α : CycleGroup D sX (m + s)}
    (hα : IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX (m + s) α) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX m
      (firstChernCapPowCycleMapOfRule D sX hX R s m α) := by
  have h1 := isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMapOfRule_sub D sX hX L hL
    R hR s m α
  have h2 := isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMap D sX hX L hL s m hα
  have h := isRationallyEquivalentToZeroCanonical_add.{u + 1} D sX hX m h1 h2
  rwa [sub_add_cancel] at h

end Rule

/-! ### Closed subspaces -/

section Closed

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)

/-- Pushforward along a closed subspace commutes with the identifications of cycle groups of
equal degrees. -/
theorem cycleGroupClosedPushforward_cycleGroupCast {a b : ℤ} (h : a = b)
    (β : CycleGroup D (Y.ι ≫ sX) a) :
    cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl b (cycleGroupCast D (Y.ι ≫ sX) h β) =
      cycleGroupCast D sX h
        (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX
          hX.2.2 (Y.ι ≫ sX) rfl a β) := by
  subst h
  rfl

/-- **The powers of the cap product commute exactly with pushforward along a closed subspace**,
the powers on `Y` being taken at the transported rules. -/
theorem cycleGroupClosedPushforward_firstChernCapPowCycleMapOfRule
    (R : ∀ m : ℤ, FirstChernComponentCycleRule D sX m) (s : ℕ) :
    ∀ (m : ℤ) (β : CycleGroup D (Y.ι ≫ sX) (m + s)),
      cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
          (Y.ι ≫ sX) rfl m
          (firstChernCapPowCycleMapOfRule D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY)
            (fun m => closedSubspaceChernRule D sX hX Y hY m (R m)) s m β) =
        firstChernCapPowCycleMapOfRule D sX hX R s m
          (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX
            hX.2.2 (Y.ι ≫ sX) rfl (m + s) β) := by
  induction s with
  | zero =>
    intro m β
    exact cycleGroupClosedPushforward_cycleGroupCast D sX hX Y hY _ β
  | succ s ih =>
    intro m β
    simp only [firstChernCapPowCycleMapOfRule, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [cycleGroupClosedPushforward_firstChernCapCycleMap D sX hX Y hY m (R m), ih,
      cycleGroupClosedPushforward_cycleGroupCast D sX hX Y hY]

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **The transported canonical rule agrees with the canonical rule of the restriction up to
rational equivalence**: for a closed subspace `Y ⊆ X` and `β ∈ Z_{k+1}(Y)`, the cap products
`c₁(𝒩) ∩ β` at the rule transported from `X` and at the canonical rule of `𝒩|_Y` differ by a
cycle rationally equivalent to zero on `Y`. Pushed forward to `X`, the difference is the explicit
locally finite sum of canonical principal divisors of Stacks 0EQT for a closed immersion, carried
by `Y`; such a cycle descends to `Y`. -/
theorem isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_closedSubspaceChernRule_sub
    (Y : ClosedSubspaces D.site D.base D.base_mem X) (k : ℤ)
    (β : CycleGroup D (Y.1.ι ≫ sX) (k + 1)) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D (Y.1.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y.1 Y.2) k
      (firstChernCapCycleMap D (Y.1.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y.1 Y.2) k
          (closedSubspaceChernRule D sX hX Y.1 Y.2 k (canonicalFirstChernRule D sX hX N hN k)) β -
        firstChernCapCycleMap D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y) k
          (canonicalFirstChernRule D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
            (closedSubspaceModuleRestrict D sX hX N Y)
            (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2)
              N hN) k) β) := by
  refine isRationallyEquivalentToZeroCanonical_of_isRationallyEquivalentToZeroWithinCanonical_closedPushforward
    D sX hX Y.1 Y.2 k ?_
  rw [map_sub, cycleGroupClosedPushforward_firstChernCapCycleMap D sX hX Y.1 Y.2 k]
  obtain ⟨hk, g, heq⟩ :=
    exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum D sX hX Y N hN
      β
  change firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
      (closedSubspaceCyclePushforward D sX hX Y (k + 1) β) -
    closedSubspaceCyclePushforward D sX hX Y k _ = _ at heq
  rw [heq]
  refine IsRationallyEquivalentToZeroWithinCanonical.uliftIndex.{u, u + 1} ?_
  refine ⟨_, _, locallyFinite_closedSubspaceComponentImage_of_ne_zero D sX hX Y β, _,
    fun V => ?_, fun V => ?_,
    fun V => isPrincipalDivisorCycleOfGood_canonicalPrincipalDivisorCycleAt
      D _ _ _ (g V) (hk V), rfl⟩
  · rw [IntegralClosedSubspace.subspacePointSet_pushforward]
    exact Set.image_subset_range _ _
  · have h := hk V
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX] at h
    exact WithBotTop.coe_injective h

end Closed

end AlgebraicGeometry.Space

end
