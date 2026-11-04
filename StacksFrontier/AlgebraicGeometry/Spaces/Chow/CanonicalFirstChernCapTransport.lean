module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceLocallyFiniteSums

/-!
# The canonical first Chern component cycles along an isomorphism

In Situation 0EDT let `e : X ≅ X'` be an isomorphism of good algebraic spaces over the base,
`𝒩'` an invertible `𝒪_{X'}`-module and `𝒩 ≅ e^*𝒩'` on `X`. For an integral closed subspace
`W ⊆ X` of δ-dimension `k + 1` with image `W' = e(W) ⊆ X'`, the component cycles of Stacks 0EQJ,
`c₁(𝒩|_W) ∩ [W]` and `c₁(𝒩'|_{W'}) ∩ [W']`, are the Weil divisors of regular meromorphic
sections `t_W` of `𝒩|_W` and `t_{W'}` of `𝒩'|_{W'}` chosen independently by Stacks 0EPQ
(`AlgebraicGeometry.Space.canonicalFirstChernRule`). Pushed forward to `X'` they are rationally
equivalent:

`(W' → X')_* (c₁(𝒩'|_{W'}) ∩ [W']) ∼_rat e_* (W → X)_* (c₁(𝒩|_W) ∩ [W])`.

Summing over the components of a `(k + 1)`-cycle `β` on `X` gives
`c₁(𝒩') ∩ e_*β ∼_rat e_*(c₁(𝒩) ∩ β)` in `Z_k(X')`.

## Main results

* `cycleFamilySum_unique`: the sum of Stacks 0EQ6 over a family with a single member is the
  pushforward of that member.
* `isRationallyEquivalentToZeroWithin_firstChernComponentCycle_canonicalFirstChernRule_equivOfIso`
  states the rational equivalence above, witnessed within `|W'|`.
* `firstChernComponentCycle_canonicalFirstChernRule_equivOfIso_sub_mem`: the rational equivalence
  above, in `Z_k(X')`.
* `isRationallyEquivalentToZero_firstChernCapCycleMap_canonicalFirstChernRule_of_iso`:
  `c₁(𝒩') ∩ e_*β ∼_rat e_*(c₁(𝒩) ∩ β)` in `Z_k(X')` for every `(k + 1)`-cycle `β` on `X`.

## References

* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sX' : X' ⟶ D.space) (hX' : D.IsGood sX')

/-- The sum of Stacks 0EQ6, part (1), over a family with a single member is the pushforward of
that member. -/
theorem cycleFamilySum_unique {J : Type v} [Unique J] (k : ℤ)
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k) :
    cycleFamilySum D sX hX W hWfin k c =
      integralClosedSubspacePushforward D sX hX (W default) k (c default) :=
  Subtype.ext (funext fun Z => (cycleFamilySum_apply D sX hX W hWfin k c Z).trans
    (finsum_unique _))

variable (e : X ≅ X') (he : e.hom ≫ sX' = sX)

include he in
/-- **The canonical first Chern component cycles along an isomorphism.** Let `e : X ≅ X'` be an
isomorphism of good algebraic spaces over the base, `𝒩'` an invertible `𝒪_{X'}`-module, `𝒩` an
invertible `𝒪_X`-module with `𝒩 ≅ e^*𝒩'`, and `W ⊆ X` an integral closed subspace with image
`W' = e(W)`. Then the component cycle of Stacks 0EQJ at `W'`, at the canonical choices, and the
pushforward along `e` of the component cycle at `W` are rationally equivalent on `X'`:

`(W' → X')_* (c₁(𝒩'|_{W'}) ∩ [W']) - e_* (W → X)_* (c₁(𝒩|_W) ∩ [W]) ∈ Rat_k(X')`.

When `dim_δ(W) ≠ k + 1` both component cycles are zero. -/
theorem
    isRationallyEquivalentToZeroWithin_firstChernComponentCycle_canonicalFirstChernRule_equivOfIso
    (k : ℤ)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (N' : Modules.{u, u} D.site D.base D.base_mem X' hX'.1)
    (hN' : IsInvertibleModule (⟨X', hX'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N')
    (α : N ≅ (modulePullback D.site D.base D.base_mem (ObjectProperty.isoMk _ e :
      (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ≅ ⟨X', hX'.1⟩).hom).obj N')
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsRationallyEquivalentToZeroWithin.{v} D sX' hX' k
      (firstChernComponentCycle D sX' hX' k (canonicalFirstChernRule D sX' hX' N' hN' k)
        (IntegralClosedSubspace.equivOfIso _ _ _ hX.1 hX'.1 (isDecentSpace_of_isGood D sX hX)
          (isDecentSpace_of_isGood D sX' hX') e W) -
      cycleGroupClosedPushforward D hX'.1 hX.1 (isDecentSpace_of_isGood D sX' hX')
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sX' hX'.2.2 sX he k
        (firstChernComponentCycle D sX hX k (canonicalFirstChernRule D sX hX N hN k) W))
      (subspacePointSet D.site D.base D.base_mem X' (IntegralClosedSubspace.equivOfIso _ _ _ hX.1
        hX'.1 (isDecentSpace_of_isGood D sX hX) (isDecentSpace_of_isGood D sX' hX') e
          W).subspace) := by
  classical
  have hdec := isDecentSpace_of_isGood D sX hX
  have hdec' := isDecentSpace_of_isGood D sX' hX'
  set W' := IntegralClosedSubspace.equivOfIso _ _ _ hX.1 hX'.1 hdec hdec' e W with hW'def
  have hdim' : deltaDimension D sX' W' = deltaDimension D sX W :=
    (IntegralClosedSubspace.deltaDimension_equivOfIso D sX' hX'.2.2 hX.1 hX'.1 hdec hdec' e
      W).trans (by rw [he])
  by_cases hW : deltaDimension D sX W = k + 1
  swap
  · rw [firstChernComponentCycle_of_deltaDimension_ne D sX hX k _ hW,
      firstChernComponentCycle_of_deltaDimension_ne D sX' hX' k _ (hdim'.trans_ne hW), map_zero,
      sub_zero]
    exact isRationallyEquivalentToZeroWithin_zero D sX' hX' k _
  have hW'k : deltaDimension D sX' W' = k + 1 := hdim'.trans hW
  rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX k _ hW,
    firstChernComponentCycle_of_deltaDimension_eq D sX' hX' k _ hW'k]
  have hie := isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom
  let φ := IntegralClosedSubspace.isoPushforward hX'.1 hX.1 hdec' hie W
  have hiφ := isClosedImmersion_of_isIso D.site D.base D.base_mem φ.hom
  have hφ : φ.hom ≫ W'.subspace.ι = W.subspace.ι ≫ e.hom :=
    IntegralClosedSubspace.isoPushforward_hom_comp_ι hX'.1 hX.1 hdec' hie W
  let WA : AlgebraicSpaces D.site D.base D.base_mem := ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩
  let WA' : AlgebraicSpaces D.site D.base D.base_mem :=
    ⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩
  let ψ : WA' ≅ WA := ObjectProperty.isoMk _ φ.symm
  have hgW := isGood_integralClosedSubspace D sX hX W
  have hgW' := isGood_integralClosedSubspace D sX' hX' W'
  have hk : deltaDimensionClosed D (W.subspace.ι ≫ sX) hgW Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hW]
  have hk' : deltaDimensionClosed D (W'.subspace.ι ≫ sX') hgW' Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX' hX' W', hW'k]
  let NW := integralClosedSubspaceRestrict D sX hX N W
  have hNW := isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W
  let NW' := integralClosedSubspaceRestrict D sX' hX' N' W'
  have hNW' := isInvertibleModule_integralClosedSubspaceRestrict D sX' hX' N' hN' W'
  let tW := componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W
  have htW := isRegularMeromorphicSection_componentMeromorphicSection sX hX
    (subspaceDivisorSetupOfIsGood D sX hX) N hN W
  let tW' := componentMeromorphicSection sX' hX' (subspaceDivisorSetupOfIsGood D sX' hX') N' hN' W'
  have htW' := isRegularMeromorphicSection_componentMeromorphicSection sX' hX'
    (subspaceDivisorSetupOfIsGood D sX' hX') N' hN' W'
  have hf := pullbacksMeromorphicSections_of_iso D.site D.base D.base_mem ψ
  let σ₀ := pullbackMeromorphicSection D.site D.base D.base_mem ψ.hom NW hf tW
  have hσ₀ := isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
    ψ.hom hf NW (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hNW) tW htW
  let iW := closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace
  let iW' := closedSubspaceHom D.site D.base D.base_mem hX'.1 W'.subspace W'.isClosedSubspace
  let eA : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ≅ ⟨X', hX'.1⟩ :=
    ObjectProperty.isoMk _ e
  have hcomp : ψ.hom ≫ iW ≫ eA.hom = iW' := by
    ext1
    show φ.inv ≫ W.subspace.ι ≫ e.hom = W'.subspace.ι
    rw [← hφ]
    exact Iso.inv_hom_id_assoc φ _
  obtain ⟨β⟩ : Nonempty ((modulePullback D.site D.base D.base_mem ψ.hom).obj NW ≅ NW') :=
    ⟨(modulePullback D.site D.base D.base_mem ψ.hom).mapIso
        ((modulePullback D.site D.base D.base_mem iW).mapIso α ≪≫
          (modulePullbackCompIso D.site D.base D.base_mem iW eA.hom).app N') ≪≫
      (modulePullbackCompIso D.site D.base D.base_mem ψ.hom (iW ≫ eA.hom)).app N' ≪≫
        eqToIso (by rw [hcomp])⟩
  let σ' := SheafOfModules.sectionsMap
    (meromorphicSectionSheafMap D.site D.base D.base_mem _ _ β.hom) σ₀
  have hσ' := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem _ _ β σ₀ hσ₀
  let hdecW' := isDecentSpace_of_isGood D _ hgW'
  have hB₁ := congrArg Subtype.val (canonicalDivisorCycle_sectionsMap_of_iso D _ hgW'
    W'.isIntegralSpace _ NW' (modulePullbackInvertible ψ.hom NW hNW) hNW' β σ₀ hσ₀ hk')
  have hB₂ := cycleClosedPushforward_canonicalDivisorCycle_pullbackMeromorphicSection_of_iso D
    (W'.subspace.ι ≫ sX') hgW' (W.subspace.ι ≫ sX) hgW W'.isIntegralSpace W.isIntegralSpace ψ NW
    hNW tW htW hk' hk
  have hψφ : ψ.hom.hom ≫ φ.hom = 𝟙 _ := φ.inv_hom_id
  have hB₃ : (canonicalDivisorCycle D _ hgW' W'.isIntegralSpace
        ((modulePullback D.site D.base D.base_mem ψ.hom).obj NW)
        (modulePullbackInvertible ψ.hom NW hNW) σ₀ hσ₀ hk').1 =
      cycleClosedPushforward D hgW'.1 hgW.1 hdecW' hiφ
        (canonicalDivisorCycle D _ hgW W.isIntegralSpace NW hNW tW htW hk).1 := by
    have hfun := cycleClosedPushforward_cycleClosedPushforward D hgW'.1 hgW.1 hgW'.1 hdecW'
      (isDecentSpace_of_isGood D _ hgW) hψφ
      (isClosedImmersion_of_isIso D.site D.base D.base_mem ψ.hom.hom) hiφ
      (isClosedImmersion_of_isIso D.site D.base D.base_mem (𝟙 _))
      (canonicalDivisorCycle D _ hgW' W'.isIntegralSpace
        ((modulePullback D.site D.base D.base_mem ψ.hom).obj NW)
        (modulePullbackInvertible ψ.hom NW hNW) σ₀ hσ₀ hk').1
    rw [cycleClosedPushforward_id_eq_self, hB₂] at hfun
    exact hfun.symm
  let A := canonicalFirstChernRule D sX' hX' N' hN' k W' hW'k
  let B := canonicalDivisorCycleAt D (W'.subspace.ι ≫ sX') hgW' W'.isIntegralSpace NW' hNW' σ' hσ'
    hk'
  have hl : IsClosedImmersion D.site D.base D.base_mem (W.subspace.ι ≫ e.hom) :=
    isClosedImmersion_comp D.site D.base D.base_mem _ _ W.isClosedSubspace.2 hie
  have hB : B.1 = cycleClosedPushforward D hgW'.1 hgW.1 hdecW' hiφ
      (canonicalDivisorCycle D _ hgW W.isIntegralSpace NW hNW tW htW hk).1 :=
    (canonicalDivisorCycleAt_coe D _ hgW' W'.isIntegralSpace NW' hNW' σ' hσ' hk').trans
      (hB₁.trans hB₃)
  have key : cycleGroupClosedPushforward D hX'.1 hX.1 hdec' hie sX' hX'.2.2 sX he k
        (integralClosedSubspacePushforward D sX hX W k
          (canonicalFirstChernRule D sX hX N hN k W hW)) =
      integralClosedSubspacePushforward D sX' hX' W' k B := by
    refine Subtype.ext ?_
    have h₁ := cycleClosedPushforward_cycleClosedPushforward D hX'.1 hX.1 W.isClosedSubspace.1
      hdec' hdec (rfl : W.subspace.ι ≫ e.hom = _) W.isClosedSubspace.2 hie hl
      (canonicalFirstChernRule D sX hX N hN k W hW).1
    have h₂ := cycleClosedPushforward_cycleClosedPushforward D hX'.1 W'.isClosedSubspace.1
      W.isClosedSubspace.1 hdec' hdecW' hφ hiφ W'.isClosedSubspace.2 hl
      (canonicalDivisorCycle D _ hgW W.isIntegralSpace NW hNW tW htW hk).1
    exact h₁.trans (h₂.symm.trans (congrArg _ hB.symm))
  rw [key, ← map_sub, ← one_smul ℤ (A - B)]
  exact ⟨PUnit.{v + 1}, fun _ => W', locallyFinite_of_finite _, fun _ => (1 : ℤ) • (A - B),
    fun _ => subset_rfl, fun _ => hW'k,
    fun _ => isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_sub D _ hgW'
      W'.isIntegralSpace NW' hNW' tW' σ' htW' hσ' hk' 1,
    (cycleFamilySum_unique D sX' hX' (J := PUnit.{v + 1}) k (fun _ => W')
      (locallyFinite_of_finite _) (fun _ => (1 : ℤ) • (A - B))).symm⟩

include he in
/-- **The canonical first Chern component cycles along an isomorphism**, as a rational
equivalence in `Z_k(X')`. Let `e : X ≅ X'` be an isomorphism of good algebraic spaces over the
base, `𝒩'` an invertible `𝒪_{X'}`-module, `𝒩 ≅ e^*𝒩'`, and `W ⊆ X` an integral closed subspace
with image `W' = e(W)`. Then

`(W' → X')_* (c₁(𝒩'|_{W'}) ∩ [W']) - e_* (W → X)_* (c₁(𝒩|_W) ∩ [W]) ∈ Rat_k(X')`. -/
theorem firstChernComponentCycle_canonicalFirstChernRule_equivOfIso_sub_mem (k : ℤ)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (N' : Modules.{u, u} D.site D.base D.base_mem X' hX'.1)
    (hN' : IsInvertibleModule (⟨X', hX'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N')
    (α : N ≅ (modulePullback D.site D.base D.base_mem (ObjectProperty.isoMk _ e :
      (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ≅ ⟨X', hX'.1⟩).hom).obj N')
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    firstChernComponentCycle D sX' hX' k (canonicalFirstChernRule D sX' hX' N' hN' k)
        (IntegralClosedSubspace.equivOfIso _ _ _ hX.1 hX'.1 (isDecentSpace_of_isGood D sX hX)
          (isDecentSpace_of_isGood D sX' hX') e W) -
      cycleGroupClosedPushforward D hX'.1 hX.1 (isDecentSpace_of_isGood D sX' hX')
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sX' hX'.2.2 sX he k
        (firstChernComponentCycle D sX hX k (canonicalFirstChernRule D sX hX N hN k) W) ∈
      rationalEquivalences.{v} D sX' hX' k :=
  (isRationallyEquivalentToZeroWithin_firstChernComponentCycle_canonicalFirstChernRule_equivOfIso
    D sX hX sX' hX' e he k N hN N' hN' α W).isRationallyEquivalentToZero

include he in
/-- **The canonical cap product with the first Chern class along an isomorphism.** Let
`e : X ≅ X'` be an isomorphism of good algebraic spaces over the base, `𝒩'` an invertible
`𝒪_{X'}`-module and `𝒩 ≅ e^*𝒩'`. For every `(k+1)`-cycle `β` on `X`, the cap products of
Stacks 0EQJ at the canonical component cycles satisfy

`c₁(𝒩') ∩ e_*β ∼_rat e_*(c₁(𝒩) ∩ β)` in `Z_k(X')`. -/
theorem isRationallyEquivalentToZero_firstChernCapCycleMap_canonicalFirstChernRule_of_iso
    (k : ℤ) (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (N' : Modules.{u, u} D.site D.base D.base_mem X' hX'.1)
    (hN' : IsInvertibleModule (⟨X', hX'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N')
    (α : N ≅ (modulePullback D.site D.base D.base_mem (ObjectProperty.isoMk _ e :
      (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ≅ ⟨X', hX'.1⟩).hom).obj N')
    (β : CycleGroup D sX (k + 1)) :
    IsRationallyEquivalentToZero.{max (u + 1) v} D sX' hX' k
      (firstChernCapCycleMap D sX' hX' k (canonicalFirstChernRule D sX' hX' N' hN' k)
          (cycleGroupClosedPushforward D hX'.1 hX.1 (isDecentSpace_of_isGood D sX' hX')
            (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sX' hX'.2.2 sX he (k + 1)
            β) -
        cycleGroupClosedPushforward D hX'.1 hX.1 (isDecentSpace_of_isGood D sX' hX')
          (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sX' hX'.2.2 sX he k
          (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) β)) := by
  classical
  have hdec := isDecentSpace_of_isGood D sX hX
  have hdec' := isDecentSpace_of_isGood D sX' hX'
  let E := IntegralClosedSubspace.equivOfIso _ _ _ hX.1 hX'.1 hdec hdec' e
  let chern := canonicalFirstChernRule D sX hX N hN k
  let chern' := canonicalFirstChernRule D sX' hX' N' hN' k
  let push := fun j : ℤ => cycleGroupClosedPushforward D hX'.1 hX.1 hdec'
    (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sX' hX'.2.2 sX he j
  have hpush : ∀ (j : ℤ) (γ : CycleGroup D sX j) (W : IntegralClosedSubspace D.site D.base
      D.base_mem X), (push j γ).1 (E W) = γ.1 W := fun j γ W =>
    cycleClosedPushforward_apply_pushforward D hX'.1 hX.1 hdec'
      (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) γ.1 W
  have hinv : ∀ {Y Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (f : Y ⟶ Z)
      (g : Z ⟶ Y), f ≫ g = 𝟙 Y → Function.LeftInverse (pointsMap D.site D.base D.base_mem Z g)
        (pointsMap D.site D.base D.base_mem Y f) := fun f g h x => by
    rw [← Function.comp_apply (f := pointsMap D.site D.base D.base_mem _ g),
      ← pointsMap_comp, h, pointsMap_id, id]
  have hT : LocallyFinite fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if β.1 W = 0 then (∅ : Set (points D.site D.base D.base_mem X'))
      else subspacePointSet D.site D.base D.base_mem X' (E W).subspace := by
    refine (β.2.1.preimage_continuous
      (continuous_pointsMap D.site D.base D.base_mem e.inv)).subset fun W => ?_
    split_ifs
    · exact Set.empty_subset _
    · rw [IntegralClosedSubspace.subspacePointSet_equivOfIso hX.1 hX'.1 hdec hdec' e W,
        Set.image_eq_preimage_of_inverse (hinv _ _ e.hom_inv_id)
          (hinv _ _ e.inv_hom_id)]
  have hrat := fun W =>
    isRationallyEquivalentToZeroWithin_firstChernComponentCycle_canonicalFirstChernRule_equivOfIso
      D sX hX sX' hX' e he k N hN N' hN' α W
  refine isRationallyEquivalentToZero_finsum_max.{u, v, u + 1} D sX' hX' k _ hT
    (fun W => β.1 W • (firstChernComponentCycle D sX' hX' k chern' (E W) -
      push k (firstChernComponentCycle D sX hX k chern W))) (fun W => ?_) (fun Z => ?_)
  · by_cases hW : β.1 W = 0
    · simp only [hW, if_true, zero_smul]
      exact isRationallyEquivalentToZeroWithin_zero D sX' hX' k _
    · simp only [hW, if_false]
      exact IsCycleFamilySumWithin.isRationallyEquivalentToZeroWithin <|
        (hrat W).isCycleFamilySumWithin.zsmul neg_mem_principalDivisors _
  · obtain ⟨Z₀, rfl⟩ := E.surjective Z
    have hfin₁ := hasFiniteSupport_firstChernCapCoeff D sX hX k chern β Z₀
    have hfin₂ := hasFiniteSupport_firstChernCapCoeff D sX' hX' k chern' (push (k + 1) β) (E Z₀)
    have hfin₂' : Function.HasFiniteSupport fun W : IntegralClosedSubspace D.site D.base
        D.base_mem X => β.1 W * (firstChernComponentCycle D sX' hX' k chern' (E W)).1 (E Z₀) := by
      refine (hfin₂.preimage E.injective.injOn).subset fun W hW => ?_
      simpa only [Function.mem_support, Set.mem_preimage, hpush] using hW
    show (firstChernCapCycleMap D sX' hX' k chern' (push (k + 1) β)).1 (E Z₀) -
        (push k (firstChernCapCycleMap D sX hX k chern β)).1 (E Z₀) = _
    rw [hpush, firstChernCapCycleMap_apply, firstChernCapCycleMap_apply,
      ← finsum_comp_equiv E]
    simp only [hpush]
    rw [← finsum_sub_distrib hfin₂' hfin₁]
    refine finsum_congr fun W => ?_
    show _ = β.1 W * ((firstChernComponentCycle D sX' hX' k chern' (E W)).1 (E Z₀) -
      (push k (firstChernComponentCycle D sX hX k chern W)).1 (E Z₀))
    rw [hpush, mul_sub]

end AlgebraicGeometry.Space

end
