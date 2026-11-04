module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatBaseChange
public import StacksFrontier.RingTheory.Rig.FlatBaseChangeReduction
public import StacksFrontier.RingTheory.Rig.FlatJacobson
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic

/-!
# The base-change assertion of Stacks 0GGR reduced to its naive form

Let `A → B` be rig-flat and `A → C` adic and topologically of finite type, all three rings
Noetherian and adic.  **Stacks 0GGR** says that `C → B ⊗̂_A C` is *rig-flat*.  Unfolding
rig-flatness (Stacks 0GGP) that asks, for every ideal of definition `J` of `C` and every
`f : C`, for *naive* rig-flatness (Stacks 0GGM) of the induced map
`C_{\{f\}} → (B ⊗̂_A C)_{\{f\}}`, and naive rig-flatness does not imply rig-flatness
(Stacks 0GGN), so the two statements are genuinely different.

The first paragraph of the proof of Stacks 0GGR closes that gap by *replacing `C` by
`C_{\{f\}}`*: the pair `A → C_{\{f\}}`, `f ∈ C_{\{f\}}` satisfies the hypotheses of
Stacks 0GGR again, the completed principal localization of the base change is the base change of
the completed principal localization, and under that identification the arrow Stacks 0GGP asks
about *is* the base-change arrow `C_{\{f\}} → B ⊗̂_A C_{\{f\}}`.  So the naive conclusion, known
for every admissible `C`, gives the rig-flat conclusion.

This file is that implication.  What remains of Stacks 0GGR after it is the *naive* statement
`AlgebraicGeometry.FormalSpace.NaiveRigFlatBaseChangeByAdicFiniteType`, which is what the
remaining paragraphs of the proof establish; this file closes paragraph 1 and nothing else.

## Main definitions

* `AlgebraicGeometry.FormalSpace.NaiveRigFlatBaseChangeByAdicFiniteType`: the naive form of the
  base-change assertion of Stacks 0GGR — same hypotheses, conclusion only that
  `C → B ⊗̂_A C` is naively rig-flat.

## Main results

* `AlgebraicGeometry.FormalSpace.rigFlat_completedTensorProduct_of_naive`: the three conclusions
  of Stacks 0GGR for one triple of rings, from the naive form.
* `AlgebraicGeometry.FormalSpace.rigFlatBaseChangeByAdicFiniteType_of_naive`: **the first
  paragraph of the proof of Stacks 0GGR** — the naive form implies
  `AlgebraicGeometry.FormalSpace.RigFlatBaseChangeByAdicFiniteType`, the shape in which
  Remark 0GBG consumes the tag.

## Implementation notes

The ingredients of the replacement are in `StacksFrontier.RingTheory.Rig.FlatBaseChangeReduction`:
`Rig.completedAway_baseChange_hypotheses` for "`A → C_{\{f\}}` satisfies the hypotheses again",
and `Rig.exists_ringEquiv_comp_algebraMap_eq_completedAwayMap` for the identification together
with its compatibility with the two arrows out of `C_{\{f\}}`.  Naive rig-flatness is carried
across the identification by `Rig.RingHom.isNaivelyRigFlat_of_ringEquiv`.

The other two conclusions of the bundle do not involve the replacement at all: adicness of the
completed tensor product is `TopologicalRing.completedTensorProduct_isAdic` and its
Noetherianity is `TopologicalRing.completedTensorProduct_isNoetherianRing`, both **Stacks
0GB4**, the latter fed by finite type on the reductions of `A → B`, which rig-flatness of
`A → B` supplies through `Rig.isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType`.

Of the two obligations on the induced map itself, adicness is
`Rig.RingHom.isAdic_completedAwayMap` at exactly the presentation Stacks 0GGP uses, and
topological finite type is `Rig.completedAwayMap_properties`, whose target topology is presented
by the ideal extended from `B ⊗̂_A C` rather than from its principal localization; the two
ideals are equal by `Rig.map_map_algebraMap_completedAway`, and
`isTopologicallyOfFiniteType_of_topologicalSpace_eq` moves the conclusion across.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GGM](https://stacks.math.columbia.edu/tag/0GGM)
* [Stacks Project, Tag 0GGN](https://stacks.math.columbia.edu/tag/0GGN)
* [Stacks Project, Tag 0GGP](https://stacks.math.columbia.edu/tag/0GGP)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.FormalSpace

section NaiveReduction

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The naive form of the base-change assertion of Stacks 0GGR.**  Under the hypotheses of
`AlgebraicGeometry.FormalSpace.RigFlatBaseChangeByAdicFiniteType` — `R₀ → R₁` rig-flat,
`R₀ → R₂` adic and topologically of finite type, all three rings Noetherian and adic — the
canonical map `R₂ → R₁ ⊗̂_{R₀} R₂` is *naively* rig-flat (Stacks 0GGM).

This is strictly weaker than the assertion of Stacks 0GGR, which asks for rig-flatness
(Stacks 0GGP): naive rig-flatness does not imply rig-flatness (Stacks 0GGN).  The first
paragraph of the proof of Stacks 0GGR is exactly the passage from this statement, quantified
over all admissible `R₂`, to the full one. -/
abbrev NaiveRigFlatBaseChangeByAdicFiniteType : Prop :=
  ∀ {R₀ R₁ R₂ : Type u} [CommRing R₀] [TopologicalSpace R₀] [IsTopologicalRing R₀]
      [IsLinearTopology R₀ R₀] [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [IsLinearTopology R₁ R₁] [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
      [IsLinearTopology R₂ R₂] [Algebra R₀ R₁] [Algebra R₀ R₂] [IsNoetherianRing R₀]
      [IsNoetherianRing R₁] [IsNoetherianRing R₂],
    TopologicalRing.IsAdic R₀ → TopologicalRing.IsAdic R₁ → TopologicalRing.IsAdic R₂ →
    Continuous (algebraMap R₀ R₁) → Continuous (algebraMap R₀ R₂) →
    Rig.RingHom.IsRigFlat (algebraMap R₀ R₁) →
    (RingHom.IsAdic (algebraMap R₀ R₂) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (algebraMap R₀ R₂)) →
    Rig.RingHom.IsNaivelyRigFlat (algebraMap R₂
      (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂)))

/-- Being topologically of finite type depends on the target's topology only, so it transports
along an equality of topologies on the target. -/
private theorem isTopologicallyOfFiniteType_of_topologicalSpace_eq {R S : Type*} [CommRing R]
    [CommRing S] {s s' : TopologicalSpace S} (φ : R →+* S) (h : s = s')
    (hφ : @TopologicalRing.IsTopologicallyOfFiniteType R S _ _ s φ) :
    @TopologicalRing.IsTopologicallyOfFiniteType R S _ _ s' φ := by
  subst h
  exact hφ

/-- **The three conclusions of Stacks 0GGR for one triple of rings, from the naive form.**
Adicness and Noetherianity of `R₁ ⊗̂_{R₀} R₂` are Stacks 0GB4 and do not use the naive
hypothesis for anything but the finite-type input they already have.

Rig-flatness of `R₂ → R₁ ⊗̂_{R₀} R₂` is where the replacement happens: its first two clauses are
the first two clauses of the naive statement at `R₂` itself, and its third asks, for an ideal of
definition `I` of `R₂` and `f : R₂`, that `R₂_{\{f\}} → (R₁ ⊗̂_{R₀} R₂)_{\{f\}}` be naively
rig-flat.  The pair `R₀ → R₂_{\{f\}}` satisfies the hypotheses again
(`Rig.completedAway_baseChange_hypotheses`), so the naive statement applies to it and gives
naive rig-flatness of `R₂_{\{f\}} → R₁ ⊗̂_{R₀} R₂_{\{f\}}`; and that map is the one asked about,
by the identification of paragraph 1 and its compatibility
(`Rig.exists_ringEquiv_comp_algebraMap_eq_completedAwayMap`). -/
theorem rigFlat_completedTensorProduct_of_naive
    (hnaive : NaiveRigFlatBaseChangeByAdicFiniteType.{u})
    {R₀ R₁ R₂ : Type u} [CommRing R₀] [TopologicalSpace R₀] [IsTopologicalRing R₀]
    [IsLinearTopology R₀ R₀] [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [IsLinearTopology R₁ R₁] [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    [IsLinearTopology R₂ R₂] [Algebra R₀ R₁] [Algebra R₀ R₂] [IsNoetherianRing R₀]
    [IsNoetherianRing R₁] [IsNoetherianRing R₂]
    (h₀ : TopologicalRing.IsAdic R₀) (h₁ : TopologicalRing.IsAdic R₁)
    (h₂ : TopologicalRing.IsAdic R₂) (hc₁ : Continuous (algebraMap R₀ R₁))
    (hc₂ : Continuous (algebraMap R₀ R₂)) (hP : Rig.RingHom.IsRigFlat (algebraMap R₀ R₁))
    (hQ : RingHom.IsAdic (algebraMap R₀ R₂) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (algebraMap R₀ R₂)) :
    TopologicalRing.IsAdic
        (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂)) ∧
      IsNoetherianRing
        (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂)) ∧
      Rig.RingHom.IsRigFlat (algebraMap R₂
        (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂))) := by
  obtain ⟨I₀, hI₀def, -⟩ := h₀.1
  obtain ⟨I₁, hI₁def, -⟩ := h₁.1
  obtain ⟨I₂, hI₂def, -⟩ := h₂.1
  obtain ⟨Ib, hIbadic, hIbmap⟩ := hP.1
  have hTadic : TopologicalRing.IsAdic
      (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂)) :=
    TopologicalRing.completedTensorProduct_isAdic hc₁ hc₂ h₁.1
      ⟨I₁, hI₁def, Ideal.fg_of_isNoetherianRing I₁⟩ h₂.1
      ⟨I₂, hI₂def, Ideal.fg_of_isNoetherianRing I₂⟩
  have hBW : TopologicalRing.IsWeaklyPreAdmissible R₀ :=
    ⟨I₀, hI₀def.1, fun x hx ↦
      TopologicalRing.CompletionOver.isTopologicallyNilpotent_of_mem_isIdealOfDefinition hI₀def hx⟩
  have hRed := Rig.isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType
    (algebraMap R₀ R₁) hc₁ hBW
    (RingHom.isTaut_of_isAdic (algebraMap R₀ R₁) hc₁ hP.1) hP.2.1
  let hTnoeth : IsNoetherianRing
      (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂)) :=
    TopologicalRing.completedTensorProduct_isNoetherianRing hc₁ hc₂ h₁.1 h₂.1
      ⟨TopologicalRing.topologicalNilradical_le_comap _ hc₁, hRed⟩
  have hnaive₀ := hnaive h₀ h₁ h₂ hc₁ hc₂ hP hQ
  refine ⟨hTadic, hTnoeth, hnaive₀.1, hnaive₀.2.1, ?_⟩
  intro I hI hImap f
  let φ := algebraMap R₂ (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂))
  let L := Localization.Away f
  let L' := Localization.Away (φ f)
  let I_f := I.map (algebraMap R₂ L)
  let J_f := (I.map φ).map (algebraMap
    (TopologicalRing.CompletedTensorProduct (R := R₀) (M := R₁) (N := R₂)) L')
  let Cf := AdicCompletion I_f L
  let Tgt := AdicCompletion J_f L'
  let I_hat := I_f.map (algebraMap L Cf)
  let J_hat := J_f.map (algebraMap L' Tgt)
  let : TopologicalSpace Cf := I_hat.adicTopology
  let : IsTopologicalRing Cf := I_hat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology Cf Cf := I_hat.isLinearTopology
  let : TopologicalSpace Tgt := J_hat.adicTopology
  have hCf : _root_.IsAdic (I.map (algebraMap R₂ Cf)) :=
    congrArg Ideal.adicTopology (Rig.map_map_algebraMap_completedAway I f)
  obtain ⟨hCfnoeth, hCfadic, hcont', hadic', hft'⟩ :=
    Rig.completedAway_baseChange_hypotheses I hI f hCf (algebraMap R₀ R₂) hc₂ hQ
  let : IsNoetherianRing Cf := hCfnoeth
  have htower : (algebraMap R₂ Cf).comp (algebraMap R₀ R₂) = algebraMap R₀ Cf :=
    (IsScalarTower.algebraMap_eq R₀ R₂ Cf).symm
  rw [htower] at hcont' hadic' hft'
  have hg := hnaive h₀ h₁ hCfadic hc₁ hcont' hP ⟨hadic', hft'⟩
  obtain ⟨e, he⟩ := Rig.exists_ringEquiv_comp_algebraMap_eq_completedAwayMap I hI f hCf Ib
    hIbadic hIbmap hQ.1 hc₂ hQ.2
  refine Rig.RingHom.isNaivelyRigFlat_of_ringEquiv _ _ e.symm ?_
    ⟨Rig.RingHom.isAdic_completedAwayMap φ I f, ?_⟩ hg
  · refine RingHom.ext fun x ↦ ?_
    exact (congrArg e.symm (DFunLike.congr_fun he x)).symm.trans (e.symm_apply_apply _)
  · exact isTopologicallyOfFiniteType_of_topologicalSpace_eq _
      (congrArg Ideal.adicTopology
        (Rig.map_map_algebraMap_completedAway (I.map φ) (φ f)).symm)
      (Rig.completedAwayMap_properties φ I f hnaive₀.2.1 hImap).2.2.2

/-- **The first paragraph of the proof of Stacks 0GGR**: the naive form of the base-change
assertion implies the assertion itself, in the shape Remark 0GBG consumes.

Deliberately untagged, exactly as
`AlgebraicGeometry.FormalSpace.rigFlat_isStableUnderBaseChangeByAdicFiniteType` is: it carries
a hypothesis that Stacks 0GGR does not, so a tag over it would stand over a hypothesis rather
than over a theorem.  What it does is remove the one obstruction that makes
Stacks 0GGR more than its naive form; the naive form itself is the subject of the remaining
paragraphs of the proof. -/
theorem rigFlatBaseChangeByAdicFiniteType_of_naive
    (hnaive : NaiveRigFlatBaseChangeByAdicFiniteType.{u}) :
    RigFlatBaseChangeByAdicFiniteType.{u} :=
  fun h₀ h₁ h₂ hc₁ hc₂ hP hQ ↦
    rigFlat_completedTensorProduct_of_naive hnaive h₀ h₁ h₂ hc₁ hc₂ hP hQ

end NaiveReduction

end AlgebraicGeometry.FormalSpace

end
