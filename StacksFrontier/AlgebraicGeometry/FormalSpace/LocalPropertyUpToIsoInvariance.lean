module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertySourceCover
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverSelf
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesUpToIso

/-!
# A local property is invariant under isomorphism of source and target

A local property `P` of morphisms in the sense of Situation 0CBA,
`TopologicalRing.PropertyIsLocalUpToIso`, is invariant under isomorphism of source and target.
The Stacks Project derives this from axiom (1), and the proof here follows it. Let `ψ : A → R` be
a continuous homomorphism with `P` and `e : A' ≅ A` an isomorphism of topological rings. The
diagram (87.21.2.1) has lower map `ψ` and identity étale maps `A → A`, `R → R`. A countably
indexed weakly admissible ring is its own completion,
`TopologicalRing.exists_ringEquiv_completionOver_id`, so `A'` (through `e`) and `R` may serve as
its completed corners, and axiom (1) then gives `P (ψ ∘ e)`. The target side is the same, with
`R'` as the upper right corner through an isomorphism `R ≅ R'`.

Only axiom (1) is used, and of the class `C` only that its rings are weakly admissible with a
countable fundamental system of neighbourhoods of zero. That holds for `WAdm^{adic*}` and for the
Noetherian adic rings, and the invariances are recorded for both.

## Main results

In the namespace `AlgebraicGeometry.FormalSpace`:

* `propertyIsInvariantUnderSourceIso_of_localizationPreservesUpToIso` and
  `propertyIsInvariantUnderTargetIsoOn_of_localizationPreservesUpToIso`: axiom (1) of
  Situation 0CBA gives invariance under isomorphism of source and target;
* `propertyIsInvariantUnderSourceIso_of_propertyIsLocalAdicStarUpToIso`,
  `propertyIsInvariantUnderTargetIsoOn_of_propertyIsLocalAdicStarUpToIso`,
  `propertyIsInvariantUnderSourceIso_of_propertyIsLocalNoetherianUpToIso` and
  `propertyIsInvariantUnderTargetIsoOn_of_propertyIsLocalNoetherianUpToIso`: the two
  invariances at `WAdm^{adic*}` and at the Noetherian adic rings.

In the namespace `TopologicalRing`, `PropertyIsLocalUpToIso.propertyIsInvariantUnderSourceIso`
and `PropertyIsLocalUpToIso.propertyIsInvariantUnderTargetIsoOn` give the same for a local
property at an arbitrary class.

## References

* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.FormalSpace

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The localization diagram of Situation 0CBA with lower map `ψ : A → R`, identity étale maps,
and upper map `ψ` transported to the completions of `A` and `R` over themselves by isomorphisms
`eA`, `eR` extending the canonical maps. -/
noncomputable def identityLocalizationDiagram {A R : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hAc : (nhds (0 : A)).IsCountablyGenerated)
    (hR : TopologicalRing.IsWeaklyAdmissible R) (hRc : (nhds (0 : R)).IsCountablyGenerated)
    (ψ : A →+* R) (hψ : Continuous ψ)
    (eA : A ≃+* TopologicalRing.CompletionOver (RingHom.id A))
    (heA : ∀ a : A, eA a = TopologicalRing.CompletionOver.canonicalMap (RingHom.id A) a)
    (heAs : Continuous eA.symm)
    (eR : R ≃+* TopologicalRing.CompletionOver (RingHom.id R))
    (heR : ∀ r : R, eR r = TopologicalRing.CompletionOver.canonicalMap (RingHom.id R) r)
    (heRc : Continuous eR) :
    TopologicalRing.LocalizationDiagram R A R A where
  toA' := RingHom.id R
  toB' := RingHom.id A
  map := ψ
  completedMap := (eR.toRingHom.comp ψ).comp eA.symm.toRingHom
  weaklyAdmissibleA := hR
  weaklyAdmissibleB := hA
  countableA := hRc
  countableB := hAc
  etaleA := RingHom.Etale.of_bijective Function.bijective_id
  etaleB := RingHom.Etale.of_bijective Function.bijective_id
  continuousMap := hψ
  continuousCompletedMap := (heRc.comp hψ).comp heAs
  commutes := by
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← heA,
      ← heR, RingEquiv.symm_apply_apply]

/-- **Invariance under isomorphism of sources, from axiom (1) of Situation 0CBA.** If the rings
of the class `C` are weakly admissible with a countable fundamental system of neighbourhoods of
zero, and `P` satisfies axiom (1) with the completed corners up to isomorphism, then `P` is
invariant under isomorphism of sources: an isomorphism is étale, and a complete ring is its own
completion. -/
theorem propertyIsInvariantUnderSourceIso_of_localizationPreservesUpToIso
    (hCw : ClassIsWeaklyAdmissible C) (hCc : ClassHasCountableNhdsZero C)
    (hP : TopologicalRing.LocalizationPreservesUpToIso C P) :
    PropertyIsInvariantUnderSourceIso C P := by
  intro A A' R _ _ _ _ _ _ _ _ _ _ _ _ hA hA' hR ψ e hψ he hes hPψ
  obtain ⟨eA, heA, heAc, heAs⟩ :=
    TopologicalRing.exists_ringEquiv_completionOver_id (hCw A hA) (hCc A hA)
  obtain ⟨eR, heR, heRc, heRs⟩ :=
    TopologicalRing.exists_ringEquiv_completionOver_id (hCw R hR) (hCc R hR)
  let D := identityLocalizationDiagram (hCw A hA) (hCc A hA) (hCw R hR) (hCc R hR) ψ hψ
    eA heA heAs eR heR heRc
  have key := hP D eR.symm (eA.symm.trans e.symm) heRs heRc (hes.comp heAs) (heAc.comp he)
    hR hA hR hA' hPψ
  beta_reduce at key
  convert key using 2
  ext x
  change ψ (e x) = eR.symm (eR (ψ (eA.symm (eA (e x)))))
  simp only [RingEquiv.symm_apply_apply]

/-- **Invariance under isomorphism of targets, from axiom (1) of Situation 0CBA.** If the rings
of the class `C` are weakly admissible with a countable fundamental system of neighbourhoods of
zero, and `P` satisfies axiom (1) with the completed corners up to isomorphism, then `P` is
invariant under isomorphism of targets: an isomorphism is étale, and a complete ring is its own
completion. -/
theorem propertyIsInvariantUnderTargetIsoOn_of_localizationPreservesUpToIso
    (hCw : ClassIsWeaklyAdmissible C) (hCc : ClassHasCountableNhdsZero C)
    (hP : TopologicalRing.LocalizationPreservesUpToIso C P) :
    PropertyIsInvariantUnderTargetIsoOn C P := by
  intro A R R' _ _ _ _ _ _ _ _ _ _ _ _ hA hR hR' ψ e hψ he hes hPψ
  obtain ⟨eA, heA, heAc, heAs⟩ :=
    TopologicalRing.exists_ringEquiv_completionOver_id (hCw A hA) (hCc A hA)
  obtain ⟨eR, heR, heRc, heRs⟩ :=
    TopologicalRing.exists_ringEquiv_completionOver_id (hCw R hR) (hCc R hR)
  let D := identityLocalizationDiagram (hCw A hA) (hCc A hA) (hCw R hR) (hCc R hR) ψ hψ
    eA heA heAs eR heR heRc
  have key := hP D (eR.symm.trans e) eA.symm (he.comp heRs) (heRc.comp hes) heAs heAc
    hR hA hR' hA hPψ
  beta_reduce at key
  convert key using 2
  ext x
  change e (ψ x) = e (eR.symm (eR (ψ (eA.symm (eA x)))))
  simp only [RingEquiv.symm_apply_apply]

end AlgebraicGeometry.FormalSpace

namespace TopologicalRing

variable {C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop}
  {P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop}

/-- A local property of morphisms of a class of countably indexed weakly admissible rings is
invariant under isomorphism of sources. -/
theorem PropertyIsLocalUpToIso.propertyIsInvariantUnderSourceIso
    (h : PropertyIsLocalUpToIso P C)
    (hCw : AlgebraicGeometry.FormalSpace.ClassIsWeaklyAdmissible C)
    (hCc : AlgebraicGeometry.FormalSpace.ClassHasCountableNhdsZero C) :
    AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderSourceIso C P :=
  AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderSourceIso_of_localizationPreservesUpToIso
    C P hCw hCc h.localizationPreserves

/-- A local property of morphisms of a class of countably indexed weakly admissible rings is
invariant under isomorphism of targets. -/
theorem PropertyIsLocalUpToIso.propertyIsInvariantUnderTargetIsoOn
    (h : PropertyIsLocalUpToIso P C)
    (hCw : AlgebraicGeometry.FormalSpace.ClassIsWeaklyAdmissible C)
    (hCc : AlgebraicGeometry.FormalSpace.ClassHasCountableNhdsZero C) :
    AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderTargetIsoOn C P :=
  AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderTargetIsoOn_of_localizationPreservesUpToIso
    C P hCw hCc h.localizationPreserves

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- A local property of morphisms of `WAdm^{adic*}` is invariant under isomorphism of sources.
The variant of Stacks 0ANG in Stacks 0ANH uses this, and it follows from axiom (1) of
Situation 0CBA. -/
@[stacks 0ANH "a local property of morphisms of WAdm^{adic*} is invariant under isomorphism of \
sources, by axiom (1), an isomorphism being etale; used by the variant of 0ANG"]
theorem propertyIsInvariantUnderSourceIso_of_propertyIsLocalAdicStarUpToIso
    (hP : TopologicalRing.PropertyIsLocalAdicStarUpToIso.{u} P) :
    PropertyIsInvariantUnderSourceIso.{u} TopologicalRing.IsAdicStar P :=
  hP.propertyIsInvariantUnderSourceIso (fun _ _ _ _ _ h ↦ Rig.weaklyAdmissible_of_isAdicRing h.1)
    (fun _ _ _ _ _ h ↦ Rig.countablyGenerated_nhds_of_isAdicRing h.1)

/-- A local property of morphisms of `WAdm^{adic*}` is invariant under isomorphism of targets.
The variant of Stacks 0ANG in Stacks 0ANH uses this, and it follows from axiom (1) of
Situation 0CBA. -/
@[stacks 0ANH "a local property of morphisms of WAdm^{adic*} is invariant under isomorphism of \
targets, by axiom (1), an isomorphism being etale; used by the variant of 0ANG"]
theorem propertyIsInvariantUnderTargetIsoOn_of_propertyIsLocalAdicStarUpToIso
    (hP : TopologicalRing.PropertyIsLocalAdicStarUpToIso.{u} P) :
    PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P :=
  hP.propertyIsInvariantUnderTargetIsoOn (fun _ _ _ _ _ h ↦ Rig.weaklyAdmissible_of_isAdicRing h.1)
    (fun _ _ _ _ _ h ↦ Rig.countablyGenerated_nhds_of_isAdicRing h.1)

/-- A local property of morphisms of Noetherian adic rings is invariant under isomorphism of
sources. -/
theorem propertyIsInvariantUnderSourceIso_of_propertyIsLocalNoetherianUpToIso
    (hP : TopologicalRing.PropertyIsLocalNoetherianUpToIso.{u} P) :
    PropertyIsInvariantUnderSourceIso.{u}
      (fun R _ _ _ _ ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P :=
  hP.propertyIsInvariantUnderSourceIso (fun _ _ _ _ _ h ↦ Rig.weaklyAdmissible_of_isAdicRing h.1)
    (fun _ _ _ _ _ h ↦ Rig.countablyGenerated_nhds_of_isAdicRing h.1)

/-- A local property of morphisms of Noetherian adic rings is invariant under isomorphism of
targets. -/
theorem propertyIsInvariantUnderTargetIsoOn_of_propertyIsLocalNoetherianUpToIso
    (hP : TopologicalRing.PropertyIsLocalNoetherianUpToIso.{u} P) :
    PropertyIsInvariantUnderTargetIsoOn.{u}
      (fun R _ _ _ _ ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P :=
  hP.propertyIsInvariantUnderTargetIsoOn (fun _ _ _ _ _ h ↦ Rig.weaklyAdmissible_of_isAdicRing h.1)
    (fun _ _ _ _ _ h ↦ Rig.countablyGenerated_nhds_of_isAdicRing h.1)

end AlgebraicGeometry.FormalSpace

end
