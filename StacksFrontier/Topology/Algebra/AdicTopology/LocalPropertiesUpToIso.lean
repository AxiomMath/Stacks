module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties

/-!
# Local properties of continuous ring maps, with the completed corners up to isomorphism

In the diagram (87.21.2.1) of Situation 0CBA, the upper corners are written
`(A')^∧ = lim A'/IA'` and `(B')^∧ = lim B'/JB'`. A limit is determined only up to unique
isomorphism, so the diagram admits any topological ring with an isomorphism of topological rings
onto the inverse limit. `TopologicalRing.LocalizationDiagram` fixes these corners as the
particular types `TopologicalRing.CompletionOver D.toA'` and `TopologicalRing.CompletionOver
D.toB'`. Its locality axioms, `TopologicalRing.LocalizationPreserves` and
`TopologicalRing.FaithfullyFlatDescent`, therefore only move a property between a ring and these
particular types. Nothing in them relates a ring to another ring isomorphic to it, so they do not
give the invariance under isomorphism that the Stacks Project reads off axiom (1).

This file states the axioms with the completed corners up to isomorphism. Axioms (1) and (2) are
asked of every `TopologicalRing.LocalizationDiagram` `D` together with isomorphisms of
topological rings `CompletionOver D.toA' ≃+* Â` and `CompletionOver D.toB' ≃+* B̂`, for the map
`B̂ → Â` they induce. Axiom (3) is unchanged. The resulting notion,
`TopologicalRing.PropertyIsLocalUpToIso`, is defined once for an arbitrary class `C` of rings. It
implies `TopologicalRing.PropertyIsLocal`, by taking both isomorphisms to be identities, so every
result proved for the literal notion transfers. Invariance under isomorphism of source and of
target follows from axiom (1) alone, as in the source, an isomorphism being étale and a complete
ring being its own completion.

## Main definitions

* `TopologicalRing.LocalizationPreservesUpToIso`, `TopologicalRing.FaithfullyFlatDescentUpToIso`:
  axioms (1) and (2) of Situation 0CBA, with the completed corners taken up to isomorphism.
* `TopologicalRing.PropertyIsLocalUpToIso`: a local property in the sense of Situation 0CBA,
  for an arbitrary class of rings.
* `TopologicalRing.PropertyIsLocalAdicStarUpToIso`: its specialisation to `WAdm^{adic*}`, the
  definition of Stacks 0ANH.
* `TopologicalRing.PropertyIsLocalNoetherianUpToIso`: its specialisation to the Noetherian adic
  rings, the definition of Stacks 0ANI.

## Main results

* `TopologicalRing.PropertyIsLocalUpToIso.toPropertyIsLocal`: a local property in this sense is
  local in the sense of `TopologicalRing.PropertyIsLocal`.

## References

* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
-/


@[expose] public section

namespace TopologicalRing

universe u

section

/-- **Axiom (1) of Situation 0CBA, with the completed corners up to isomorphism.** For every
localization diagram `D` between rings of the class `C`, and every pair of topological rings
`Â`, `B̂` of the class identified with the completions `CompletionOver D.toA'` and
`CompletionOver D.toB'` by isomorphisms of topological rings, `P(φ)` implies `P(φ')` for the
induced map `φ' : B̂ → Â`. -/
public abbrev LocalizationPreservesUpToIso
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop) : Prop :=
  ∀ {A B A' B' Ahat Bhat : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing A'] [CommRing B']
    [CommRing Ahat] [TopologicalSpace Ahat] [IsTopologicalRing Ahat] [IsLinearTopology Ahat Ahat]
    [CommRing Bhat] [TopologicalSpace Bhat] [IsTopologicalRing Bhat] [IsLinearTopology Bhat Bhat]
    (D : LocalizationDiagram A B A' B')
    (eA : CompletionOver D.toA' ≃+* Ahat) (eB : CompletionOver D.toB' ≃+* Bhat),
    Continuous eA → Continuous eA.symm → Continuous eB → Continuous eB.symm →
    C A → C B → C Ahat → C Bhat →
      P D.map → P ((eA.toRingHom.comp D.completedMap).comp eB.symm.toRingHom)

/-- **Axiom (2) of Situation 0CBA, with the completed corners up to isomorphism.** For every
localization diagram `D` between rings of the class `C` with `A → A'` faithfully flat, and every
pair of topological rings `Â`, `B̂` of the class identified with the completions by isomorphisms
of topological rings, `P(φ')` for the induced map `φ' : B̂ → Â` implies `P(φ)`. -/
public abbrev FaithfullyFlatDescentUpToIso
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop) : Prop :=
  ∀ {A B A' B' Ahat Bhat : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing A'] [CommRing B']
    [CommRing Ahat] [TopologicalSpace Ahat] [IsTopologicalRing Ahat] [IsLinearTopology Ahat Ahat]
    [CommRing Bhat] [TopologicalSpace Bhat] [IsTopologicalRing Bhat] [IsLinearTopology Bhat Bhat]
    (D : LocalizationDiagram A B A' B')
    (eA : CompletionOver D.toA' ≃+* Ahat) (eB : CompletionOver D.toB' ≃+* Bhat),
    Continuous eA → Continuous eA.symm → Continuous eB → Continuous eB.symm →
    C A → C B → C Ahat → C Bhat → D.toA'.FaithfullyFlat →
      P ((eA.toRingHom.comp D.completedMap).comp eB.symm.toRingHom) → P D.map

/-- **A local property of Situation 0CBA.** A property `P` of morphisms of a class `C` of
countably indexed weakly admissible rings is local when axioms (1) and (2) hold for every diagram
(87.21.2.1), whose completed corners are any rings isomorphic to the inverse limits
`lim A'/IA'` and `lim B'/JB'`, and axiom (3) holds for finite products of targets. -/
public structure PropertyIsLocalUpToIso
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop)
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop := IsCountablyWeaklyAdmissible) : Prop where
  /-- Axiom (1): `P` passes from `φ` to the induced map of completed corners, these being any
  rings isomorphic to the completions. -/
  localizationPreserves : LocalizationPreservesUpToIso C P
  /-- Axiom (2): `P` descends from the induced map of completed corners to `φ` along a faithfully
  flat `A → A'`, the corners being any rings isomorphic to the completions. -/
  faithfullyFlatDescent : FaithfullyFlatDescentUpToIso C P
  /-- Axiom (3): `P` is stable under finite products of targets. -/
  finiteProduct : FiniteProductPreserves C P

/-- Taking both completed corners to be the completions themselves, a local property with the
completed corners up to isomorphism is local in the sense of `TopologicalRing.PropertyIsLocal`. -/
public theorem PropertyIsLocalUpToIso.toPropertyIsLocal
    {P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop}
    {C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop}
    (h : PropertyIsLocalUpToIso P C) : PropertyIsLocal P C where
  localizationPreserves := by
    intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hP
    have key := h.localizationPreserves D (RingEquiv.refl _) (RingEquiv.refl _)
      continuous_id continuous_id continuous_id continuous_id hA hB hA' hB' hP
    exact key
  faithfullyFlatDescent := by
    intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hff hP
    exact h.faithfullyFlatDescent D (RingEquiv.refl _) (RingEquiv.refl _)
      continuous_id continuous_id continuous_id continuous_id hA hB hA' hB' hff hP
  finiteProduct := h.finiteProduct

end

section

/-- A property `P` of morphisms of `WAdm^{adic*}`, the adic topological rings possessing a
finitely generated ideal of definition, is local when axioms (1), (2) and (3) of Situation 0CBA
hold for morphisms of `WAdm^{adic*}`. The completed corners of the diagrams of axioms (1) and (2)
are any rings isomorphic to the inverse limits. -/
@[stacks 0ANH "the first half, the definition of a local property of morphisms of WAdm^{adic*}: \
axioms (1), (2), (3) of Situation 0CBA for morphisms of WAdm^{adic*}, the completed corners of \
the diagram being any limits lim A'/IA', lim B'/JB'"]
public abbrev PropertyIsLocalAdicStarUpToIso (P : ∀ {B A : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A], (B →+* A) → Prop) : Prop :=
  PropertyIsLocalUpToIso P
    (fun R => IsAdic R ∧ ∃ I : Ideal R, IsIdealOfDefinition I ∧ I.FG)

/-- A property `P` of morphisms of `WAdm^{Noeth}`, the adic topological rings whose underlying
ring is Noetherian, is local when axioms (1), (2) and (3) of Situation 0CBA hold for morphisms of
`WAdm^{Noeth}`. The completed corners of the diagrams of axioms (1) and (2) are any rings
isomorphic to the inverse limits. -/
@[stacks 0ANI "the definition of a local property of morphisms of WAdm^Noeth: axioms (1), (2), \
(3) of Situation 0CBA for morphisms of WAdm^Noeth, the completed corners of the diagram being any \
limits lim A'/IA', lim B'/JB'"]
public abbrev PropertyIsLocalNoetherianUpToIso (P : ∀ {B A : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A], (B →+* A) → Prop) : Prop :=
  PropertyIsLocalUpToIso P (fun R => IsAdic R ∧ IsNoetherianRing R)

end

end TopologicalRing

end
