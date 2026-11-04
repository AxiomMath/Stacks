module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalClosedSubschemeAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicClosedSubschemeRigidity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 09ZT in the two packagings that Stacks 0A42 and Stacks 0899 consume

`AlgebraicGeometry.exists_finite_algebraization_of_adicFiniteSystem`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/FiniteAlgebraization.lean`) is Stacks 09ZT with
Grothendieck existence for finite sheaves of algebras carried as the hypothesis `halg`. Its
conclusion is also exactly what the two named hypotheses of the carriers of Stacks 0A42 and
Stacks 0899 ask for, once the existential quantifiers are regrouped. This file records the two
regroupings.

## Main results

* `adicFiniteAlgebraization_of_adicFiniteAlgebraAlgebraization_of_qcSeparatedFiniteType` — the
  packaging `AdicFiniteAlgebraization` that Stacks 0A42 consumes, asking `halg` only of a
  morphism that is separated, locally of finite type and quasi-compact.
* `adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization` — the packaging
  `AdicFiniteSystemAlgebraization` that Stacks 0899 consumes.

Together these make `AdicFiniteAlgebraAlgebraization` the single input behind all three of the
`halg` hypotheses of Stacks 09ZT, 0A42 and 0899: the named hypotheses of 0A42 and 0899 are not
assumptions independent of the one of 09ZT, and whatever discharges that one discharges them.

## Implementation notes

Neither identification is definitional. `AdicFiniteSystemAlgebraization` puts `W`, `g` and `k`
under one `∃` and the finiteness of `g` inside the conjunction, whereas the conclusion of
`exists_finite_algebraization_of_adicFiniteSystem` binds `k` under a second `∃` nested to the
right of `IsFinite`/`IsProper`; so the identification is the term below, not `rfl`.

No `@[stacks]` attribute is attached here: both statements are conditional on `halg`, and
Stacks 09ZT is registered on the content that is proved *from* `halg`, not on a repackaging of
`halg` itself.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Adic rigidity over a complete base -/

/-- **The uniqueness clause of Stacks 0A42 holds over a complete base.** For a Noetherian ring
`A` complete with respect to `I`, the predicate `AlgebraicGeometry.AdicMorphismRigidity` is
satisfied.

This is `AlgebraicGeometry.hom_ext_of_adicBaseChangeMap` supplied with
`Stacks.AdicClosedSubschemeRigidity.adicRigidity`. That lemma asks only that `fP` be proper and
`fW` separated, so
the `LocallyOfFiniteType` and `QuasiCompact` hypotheses of the predicate are not needed; neither
Grothendieck existence (Stacks 088C) nor the full faithfulness of completion (Stacks 0883)
enters. -/
@[ega "III 5.4.1" "injectivity of f ↦ f̂"]
public theorem adicMorphismRigidity (A : Type u) [CommRing A] (I : Ideal A) [IsNoetherianRing A]
    [IsAdicComplete I A] : AdicMorphismRigidity A I := fun fP fW hP hW _ _ a ha b hb h =>
  have : IsProper fP := hP
  have : IsSeparated fW := hW
  hom_ext_of_adicBaseChangeMap A I (Stacks.AdicClosedSubschemeRigidity.adicRigidity A I) fP fW a b
    ha hb h

/-- **Stacks 09ZT in the packaging that Stacks 0A42 consumes.** The hypothesis
`AlgebraicGeometry.AdicFiniteAlgebraization` of
`AlgebraicGeometry.existsUnique_algebraization_adicBaseChangeMap` is exactly the conclusion of
`exists_finite_algebraization_of_adicFiniteSystem` with the finiteness of the algebraized morphism
forgotten, so the latter discharges it.

`halg` is asked only of a morphism that is separated, locally of finite type and quasi-compact,
which is all `AdicFiniteAlgebraization` ever applies it to: those three are hypotheses of that
predicate, and the proof below introduces them before `halg` is used. Asked of an arbitrary
`fP : P ⟶ Spec A` the binder is not satisfiable from this chapter at all —
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraData` produces
`AdicFiniteAlgebraAlgebraization` exactly under those three instances, so the over-general form
could never be supplied even once the chapter's own binders are discharged. -/
public theorem adicFiniteAlgebraization_of_adicFiniteAlgebraAlgebraization_of_qcSeparatedFiniteType
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (halg : ∀ {P : Scheme.{u}} (fP : P ⟶ Spec (.of A)) [IsSeparated fP]
      [LocallyOfFiniteType fP] [QuasiCompact fP],
      AdicFiniteAlgebraAlgebraization A I fP) :
    AdicFiniteAlgebraization A I := by
  intro P fP hsep hft hqc Zn zToP tr htr hfinite hproper
  have := hsep
  have := hft
  have := hqc
  obtain ⟨Z, a, hafin, haproper, k, hcart, hka⟩ :=
    exists_finite_algebraization_of_adicFiniteSystem A I fP (halg fP) Zn zToP tr htr hfinite
      hproper
  exact ⟨Z, a, haproper, k, hcart, hka⟩

/-- **Stacks 09ZT in the packaging that Stacks 0899 consumes.** The hypothesis
`AlgebraicGeometry.AdicFiniteSystemAlgebraization` of
`AlgebraicGeometry.exists_closedImmersion_algebraization_of_isPullback` asks for exactly what
`exists_finite_algebraization_of_adicFiniteSystem` concludes, with the existential quantifiers
regrouped: it is the same `W`, the same finite `g : W ⟶ X` proper over `Spec A`, and the same maps
`kₙ` exhibiting each `Zₙ` as `W ×_{Spec A} Sₙ` over `g`. So the sheaf-of-algebras hypothesis of
Stacks 09ZT discharges it, and the `halg` of Stacks 0899 is not an assumption independent of the
`halg` of Stacks 09ZT. -/
public theorem adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (halg : AdicFiniteAlgebraAlgebraization A I f) :
    AdicFiniteSystemAlgebraization A I f := by
  intro Z j t hcart hfin hproper
  obtain ⟨W, g, hgfin, hgproper, k, hkcart, hkg⟩ :=
    exists_finite_algebraization_of_adicFiniteSystem A I f halg Z j t hcart hfin hproper
  exact ⟨W, g, k, hgfin, hgproper, hkcart, hkg⟩

end AlgebraicGeometry

end
