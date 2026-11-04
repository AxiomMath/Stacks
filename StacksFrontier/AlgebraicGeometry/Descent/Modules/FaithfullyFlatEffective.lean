module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.EffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent of modules along a faithfully flat ring map

Stacks 023N says that for a faithfully flat ring map `R → A` every descent datum on modules is
effective and that base extension `M ↦ (A ⊗[R] M, can)` is an equivalence onto the category of
descent data.  The equivalence of effective descent with universal injectivity is Stacks 08XA,
already available as
`ModuleCat.isEffectiveDescentMorphismForModules_iff_universallyInjective`, so the whole content
of Stacks 023N is the implication *faithfully flat ⇒ universally injective*, which is
Stacks 08WP.

## Main results

* `Algebra.UniversallyInjective.of_faithfullyFlat`: a faithfully flat algebra map is universally
  injective.
* `ModuleCat.baseExtension_essSurj_of_faithfullyFlat`: part (1) of Stacks 023N — every descent
  datum on modules along a faithfully flat ring map is effective.
* `ModuleCat.isEffectiveDescentMorphismForModules_of_faithfullyFlat`: part (2) of Stacks 023N —
  base extension along a faithfully flat ring map is an equivalence onto descent data.
* `ModuleCat.baseExtensionFullyFaithfulOfFaithfullyFlat`: the full faithfulness contained in
  that equivalence, which is the form in which descent of morphisms is consumed.

## Implementation notes

Stacks 08WP is already discharged in this repository, by
`faithfullyFlat_universallyInjective` (tagged through the `add_to_stacks 08WP` of
`StacksFrontier/AlgebraicGeometry/Descent/UniversallyInjective/Defs.lean`), so
`Algebra.UniversallyInjective.of_faithfullyFlat` carries no `@[stacks 08WP]` attribute.  It is
nevertheless not a duplicate: `faithfullyFlat_universallyInjective` takes a bare ring
homomorphism `φ` and states universal injectivity of `Algebra.linearMap` for the algebra
structure `φ.toAlgebra` that it builds itself.  At an ambient `[Algebra R A]` that is a
*different* term in the instance slot of `Algebra.linearMap R A`, so the conclusion does not
unify with `Algebra.UniversallyInjective R A` — which is what Stacks 08XA consumes — and no
universe instantiation repairs it.  The `Algebra`-instance form therefore has to be obtained
directly, from Mathlib's `Module.FaithfullyFlat.tensorProduct_mk_injective`.

Part (3) of Stacks 023N, that the inverse equivalence is `ModuleCat.pushforward` (the invariants
`H⁰` of the associated cosimplicial object), is proved in
`StacksFrontier/AlgebraicGeometry/Descent/Modules/InvariantsInverseFunctor.lean`, as
`Stacks.Descent.faithfullyFlatInvariantsEquivalence` together with
`Stacks.Descent.faithfullyFlatInvariantsEquivalence_inverse`.  It is not proved here because it
needs the unit and the counit of the base-extension/invariants pair as natural isomorphisms,
whereas `ModuleCat.isEffectiveDescentMorphismForModules_iff_universallyInjective` only produces
the equivalence objectwise.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 08WP](https://stacks.math.columbia.edu/tag/08WP)
* [Stacks Project, Tag 08XA](https://stacks.math.columbia.edu/tag/08XA)
-/

@[expose] public section

open scoped TensorProduct

universe u w

/-- A faithfully flat algebra map is universally injective: for every `R`-module `Q` the map
`R ⊗[R] Q → A ⊗[R] Q` induced by `R → A` is injective.  This is the `Algebra`-instance form of
Stacks 08WP; see the implementation notes for why it is stated separately. -/
theorem Algebra.UniversallyInjective.of_faithfullyFlat (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.FaithfullyFlat R A] : Algebra.UniversallyInjective R A := by
  intro Q _ _
  have h : Function.Injective (TensorProduct.mk R A Q 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective Q
  have hfac : ⇑((TensorProduct.mk R A Q) 1) =
      ((Algebra.linearMap R A).rTensor Q) ∘ ((_root_.TensorProduct.lid R Q).symm) := by
    funext q
    simp
  rw [hfac] at h
  intro x y hxy
  obtain ⟨x', rfl⟩ := (_root_.TensorProduct.lid R Q).symm.surjective x
  obtain ⟨y', rfl⟩ := (_root_.TensorProduct.lid R Q).symm.surjective y
  exact congrArg _ (h hxy)

namespace ModuleCat

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]

/-- **Stacks 023N, part (2).** For a faithfully flat ring map `R → A`, base extension
`M ↦ (A ⊗[R] M, can)` is an equivalence from `R`-modules onto the category of descent data for
modules along `R → A`. -/
@[stacks 023N "(2)",
  sga "1 VIII 1.6" "effectivity",
  sga "1 VIII 1.1" "affine case",
  sga "4½ Arcata 1.4.5" "affine case", sga "4½ Arcata 1.4" "module equivalence"]
theorem isEffectiveDescentMorphismForModules_of_faithfullyFlat :
    IsEffectiveDescentMorphismForModules.{u, u, w} R A :=
  (isEffectiveDescentMorphismForModules_iff_universallyInjective R A).mpr
    (.of_faithfullyFlat R A)

/-- **Stacks 023N, part (1).** Every descent datum on modules along a faithfully flat ring map
`R → A` is effective, that is, lies in the essential image of base extension. -/
@[stacks 023N "(1)",
  sga "1 VIII 1.6" "effectivity",
  sga "1 VIII 1.1" "affine case, effectivity",
  sga "4½ Arcata 1.4.5" "ess. surj. (affine)"]
theorem baseExtension_essSurj_of_faithfullyFlat :
    (baseExtension.{u, u, w} R A).functor.EssSurj :=
  have := isEffectiveDescentMorphismForModules_of_faithfullyFlat.{u, w} R A
  inferInstance

/-- Descent of morphisms of modules along a faithfully flat ring map: base extension is fully
faithful.  This is the half of `ModuleCat.isEffectiveDescentMorphismForModules_of_faithfullyFlat`
that the full faithfulness statements of Stacks 023S and Stacks 023T consume. -/
noncomputable def baseExtensionFullyFaithfulOfFaithfullyFlat :
    (baseExtension.{u, u, w} R A).functor.FullyFaithful :=
  have := isEffectiveDescentMorphismForModules_of_faithfullyFlat.{u, w} R A
  .ofFullyFaithful _

end ModuleCat

end
