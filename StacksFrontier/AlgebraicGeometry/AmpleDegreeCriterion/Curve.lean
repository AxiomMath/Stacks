module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Basic
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Basic

/-!
# Tag 0B5X: ampleness and degree on a proper curve

An invertible module on a proper curve over a field is ample exactly when its degree is
positive ([Stacks, Tag 0B5X]). This file assembles the two directions.

The forward direction is proved:
`AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_devissage` carries the dévissage of
[Stacks, Tag 01YH], the finite dimensionality of [Stacks, Tag 02O6] at the structure sheaf and
at the coherent modules supported in a proper closed subset, and [Stacks, Tag 0B40] part 2 as
hypotheses. The converse is
`AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_exists_isZero_h1_idealSheaf`, the criterion
of [Stacks, Tag 0B5P], applied to the cohomological vanishing that the source's third paragraph
derives from positivity of the degree — and *that* derivation is the one hypothesis carried
here, `hvan`.

## Main results

* `AlgebraicGeometry.isAmple_iff_degree_pos`: **both directions of [Stacks, Tag 0B5X]**, with
  the five inputs the library does not yet have carried as explicit hypotheses.

## What `hvan` is, and why it is an implication

The source's converse runs: from `deg 𝓛 > 0` the dimension of `H⁰(X, 𝓛^{⊗ n})` grows linearly,
so a nonzero section vanishing at a prescribed finite set exists, so some `X_s` is affine; then
for every quasi-coherent ideal sheaf `ℐ` the maps `ℐ ⊗ 𝓛^{⊗ mn} → ℐ ⊗ 𝓛^{⊗ (m+1)n}` given by
`s` are injective with cokernel supported off `X_s`, so by [Stacks, Tag 0B3J] the induced maps
on `H¹` are surjective; `H¹(X, ℐ)` is finite dimensional ([Stacks, Tag 02O6]) and every element
dies eventually ([Stacks, Tag 01XR]), so some `H¹(X, ℐ ⊗ 𝓛^{⊗ en})` vanishes. Only then does
[Stacks, Tag 0B5P] apply.

`hvan` is exactly that paragraph: *positivity of the degree implies the vanishing hypothesis of
Tag 0B5P*. It is stated as an implication rather than as a bare hypothesis on purpose. Assumed
unconditionally, the vanishing hypothesis makes `𝓛` ample outright, the left side of the
biconditional becomes constantly true, and what is left to prove is not Tag 0B5X but
`0 < deg 𝓛` — a statement the hypothesis set would then have to force. As an implication it
forces nothing: for every `𝓛` of non-positive degree `hvan` is inhabited vacuously, by
`fun h => absurd h hneg`, so the hypothesis set is consistent with both sides of the
biconditional being false. That is the joint-satisfiability guard that a biconditional with a
positivity condition on one side needs, and it is why `hvan` is not a bare hypothesis.

## Implementation notes

**The Stacks attribute for Tag 0B5X names the five carried hypotheses.** Five hypotheses that
the tag does not carry appear in the statement: `hdev` ([Stacks, Tag 01YH]), `hclosed` and
`hunit` ([Stacks, Tag 02O6]), `hpos` ([Stacks, Tag 0B40] part 2) and `hvan` (the paragraph
above, whose own inputs are [Stacks, Tag 0B3J], [Stacks, Tag 01XR] and [Stacks, Tag 02O6]
again). Four of the five are already the hypotheses of the forward direction; `hvan` is
what the converse adds. The attribute's label names all five, which is how the neighbouring
degree tags of this tree record the same situation — `@[stacks 0AYZ "with `hfin`
([Stacks, Tag 02O6] over a field) carried as a hypothesis"]` in
`../Variety/Curve/PullbackDegree.lean`. The statement is written so that discharging them is a
substitution and not an edit, which is what became of the `hfin` of
`../CurveDegreeTensor/Cohomological.lean`: [Stacks, Tag 02O6] over a field is a theorem of this
library, `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`, and
`hclosed` and `hunit` here are two of its instances.

The forward direction alone, with only the four inputs of the source's first paragraph and no
hypothesis mentioning cohomological vanishing, carries the tag separately as
`AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_inputs` of
`./Components.lean`.

**`hdim` is an explicit argument** because `AlgebraicGeometry.invertibleCurveDegree` takes the
dimension bound as an argument. On a curve it is `le_of_eq (IsCurve.topologicalKrullDim_eq_one
f)`, which is the instantiation the statement of Tag 0B5X uses; no separate declaration is needed for
it.

**Quasi-compactness is not a hypothesis.** `IsProper f` gives `QuasiCompact f`, and
`Spec (.of k)` is quasi-compact, so `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`
supplies the `CompactSpace X` that Tag 0B5P needs.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0B3J](https://stacks.math.columbia.edu/tag/0B3J)
* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules (nonvanishingLocus)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
-- (open removed: its only name was the merged moduleGlobalSections)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Both directions of [Stacks, Tag 0B5X].** On a proper curve over a field an invertible
module is ample exactly when its degree is positive, given the five inputs the library does not
yet have:

* `hdev` is the dévissage of [Stacks, Tag 01YH];
* `hclosed` and `hunit` are [Stacks, Tag 02O6] at the coherent modules supported in a proper
  closed subset and at the structure sheaf;
* `hpos` follows from [Stacks, Tag 0B40] part 2;
* `hvan` is the source's third paragraph: positivity of the degree gives, for every closed
  subscheme, a positive power killing `H¹` of its ideal sheaf twisted by that power.

The forward direction is
`AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_devissage`; the converse is
`AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_exists_isZero_h1_idealSheaf`, the criterion
of [Stacks, Tag 0B5P], fed by `hvan`.

The tag's label names the five carried hypotheses; see the implementation notes of this file. -/
-- No `@[stacks 0B5X]` registration here: this statement takes five inputs the source proves
-- rather than assumes — `hdev` ([Stacks, Tag 01YH]), `hclosed` and `hunit` ([Stacks, Tag 02O6]),
-- `hpos` ([Stacks, Tag 0B40] part 2) and `hvan` (the source's third paragraph). Four of the five
-- are now discharged in `CurveInputs.lean`, where the forward implication carries the tag
-- unconditionally; the biconditional is registered once `hvan` is proved too.
public theorem isAmple_iff_degree_pos [IsCurve k f] [IsProper f]
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hunit : ∀ m,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m))
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hpos : ∀ n : ℕ, 1 ≤ n → ∀ s : (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        (∃ x : X, x ∈ nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) →
        nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ≠ Set.univ →
        0 < @invertibleCurveDegree k _ X f _ hdim
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ))
          (tensorPower_isInvertible X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)))
    (hvan : 0 < invertibleCurveDegree k f hdim L →
      ∀ {Z : Scheme.{u}} (i : Z ⟶ X), IsClosedImmersion i → ∃ n : ℕ, 1 ≤ n ∧
        IsZero (((moduleGlobalSections X).rightDerived 1).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
            ((tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ))))))) :
    Scheme.Modules.IsAmple X L ↔ 0 < invertibleCurveDegree k f hdim L := by
  refine ⟨invertibleCurveDegree_pos_of_isAmple_of_devissage k f hdev hclosed hunit hdim L hpos,
    fun hdeg => ?_⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact Scheme.Modules.isAmple_of_forall_exists_isZero_h1_idealSheaf L (hvan hdeg)

end AlgebraicGeometry

end
