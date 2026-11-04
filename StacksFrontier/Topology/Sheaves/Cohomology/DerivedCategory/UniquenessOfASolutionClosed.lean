module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCoherenceClosed
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessNonDegenerateWitness

/-!
# The uniqueness clause of Tag 0D68, on one equation between canonical comparisons

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it
(Situation 0D67).  The uniqueness clause of [Stacks, Tag 0D68] was reduced, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolutionFromTheSite`, to
the coherence of the two restrictions of morphisms, and that coherence was reduced, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCoherence`, to a single
equation between the two canonical comparisons, with no system involved:

```
canonicalCompareIso K hTW hWO = overMapCompareIso K hTW
```

This file runs the rest of the chain off that equation.  Granted it — as the hypothesis `hcan`,
which quantifies over the open `O`, the object `K` and the two inclusions, and mentions no system
— the coherence holds for *every* system, hence the uniqueness clause on the source's own
hypotheses (1) and (2), hence the non-degenerate witness on `Spec (ℤ × ℤ)` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessNonDegenerateWitness`.

## Main results

* `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom_of_canonical` — the coherence
  between `Stacks.DerivedGlueing.restrictHomBelow` and
  `AlgebraicGeometry.RingedSite.restrictDerivedHom`, for every system, granted `hcan`.
* `Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_of_canonical` — clause (a) of
  [Stacks, Tag 0D68] on hypotheses (1) and (2) of the tag, granted `hcan`.
* `Stacks.DerivedGlueing.exists_unique_solutionIso_nonDegenerate_of_canonical` — the same at a
  covering collection on `Spec (ℤ × ℤ)` that does not contain the whole space, where the already
  unconditional single-member case
  `Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem` does not apply.

## What is granted, and why

Exactly one thing, `hcan`, and it mentions no system.  By
`Stacks.DerivedGlueing.canonicalCompareIso_eq_of_forall_Q` it is enough to have it at the class
of a complex; by `Stacks.DerivedGlueing.restrictionCompareIso_trans_eq_canonical` it then gives
the coherence for every system at once.

No `@[stacks]` attribute is attached: every statement below is conditional on `hcan`, and a
conditional statement must not be registered for Tag 0D68.  The hypothesis `hcan` is discharged in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolutionUnconditional`, and
it is `Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_unconditional` there — the
unconditional form of the second statement below — that carries the uniqueness clause of the tag.

## References

* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe u

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The coherence between the two restrictions of morphisms, granted the identification of the
two canonical comparisons.** -/
theorem restrictHomBelow_eq_restrictDerivedHom_of_canonical (S : LocallyGiven X)
    (hcan : ∀ {O : Opens X.carrier} (K : OpenDerivedCategory X O) {T W : Opens X.carrier}
      (hTW : T ≤ W) (hWO : W ≤ O), canonicalCompareIso K hTW hWO = overMapCompareIso K hTW)
    {O : Opens X.carrier} (K L : OpenDerivedCategory X O) {T W : Opens X.carrier}
    (hTW : T ≤ W) (hWO : W ≤ O)
    (phi : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L) :
    homEquivSlice S K L (hTW.trans hWO) (restrictHomBelow S hTW hWO phi) =
      RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)
        (homEquivSlice S K L hWO phi) :=
  restrictHomBelow_eq_restrictDerivedHom_of_compareIso S K L hTW hWO
    ((restrictionCompareIso_trans_eq_canonical S K hTW hWO).trans (hcan K hTW hWO))
    ((restrictionCompareIso_trans_eq_canonical S L hTW hWO).trans (hcan L hTW hWO)) phi

/-- **Clause (a) of [Stacks, Tag 0D68], granted the identification of the two canonical
comparisons.** -/
theorem exists_unique_solutionIso_of_covers_of_canonical (S : LocallyGiven X)
    (hcan : ∀ {O : Opens X.carrier} (K : OpenDerivedCategory X O) {T W : Opens X.carrier}
      (hTW : T ≤ W) (hWO : W ≤ O), canonicalCompareIso K hTW hWO = overMapCompareIso K hTW)
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : Solution S) :
    ∃! ψ : A.obj ≅ B.obj, A.IsCompatibleHom B ψ.hom :=
  exists_unique_solutionIso_of_covers_of_coherence S
    (restrictHomBelow_eq_restrictDerivedHom_of_canonical S hcan) hcover hinter hExt A B

/-- **The non-degenerate witness, granted the identification of the two canonical
comparisons.** -/
theorem exists_unique_solutionIso_nonDegenerate_of_canonical
    (hcan : ∀ {O : Opens (specULiftProdRingedSpace.{u}).carrier}
      (K : OpenDerivedCategory specULiftProdRingedSpace.{u} O)
      {T W : Opens (specULiftProdRingedSpace.{u}).carrier} (hTW : T ≤ W) (hWO : W ≤ O),
      canonicalCompareIso K hTW hWO = overMapCompareIso K hTW)
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤))
    (A B : Solution (nonDegenerateSystem.{u} F)) :
    ∃! ψ : A.obj ≅ B.obj, A.IsCompatibleHom B ψ.hom :=
  exists_unique_solutionIso_nonDegenerate F A B
    (restrictHomBelow_eq_restrictDerivedHom_of_canonical (nonDegenerateSystem.{u} F) hcan)

end Stacks.DerivedGlueing

end
