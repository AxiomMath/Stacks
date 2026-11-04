module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.Modification
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Tautological
public import StacksCore.Tactic.StacksAttribute

/-!
# Filtrations with invertible quotients after a modification, with nothing carried

On an integral scheme `X` a finite locally free module `ℰ` of rank `r` acquires, after pullback
along a modification `f : X' ⟶ X`, a filtration of length `r` whose successive quotients are
invertible `𝒪_{X'}`-modules. This is [Stacks, Tag 0AYP].

`Stacks.ProjectiveBundleSplitting.exists_modification_hasInvertibleFiltration_of_epi` proves it
from one input: that the tautological map `π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` of the projective bundle of a
finite locally free module on an integral scheme is an epimorphism. That input is
`Stacks.ProjectiveBundleSplitting.epi_tautologicalMap`, so the theorem holds with the source's
hypotheses and no others.

## Main results

* `Stacks.ProjectiveBundleSplitting.exists_modification_hasInvertibleFiltration'`:
  **Tag 0AYP**.

## References

* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.WeilCohomology (HasInvertibleFiltration)

universe u

namespace Stacks.ProjectiveBundleSplitting

/-- **Stacks Project, Tag 0AYP.** Let `X` be an integral scheme and `ℰ` a finite locally free
`𝒪_X`-module of rank `r`. There is a modification `f : X' ⟶ X` such that `f^*ℰ` has a filtration
`0 = ℰ_0 ⊆ ℰ_1 ⊆ … ⊆ ℰ_r = f^*ℰ` by finite locally free submodules whose successive quotients
are invertible `𝒪_{X'}`-modules.

This is `exists_modification_hasInvertibleFiltration_of_epi` with its one input, the epimorphy
of the tautological map of a projective bundle, supplied by `epi_tautologicalMap`. -/
@[stacks 0AYP]
theorem exists_modification_hasInvertibleFiltration' (r : ℕ) (X : Scheme.{u}) [IsIntegral X]
    (E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X), IsModification f ∧
      HasInvertibleFiltration X' ((Scheme.Modules.pullback f).obj E) r :=
  exists_modification_hasInvertibleFiltration_of_epi
    (fun _ _ F _ hqcF => epi_tautologicalMap F hqcF) r X E hE

end Stacks.ProjectiveBundleSplitting

end
