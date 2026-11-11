module

public import StacksFrontier.AlgebraicGeometry.Perfect.CoherentBaseCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperSupportGlobalSectionsPerfect
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology over a coherent base ring is coherent

Let `R` be a coherent ring, let `X` be a scheme of finite presentation over `R` and let `G` be an
`𝒪_X`-module of finite presentation, flat over `R`, with support proper over `R`. Then every
cohomology module `Hⁱ(X, G)` is a coherent `R`-module. This is [Stacks, Tag 0EX6].

## Main results

* `…CoherentBaseCohomology.isCoherent_rightDerived_moduleGlobalSections`:
  **[Stacks, Tag 0EX6]**, under exactly the source's hypotheses.

## Implementation notes

The proof is the source's: combine [Stacks, Tag 0A1H] with [Stacks, Tag 0658] and
[Stacks, Tag 0EWZ].

* [Stacks, Tag 0A1H], for `E = 𝒪_X` and the one-term complex `G` over the affine base `Spec R`,
  gives that `RΓ(X, G)` is a perfect object of `D(R)`. This is
  `…ProperSupportGlobalSectionsPerfect.isPerfect_derivedGlobalSectionsOverBase_of_properSupport`,
  which reads `AlgebraicGeometry.isPerfect_derivedPushforward_tensor` in `D(R)`.
* [Stacks, Tag 0658] and [Stacks, Tag 0EWZ] turn perfectness over the coherent ring `R` into
  coherence of every cohomology module; together with the identification of the cohomology of
  `RΓ(X, G)` with `Hⁱ(X, G)` this is
  `…CoherentBaseCohomology.isCoherent_cohomology_of_isPerfect_derivedGlobalSections`.

**Spelling of the hypotheses.** "Of finite presentation over `R`" is [Stacks, Tag 01TP] (3),
spelled out as its three constituent properties of `f : X ⟶ Spec R`. "Support proper over `R`"
is: the support of `G` is a closed subset `Z` of `X` that is proper over `R`
(`AlgebraicGeometry.IsProperOver`, [Stacks, Tag 0CYS]). `Hⁱ(X, G)` is the `i`-th right derived
functor of global sections, an `R`-module by restriction of scalars along `R ⟶ Γ(X, 𝒪_X)`; in
negative degrees there is nothing to prove, so `i` ranges over `ℕ`.

## References

* [Stacks Project, Tag 0EX6](https://stacks.math.columbia.edu/tag/0EX6)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
* [Stacks Project, Tag 0EWZ](https://stacks.math.columbia.edu/tag/0EWZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProperSupportGlobalSectionsPerfect

universe u

namespace Stacks.AlgebraicGeometry.CoherentBaseCohomology

/-- **[Stacks, Tag 0EX6].** Let `R` be a coherent ring, let `f : X ⟶ Spec R` be of finite
presentation and let `G` be an `𝒪_X`-module of finite presentation, flat over `R`, whose support
is proper over `R`. Then for every `i` the cohomology module `Hⁱ(X, G)`, with its `R`-action
restricted along `R ⟶ Γ(X, 𝒪_X)`, is a coherent `R`-module.

The source's proof: `RΓ(X, G)` is a perfect object of `D(R)` by [Stacks, Tag 0A1H]
(`…ProperSupportGlobalSectionsPerfect.isPerfect_derivedGlobalSectionsOverBase_of_properSupport`),
and over a coherent ring the cohomology modules of a perfect complex are coherent by
[Stacks, Tag 0658] and [Stacks, Tag 0EWZ]
(`isCoherent_cohomology_of_isPerfect_derivedGlobalSections`).

This is the complete statement of [Stacks, Tag 0EX6], hypothesis by hypothesis:
* "`R` is a coherent ring" is `[IsCoherentRing R]`;
* "`X` is of finite presentation over `R`" is `LocallyOfFinitePresentation f`, `QuasiCompact f`
  and `QuasiSeparated f` ([Stacks, Tag 01TP] (3));
* "`𝒢` is of finite presentation" is `[G.IsFinitePresentation]`;
* "flat over `R`" is `hflat`: every stalk of `G` is flat over the corresponding local ring of
  `Spec R` ([Stacks, Tag 08KT]);
* "with support proper over `R`" is `hsupp`: the support of `G` is a closed subset of `X`
  proper over `R` ([Stacks, Tag 0CYM]);
* "`Hⁱ(X, 𝒢)` is a coherent `R`-module" is the conclusion, for every `i : ℕ`; in negative
  degrees the cohomology vanishes. -/
@[stacks 0EX6 "Hⁱ(X, G) as the right derived functors of global sections, i ≥ 0"]
theorem isCoherent_rightDerived_moduleGlobalSections
    {R : Type u} [CommRing R] [IsCoherentRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (G : X.Modules) [G.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom G)
    (hsupp : ∃ Z : TopologicalSpace.Closeds X,
      (Z : Set X) = SheafOfModules.supp G ∧ IsProperOver f Z)
    (i : ℕ) :
    Module.IsCoherent R
      ((ModuleCat.restrictScalars (Stacks.Cech.globalRingHom f).hom).obj
        (((AlgebraicGeometry.moduleGlobalSections X).rightDerived i).obj G)) :=
  isCoherent_cohomology_of_isPerfect_derivedGlobalSections f G hflat hsupp
    (isPerfect_derivedGlobalSectionsOverBase_of_properSupport f G hflat
      (hsupp.imp fun _ h => ⟨h.2, h.1.symm.subset⟩)) i

end Stacks.AlgebraicGeometry.CoherentBaseCohomology

end
