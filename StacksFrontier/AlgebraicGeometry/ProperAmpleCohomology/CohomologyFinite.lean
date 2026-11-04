module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic

/-!
# Finiteness of the cohomology of a coherent module on a proper scheme over a Noetherian ring

[Stacks, Tag 0B5T] says: let `R` be a Noetherian ring, let `X ⟶ Spec R` be proper, let `ℒ` be an
ample invertible `𝒪_X`-module and let `ℱ` be a coherent `𝒪_X`-module. Then

1. the graded ring `A = ⨁_{d ≥ 0} H⁰(X, ℒ ^⊗ d)` is a finitely generated `R`-algebra;
2. there are an `r ≥ 0`, integers `d₁, …, d_r` and a surjection `⨁_{j} ℒ ^⊗ dⱼ ↠ ℱ`;
3. `H ᵖ(X, ℱ)` is a finite `R`-module for every `p`;
4. `H ᵖ(X, ℱ ⊗ ℒ ^⊗ d) = 0` for `p > 0` and all `d` large enough;
5. for every `k ∈ ℤ` the graded `A`-module `⨁_{d ≥ k} H⁰(X, ℱ ⊗ ℒ ^⊗ d)` is a finite `A`-module.

**This file proves clause (3), and it proves it with neither the ample invertible module nor any
hypothesis beyond [Stacks, Tag 02O6]'s own.** `ProperAmpleCohomology/Basic.lean` proves clauses
(2) and (4).

## The route, and the route the sibling file predicted

`ProperAmpleCohomology/Basic.lean` records clause (3) as "blocked above, on [Stacks, Tag 01VT]
clause (5), through clause (3) of [Stacks, Tag 01YS]". That is not the only
route: [Stacks, Tag 02O6] — the finiteness of `Hⁱ(Y, 𝒢)` as a module
over a Noetherian `R` for `g : Y ⟶ Spec R` proper and `𝒢` coherent — is proved unconditionally as
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, and its transport of scalars
from `Γ(Spec R, ⊤)` to `R` is
`Stacks.AlgebraicGeometry.GradedProperCohomology.tag02O6`. Clause (3) of [Stacks, Tag 0B5T] is
exactly that proposition instantiated at the tag's own data; no projective embedding and no
ampleness enter.

## The spelling of the cohomology module

`Hᵖ(X, ℱ)` is `Stacks.AlgebraicGeometry.GradedProperCohomology.cohomologyOf X p ℱ`, the `p`-th
right derived functor of global sections of `𝒪_X`-modules, which is a module over `Γ(X, ⊤)`; the
`R`-module structure is restriction of scalars along
`Stacks.AlgebraicGeometry.GradedProperCohomology.specAlgebraRingHom R f`, the ring map
`R →+* Γ(X, ⊤)` that `f : X ⟶ Spec R` induces on global functions. This is the spelling in which
[Stacks, Tag 02O6] is stated over a ring in this library, and the one [Stacks, Tag 0897] part (1)
consumes.

## Main results

* `Stacks.AlgebraicGeometry.ProperAmpleCohomology.moduleFinite_cohomology`: **clause (3)**, at the
  tag's own hypotheses.
* `Stacks.AlgebraicGeometry.ProperAmpleCohomology.moduleFinite_cohomology_of_isProper`: the same
  without the ample invertible module, which is the statement that is actually proved and the one
  to apply.

## References

* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample
open Stacks.AlgebraicGeometry.GradedProperCohomology

universe u

namespace Stacks.AlgebraicGeometry.ProperAmpleCohomology

/-! ### Clause (3), without the ample invertible module -/

/-- **Clause (3) of [Stacks, Tag 0B5T], with no ample invertible module.** For `R` a Noetherian
ring, `f : X ⟶ Spec R` proper and `ℱ` a coherent `𝒪_X`-module, the cohomology `Hᵖ(X, ℱ)` is a
finite `R`-module in every degree `p`.

This is `Stacks.AlgebraicGeometry.GradedProperCohomology.tag02O6`, i.e. [Stacks, Tag 02O6] read
over the base ring, applied at `f` and `ℱ`. -/
theorem moduleFinite_cohomology_of_isProper {X : Scheme.{u}} {R : Type u} [CommRing R]
    [IsNoetherianRing R] (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (p : ℕ) :
    Module.Finite R ((ModuleCat.restrictScalars (specAlgebraRingHom R f)).obj
      (cohomologyOf X p F)) :=
  tag02O6 R inferInstance X f inferInstance F inferInstance p

/-! ### Clause (3), at [Stacks, Tag 0B5T]'s own hypotheses -/

/-- **Clause (3) of [Stacks, Tag 0B5T].** Let `R` be a Noetherian ring, let `f : X ⟶ Spec R` be
proper, let `ℒ` be an ample invertible `𝒪_X`-module and let `ℱ` be a coherent `𝒪_X`-module. Then
`Hᵖ(X, ℱ)` is a finite `R`-module for every `p`.

This is `moduleFinite_cohomology_of_isProper` with the tag's remaining hypotheses bound; the
ample invertible module is not used, and the more general statement is the one to apply. The
tag's clause (3) is recorded here so that it sits on a declaration stating the clause in the
tag's own setting. -/
@[stacks 0B5T "clause (3), the finiteness of the cohomology of a coherent module over the \
Noetherian base ring"]
theorem moduleFinite_cohomology {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (F L : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [IsInvertibleModule X L] (_hL : IsAmple X L) (p : ℕ) :
    Module.Finite R ((ModuleCat.restrictScalars (specAlgebraRingHom R f)).obj
      (cohomologyOf X p F)) :=
  moduleFinite_cohomology_of_isProper f F p

end Stacks.AlgebraicGeometry.ProperAmpleCohomology

end
