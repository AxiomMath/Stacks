module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFunctorial

/-!
# Base change of the conormal module reduces to the map of defining ideal sheaves

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `Z` a closed subspace of `X` and `Z'` a closed subspace of `X'`.  Stacks 04CQ asserts that
for a *cartesian* such square the canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of Stacks 04CP is
surjective, and that it is an isomorphism when `g` is flat.

Both assertions are about a composite whose first factor is already known to be invertible:
`AlgebraicGeometry.Space.conormalMap` is the comparison
`AlgebraicGeometry.Space.conormalPullbackComparison`, an isomorphism, followed by the inverse
image along `i` of the map `g^*𝓘' ⟶ 𝓘` of defining ideal sheaves.  So each assertion is an
assertion about `AlgebraicGeometry.Space.idealSheafMap` alone, and surjectivity transfers because
the inverse image of modules is a left adjoint and a left adjoint preserves epimorphisms.

## Main results

* `AlgebraicGeometry.Space.epi_conormalMap_of_epi_idealSheafMap`: **the surjectivity clause of
  Stacks 04CQ, reduced to the map of defining ideal sheaves.**  If `g^*𝓘' ⟶ 𝓘` is surjective
  then so is `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}`.  This is the companion of
  `AlgebraicGeometry.Space.isIso_conormalMap_of_isIso_idealSheafMap`, which does the same for the
  invertibility clause.
* `AlgebraicGeometry.Space.isIso_conormalMap_iff_mono_of_epi_idealSheafMap`: under the same
  hypothesis the invertibility clause is **injectivity**: `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` is an
  isomorphism exactly when it is a monomorphism.  Modules on the small étale site are a balanced
  category, so surjectivity, which the hypothesis already gives, is half of invertibility.

## Implementation notes

**The attribute carries a clause string, not the bare tag.**  The statement below assumes
surjectivity of `AlgebraicGeometry.Space.idealSheafMap`, which Stacks 04CQ does not assume — the
source assumes instead that the square is cartesian — so what is claimed is the reduction, and the
clause string says so.  The convention is that of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModule_of_h03DO` and of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback`.

**Why the reduction is all that is available here.**  Deducing surjectivity, or invertibility, of
`AlgebraicGeometry.Space.idealSheafMap` from cartesianness and flatness of `g` is out of reach of
this development, and the obstruction is not about conormal modules.  The source proves Stacks
04CQ by passing to surjective étale scheme charts of `X` and of `X'` and quoting the scheme-level
statement, Stacks 0473; of that statement only the surjectivity clause is carried here, as
`Stacks.Immersion.epi_immersionConormalSheafMap`, and the flat clause is absent.  Nor is the
passage to charts available for the source of the map: `g` is flat, not étale, and
`AlgebraicGeometry.Space.modulePullback` has a sectionwise description
(`AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj`, read through
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`) only along an étale morphism.
Along a general morphism it is an inverse image followed by an extension of scalars, each of them
a sheafification, and this development has neither left exactness of it under a flatness
hypothesis nor a stalkwise description of it, so no criterion applies to a morphism out of
`(modulePullback g).obj 𝓘'`.

**The two-way forms are not stated.**  That `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` is surjective, resp.
invertible, *exactly* when the inverse image along `i` of `g^*𝓘' ⟶ 𝓘` is — the algebraic-space
counterpart of the ringed-space `Stacks.ClosedImmersion.isIso_conormalSheafMap_iff` — is true by
the same cancellation, but the converse halves need `Epi (c ≫ m)`, resp. `IsIso (c ≫ m)`, to be
read off a hypothesis about `AlgebraicGeometry.Space.conormalMap` in an instance argument.  That
comparison exhausts the default heartbeat budget, and only the forward halves are needed for
Stacks 04CQ.

## References

* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The surjectivity clause of Stacks 04CQ, reduced to the map of defining ideal sheaves.**
If the map `g^*𝓘' ⟶ 𝓘` of `AlgebraicGeometry.Space.idealSheafMap` attached to a commutative
square of closed subspaces is surjective, then so is the map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of
conormal modules of [Stacks Project, Tag 04CP].

`AlgebraicGeometry.Space.conormalMap` is the isomorphism
`AlgebraicGeometry.Space.conormalPullbackComparison` followed by the inverse image along the
inclusion of `Z` of the map of defining ideal sheaves.  The inverse image of modules is a left
adjoint, by the adjunction of [Stacks Project, Tag 03LU], and a left adjoint preserves
epimorphisms.

Surjectivity of `g^*𝓘' ⟶ 𝓘` is what [Stacks Project, Tag 04CQ] obtains from cartesianness of the
square, by reduction to the scheme-level [Stacks Project, Tag 0473]; that reduction is not
carried in this development, so the hypothesis is assumed.  The invertibility clause reduces the
same way, by `AlgebraicGeometry.Space.isIso_conormalMap_of_isIso_idealSheafMap`. -/
@[stacks 04CQ "surjectivity, reduced to surjectivity of the map of defining ideal sheaves"]
theorem epi_conormalMap_of_epi_idealSheafMap
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (h : Epi (idealSheafMap B S hS Z Z' g f hsq)) :
    Epi (conormalMap B S hS Z Z' g f hsq) := by
  have : (modulePullback B S hS (subspaceInclusion B S hS X Z)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z))
  rw [conormalMap]
  refine epi_comp'
    (@IsIso.epi_of_iso _ _ _ _ _ (isIso_conormalPullbackComparison B S hS Z Z' g f hsq)) ?_
  exact @Functor.map_epi _ _ _ _ _ _ _ _ _ h

/-- **Once the map of defining ideal sheaves is surjective, the invertibility clause of
[Stacks Project, Tag 04CQ] is injectivity.**  If `g^*𝓘' ⟶ 𝓘` is surjective then
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` is an isomorphism exactly when it is a monomorphism.

Surjectivity of the conormal map is `AlgebraicGeometry.Space.epi_conormalMap_of_epi_idealSheafMap`
and modules on the small étale site of an algebraic space form a balanced category, so an
epimorphism that is a monomorphism is invertible.  Both the surjectivity clause of that tag and
the conormal-module condition of [Stacks Project, Tag 06BH] are therefore reached from one
hypothesis on `AlgebraicGeometry.Space.idealSheafMap` plus injectivity.

No tag is placed: the hypothesis is the surjectivity that those two tags derive from
cartesianness of the square, which this development does not derive. -/
theorem isIso_conormalMap_iff_mono_of_epi_idealSheafMap
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (h : Epi (idealSheafMap B S hS Z Z' g f hsq)) :
    IsIso (conormalMap B S hS Z Z' g f hsq) ↔ Mono (conormalMap B S hS Z Z' g f hsq) := by
  have := epi_conormalMap_of_epi_idealSheafMap B S hS Z Z' g f hsq h
  exact ⟨fun _ => inferInstance, fun _ => isIso_of_mono_of_epi _⟩

end AlgebraicGeometry.Space

end
