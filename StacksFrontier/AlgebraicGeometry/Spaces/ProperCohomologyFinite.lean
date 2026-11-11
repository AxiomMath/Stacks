module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Finiteness of cohomology over the base: reduction to finitely many degrees

This file provides two pieces used around [Stacks, Tag 08AS] (for a Noetherian ring `A`, a
proper morphism of algebraic spaces `f : X ⟶ Spec A` and a coherent `𝒪_X`-module `F`, every
`H^i(X, F)` is a finite `A`-module).

* The transport layer for `AlgebraicGeometry.Space.cohomologyOverBase`: cohomology over the
  base ring is a functor, so isomorphic modules have isomorphic cohomology in every degree, and
  finiteness over the base transports along that isomorphism.  This is the analogue, for
  algebraic spaces, of the transport results that
  `StacksDraft.AlgebraicGeometry.F3.HigherDirectImageCoherent.Basic` supplies for the
  scheme-level [Stacks, Tag 02O5], and of
  `AlgebraicGeometry.finrank_cohomologyOverField_eq_of_iso` for a scheme over a field.
* A reduction: finiteness in every degree follows from finiteness in the finitely many degrees
  below a degree beyond which the cohomology vanishes (the vanishing being [Stacks, Tag 072C]).

[Stacks, Tag 08AS] itself is proved, from [Stacks, Tag 08AR], as
`AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_isProper_of_isCoherent` in
`StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyOverBaseFinite`, using the transport
result of this file; the reduction here is not needed for it.

## Main definitions

* `AlgebraicGeometry.Space.cohomologyOverBaseIso`: an isomorphism of `𝒪_X`-modules induces an
  `A`-linear isomorphism of their cohomology modules over the base ring, in every degree.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_isProper`: the cohomology over
  `A` of a coherent module on a proper algebraic space over `Spec A` is finite in every degree,
  given a vanishing bound and finiteness in the degrees below it.
* `AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_iso`: finiteness over the base
  ring of the cohomology of an `𝒪_X`-module in a given degree is invariant under isomorphism
  of the module.  No hypothesis on the base ring, on a morphism to the base, or on the module
  is used.

## Implementation notes

`AlgebraicGeometry.Space.cohomologyOverBase` is a composite of two functors — the derived
global sections of the small étale ringed site, and restriction of scalars along
`AlgebraicGeometry.Space.baseRingHom` — so an isomorphism of modules is carried to an
isomorphism of `A`-modules by `CategoryTheory.Functor.mapIso` twice.  No exactness and no
injective resolution is involved; the transport holds in every degree at once.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- For a Noetherian ring `A`, a proper algebraic space `X` over `Spec A` and a coherent
`𝒪_X`-module `F`, if `Hⁱ(X, F)` vanishes for `i ≥ N` and is a finite `A`-module for `i < N`,
then it is a finite `A`-module in every degree.  Properness and coherence are not used in the
proof.  Without the hypotheses `hvan` and `hlt` this is [Stacks, Tag 08AS],
`AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_isProper_of_isCoherent`. -/
theorem moduleFinite_cohomologyOverBase_of_isProper [IsNoetherianRing A]
    (f : X ⟶ CategoryTheory.yoneda.obj (baseObject A B hA))
    (_hf : IsProper B (Spec (.of A)) hA f)
    (F : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX)
    [IsCoherent B (Spec (.of A)) hA X hX F] (N : ℕ)
    (hvan : ∀ i, N ≤ i → Limits.IsZero (cohomologyOverBase.{u, w} A B hA X hX F i))
    (hlt : ∀ i < N, Module.Finite A (cohomologyOverBase.{u, w} A B hA X hX F i)) (i : ℕ) :
    Module.Finite A (cohomologyOverBase.{u, w} A B hA X hX F i) := by
  by_cases h : i < N
  · exact hlt i h
  · have := ModuleCat.subsingleton_of_isZero (hvan i (by omega))
    have : Finite (cohomologyOverBase.{u, w} A B hA X hX F i) := Finite.of_subsingleton
    infer_instance

/-- An isomorphism of `𝒪_X`-modules on an algebraic space over `Spec A` induces, in every
degree, an isomorphism of their cohomology modules over the base ring.

Both constituents of `AlgebraicGeometry.Space.cohomologyOverBase` are functors — the derived
global sections of the small étale ringed site, and restriction of scalars along
`AlgebraicGeometry.Space.baseRingHom` — so this is `CategoryTheory.Functor.mapIso` applied
twice. -/
def cohomologyOverBaseIso {M N : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX}
    (e : M ≅ N) (i : ℕ) :
    cohomologyOverBase.{u, w} A B hA X hX M i ≅ cohomologyOverBase.{u, w} A B hA X hX N i :=
  (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).mapIso
    ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
          i).mapIso e)

/-- **Finiteness of cohomology over the base ring is invariant under isomorphism of the
module.**  If an `𝒪_X`-module has cohomology of finite type over `A` in some degree, then so
does every module isomorphic to it, in that same degree.

This is the transport step that any dévissage towards [Stacks, Tag 08AS] needs first, and it
is unconditional: no Noetherian hypothesis on `A`, no morphism `X ⟶ Spec A`, no properness and
no coherence enter.  The isomorphism of `A`-modules is
`AlgebraicGeometry.Space.cohomologyOverBaseIso`, read as a linear equivalence. -/
theorem moduleFinite_cohomologyOverBase_of_iso
    {M N : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX} (e : M ≅ N) (i : ℕ)
    [Module.Finite A (cohomologyOverBase.{u, w} A B hA X hX M i)] :
    Module.Finite A (cohomologyOverBase.{u, w} A B hA X hX N i) :=
  Module.Finite.equiv (cohomologyOverBaseIso.{u, w} A B hA X hX e i).toLinearEquiv

end AlgebraicGeometry.Space

end
