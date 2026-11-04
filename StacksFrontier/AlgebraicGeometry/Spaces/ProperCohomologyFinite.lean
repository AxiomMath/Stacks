module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Finite cohomology of a proper algebraic space over an affine base

[Stacks, Tag 08AS] asserts that for a Noetherian ring `A`, a proper morphism of algebraic
spaces `f : X ⟶ Spec A` and a coherent `𝒪_X`-module `F`, every cohomology module
`H^i(X, F)` is a finite `A`-module.  That conclusion is reached here, in every degree, from
finiteness in the finitely many degrees below a degree beyond which the cohomology vanishes —
the vanishing being [Stacks, Tag 072C] and the finiteness below it being the one place where
[Stacks, Tag 08AR] is used.  The implementation notes record what blocks a direct proof of
[Stacks, Tag 08AR] here, including an obstruction that is not merely an unproved input.

Alongside it the file provides the transport layer that every argument about the finiteness of
`AlgebraicGeometry.Space.cohomologyOverBase` needs before it can begin: cohomology over the
base ring is a functor, so isomorphic modules have isomorphic cohomology in every degree, and
finiteness over the base transports along that isomorphism.  This is the exact analogue, for
algebraic spaces, of the transport results that
`StacksDraft.AlgebraicGeometry.F3.HigherDirectImageCoherent.Basic` supplies for the
scheme-level [Stacks, Tag 02O5], and of
`AlgebraicGeometry.finrank_cohomologyOverField_eq_of_iso` for a scheme over a field.

## Main definitions

* `AlgebraicGeometry.Space.cohomologyOverBaseIso`: an isomorphism of `𝒪_X`-modules induces an
  `A`-linear isomorphism of their cohomology modules over the base ring, in every degree.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_isProper`: **[Stacks, Tag 08AS].**
  The cohomology over `A` of a coherent module on a proper algebraic space over `Spec A` is a
  finite `A`-module in every degree, given finiteness in the degrees below a vanishing bound.
* `AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_iso`: finiteness over the base
  ring of the cohomology of an `𝒪_X`-module in a given degree is invariant under isomorphism
  of the module.  No hypothesis on the base ring, on a morphism to the base, or on the module
  is used.

## Implementation notes

**Why Tag 08AR is not proved here.**  The source's proof of Tag 08AS is: the higher direct image
`R^i f_* F` is quasi-coherent ([Stacks, Tag 0720]), hence is the module associated to
`Γ(Spec A, R^i f_* F) = H^i(X, F)` ([Stacks, Tag 0733] together with the vanishing of higher
cohomology of quasi-coherent modules on an affine, [Stacks, Tag 01XB]); `R^i f_* F` is
coherent exactly when `H^i(X, F)` is of finite type ([Stacks, Tag 07UB]); and `R^i f_* F`
*is* coherent by [Stacks, Tag 08AR].  Three independent things stand in the way.

1. [Stacks, Tag 08AR] is absent, and so is its scheme-level counterpart
   [Stacks, Tag 02O5]: see the implementation notes of
   `StacksDraft.AlgebraicGeometry.F3.HigherDirectImageCoherent.Basic`, which record that
   dévissage for coherent modules, Chow's lemma, the relative Leray spectral sequence and the
   vanishing for relatively ample invertible sheaves are all missing.  Correspondingly the
   scheme-level statements of `StacksDraft.AlgebraicGeometry.F3b.EulerCharAdditivity.Basic`
   carry finite-dimensionality of cohomology as an explicit hypothesis rather than deriving
   it.

2. There are no higher direct images of modules along a morphism of algebraic spaces at all.
   The ordinary direct image is
   `AlgebraicGeometry.Space.modulePushforward`, and it exists only as a functor
   `Modules.{u, u} ⥤ Modules.{u, u}`.  The implementation notes of
   `StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage`, which is where the underlying
   `AlgebraicGeometry.Space.modulePushforwardOfStructureMap` is built, explain that the module
   universe is forced to be the universe of the structure rings, because the direct image of
   the underlying sheaves of sets is available only there.

3. The two universes do not meet.  `AlgebraicGeometry.Space.cohomologyOverBase` is built from
   `Stacks.Cohomology.SiteModules.globalModuleCohomology`, which is [Stacks, Tag 071H] for an
   arbitrary ringed site and whose module universe must contain
   the universe of the site; the small étale site of an algebraic space over a `Scheme.{u}` is
   `AlgebraicGeometry.Space.RingedSite.{u + 1, u, u}`, so that universe is `max (u + 1) w`
   and is never `u`.  Hence `R^i f_* F` is not merely unproved but cannot be *written* at the
   universe at which the cohomology of Tag 08AS lives: it would be a derived functor of a
   functor that does not exist there.  Generalizing
   `AlgebraicGeometry.Space.modulePushforward` to a free module universe is therefore a
   prerequisite of Tag 08AS over and above Tag 08AR.

For the same reason the dévissage step of the proof of [Stacks, Tag 08AR] — finiteness for the
middle term of a short exact sequence — is not available either:
`Stacks.Cohomology.SiteModules.exists_universal_cohomologyDeltaFunctor`, which is the only
long exact cohomology sequence in the library for cohomology of modules on a site, is stated
for a `CategoryTheory.SmallCategory` site and for
`Stacks.Cohomology.SiteModules.cohomologyFunctor`, whose module universe equals the site's.
The small étale site is only `CategoryTheory.EssentiallySmall.{u}`, with objects in
`Type (u + 1)`.

**What is transported.**  `AlgebraicGeometry.Space.cohomologyOverBase` is a composite of two
functors — the derived global sections of the small étale ringed site, and restriction of
scalars along `AlgebraicGeometry.Space.baseRingHom` — so an isomorphism of modules is carried
to an isomorphism of `A`-modules by `CategoryTheory.Functor.mapIso` twice.  No exactness and
no injective resolution is involved; in particular the transport holds in every degree at
once and needs none of the inputs listed above.

**How Tag 08AS is nevertheless stated.**  Finiteness in a degree above a vanishing bound is
free, so the conclusion of Tag 08AS in *every* degree follows from its conclusion in the
finitely many degrees below such a bound; that reduction is
`AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_isProper`, which carries the bound
and the finiteness below it as the hypotheses `hvan` and `hlt`.  The bound is supplied by
[Stacks, Tag 072C] in
`StacksFrontier.AlgebraicGeometry.Spaces.CohomologicalDimension`, uniformly in the coherent
module; `hlt` is where [Stacks, Tag 08AR] is needed and is not discharged anywhere.  The
transport results carry no `@[stacks]` attribute, being no part of Tag 08AS.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
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

/-- **Stacks 08AS.**  For a Noetherian ring `A`, a proper algebraic space `X` over `Spec A` and
a coherent `𝒪_X`-module `F`, every cohomology module `Hⁱ(X, F)` is a finite `A`-module: above
the vanishing bound `N` the module is zero, hence finite, and below it finiteness is assumed.
Properness and coherence are the hypotheses under which the bound and that finiteness hold and
are used nowhere in the proof. -/
@[stacks 08AS "with the finiteness in the degrees below the vanishing bound carried as the \
hypothesis hlt, that being the one step needing Stacks 08AR, whose higher direct images cannot \
be written at the module universe of cohomologyOverBase"]
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
