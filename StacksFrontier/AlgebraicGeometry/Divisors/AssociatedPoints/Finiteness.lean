module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.Depth.FlatFibreAssociatedPrime
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# Finiteness of the sections of a finite type module on an affine open

For a quasi-coherent `𝒪_X`-module `F` of finite type on a scheme `X` and an affine open `U`,
the `Γ(X, U)`-module `Γ(F, U)` is finite. This file also collects the module-theoretic
transport lemmas for depth and for associated primes that the affine-local arguments about
associated points rely on.

## Main results

* `AlgebraicGeometry.moduleFinite_sections_on_affine`: the sections of a quasi-coherent module
  of finite type on an affine open form a finite module over the ring of functions.
* `AlgebraicGeometry.isFiniteType_of_scheme_iso`: being of finite type is invariant under an
  isomorphism of `𝒪_X`-modules.
* `isAssociatedPrimeStacks_iff_mem_associatedPrimes`: over a Noetherian ring the
  exact-annihilator notion of an associated prime agrees with Mathlib's.

## Implementation notes

Finiteness on an affine open is obtained by restricting `F` along `IsAffineOpen.fromSpec` and
invoking the global `Spec` case, which is Stacks tag 01PB; the identification of sections is
`AlgebraicGeometry.fromSpecSectionsLinearEquiv`.

## References

* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

/-- Alias of `Stacks.Depth.isAssociatedPrimeStacks_iff_mem_associatedPrimes`. -/
alias isAssociatedPrimeStacks_iff_mem_associatedPrimes :=
  Stacks.Depth.isAssociatedPrimeStacks_iff_mem_associatedPrimes

namespace AlgebraicGeometry

/-- Being of finite type is invariant under an isomorphism of `𝒪_X`-modules: generating
sections transport along the isomorphism. -/
lemma isFiniteType_of_scheme_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    [F.IsFiniteType] : SheafOfModules.IsFiniteType.{u, u, u} G := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let q' : G.LocalGeneratorsData.{u, u, u, u} :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i =>
        (q.generators i).ofEpi ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom }
  have hq' : SheafOfModules.LocalGeneratorsData.IsFiniteType.{u, u, u, u} q' := by
    constructor
    intro i
    dsimp [q']
    have hfin : (q.generators i).IsFiniteType := hq.isFiniteType i
    infer_instance
  exact SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨q', hq'⟩

/-- The global sections of a quasi-coherent module of finite type on an affine scheme form a
finite module. -/
lemma moduleFinite_of_isFiniteType_qc (R : CommRingCat.{u}) (F : (Spec R).Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] : Module.Finite (↑R) Γ(F, ⊤) := by
  have : (tilde (moduleSpecΓFunctor.obj F)).IsFiniteType :=
    isFiniteType_of_scheme_iso (asIso F.fromTildeΓ).symm
  exact (tilde_isFiniteType_iff (moduleSpecΓFunctor.obj F)).mp this

/-- The sections of a quasi-coherent module of finite type over an affine open form a finite
module over the ring of functions on that open. -/
lemma moduleFinite_sections_on_affine {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(F, U) := by
  have hpull : ((Scheme.Modules.pullback hU.fromSpec).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType hU.fromSpec.toLRSHom.toShHom F
  have hrestrict : (F.restrict hU.fromSpec).IsFiniteType :=
    isFiniteType_of_scheme_iso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app F).symm
  have hfinite : Module.Finite Γ(X, U) Γ(F.restrict hU.fromSpec, ⊤) :=
    moduleFinite_of_isFiniteType_qc (CommRingCat.of Γ(X, U)) (F.restrict hU.fromSpec)
  exact Module.Finite.of_surjective (fromSpecSectionsLinearEquiv F hU).toLinearMap
    (fromSpecSectionsLinearEquiv F hU).surjective

end AlgebraicGeometry
