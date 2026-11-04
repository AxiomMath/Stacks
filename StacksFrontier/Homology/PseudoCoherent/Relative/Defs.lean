module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksFrontier.Algebra.Homology.PseudoCoherent

@[expose] public section

/-!
# Pseudo-coherence relative to a base ring

Let `A` be a finite-type algebra over a commutative ring `R`. An object of `D(A)` is
`m`-pseudo-coherent *relative to `R`* when, after restriction of scalars along a polynomial
presentation of `A` over `R`, it is `m`-pseudo-coherent over that polynomial algebra; it is
pseudo-coherent relative to `R` when this holds for every `m`. The corresponding notions for
a module are obtained by placing it in degree zero.

## Main definitions

* `PseudoCoherence.IsRelativelyPseudoCoherentFrom` (Stacks 065I (1));
* `PseudoCoherence.IsRelativelyPseudoCoherent` (Stacks 065I (2));
* `PseudoCoherence.IsModuleRelativelyPseudoCoherentFrom` (Stacks 065I (3));
* `PseudoCoherence.IsModuleRelativelyPseudoCoherent` (Stacks 065I (4)).

## Implementation notes

Complexes are represented by their objects in the derived category, and a module by its image
under the degree-zero single-object functor.

The definition quantifies over *every* finite polynomial presentation of `A` over `R`. Stacks
065H shows that one presentation suffices, so nothing is lost by the stronger-looking
formulation; taking the universal form here makes the four predicates usable without carrying a
choice of presentation, and Stacks 065H is what lets a caller discharge them from a single one.

Fixed-degree pseudo-coherence over the polynomial algebra is
`StacksDraft.PseudoCoherence.IsPseudoCoherentFrom`, which carries tag 064Q (1) in
`StacksFrontier/Algebra/Homology/PseudoCoherent.lean`. It applies here unchanged: what is being
tested is the restriction of scalars of `K` along the presentation, an object of the derived
category of the polynomial algebra like any other. So this module carries no tag and imports
no tagged module, and the four predicates it defines are stated entirely in the conceptual vocabulary.

## References

* [The Stacks Project, Definition 15.82.4 (065I)](https://stacks.math.columbia.edu/tag/065I)
* [The Stacks Project, Lemma 15.82.3 (065H)](https://stacks.math.columbia.edu/tag/065H)
-/

open CategoryTheory

namespace PseudoCoherence

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- Fixed-degree pseudo-coherence transports along an isomorphism in the derived category. -/
public lemma isPseudoCoherentFrom_of_iso {R : Type u} [Ring R]
    {K L : DerivedCategory (ModuleCat.{v} R)} {m : ℤ}
    (h : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom K m) (e : K ≅ L) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom L m := by
  obtain ⟨E, hE, a, ha, ha'⟩ := h
  refine ⟨E, hE, a ≫ e.hom, ?_, ?_⟩
  · intro i hi
    have := ha i hi
    simp only [Functor.map_comp]
    infer_instance
  · have := ha'
    simp only [Functor.map_comp]
    infer_instance

/-- Fixed-degree pseudo-coherence is invariant under an isomorphism in the derived category. -/
public lemma isPseudoCoherentFrom_iso_iff {R : Type u} [Ring R]
    {K L : DerivedCategory (ModuleCat.{v} R)} (e : K ≅ L) (m : ℤ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom K m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom L m :=
  ⟨fun h => isPseudoCoherentFrom_of_iso h e, fun h => isPseudoCoherentFrom_of_iso h e.symm⟩

/-- **Stacks 065I (1).** An object of `D(A)` is `m`-pseudo-coherent relative to `R` if its
restriction of scalars along every finite polynomial presentation of `A` over `R` is
`m`-pseudo-coherent. By Stacks 065H it is equivalent to require this of one presentation. -/
@[stacks 065I "(1)"]
public def IsRelativelyPseudoCoherentFrom
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective f →
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory.obj K) m

/-- **Stacks 065I (2).** An object of `D(A)` is pseudo-coherent relative to `R` if it is
`m`-pseudo-coherent relative to `R` for every integer `m`. -/
@[stacks 065I "(2)"]
public def IsRelativelyPseudoCoherent
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∀ m : ℤ, IsRelativelyPseudoCoherentFrom (R := R) K m

/-- **Stacks 065I (3).** An `A`-module is `m`-pseudo-coherent relative to `R` if the object
concentrated in degree zero that it determines has that property. -/
@[stacks 065I "(3)"]
public def IsModuleRelativelyPseudoCoherentFrom
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : Type u) [AddCommGroup M] [Module A M] (m : ℤ) : Prop :=
  IsRelativelyPseudoCoherentFrom (R := R)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) m

/-- **Stacks 065I (4).** An `A`-module is pseudo-coherent relative to `R` if the object
concentrated in degree zero that it determines has that property. -/
@[stacks 065I "(4)"]
public def IsModuleRelativelyPseudoCoherent
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : Type u) [AddCommGroup M] [Module A M] : Prop :=
  IsRelativelyPseudoCoherent (R := R)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))

/-- Relative pseudo-coherence is relative `m`-pseudo-coherence for every `m`, by definition. -/
public theorem isRelativelyPseudoCoherent_iff_forall
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat.{u} A)) :
    IsRelativelyPseudoCoherent (R := R) K ↔
      ∀ m : ℤ, IsRelativelyPseudoCoherentFrom (R := R) K m :=
  Iff.rfl

/-- A module is pseudo-coherent relative to `R` exactly when it is relatively
`m`-pseudo-coherent for every `m`. -/
public theorem isModuleRelativelyPseudoCoherent_iff_forall
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : Type u) [AddCommGroup M] [Module A M] :
    IsModuleRelativelyPseudoCoherent (R := R) (A := A) M ↔
      ∀ m : ℤ, IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) M m :=
  Iff.rfl

end PseudoCoherence
