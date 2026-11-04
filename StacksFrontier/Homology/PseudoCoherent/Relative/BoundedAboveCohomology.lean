module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.Homology.PseudoCoherent.Locality

@[expose] public section

/-!
# Relative pseudo-coherence of a bounded-above complex, cohomology form

The cohomological variant of Stacks 0677.

## Main results

* `PseudoCoherence.relativelyPseudoCoherent_of_boundedAbove_cohomology` (Stacks 0678).

## Implementation notes

One polynomial presentation at a time, reducing to tag 066B over the polynomial algebra;
066B is cluster 10's, in `Homology/PseudoCoherent/Module.lean`.

## References

* [The Stacks Project, Lemma 15.82.10 (0678)](https://stacks.math.columbia.edu/tag/0678)
-/

open CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-!
# Relative pseudo-coherence from relatively pseudo-coherent cohomology

Let `A` be a finite-type algebra over a commutative ring `R`. A cohomologically bounded-above
object of the derived category of `A`-modules is relatively `m`-pseudo-coherent when its
cohomology in degree `i` is relatively `(m - i)`-pseudo-coherent. Consequently, if all its
cohomology modules are relatively pseudo-coherent, then so is the object.

## Main definitions

No new definitions are introduced.

## Main results

* `relativelyPseudoCoherent_of_boundedAbove_cohomology`
  gives the cohomological criteria for relative pseudo-coherence.

## Implementation notes

Membership in the bounded-above derived category is expressed by eventual vanishing of the
homology objects. The fixed-degree and unqualified assertions of the source are packaged in a
conjunction.

## References

* [Stacks Project, Tag 0678](https://stacks.math.columbia.edu/tag/0678)
-/

private noncomputable def restrictedHomologyIso
    {S : Type*} {B : Type*} [CommRing S] [CommRing B] (g : S →+* B)
    (K : DerivedCategory (ModuleCat.{u} B)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj
        ((ModuleCat.restrictScalars g).mapDerivedCategory.obj K) ≅
      (ModuleCat.restrictScalars g).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj K) :=
  (_root_.StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (ModuleCat.restrictScalars g) i).app K

private noncomputable def restrictedSingleHomologyIso
    {S : Type*} {B : Type*} [CommRing S] [CommRing B] (g : S →+* B)
    (K : DerivedCategory (ModuleCat.{u} B)) (i : ℤ) :
    (ModuleCat.restrictScalars g).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj K)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj
          ((ModuleCat.restrictScalars g).mapDerivedCategory.obj K)) :=
  ((ModuleCat.restrictScalars g).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).mapIso
      (restrictedHomologyIso g K i).symm

/-- **Stacks 0678.** A cohomologically bounded-above derived object whose cohomology modules
are relatively pseudo-coherent in the corresponding degrees is relatively pseudo-coherent. -/
@[stacks 0678]
public theorem relativelyPseudoCoherent_of_boundedAbove_cohomology
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (hK : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    ((∀ i : ℤ, IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) (m - i)) →
      IsRelativelyPseudoCoherentFrom (R := R) K m) ∧
    ((∀ i : ℤ, IsModuleRelativelyPseudoCoherent (R := R) (A := A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) →
      IsRelativelyPseudoCoherent (R := R) K) := by
  obtain ⟨b, hb⟩ := hK
  have key (m : ℤ) (h : ∀ i : ℤ, IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) (m - i)) :
      IsRelativelyPseudoCoherentFrom (R := R) K m := fun n f hf ↦
    (pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove_cohomology
      ((ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory.obj K)
      ⟨b, fun i hi ↦ ((ModuleCat.restrictScalars f.toRingHom).map_isZero (hb i hi)).of_iso
        (restrictedHomologyIso f.toRingHom K i)⟩).1 m
      fun i ↦ isPseudoCoherentFrom_of_iso (h i n f hf) (restrictedSingleHomologyIso f.toRingHom K i)
  exact ⟨key m, fun h m ↦ key m fun i ↦ h i (m - i)⟩

end PseudoCoherence
