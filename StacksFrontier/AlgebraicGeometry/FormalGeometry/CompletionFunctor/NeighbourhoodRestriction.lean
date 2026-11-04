module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.ExtensionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicArtinRees
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternative
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer

/-!
# Passing from a neighbourhood `V` of the formal locus to `U`

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, put `U = Spec(A) ∖ V(𝔞)` and let `𝒱` be the
open subschemes of `U` containing `U ∩ V(I)`, ordered by reverse inclusion. This file relates
modules on a member `V` of `𝒱` to modules on `U`: the condition on the associated points of a
module on `U` bounding the dimension of their closures only concerns the associated points lying
in `V`, the members of `𝒱` contained in `V` are cofinal in `𝒱`, and every coherent module on `V`
satisfying the condition extends to a coherent module on `U` satisfying it.

## Main definitions

* `Stacks.Algebraization.colimitSectionsNearVanishingUnderIso` — the cofinality isomorphism.
* `Stacks.Algebraization.AssociatedPointsClosureDimensionBoundOn` — the dimension condition on
  the associated points of a module on a member `V` of `𝒱`.

## Main results

* `Stacks.Algebraization.OpensNearVanishing.mem_openSet_of_le` — a point of `U` generizing a
  point of `U ∩ V(I)` lies in every member of `𝒱`.
* `Stacks.Algebraization.associatedPointsClosureDimensionBound_of_mem_openSet` — the dimension
  condition on a module on `U` from the condition at its associated points in `V`.
* `Stacks.Algebraization.associatedPointsClosureDimensionBound_of_isFiniteLocallyFree_restrict`
  — the dimension condition for a module finite locally free on `V`, from the dimension bound at
  the associated primes of `A`.
* `Stacks.Algebraization.exists_extension_associatedPointsClosureDimensionBound` — a coherent
  module on `V` satisfying the condition extends to a coherent module on `U` satisfying it.

## References

* [Stacks Project, Tag 0EIV](https://stacks.math.columbia.edu/tag/0EIV)
* [Stacks Project, Tag 0EKU](https://stacks.math.columbia.edu/tag/0EKU)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A] {I a : Ideal A}

/-- If the prime of `x ∈ U` is contained in a prime `y` containing `I` but not `𝔞`, then `x` lies
in every member `V` of `𝒱`. -/
theorem OpensNearVanishing.mem_openSet_of_le (V : OpensNearVanishing A I a)
    (x : (complementZeroLocus A a : Scheme)) (y : PrimeSpectrum A)
    (hxy : x.1.asIdeal ≤ y.asIdeal) (hyI : I ≤ y.asIdeal) (hya : ¬ a ≤ y.asIdeal) :
    x ∈ V.openSet := by
  let y' : (complementZeroLocus A a : Scheme) :=
    ⟨y, fun hy ↦ hya ((PrimeSpectrum.mem_zeroLocus _ _).1 hy)⟩
  have hsp : x ⤳ y' := Topology.IsInducing.subtypeVal.specializes_iff.1
    ((PrimeSpectrum.le_iff_specializes _ _).1 hxy)
  exact hsp.mem_open V.openSet.isOpen (V.contains_vanishing y' hyI)

/-- An associated point of a module on `U` lying in a member `V` of `𝒱` is an associated point of
its restriction to `V`. -/
private theorem mem_associatedPoints_restrict (V : OpensNearVanishing A I a)
    (F : (complementZeroLocus A a : Scheme).Modules) (x : (complementZeroLocus A a : Scheme))
    (hxV : x ∈ V.openSet) (hx : x ∈ Stacks.Divisors.associatedPoints F) :
    (⟨x, hxV⟩ : V.openSet.toScheme) ∈ Stacks.Divisors.associatedPoints (F.restrict V.openSet.ι) :=
  (Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff
    V.openSet.ι F ⟨x, hxV⟩).2 hx

variable [IsNoetherianRing A]

/-- For every member `V` of `𝒱`, the condition `AssociatedPointsClosureDimensionBound` for a
module `F` on `U` holds as soon as it holds at the associated points of `F` lying in `V`. -/
theorem associatedPointsClosureDimensionBound_of_mem_openSet (V : OpensNearVanishing A I a)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (h : ∀ x : (complementZeroLocus A a : Scheme), x ∈ Stacks.Divisors.associatedPoints F →
      x ∈ V.openSet → ¬ I ≤ x.1.asIdeal →
      (∃ y : PrimeSpectrum A, x.1.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, x.1.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
          krullDimToEInt (closureLocalDimension A x.1 z)) :
    AssociatedPointsClosureDimensionBound A I a F := by
  rintro x hx hxI ⟨y, hxy, hyI, hya⟩
  exact h x hx (V.mem_openSet_of_le x y hxy hyI hya) hxI ⟨y, hxy, hyI, hya⟩

omit [IsNoetherianRing A] in
/-- The colimit over `𝒱` of the sections of `F` near the formal locus is the colimit over the
members of `𝒱` contained in a fixed member `V`. -/
def colimitSectionsNearVanishingUnderIso (V : OpensNearVanishing A I a)
    (F : (complementZeroLocus A a : Scheme).Modules) :
    colimit (Under.forget V ⋙ sectionsNearVanishing A I a F) ≅
      colimit (sectionsNearVanishing A I a F) :=
  Functor.Final.colimitIso (Under.forget V) (sectionsNearVanishing A I a F)

/-- An associated point of a finite locally free module on a member `V` of `𝒱` has an associated
prime of `A` as its prime. -/
private theorem isAssociatedPrimeStacks_of_mem_associatedPoints
    (V : OpensNearVanishing A I a) (F : V.openSet.toScheme.Modules)
    (hF : Scheme.Modules.IsFiniteLocallyFree F) (x : V.openSet.toScheme)
    (hx : x ∈ Stacks.Divisors.associatedPoints F) :
    IsAssociatedPrimeStacks A A x.1.1.asIdeal :=
  Stacks.Divisors.isAssociatedPrimeStacks_of_mem_schemeAssociatedPoints
    (V.openSet.ι ≫ (complementZeroLocus A a).ι)
    (Stacks.Divisors.associatedPoints_subset_schemeAssociatedPoints_of_isFiniteLocallyFree _
      hF hx)

/-- Let `F` be a module on `U` whose restriction to a member `V` of `𝒱` is finite locally free,
and assume that for every associated prime `𝔭` of `A` with `I ⊄ 𝔭` and `V(𝔭) ∩ V(I) ⊄ V(𝔞)` and
every `𝔮 ∈ V(𝔭) ∩ V(𝔞)`, `dim((A/𝔭)_𝔮) > cd(A, I) + 1`. Then `F` satisfies
`AssociatedPointsClosureDimensionBound`. -/
theorem associatedPointsClosureDimensionBound_of_isFiniteLocallyFree_restrict
    (V : OpensNearVanishing A I a) (F : (complementZeroLocus A a : Scheme).Modules)
    (hF : Scheme.Modules.IsFiniteLocallyFree (F.restrict V.openSet.ι))
    (hdim : ∀ p : PrimeSpectrum A, IsAssociatedPrimeStacks A A p.asIdeal →
      ¬ I ≤ p.asIdeal →
      (∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, p.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
          krullDimToEInt (closureLocalDimension A p z)) :
    AssociatedPointsClosureDimensionBound A I a F := by
  refine associatedPointsClosureDimensionBound_of_mem_openSet V F fun x hx hxV ↦ ?_
  exact hdim x.1 (isAssociatedPrimeStacks_of_mem_associatedPoints V _ hF _
    (mem_associatedPoints_restrict V F x hxV hx))

/-! ### Modules on a neighbourhood and their coherent extensions to `U` -/

/-- The dimension condition on the associated points of a module `F` on a member `V` of `𝒱`:
whenever `x` is an associated point of `F` outside `V(I)` whose closure meets `V(I)` outside
`V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`. -/
def AssociatedPointsClosureDimensionBoundOn (V : OpensNearVanishing A I a)
    (F : V.openSet.toScheme.Modules) : Prop :=
  ∀ x : V.openSet.toScheme, x ∈ Stacks.Divisors.associatedPoints F →
    ¬ I ≤ x.1.1.asIdeal →
    (∃ y : PrimeSpectrum A, x.1.1.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
    ∀ z : PrimeSpectrum A, x.1.1.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (closureLocalDimension A x.1.1 z)

/-- If `F'` is a module on `U` whose restriction to a member `V` of `𝒱` is isomorphic to a module
`F` on `V` satisfying `AssociatedPointsClosureDimensionBoundOn`, then `F'` satisfies
`AssociatedPointsClosureDimensionBound`. -/
theorem associatedPointsClosureDimensionBound_of_restrictIso (V : OpensNearVanishing A I a)
    (F' : (complementZeroLocus A a : Scheme).Modules) (F : V.openSet.toScheme.Modules)
    (e : F'.restrict V.openSet.ι ≅ F) (h : AssociatedPointsClosureDimensionBoundOn V F) :
    AssociatedPointsClosureDimensionBound A I a F' := by
  refine associatedPointsClosureDimensionBound_of_mem_openSet V F' fun x hx hxV ↦ ?_
  exact h ⟨x, hxV⟩ ((Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_congr e
    ⟨x, hxV⟩).1 (mem_associatedPoints_restrict V F' x hxV hx))

/-- A coherent module `F` on `V ∈ 𝒱` is the restriction of a coherent module `F'` on `U` all of
whose associated points lie in `V`, and if `F` satisfies `AssociatedPointsClosureDimensionBoundOn`
then `F'` satisfies `AssociatedPointsClosureDimensionBound`. -/
theorem exists_extension_associatedPointsClosureDimensionBound (V : OpensNearVanishing A I a)
    (F : V.openSet.toScheme.Modules) [F.IsCoherent]
    (h : AssociatedPointsClosureDimensionBoundOn V F) :
    ∃ F' : AlgebraicGeometry.SheafOfModules.CoherentModules
        (complementZeroLocus A a : Scheme).ringCatSheaf,
      Nonempty (Scheme.Modules.restrict F'.obj V.openSet.ι ≅ F) ∧
        Stacks.Divisors.associatedPoints F'.obj ⊆ (V.openSet : Set _) ∧
        AssociatedPointsClosureDimensionBound A I a F'.obj := by
  have : IsNoetherian (complementZeroLocus A a : Scheme) := ⟨⟩
  obtain ⟨F', hF', ⟨e⟩, hass⟩ := exists_isCoherent_extension_associatedPoints_subset V.openSet F
  exact ⟨⟨F', hF'⟩, ⟨e⟩, hass, associatedPointsClosureDimensionBound_of_restrictIso V F' F e h⟩

/-- A finite locally free module on a member `V` of `𝒱` satisfies
`AssociatedPointsClosureDimensionBoundOn` as soon as the dimension bound holds at the associated
primes of `A`. -/
theorem associatedPointsClosureDimensionBoundOn_of_isFiniteLocallyFree
    (V : OpensNearVanishing A I a) (F : V.openSet.toScheme.Modules)
    (hF : Scheme.Modules.IsFiniteLocallyFree F)
    (hdim : ∀ p : PrimeSpectrum A, IsAssociatedPrimeStacks A A p.asIdeal →
      ¬ I ≤ p.asIdeal →
      (∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, p.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
          krullDimToEInt (closureLocalDimension A p z)) :
    AssociatedPointsClosureDimensionBoundOn V F := fun x hx ↦
  hdim x.1.1 (isAssociatedPrimeStacks_of_mem_associatedPoints V F hF x hx)

end Stacks.Algebraization

end
