module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.CanonicalSectionsWithSupportTriangle
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Data.ZMod.Basic

/-!
# A non-degenerate instance of the triangle for sections with support

[Stacks, Tag 0G71] is stated for a ringed space `X` and a closed subset `Z`, and both
extreme cases make a term of the triangle vanish: for `Z = ∅` the first term is zero, and
for `Z = X` the third term is.  This file exhibits a ringed space and a closed subset that
is neither, so the triangle of
`Stacks.Cohomology.SectionsWithSupport.canonicalSectionsWithSupportTriangle_distinguished`
is not vacuous, and instantiates that theorem there.

The space is `Spec (ULift ℤ)` at an arbitrary universe `u`, so the witness lives at the same
universe as the theorem and is not pinned to `Type 0`.  The closed subset is the zero locus
of `2`; the prime `(2)` lies in it and the generic point `(0)` does not.

## Main results

* `closedSet_isClosed`, `closedSet_ne_empty`, `closedSet_ne_univ`: the witness closed subset
  is closed, non-empty and proper.
* `triangle_distinguished`: [Stacks, Tag 0G71] at this witness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SectionsWithSupport

universe u

namespace Stacks.Cohomology.SectionsWithSupport.Witness

attribute [local instance] HasDerivedCategory.standard

/-- The witness ringed space `Spec (ULift ℤ)`, at an arbitrary universe. -/
public noncomputable abbrev space : RingedSpace.{u, u} :=
  (Spec (CommRingCat.of (ULift.{u} ℤ))).toRingedSpace

/-- Reduction modulo `2`, used to name a prime containing `2`. -/
public abbrev reductionMod2 : ULift.{u} ℤ →+* ZMod 2 :=
  (Int.castRingHom (ZMod 2)).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom

/-- The map to the rationals, used to name the generic point. -/
public abbrev toRationals : ULift.{u} ℤ →+* ℚ :=
  (Int.castRingHom ℚ).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom

/-- The witness closed subset: the zero locus of `2`. -/
public abbrev closedSet : Set space.{u} := PrimeSpectrum.zeroLocus {ULift.up (2 : ℤ)}

/-- The witness subset `closedSet` is closed. -/
public lemma closedSet_isClosed : IsClosed closedSet.{u} :=
  PrimeSpectrum.isClosed_zeroLocus _

/-- Reduction modulo `2` sends `2` to `0`. -/
public lemma reductionMod2_two : reductionMod2.{u} (ULift.up (2 : ℤ)) = 0 := by
  change ((2 : ℤ) : ZMod 2) = 0
  decide

/-- The map to the rationals does not send `2` to `0`. -/
public lemma toRationals_two : toRationals.{u} (ULift.up (2 : ℤ)) ≠ 0 := by
  change ((2 : ℤ) : ℚ) ≠ 0
  norm_num

/-- The prime `(2)`, a point of the witness closed subset. -/
public abbrev pointIn : space.{u} :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  PrimeSpectrum.comap reductionMod2 ⟨⊥, Ideal.isPrime_bot⟩

/-- The generic point `(0)`, a point outside the witness closed subset. -/
public abbrev pointOut : space.{u} :=
  PrimeSpectrum.comap toRationals ⟨⊥, Ideal.isPrime_bot⟩

/-- The prime `(2)` lies in the witness closed subset. -/
public lemma pointIn_mem : pointIn.{u} ∈ closedSet.{u} :=
  Set.singleton_subset_iff.2 (Ideal.mem_bot.2 reductionMod2_two.{u})

/-- The generic point `(0)` does not lie in the witness closed subset. -/
public lemma pointOut_notMem : pointOut.{u} ∉ closedSet.{u} := fun h =>
  toRationals_two.{u} (Ideal.mem_bot.1 (h (Set.mem_singleton _)))

/-- The witness closed subset is non-empty, so the first term of the triangle is not forced
to vanish. -/
public lemma closedSet_ne_empty : closedSet.{u} ≠ ∅ := fun h => by
  have hm := pointIn_mem.{u}
  rw [h] at hm
  exact hm

/-- The witness closed subset is proper, so the open complement is non-empty and the third
term of the triangle is not forced to vanish. -/
public lemma closedSet_ne_univ : closedSet.{u} ≠ Set.univ := fun h =>
  pointOut_notMem.{u} (h ▸ Set.mem_univ _)

/-- A named object of `D(O_X)` at the witness: the unit module sheaf placed in degree `0`. -/
public noncomputable abbrev object : DerivedModuleSheaves space.{u} :=
  DerivedCategory.Q.obj
    ((HomologicalComplex.single (ModuleSheaves space.{u}) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (structureSheafRing space.{u})))

/-- [Stacks, Tag 0G71] at the witness, for an arbitrary object of `D(O_X)`. -/
public theorem triangle_distinguished (K : DerivedModuleSheaves space.{u}) :
    canonicalSectionsWithSupportTriangle space.{u} closedSet.{u} closedSet_isClosed.{u} K ∈
      distTriang (DerivedGlobalModules space.{u}) :=
  canonicalSectionsWithSupportTriangle_distinguished space closedSet closedSet_isClosed K

/-- [Stacks, Tag 0G71] at the witness and at the named object. -/
public theorem triangle_distinguished_at_object :
    canonicalSectionsWithSupportTriangle space.{u} closedSet.{u} closedSet_isClosed.{u}
        object.{u} ∈ distTriang (DerivedGlobalModules space.{u}) :=
  triangle_distinguished object

end Stacks.Cohomology.SectionsWithSupport.Witness
