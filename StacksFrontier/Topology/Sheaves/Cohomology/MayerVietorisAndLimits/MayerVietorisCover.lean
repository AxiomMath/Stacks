module

public import Mathlib.AlgebraicGeometry.Scheme
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.MayerVietorisCanonical
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# A two-open cover of a ringed space by proper opens

Stacks 08BV, in the form
`Stacks.Cohomology.MayerVietoris.exists_distinguished_triangle_of_cover_rightDerived`, applies to
a sheaf of rings `O` on a topological space together with two opens `U`, `V` satisfying
`U ⊔ V = ⊤`. That hypothesis has trivial solutions -- `U = ⊤` with `V = ⊤`, or `V = ⊥` -- at which
the triangle degenerates. This file exhibits a solution at which it does not: on the spectrum of
the integers, the basic opens of `2` and of `3` cover, and neither is the whole space.

## Main definitions

* `Stacks.Cohomology.MayerVietoris.Cover.specIntegers`: the spectrum of `ℤ` as a ringed space at a
  free universe, and `specIntegersSheaf` its structure sheaf read as a sheaf of rings.
* `Stacks.Cohomology.MayerVietoris.Cover.basicOpenTwo` and `basicOpenThree`: the basic opens of `2`
  and of `3`.

## Main results

* `Stacks.Cohomology.MayerVietoris.Cover.basicOpenTwo_sup_basicOpenThree`: the two basic opens
  cover the spectrum, because a prime containing both `2` and `3` would contain `3 - 2 = 1`.
* `Stacks.Cohomology.MayerVietoris.Cover.basicOpenTwo_ne_top` and `basicOpenThree_ne_top`: neither
  is the whole space, because `2` and `3` are not units of `ℤ`.
* `Stacks.Cohomology.MayerVietoris.Cover.exists_distinguished_triangle_specIntegers`: Stacks 08BV
  read at this cover, which is also the check that no instance binder of the general statement
  makes it uninstantiable at a concrete space.

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Cohomology.MayerVietoris.Cover

-- The model of `D(O)` is `local` in the file that states Stacks 08BV, so it has to be named
-- again to write the triangle out here; the priority is what keeps a global model from capturing
-- the occurrences, which shows up as a universe mismatch rather than as a missing instance.
attribute [local instance 10000] HasDerivedCategory.standard

/-- The spectrum of `ℤ`, at a free universe, as a ringed space. -/
def specIntegers : RingedSpace.{u, u} :=
  (Spec (CommRingCat.of (ULift.{u} ℤ))).toRingedSpace

/-- The structure sheaf of `Spec ℤ`, read as a sheaf of possibly noncommutative rings, which is
the shape in which Stacks 08BV takes it. -/
def specIntegersSheaf :
    Sheaf (Opens.grothendieckTopology specIntegers.{u}.carrier) RingCat.{u} :=
  structureSheafRing specIntegers.{u}

/-- The basic open of `2` in `Spec ℤ`. -/
def basicOpenTwo : Opens specIntegers.{u}.carrier :=
  PrimeSpectrum.basicOpen (ULift.up (2 : ℤ))

/-- The basic open of `3` in `Spec ℤ`. -/
def basicOpenThree : Opens specIntegers.{u}.carrier :=
  PrimeSpectrum.basicOpen (ULift.up (3 : ℤ))

/-- The basic opens of `2` and of `3` cover `Spec ℤ`: a prime containing both would contain
`3 - 2 = 1`. -/
theorem basicOpenTwo_sup_basicOpenThree : basicOpenTwo.{u} ⊔ basicOpenThree.{u} = ⊤ := by
  refine le_antisymm le_top fun p _ => ?_
  rw [Opens.mem_sup]
  by_cases h2 : (ULift.up (2 : ℤ) : ULift.{u} ℤ) ∈ p.asIdeal
  · by_cases h3 : (ULift.up (3 : ℤ) : ULift.{u} ℤ) ∈ p.asIdeal
    · exfalso
      refine p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem ?_ isUnit_one)
      have key : (ULift.up (3 : ℤ) : ULift.{u} ℤ) - ULift.up (2 : ℤ) = 1 := rfl
      rw [← key]
      exact p.asIdeal.sub_mem h3 h2
    · exact Or.inr ((PrimeSpectrum.mem_basicOpen _ _).2 h3)
  · exact Or.inl ((PrimeSpectrum.mem_basicOpen _ _).2 h2)

/-- The basic open of `n` in `Spec ℤ` is not the whole space when `n` has no right inverse. -/
private theorem basicOpen_up_ne_top (n : ℤ) (hn : ∀ w : ℤ, n * w ≠ 1) :
    (PrimeSpectrum.basicOpen (ULift.up n : ULift.{u} ℤ)) ≠ ⊤ := by
  intro h
  have hc : ((PrimeSpectrum.zeroLocus {(ULift.up n : ULift.{u} ℤ)})ᶜ) = Set.univ := by
    rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    exact Opens.ext_iff.mp h
  have hz : PrimeSpectrum.zeroLocus {(ULift.up n : ULift.{u} ℤ)} = ∅ := by
    simpa using hc
  rw [← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_empty_iff_eq_top,
    Ideal.span_singleton_eq_top] at hz
  obtain ⟨w, hw⟩ := hz.exists_right_inv
  exact hn w.down (by simpa using congrArg ULift.down hw)

/-- The basic open of `2` is not the whole of `Spec ℤ`: it is, only if `2` is a unit. -/
theorem basicOpenTwo_ne_top : basicOpenTwo.{u} ≠ ⊤ :=
  basicOpen_up_ne_top 2 fun _ => by omega

/-- The basic open of `3` is not the whole of `Spec ℤ`: it is, only if `3` is a unit. -/
theorem basicOpenThree_ne_top : basicOpenThree.{u} ≠ ⊤ :=
  basicOpen_up_ne_top 3 fun _ => by omega

/-- **Stacks 08BV at a cover by two proper opens.**  The Mayer--Vietoris triangle of
`Spec ℤ = D(2) ∪ D(3)`, obtained by instantiating
`Stacks.Cohomology.MayerVietoris.exists_distinguished_triangle_of_cover_rightDerived`.  Besides
witnessing that the general statement's hypotheses have a non-degenerate solution, this is the
check that none of its instance binders -- in particular the Grothendieck abelian and derived
category instances, which are pinned to the universe of the space -- makes it uninstantiable at a
concrete ringed space. -/
theorem exists_distinguished_triangle_specIntegers :
    ∃ (rU : (CategoryTheory.Functor.id
          (DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u})) :
        DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u}) ⥤
          DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u})) ⟶
        rightDerivedRestrictPush specIntegersSheaf.{u} basicOpenTwo.{u})
      (rV : (CategoryTheory.Functor.id
          (DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u})) :
        DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u}) ⥤
          DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u})) ⟶
        rightDerivedRestrictPush specIntegersSheaf.{u} basicOpenThree.{u})
      (dU : rightDerivedRestrictPush specIntegersSheaf.{u} basicOpenTwo.{u} ⟶
        rightDerivedRestrictPush specIntegersSheaf.{u} (basicOpenTwo.{u} ⊓ basicOpenThree.{u}))
      (dV : rightDerivedRestrictPush specIntegersSheaf.{u} basicOpenThree.{u} ⟶
        rightDerivedRestrictPush specIntegersSheaf.{u} (basicOpenTwo.{u} ⊓ basicOpenThree.{u}))
      (δ : rightDerivedRestrictPush specIntegersSheaf.{u}
          (basicOpenTwo.{u} ⊓ basicOpenThree.{u}) ⟶
        (CategoryTheory.Functor.id
            (DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u})) :
          DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u}) ⥤
            DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u})) ⋙
          shiftFunctor (DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u})) (1 : ℤ)),
      ∀ E, Triangle.mk (biprod.lift (rU.app E) (rV.app E))
        (biprod.desc (dU.app E) (dV.app E)) (δ.app E) ∈
          distTriang (DerivedCategory (SheafOfModules.{u} specIntegersSheaf.{u})) := by
  obtain ⟨_, _, rU, rV, dU, dV, δ, _, _, _, _, _, _, h⟩ :=
    exists_distinguished_triangle_of_cover_rightDerived specIntegersSheaf.{u}
      basicOpenTwo.{u} basicOpenThree.{u} basicOpenTwo_sup_basicOpenThree.{u}
  exact ⟨rU, rV, dU, dV, δ, h⟩

end Stacks.Cohomology.MayerVietoris.Cover

end
