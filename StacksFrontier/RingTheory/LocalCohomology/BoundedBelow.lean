module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.RingTheory.LocalCohomology.BoundedComparison

/-!
# Local cohomology with support in `T` of a module vanishes in negative degrees

Let `A` be a commutative ring, `T ⊆ Spec(A)` a subset and `M` an `A`-module. Sections with
support in `T` is a left exact functor, so its total right derived functor moves cohomology to
the right: the object `RΓ_T(M[0])` of the unbounded derived category lies in degrees `≥ 0`, and
consequently `H^i_T(M) = 0` for every `i < 0`.

The proof is the general left `t`-exactness of a right derived functor on the bounded-below
derived category, `CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`, transported to the
unbounded derived category along the comparison
`Stacks.LocalCohomology.nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso` of
Tag 0EF4. No hypothesis on `A`, on `T` or on `M` is needed.

## Main results

* `Stacks.LocalCohomology.isGE_derivedSectionsWithSupportIn_single` — `RΓ_T(M[0])` lies in
  degrees `≥ 0`.
* `Stacks.LocalCohomology.isZero_localCohomologyWithSupportIn_single_of_neg` — `H^i_T(M)`
  vanishes for `i < 0`.

## Implementation notes

The module `M` enters as the object `M[0]` of the *unbounded* derived category, which is the
shape in which the finiteness and annihilator criteria for local cohomology are stated. The
bounded-below object `M[0]` of `D⁺(A)` is identified with it by
`DerivedCategory.Plus.singleFunctorιIso`, whose components the proof transports along.

## References

* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- The total right derived functor of sections with support in `T`, applied to a module placed
in degree zero, lies in degrees `≥ 0`.

Sections with support is left exact, so on the bounded-below derived category its right derived
functor is left `t`-exact; the bounded-below and unbounded derived functors agree on
bounded-below objects. -/
theorem isGE_derivedSectionsWithSupportIn_single (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) :
    ((derivedSectionsWithSupportIn.{u, v} A T).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)).IsGE 0 := by
  let F := sectionsWithSupportInFunctor.{u, v} A T
  let Y := (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M
  have : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  have : F.Additive := by dsimp [F]; infer_instance
  have hY : Y.IsGE 0 := by dsimp [Y]; infer_instance
  have hplus : ((derivedSectionsWithSupportInPlus.{u, v} A T).obj Y).IsGE 0 := by
    show (F.rightDerivedFunctorPlus.obj Y).IsGE 0
    exact isGE_rightDerivedFunctorPlus_obj F Y 0
  have hinc : ((derivedSectionsWithSupportInPlus.{u, v} A T ⋙
      DerivedCategory.Plus.ι).obj Y).IsGE 0 :=
    (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).2 hplus
  obtain ⟨e⟩ := nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso.{u, v} A T
  have : ((derivedSectionsWithSupportIn.{u, v} A T).obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
        DerivedCategory.Plus.ι).obj M)).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso (e.app Y) 0
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((derivedSectionsWithSupportIn.{u, v} A T).mapIso
      ((DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{max u v} A) 0).app M)) 0

/-- Local cohomology with support in `T` of a module vanishes in negative degrees. -/
theorem isZero_localCohomologyWithSupportIn_single_of_neg (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) (i : ℤ) (hi : i < 0) :
    Limits.IsZero (localCohomologyWithSupportIn.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :=
  have := isGE_derivedSectionsWithSupportIn_single.{u, v} A T M
  DerivedCategory.isZero_of_isGE _ 0 i hi

/-- Local cohomology with support in `T` of a module is trivial in negative degrees. -/
theorem subsingleton_localCohomologyWithSupportIn_single_of_neg (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) (i : ℤ) (hi : i < 0) :
    Subsingleton (localCohomologyWithSupportIn.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (isZero_localCohomologyWithSupportIn_single_of_neg.{u, v} A T M i hi)

end Stacks.LocalCohomology
