module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# The cone of multiplication by a ring element

Let `R` be a commutative ring, let `f : R`, and let `M` be an object of the derived category
`D(R)` of `R`-modules. Multiplication by `f` is an endomorphism `f • 𝟙 M` of `M`, and this file
records what its cone `C` controls: if the negative cohomology of `M` vanishes after localizing
away from `f`, and the cohomology of `C` vanishes in degrees below `-1`, then the negative
cohomology of `M` vanishes outright.

## Main definitions

There are no new definitions. The cone is represented intrinsically, by a distinguished triangle
`M ⟶ C ⟶ M⟦1⟧` whose first map is `f • 𝟙 M`; localization of a cohomology module away from `f`
is `LocalizedModule.Away f`.

## Main results

* `Stacks.DerivedCategory.MultiplicationCone.homology_isZero_of_localization_and_cone_isZero`: the
  boundedness criterion
  described above.

## Stacks tags

* [0H84](https://stacks.math.columbia.edu/tag/0H84)

## References

* [Stacks Project, Tag 0H84](https://stacks.math.columbia.edu/tag/0H84)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.DerivedCategory.MultiplicationCone

universe u v

attribute [local instance] HasDerivedCategory.standard

private noncomputable instance homologyFunctorLinear
    {R : Type u} [CommRing R] (i : ℤ) :
    Functor.Linear R
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i) where
  map_smul f r := by
    change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map
        (r • f)) = _
    rw [show (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℤ) i).map (r • f) = r •
        (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
          (ComplexShape.up ℤ) i).map f by rfl]
    apply ShortComplex.homologyMap_smul

private noncomputable instance derivedHomologyFunctorLinear
    {R : Type u} [CommRing R] (i : ℤ) :
    Functor.Linear R (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i) :=
  letI : Localization.Lifting (DerivedCategory.Q (C := ModuleCat.{v} R))
      (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i)
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i) :=
    ⟨DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i⟩
  (Localization.functor_linear_iff (DerivedCategory.Q (C := ModuleCat.{v} R))
    (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)) R
    (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i)
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i)).mp inferInstance

/-- If multiplication by `f` is injective on `N` and `N` vanishes after localizing away from `f`,
then `N` vanishes. -/
theorem subsingleton_of_injective_smul_of_subsingleton_away {R : Type*} [CommRing R] (f : R)
    {N : Type*} [AddCommGroup N] [Module R N] (hf : Function.Injective (f • · : N → N))
    [Subsingleton (LocalizedModule.Away f N)] : Subsingleton N := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq f
    (f := LocalizedModule.mkLinearMap (Submonoid.powers f) N) (x := x) (y := y)
    (Subsingleton.elim _ _)
  induction n generalizing x y with
  | zero => simpa using hn
  | succ n ih => exact hf (ih _ _ (by simpa [pow_succ, mul_smul] using hn))

/-- Let `C` be a cone of multiplication by `f` on `M`. If every negative cohomology module of
`M` vanishes after localizing away from `f`, and the cohomology of `C` vanishes in degrees below
`-1`, then every negative cohomology module of `M` vanishes. -/
@[stacks 0H84]
theorem homology_isZero_of_localization_and_cone_isZero
    {R : Type u} [CommRing R]
    (f : R) (M C : DerivedCategory (ModuleCat.{v} R))
    (g : M ⟶ C) (h : C ⟶ M⟦1⟧)
    (hC : Triangle.mk (f • 𝟙 M) g h ∈
      distTriang (DerivedCategory (ModuleCat.{v} R)))
    (hM : ∀ i : ℤ, i < 0 →
      IsZero (ModuleCat.of R (LocalizedModule.Away f
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj M))))
    (hcone : ∀ i : ℤ, i < -1 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj C)) :
    ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj M) := by
  intro i hi
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map (f • 𝟙 M)) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff (Triangle.mk (f • 𝟙 M) g h) hC
      (i - 1) i (by omega)).2 ((hcone (i - 1) (by omega)).eq_of_src _ _)
  have hinj := (ModuleCat.mono_iff_injective _).mp this
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, ← ModuleCat.lsmul_eq_smul_id] at hinj
  have := ModuleCat.isZero_iff_subsingleton.mp (hM i hi)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact subsingleton_of_injective_smul_of_subsingleton_away f hinj

end Stacks.DerivedCategory.MultiplicationCone
