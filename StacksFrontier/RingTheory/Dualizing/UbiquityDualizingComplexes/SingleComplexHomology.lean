module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Noetherian
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.Perfect.Duality
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.RingTheory.Dualizing.Complex

/-!
# Maps out of a single complex concentrated in degree zero

A morphism in the derived category out of the complex concentrated in degree `n` on a
projective object is determined by, and may be prescribed through, the induced map on
cohomology in degree `n`. Taking the object to be the ring itself, this identifies
`Hom(R, X)` in the derived category with `H⁰(X)`, and hence turns the vanishing of a
hom-group into the vanishing of the degree-zero cohomology of the derived internal Hom.

## Main results

* `Dualizing.hom_subsingleton_iff_derivedInternalHom_homology_isZero`: a hom-group in the
  derived category of modules is a subsingleton exactly when the degree-zero cohomology of the
  derived internal Hom vanishes.

## Implementation notes

The identification `Hom(R, X) ≃ H⁰(X)` comes from the projectivity of `R` as a module over
itself, through `StacksDraft.Perfect.single_derived_homology_bijective`. Passing from the derived
Hom over `R` to the derived internal Hom over `R` requires moving the scalars to `ULift R`, which
is what `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` does; that equivalence
is fully faithful, so the hom-groups on the two sides correspond.

## References

* [Stacks Project, Tag 0DWC](https://stacks.math.columbia.edu/tag/0DWC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

noncomputable section


private abbrev baseUnitComplex (R : Type u) [CommRing R] :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)

private abbrev baseUnitObject (R : Type u) [CommRing R] :=
  DerivedCategory.Q.obj (baseUnitComplex R)

private def baseUnitHomologyClass (R : Type u) [CommRing R] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj (baseUnitObject R) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).inv.app
      (baseUnitComplex R) <|
    (HomologicalComplex.homologyFunctorSingleIso (ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).inv.app (ModuleCat.of R R) (1 : R)

private def baseUnitToHomology (R : Type u) [CommRing R]
    (X : DerivedCategory (ModuleCat.{u} R)) :
    (baseUnitObject R ⟶ X) →+
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X : Type u) where
  toFun f := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f
    (baseUnitHomologyClass R)
  map_zero' := by simp [baseUnitHomologyClass]
  map_add' f g := by simp [baseUnitHomologyClass]

private theorem baseUnitToHomology_bijective (R : Type u) [CommRing R]
    (X : DerivedCategory (ModuleCat.{u} R)) :
    Function.Bijective (baseUnitToHomology R X) := by
  let P := ModuleCat.of R R
  let M := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X
  exact ((LinearMap.ringLmapEquivSelf R R M).bijective.comp
    (ModuleCat.homLinearEquiv (M := P) (N := M) (S := R)).bijective).comp
    (StacksDraft.Perfect.single_derived_homology_bijective P X 0)

private theorem hom_subsingleton_iff_derivedHom_homology_isZero
    {R : Type u} [CommRing R] (X Y : DerivedCategory (ModuleCat.{u} R)) :
    Subsingleton (X ⟶ Y) ↔
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj
          (Opposite.op X, Y))) := by
  let D := StacksDraft.DerivedHom.derivedHomAdjunction (R := R)
  let H := D.hom.obj (Opposite.op X, Y)
  let e : (baseUnitObject R ⟶ H) ≃ ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} R) 0).obj H : Type u) :=
    Equiv.ofBijective (baseUnitToHomology R H) (baseUnitToHomology_bijective R H)
  exact ((D.homZeroEquiv X Y).toEquiv.symm.trans e).subsingleton_congr.trans
    ModuleCat.isZero_iff_subsingleton.symm

/-- Morphisms `X ⟶ Y` in the derived category of `R`-modules form a subsingleton exactly when the
degree-zero cohomology of the derived internal Hom of `X` and `Y` is zero. -/
public theorem hom_subsingleton_iff_derivedInternalHom_homology_isZero
    {R : Type u} [CommRing R] (X Y : DerivedCategory (ModuleCat.{max u v} R)) :
    Subsingleton (X ⟶ Y) ↔
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v} R).obj
          (Opposite.op X, Y))) := by
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v,
    max u v + 1} R
  let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{max u v} R ≃+* R)
  let D := StacksDraft.DerivedHom.derivedHomAdjunctionULift.{u, max u v, max u v + 1} (R := R)
  let H := D.hom.obj (Opposite.op (E.functor.obj X), E.functor.obj Y)
  let H₀ := (DerivedCategory.homologyFunctor
    (ModuleCat.{max u v} (ULift.{max u v} R)) 0).obj H
  let HR := (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v} R).obj
    (Opposite.op X, Y)
  let HR₀ := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj HR
  have hbridge : HR = e.inverse.mapDerivedCategory.obj H := rfl
  have hLift := hom_subsingleton_iff_derivedHom_homology_isZero
    (R := ULift.{max u v} R) (E.functor.obj X) (E.functor.obj Y)
  have hzeroEquiv : Limits.IsZero HR₀ ↔ Limits.IsZero H₀ :=
    ⟨fun h => by
      simpa [H₀, HR, hbridge] using ((e.functor.map_isZero h).of_iso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso e.functor 0).app HR)).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{max u v} R)) 0).mapIso
          (E.counitIso.app H).symm),
    fun h => by
      simpa [H₀, HR₀, HR, hbridge] using (e.inverse.map_isZero h).of_iso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso e.inverse 0).app H)⟩
  exact (Equiv.ofBijective E.functor.map
    (E.fullyFaithfulFunctor.map_bijective X Y)).subsingleton_congr.trans
      (hLift.trans hzeroEquiv.symm)

end

end Dualizing
