module

public import StacksFrontier.Homology.TorAmplitude.Defs

/-!
# Tor amplitude of direct summands

If a biproduct of two objects of the derived category of modules over a commutative ring has
Tor amplitude in an interval, then each summand has Tor amplitude in the same interval. The
argument is a retract argument: each summand is a retract of the biproduct, and a retract of a
zero object is zero.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitude_of_biprod`: Tor amplitude passes from a biproduct
  to both summands.

## Implementation notes

The derived tensor product is supplied together with the comparison morphisms and their
left-derived-functor universal properties required by
`StacksDraft.TorAmplitude.HasTorAmplitude`.

## References

* [Stacks Project, Tag 066G](https://stacks.math.columbia.edu/tag/066G)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace StacksDraft.TorAmplitude

universe u v

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

/-- A retract of an object sent to zero by a functor is itself sent to zero: if `i ≫ p = 𝟙 X`
and `F.obj Y` is zero, then `F.obj X` is zero. -/
theorem isZero_of_retract {R : Type u} [CommRing R]
    (F : DerivedCategory (ModuleCat.{v} R) ⥤ ModuleCat.{v} R)
    (X Y : DerivedCategory (ModuleCat.{v} R)) (i : X ⟶ Y) (p : Y ⟶ X)
    (hip : i ≫ p = 𝟙 X) (hY : IsZero (F.obj Y)) : IsZero (F.obj X) := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id, ← hip, F.map_comp, hY.eq_zero_of_tgt (F.map i),
    zero_comp]

/-- If `K ⊕ L` has Tor amplitude in `[a, b]`, then both `K` and `L` have Tor amplitude in
`[a, b]`. -/
@[stacks 066G]
public theorem hasTorAmplitude_of_biprod {R : Type u} [CommRing R]
    (derivedTensor :
      DerivedCategory (ModuleCat.{v} R) ⥤
        DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R))
    (comparison : ∀ M : ModuleCat.{v} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)))
    (K L : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ)
    (h : HasTorAmplitude derivedTensor comparison isLeftDerived (K ⊞ L) a b) :
    HasTorAmplitude derivedTensor comparison isLeftDerived K a b ∧
      HasTorAmplitude derivedTensor comparison isLeftDerived L a b := by
  have key : ∀ (X : DerivedCategory (ModuleCat.{v} R)) (i : X ⟶ K ⊞ L) (p : K ⊞ L ⟶ X),
      i ≫ p = 𝟙 X → HasTorAmplitude derivedTensor comparison isLeftDerived X a b :=
    fun X i p hip M n hn => isZero_of_retract
      (derivedTensor.flip.obj _ ⋙ DerivedCategory.homologyFunctor _ n) X _ i p hip (h M n hn)
  exact ⟨key K _ _ biprod.inl_fst, key L _ _ biprod.inr_snd⟩

end

end StacksDraft.TorAmplitude
