module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.Basic
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import StacksFrontier.RingTheory.Dualizing.DerivedHomFiniteCohomology
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSurjective
import StacksCore.Tactic.StacksAttribute

/-!
# Injective amplitude is preserved by localization

Let `R` be a Noetherian ring and `f : R`. If `L` in `D(R)` has injective amplitude in `[a, b]`,
then so does `L ⊗_R R_f` in `D(R_f)`, where `R_f = Γ(Spec R, D(f))`.

The argument is degreewise. Choose a complex `I` of injective `R`-modules, vanishing outside
`[a, b]`, with `L ≅ I` in `D(R)`. Extension of scalars along `R ⟶ R_f` is additive, so it
carries the zero objects of `I` to zero objects and the image complex still vanishes outside
`[a, b]`; it is flat, so it is exact and the image complex still represents `L ⊗_R R_f`; and
each `R_f ⊗_R I^i` is the localization of the injective module `I^i`, hence injective over
`R_f` by [Stacks, Tag 0A6I], which is where the Noetherian hypothesis enters.

## Main results

* `AlgebraicGeometry.AffineExt.hasInjectiveAmplitude_extD_locMap`: derived extension of scalars
  along `R ⟶ R_f` preserves injective amplitude in `[a, b]`.

## References

* [Stacks Project, Tag 0A6I](https://stacks.math.columbia.edu/tag/0A6I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.AffineExt

attribute [local instance] HasDerivedCategory.standard

/-- **Injective amplitude is preserved by localization.** Over a Noetherian ring `R`, if `L` in
`D(R)` has injective amplitude in `[a, b]`, then `L ⊗_R R_f` has injective amplitude in `[a, b]`
over `R_f`.

A bounded complex of injective `R`-modules representing `L` is carried degreewise, and in the
same degrees, to a bounded complex of injective `R_f`-modules representing `L ⊗_R R_f`: the
terms stay injective by [Stacks, Tag 0A6I], the bounds are preserved because an additive functor
carries zero objects to zero objects, and the complex still represents the localization because
extension of scalars along a localization is exact. -/
@[stacks 0A6I "injective amplitude is preserved by localization"]
theorem hasInjectiveAmplitude_extD_locMap (R : CommRingCat.{u}) [IsNoetherianRing R]
    (L : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) (f : R)
    (hL : StacksDraft.InjectiveDimension.HasInjectiveAmplitude L a b) :
    StacksDraft.InjectiveDimension.HasInjectiveAmplitude ((extD (locMap R f)).obj L) a b := by
  obtain ⟨I, hge, hle, hinj, ⟨eI⟩⟩ := hL
  refine ⟨((ModuleCat.extendScalars.{u, u, u} (locMap R f).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I,
    Dualizing.isStrictlyGE_mapHomologicalComplex _ I a hge,
    Dualizing.isStrictlyLE_mapHomologicalComplex _ I b hle, fun i => ?_, ⟨?_⟩⟩
  · have := hinj i
    exact Dualizing.injective_extendScalars.{u, u} (Submonoid.powers f) (I.X i)
  · exact (extD (locMap R f)).mapIso eI ≪≫
      (Functor.mapDerivedCategoryFactors
        (ModuleCat.extendScalars.{u, u, u} (locMap R f).hom)).app I

end AlgebraicGeometry.AffineExt

end
