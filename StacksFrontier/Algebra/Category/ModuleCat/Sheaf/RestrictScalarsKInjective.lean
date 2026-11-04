module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.ChangeOfRingsReduction
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.FlatMapIsoInvariance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of scalars along a flat map of ring sheaves preserves K-injectivity

Let `f : 𝒪 ⟶ 𝒪'` be a flat morphism of sheaves of commutative rings on a site. A K-injective
complex of sheaves of `𝒪'`-modules is then K-injective as a complex of sheaves of
`𝒪`-modules.

This is [Stacks, Tag 093Y] for the morphism of ringed topoi which is the identity on topoi and
`f` on structure sheaves: its pushforward is restriction of scalars and its pullback is
extension of scalars, and flatness of `f` is exactness of the latter.

## Main results

* `Stacks.SheafOfModules.ChangeOfRings.preservesFiniteLimits_extendScalars_of_isFlatMap`:
  extension of scalars along a flat morphism is left exact, for the *abstract* extension of
  scalars — the left adjoint of restriction of scalars.
* `Stacks.SheafOfModules.ChangeOfRings.isKInjective_restrictScalars_of_isFlatMap`: restriction
  of scalars along a flat morphism of sheaves of rings preserves K-injective complexes.

## Implementation notes

The criterion is [Stacks, Tag 08BJ],
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`: a right adjoint whose left adjoint
is exact preserves K-injectivity. The right adjoint is `SheafOfModules.restrictScalars`, the
left adjoint is `Stacks.Sheaves.ModuleAdjunction.extendScalars`, and the adjunction is
`Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction`.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (IsFlatMap IsFlatMapULift)

universe u

namespace Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O O' : Sheaf J CommRingCat.{u}}

/-- **Extension of scalars along a flat morphism of sheaves of commutative rings is left
exact**, for the abstract extension of scalars `Stacks.Sheaves.ModuleAdjunction.extendScalars`,
the left adjoint of restriction of scalars. -/
theorem preservesFiniteLimits_extendScalars_of_isFlatMap (f : O ⟶ O') (hf : IsFlatMap f) :
    PreservesFiniteLimits (Stacks.Sheaves.ModuleAdjunction.extendScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map f)) :=
  have hu : IsFlatMapULift.{u, u, u} f :=
    (AlgebraicGeometry.SheafOfModules.isFlatMapULift_iff_isFlatMap f).2 hf
  @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    (Stacks.Sheaves.DerivedPullback.FlatExtendScalars.extendScalarsIsoChangeOfRings f).symm
    (Stacks.Sheaves.RingedToposModules.extendScalars_preservesFiniteLimits J f hu)

/-- **Stacks Tag 093Y for change of rings.** If `f : 𝒪 ⟶ 𝒪'` is a flat morphism of sheaves of
commutative rings on a site, then a K-injective complex of sheaves of `𝒪'`-modules is
K-injective as a complex of sheaves of `𝒪`-modules. -/
theorem isKInjective_restrictScalars_of_isFlatMap (f : O ⟶ O') (hf : IsFlatMap f)
    (K : CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O')) ℤ)
    [K.IsKInjective] :
    CochainComplex.IsKInjective
      (((_root_.SheafOfModules.restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) :=
  have := preservesFiniteLimits_extendScalars_of_isFlatMap J f hf
  have := (Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map f)).leftAdjoint_preservesColimits
  @CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _ _ _ _ _ _ _ _ _
    (Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map f)) _ _ K ‹_›

end Stacks.SheafOfModules.ChangeOfRings

end
