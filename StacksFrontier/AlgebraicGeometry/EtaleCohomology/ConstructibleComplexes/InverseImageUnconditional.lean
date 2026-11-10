module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleModuleSheafInstances

/-!
# Derived inverse image of a complex with constructible cohomology, on the small étale sites

Let `Λ` be a Noetherian ring and `f : X ⟶ Y` a morphism of schemes. If `K ∈ D_c(Y_étale, Λ)`,
then `Lf^*K ∈ D_c(X_étale, Λ)`. This is Tag 095Y, stated with no data beyond `Λ`, `f` and `K`.

## Main results

* `Stacks.EtaleCohomology.isConstructible_mapDerivedCategory_smallEtaleSheafPullback` —
  **Tag 095Y**.

## Implementation notes

`Stacks.EtaleCohomology.isConstructible_derivedPullback` proves the statement relative to the
existence of sheafification on the small étale sites of `X` and `Y` and on their slices, and of
the inverse image `f⁻¹` as left adjoint of direct image along every small étale base change. All
of these are theorems of the base about the small étale site, which is essentially small at
every universe containing that of the schemes, and they are found by instance search here:
`AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat_of_univLE`,
`AlgebraicGeometry.SmallEtale.hasSheafify_over_moduleCat_of_univLE` and
`AlgebraicGeometry.smallEtaleBaseChange_isRightAdjoint_sheafPushforward_moduleCat`. They live
in a separate file from `isConstructible_derivedPullback` so that the many importers of that
file do not see three further global instances.

The coefficient universe is `ModuleCat.{max (u + 1) w} Λ` for an arbitrary `w`, the universe at
which exactness of inverse image,
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat`, is proved. The
derived category is the standard model `CategoryTheory.HasDerivedCategory.standard`, the model at
which `Stacks.EtaleCohomology.IsConstructible` (and so `D_c`) is defined.

## References

* [Stacks Project, Tag 095Y](https://stacks.math.columbia.edu/tag/095Y)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w r

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
  preservesFiniteLimits_smallEtaleSheafPullback_moduleCat
  preservesFiniteColimits_smallEtaleSheafPullback_moduleCat
  additive_smallEtaleSheafPullback_moduleCat

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]

/-- **Stacks 095Y.** Let `Λ` be a Noetherian ring and `f : X ⟶ Y` a morphism of schemes. If
`K ∈ D_c(Y_étale, Λ)`, that is the cohomology sheaves of `K` are constructible in every degree,
then `Lf^*K ∈ D_c(X_étale, Λ)`.

Inverse image of module sheaves is exact, so `Lf^*` is the termwise functor
`CategoryTheory.Functor.mapDerivedCategory` and `Hⁱ(Lf^*K) ≅ f⁻¹(HⁱK)`, which is constructible by
Tag 095G; this is `Stacks.EtaleCohomology.isConstructible_derivedPullback`, whose sheafification
and inverse-image instances are supplied by the small étale site. -/
@[stacks 095Y]
public theorem isConstructible_mapDerivedCategory_smallEtaleSheafPullback {X Y : B.Scheme}
    (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (SmallEtale.topology B Y.obj Y.property)
      (ModuleCat.{max (u + 1) w} Λ)))
    (hK : IsConstructible B Y Λ K) :
    IsConstructible B X Λ
      (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).mapDerivedCategory.obj K) :=
  have : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max (u + 1) w} Λ) := fun _ _ => inferInstance
  isConstructible_derivedPullback B Λ f K hK

end Stacks.EtaleCohomology

end
