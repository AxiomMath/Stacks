module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.ModuleExactness
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality

/-!
# Restriction and extension by zero of complexes with constructible cohomology

Let `Λ` be a Noetherian ring and let `j : U ⟶ X` be an object of the small étale site of `X`. If
`K` lies in `D_c(X_étale, Λ)` then `K|_U` lies in `D_c(U_étale, Λ)`, and if `M` lies in
`D_c(U_étale, Λ)` and `j` is quasi-compact and quasi-separated then `j_! M` lies in
`D_c(X_étale, Λ)`. Here `D_c` is the predicate `Stacks.EtaleCohomology.IsConstructible` on the
derived category of sheaves of `Λ`-modules on the small étale site, and restriction and extension
by zero are `AlgebraicGeometry.moduleRestriction` and `AlgebraicGeometry.moduleExtensionByZero`.

## Main definitions

* `AlgebraicGeometry.smallEtaleModuleInverseImage`: the inverse image of sheaves of `Λ`-modules
  along the structure morphism of `U`.
* `AlgebraicGeometry.moduleRestrictionIsoSmallInverseImage`: restriction of sheaves of
  `Λ`-modules along `U ⟶ X` is the inverse image along the structure morphism of `U`.

## Main results

* `Stacks.EtaleCohomology.isConstructible_derivedRestriction`: restriction preserves
  `D_c`.
* `Stacks.EtaleCohomology.isConstructible_derivedModuleExtensionByZero`: extension by zero along a
  quasi-compact quasi-separated étale morphism preserves `D_c`.

## References

* [Stacks Project, Tag 095X](https://stacks.math.columbia.edu/tag/095X)
* [Stacks Project, Tag 095Y](https://stacks.math.columbia.edu/tag/095Y)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (X : B.Scheme) (U : SmallEtale B X.obj X.property)

/-- The inverse image of sheaves of `Λ`-modules along the structure morphism of an étale object
`U` of the small étale site of `X`. -/
public abbrev smallEtaleModuleInverseImage :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ) ⥤
      Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
        (ModuleCat.{max (u + 1) r} Λ) :=
  (smallEtaleBaseChange B U.obj.hom).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)

/-- Restriction of sheaves of `Λ`-modules along `U ⟶ X` is isomorphic to the inverse image along
the structure morphism of `U`. -/
public def moduleRestrictionIsoSmallInverseImage :
    smallEtaleModuleInverseImage B Λ X U ≅
      moduleRestriction.{u, r, max (u + 1) r} B X.obj X.property U Λ :=
  smallInverseImageIsoPostcomposePushforward B U.obj.hom (ModuleCat.{max (u + 1) r} Λ)

section Exactness

variable [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
  [HasSheafify (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (ModuleCat.{max (u + 1) r} Λ)]

/-- Restriction of sheaves of modules along `U ⟶ X` preserves finite colimits. -/
public instance moduleRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (moduleRestriction.{u, r, max (u + 1) r} B X.obj X.property U Λ) :=
  haveI : PreservesFiniteColimits (smallEtaleModuleInverseImage B Λ X U) :=
    preservesFiniteColimits_smallEtaleSheafPullback_moduleCat B U.obj.hom Λ
  preservesFiniteColimits_of_natIso (moduleRestrictionIsoSmallInverseImage B Λ X U)

/-- Restriction of sheaves of modules along `U ⟶ X` preserves finite limits. -/
public instance moduleRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (moduleRestriction.{u, r, max (u + 1) r} B X.obj X.property U Λ) :=
  haveI : PreservesFiniteLimits (smallEtaleModuleInverseImage B Λ X U) :=
    preservesFiniteLimits_smallEtaleSheafPullback_moduleCat B U.obj.hom Λ
  preservesFiniteLimits_of_natIso (moduleRestrictionIsoSmallInverseImage B Λ X U)

/-- Restriction of sheaves of modules along `U ⟶ X` is additive. -/
public instance moduleRestriction_additive :
    (moduleRestriction.{u, r, max (u + 1) r} B X.obj X.property U Λ).Additive :=
  haveI : (smallEtaleModuleInverseImage B Λ X U).Additive :=
    additive_smallEtaleSheafPullback_moduleCat B U.obj.hom Λ
  Functor.additive_of_iso (moduleRestrictionIsoSmallInverseImage B Λ X U)

/-- Extension by zero of sheaves of modules preserves finite colimits. -/
public instance moduleExtensionByZero_preservesFiniteColimits :
    PreservesFiniteColimits (moduleExtensionByZero.{u, r} B X.obj X.property U Λ) :=
  haveI : PreservesColimitsOfSize.{0, 0}
      (moduleExtensionByZero.{u, r} B X.obj X.property U Λ) :=
    (moduleExtensionByZeroAdjunction B X.obj X.property U Λ).leftAdjoint_preservesColimits
  inferInstance

/-- Extension by zero of sheaves of modules is additive. -/
public instance moduleExtensionByZero_additive :
    (moduleExtensionByZero.{u, r} B X.obj X.property U Λ).Additive :=
  haveI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (moduleExtensionByZero.{u, r} B X.obj X.property U Λ)
  Functor.additive_of_preservesBinaryBiproducts _

end Exactness

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

section

variable (X : B.Scheme) (U : SmallEtale B X.obj X.property)
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
  [HasSheafify (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (ModuleCat.{max (u + 1) r} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]

omit [IsNoetherianRing Λ] in
/-- Let `Λ` be a Noetherian ring, let `X` be a scheme and let `U` be an object of the small étale
site of `X`. If a complex `K` of étale sheaves of `Λ`-modules on `X` lies in `D_c(X_étale, Λ)`,
then its restriction `K|_U` lies in `D_c(U_étale, Λ)`. -/
@[stacks 095X "part (1)"]
public theorem isConstructible_derivedRestriction
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsConstructible B X Λ K) :
    IsConstructible B U.obj.left Λ
      ((moduleRestriction.{u, r, max (u + 1) r} B X.obj X.property U
        Λ).mapDerivedCategory.obj K) := by
  intro i
  refine isConstructibleModuleSheaf_congr B Λ U.obj.left
    (((moduleRestriction.{u, r, max (u + 1) r} B X.obj X.property U
      Λ).mapDerivedCategoryCompHomologyFunctorIso i).app K).symm ?_
  exact isConstructibleModuleSheaf_congr B Λ U.obj.left
    ((moduleRestrictionIsoSmallInverseImage B Λ X U).app _)
    (isConstructibleModuleSheaf_pullback B Λ U.obj.hom _ (hK i))

/-- Let `Λ` be a Noetherian ring, let `X` be a scheme and let `U` be an object of the small étale
site of `X` whose structure morphism `j : U ⟶ X` is quasi-compact and quasi-separated. If a complex
`M` of étale sheaves of `Λ`-modules on `U` lies in `D_c(U_étale, Λ)`, then `j_! M` lies in
`D_c(X_étale, Λ)`. -/
@[stacks 095X "part (2)"]
public theorem isConstructible_derivedModuleExtensionByZero
    (hqc : QuasiCompact (B.inclusion.map U.obj.hom))
    (hqs : QuasiSeparated (B.inclusion.map U.obj.hom))
    (M : DerivedCategory (Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hM : IsConstructible B U.obj.left Λ M) :
    IsConstructible B X Λ
      ((moduleExtensionByZero.{u, r} B X.obj X.property U Λ).mapDerivedCategory.obj M) := by
  intro i
  refine isConstructibleModuleSheaf_congr B Λ X
    (((moduleExtensionByZero.{u, r} B X.obj X.property U
      Λ).mapDerivedCategoryCompHomologyFunctorIso i).app M).symm ?_
  exact isConstructibleModuleSheaf_moduleExtensionByZero B Λ X U hqc hqs _ (hM i)

end

end Stacks.EtaleCohomology

end
