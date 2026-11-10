module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekFiniteTor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction and extension by zero preserve membership of `D_ctf`

Let `Λ` be a Noetherian ring and let `j : U ⟶ X` be an étale morphism of schemes, presented as
an object `U` of the small étale site of `X`. Tag 0962 says that

1. `K|_U ∈ D_ctf(U_étale, Λ)` if `K ∈ D_ctf(X_étale, Λ)`, and
2. `j_! M ∈ D_ctf(X_étale, Λ)` if `M ∈ D_ctf(U_étale, Λ)` and `j` is quasi-compact and
   quasi-separated.

This file states both parts as propositions about the objects themselves: membership of
`D_ctf` is a predicate on the unbounded derived category of sheaves of `Λ`-modules on the small
étale site, and the two statements apply it to the images of a given object under the derived
restriction functor and the derived extension-by-zero functor of Tag 03S3.

## Main definitions

* `Stacks.EtaleCohomology.IsConstructibleFiniteTor`: membership of `D_ctf(X_étale, Λ)` for an
  object of `D(X_étale, Λ)`, Tag 03TQ: its cohomology sheaves are constructible and its image in
  the derived category of modules over the constant coefficient ring sheaf locally has finite
  Tor dimension.

## Main results

* `Stacks.EtaleCohomology.isConstructibleFiniteTor_iff_exists`: the predicate is membership of
  the full subcategory `Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory`.
* `Stacks.EtaleCohomology.isConstructibleFiniteTor_derivedRestriction`: **Tag 0962, part (1)**.
* `Stacks.EtaleCohomology.isConstructibleFiniteTor_derivedExtensionByZero`: **Tag 0962,
  part (2)**.

## Implementation notes

The restriction `K|_U` is the image of `K` under `(moduleRestriction B X.obj X.property U Λ)`
mapped to the derived categories, and `j_! M` the image of `M` under
`(moduleExtensionByZero B X.obj X.property U Λ)` mapped to the derived categories; both are
exact functors of Tag 03S3. The proofs are those of
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryRestriction` and
`Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryExtensionByZero`, whose outputs are
by construction these two objects.

The derived category of sheaves of `Λ`-modules is the standard model,
`HasDerivedCategory.standard`, the model under which `Stacks.EtaleCohomology.IsConstructible`,
and so `D_ctf` itself, is stated.

## References

* [Stacks Project, Tag 0962](https://stacks.math.columbia.edu/tag/0962)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w r d

namespace Stacks.EtaleCohomology

section Membership

attribute [local instance] HasDerivedCategory.standard
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
    (constantCoefficientRingedSite.{u, w, r} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O) (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

/-- **Membership of `D_ctf(X_étale, Λ)`**, Tag 03TQ, for an object `K` of the derived category
of sheaves of `Λ`-modules on the small étale site of `X`: the cohomology sheaves of `K` are
constructible, and the image of `K` in the derived category of modules over the constant
coefficient ring sheaf locally has finite Tor dimension, measured against the family `T` of
derived tensor products on the slices. -/
@[sga "5 III 1.1"]
public def IsConstructibleFiniteTor
    (T : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))) :
    Prop :=
  IsConstructible B X Λ K ∧
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, w, r} B X Λ) T
      ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj K)

omit [IsNoetherianRing Λ] in
/-- `Stacks.EtaleCohomology.IsConstructibleFiniteTor` is membership of the full subcategory
`Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory` of Tag 03TQ: an object of
`D(X_étale, Λ)` satisfies it exactly when it underlies an object of `D_ctf(X_étale, Λ)`. -/
public theorem isConstructibleFiniteTor_iff_exists
    (T : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))) :
    IsConstructibleFiniteTor.{u, w, r, d} B X Λ T K ↔
      ∃ L : ConstructibleFiniteTorDerivedCategory.{u, w, r, d} B X Λ T, L.obj.obj = K := by
  constructor
  · rintro ⟨hc, ht⟩
    exact ⟨⟨⟨K, hc⟩, ht⟩, rfl⟩
  · rintro ⟨L, rfl⟩
    exact ⟨L.obj.property, L.property⟩

end Membership

section Etale

attribute [local instance] HasDerivedCategory.standard
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat
  AlgebraicGeometry.preservesFiniteColimits_smallEtaleSheafPullback_moduleCat
  AlgebraicGeometry.additive_smallEtaleSheafPullback_moduleCat

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (U : SmallEtale B X.obj X.property)
  (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
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
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ))]
  [hSliceDerivedX : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V))]
  [hSliceDerivedU : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r}
      B U.obj.left Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V))]
  [∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O).Additive]
  [∀ (V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O).obj M).Additive]
  [∀ (V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O)
      (ComplexShape.up ℤ)]
  [∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V).O).Additive]
  [∀ (V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V).O).obj
        M).Additive]
  [∀ (V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V).O)
      (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

omit [IsNoetherianRing Λ] in
/-- **Stacks 0962, part (1).** Let `Λ` be a Noetherian ring and let `j : U ⟶ X` be an étale
morphism of schemes, the object `U` of the small étale site of `X`. If `K` lies in
`D_ctf(X_étale, Λ)`, then its restriction `K|_U`, the image of `K` under the derived functor of
the restriction functor of Tag 03S3, lies in `D_ctf(U_étale, Λ)`.

This is `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryRestriction`, whose output
is `K|_U` by construction: constructibility by Tag 095X part (1), and locally finite Tor
dimension by the finite-Tor-dimension half of Tag 0963 at the structure morphism of `U`,
transported along Tag 03S3 part (3). -/
@[stacks 0962 "part (1): for K in D_ctf(X_et, Λ), the restriction K|_U — the image of K under \
the derived restriction functor of Tag 03S3 — satisfies membership of D_ctf(U_et, Λ)"]
public theorem isConstructibleFiniteTor_derivedRestriction
    (T : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V))
    (T' : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V))
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsConstructibleFiniteTor.{u, max (u + 1) r, r, d} B X Λ T K) :
    IsConstructibleFiniteTor.{u, max (u + 1) r, r, d} B U.obj.left Λ T'
      ((moduleRestriction.{u, r, max (u + 1) r} B X.obj X.property U Λ).mapDerivedCategory.obj
        K) :=
  let L := constructibleFiniteTorDerivedCategoryRestriction.{u, r, d} B X U Λ T T'
    ⟨⟨K, hK.1⟩, hK.2⟩
  ⟨L.obj.property, L.property⟩

/-- **Stacks 0962, part (2).** Let `Λ` be a Noetherian ring and let `j : U ⟶ X` be an étale
morphism of schemes, the object `U` of the small étale site of `X`, which is quasi-compact and
quasi-separated. If `M` lies in `D_ctf(U_étale, Λ)`, then its extension by zero `j_! M`, the
image of `M` under the derived functor of the extension-by-zero functor of Tag 03S3, lies in
`D_ctf(X_étale, Λ)`.

This is `Stacks.EtaleCohomology.constructibleFiniteTorDerivedCategoryExtensionByZero`, whose
output is `j_! M` by construction: constructibility by Tag 095X part (2), and locally finite Tor
dimension read at the stalks by Tag 03S5 and Tag 0DJJ. -/
@[stacks 0962 "part (2): for j quasi-compact and quasi-separated and M in D_ctf(U_et, Λ), the \
extension by zero j_! M — the image of M under the derived extension-by-zero functor of Tag \
03S3 — satisfies membership of D_ctf(X_et, Λ)"]
public theorem isConstructibleFiniteTor_derivedExtensionByZero
    (hqc : QuasiCompact (B.inclusion.map U.obj.hom))
    (hqs : QuasiSeparated (B.inclusion.map U.obj.hom))
    (T : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V))
    (T' : ∀ V : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B U.obj.left Λ).over V))
    (M : DerivedCategory (Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hM : IsConstructibleFiniteTor.{u, max (u + 1) r, r, d} B U.obj.left Λ T' M) :
    IsConstructibleFiniteTor.{u, max (u + 1) r, r, d} B X Λ T
      ((moduleExtensionByZero.{u, r} B X.obj X.property U Λ).mapDerivedCategory.obj M) :=
  let L := constructibleFiniteTorDerivedCategoryExtensionByZero.{u, r, d} B X U Λ hqc hqs T T'
    ⟨⟨M, hM.1⟩, hM.2⟩
  ⟨L.obj.property, L.property⟩

end Etale

end Stacks.EtaleCohomology

end
