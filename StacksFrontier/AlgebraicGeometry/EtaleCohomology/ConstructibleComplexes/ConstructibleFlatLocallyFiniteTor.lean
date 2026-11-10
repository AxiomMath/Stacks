module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatSliceFlat
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatFiniteTor

/-!
# A bounded complex of constructible flat sheaves has locally finite Tor dimension

Condition (2) of Tag 03TT asks that an object `K` of `D(X_étale, Λ)` be represented by a bounded
complex of constructible flat sheaves of `Λ`-modules. Membership of `D_ctf(X_étale, Λ)`, Tag
03TQ, asks for two things: constructible cohomology sheaves, which
`Stacks.EtaleCohomology.isConstructible_of_isRepresentedByConstructibleFlatComplex` reads off
such a representative, and locally finite Tor dimension in the sense of Tag 08FZ of the image of
`K` over the constant coefficient ringed site of Tag 03TR. This file proves the second.

More precisely, if `K` is represented by a complex concentrated in `[a, b]` whose terms have flat
étale stalks, for instance constructible flat sheaves, then on every slice of the small étale site
the restriction of the image of `K` has Tor amplitude in `[a, b]`; this is Tag 08G1 on the slice.

## Main definitions

* `AlgebraicGeometry.restrictedConstantCoefficientComplex`: the degreewise restriction to a slice
  of the degreewise image over the constant coefficient ring sheaf of a complex of sheaves of
  `Λ`-modules.

## Main results

In the namespace `AlgebraicGeometry`:

* `restrictedConstantCoefficientComplexIso`: that complex represents the derived restriction to
  the slice of the image of the object represented by the original complex.
* `isFlat_over_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`: a
  constructible flat sheaf of `Λ`-modules becomes a flat sheaf of modules on every slice of the
  constant coefficient ringed site.

In the namespace `Stacks.EtaleCohomology`:

* `hasTorAmplitude_derivedRestriction_of_flat_etaleModuleStalk` and
  `hasTorAmplitude_derivedRestriction_of_constructibleFlatComplex`: the restriction to each slice
  of the image of an object represented by a bounded complex of sheaves with flat étale stalks,
  respectively of constructible flat sheaves, has Tor amplitude in the interval the complex is
  concentrated in.
* `locallyHasFiniteTorDimension_of_flat_etaleModuleStalk`: **the Tor-dimension half of the
  direction (2) ⟹ (1) of Tag 03TT**, for a representative with flat étale stalks.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w r d

namespace AlgebraicGeometry

section SliceFlat

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective

/-- **A constructible flat sheaf of `Λ`-modules is flat over the constant coefficient ring sheaf
on every slice of the small étale site.**

This is the slicewise form of
`isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`. -/
public theorem isFlat_over_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F)
    (V : SmallEtale B X.obj X.property) :
    Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r, max (u + 1) w r}
      (O := ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O)
      ((SheafOfModules.overFunctor
          (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
            (constantCoefficientSheaf.{u, w, r} B X Λ)) V).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F)) :=
  isFlat_over_moduleSheafOverConstantCoefficients_of_forall_flat.{u, w, r} B X Λ F
    (fun s =>
      have := etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf B X Λ F hF s
      Module.Flat.of_projective) V

end SliceFlat

end AlgebraicGeometry

namespace AlgebraicGeometry

section RestrictedComplex

attribute [local instance] HasDerivedCategory.standard
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

/-- The degreewise restriction to the slice over `V`, of the degreewise image over the constant
coefficient ring sheaf, of a complex of sheaves of `Λ`-modules on the small étale site. -/
public abbrev restrictedConstantCoefficientComplex
    (V : (constantCoefficientRingedSite.{u, w, r} B X Λ).C)
    (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ) :
    CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V)) ℤ :=
  ((SheafOfModules.overFunctor.{max (u + 1) w r}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) w r}
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O) V).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
    (((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C)

/-- A degree in which `C` vanishes is a degree in which the restricted image complex vanishes. -/
public theorem isZero_restrictedConstantCoefficientComplex_X
    (V : (constantCoefficientRingedSite.{u, w, r} B X Λ).C)
    (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ)
    (i : ℤ) (hi : IsZero (C.X i)) :
    IsZero ((restrictedConstantCoefficientComplex.{u, w, r} B X Λ V C).X i) :=
  Functor.map_isZero
    (SheafOfModules.overFunctor.{max (u + 1) w r}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) w r}
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O) V)
    (Functor.map_isZero (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) hi)

variable
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

attribute [local instance 2000] AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

/-- **The degreewise restriction of the degreewise image of a representative represents the
derived restriction of the image.** If `C` represents `K` in `D(X_étale, Λ)`, then
`AlgebraicGeometry.restrictedConstantCoefficientComplex` at `C` represents the restriction to the
slice over `V` of the image of `K` over the constant coefficient ringed site.

The isomorphism is the two comparisons `CategoryTheory.Functor.mapDerivedCategoryFactors`
composed with the derived restriction of `e`. -/
public def restrictedConstantCoefficientComplexIso
    (V : (constantCoefficientRingedSite.{u, w, r} B X Λ).C)
    (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ)
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    (e : DerivedCategory.Q.obj C ≅ K) :
    DerivedCategory.Q.obj (restrictedConstantCoefficientComplex.{u, w, r} B X Λ V C) ≅
      (RingedSite.derivedRestriction.{u + 1, u, max (u + 1) w r, d}
        (constantCoefficientRingedSite.{u, w, r} B X Λ) V).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj K) :=
  letI : HasDerivedCategory.{d}
      (SheafOfModules.{max (u + 1) w r}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) w r}
          (constantCoefficientRingedSite.{u, w, r} B X Λ).O).over V)) := hSliceDerived V
  ((SheafOfModules.overFunctor.{max (u + 1) w r}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) w r}
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O)
      V).mapDerivedCategoryFactors.{d, d, _, _, _, _}.app
    (((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C)).symm ≪≫
    (RingedSite.derivedRestriction.{u + 1, u, max (u + 1) w r, d}
      (constantCoefficientRingedSite.{u, w, r} B X Λ) V).mapIso
      (((moduleSheafOverConstantCoefficientsFunctor.{u, w,
        r} B X Λ).mapDerivedCategoryFactors.{_, d, _, _, _, _}.app C).symm ≪≫
        (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.mapIso e)

end RestrictedComplex

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
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
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O) (ComplexShape.up ℤ)]

attribute [local instance 2000] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

/-- **The restriction to a slice of the image of an object represented by a bounded complex of
sheaves with flat étale stalks has Tor amplitude in the interval the complex is concentrated
in.**

This is Tag 08G1, in the direction that produces Tor amplitude from a flat representative, on the
slice over `V`. -/
public theorem hasTorAmplitude_derivedRestriction_of_flat_etaleModuleStalk
    (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ) (a b : ℤ)
    (hGE : C.IsStrictlyGE a) (hLE : C.IsStrictlyLE b)
    (hC : ∀ (i : ℤ) (s : GeometricPoint X.obj),
      Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj (C.X i)))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    (e : DerivedCategory.Q.obj C ≅ K)
    (T : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))
    (V : (constantCoefficientRingedSite.{u, w, r} B X Λ).C) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude (T V)
      ((RingedSite.derivedRestriction.{u + 1, u, max (u + 1) w r, d}
        (constantCoefficientRingedSite.{u, w, r} B X Λ) V).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj K))
      a b := by
  refine Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative
    (T V) _ a b (restrictedConstantCoefficientComplex.{u, w, r} B X Λ V C)
    (fun i => isFlat_over_moduleSheafOverConstantCoefficients_of_forall_flat.{u, w, r}
      B X Λ (C.X i) (hC i) V)
    (fun i hi => ?_)
    (restrictedConstantCoefficientComplexIso.{u, w, r, d} B X Λ V C K e)
  refine isZero_restrictedConstantCoefficientComplex_X.{u, w, r} B X Λ V C i ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hi | hi
  · exact C.isZero_of_isStrictlyGE a i hi
  · exact C.isZero_of_isStrictlyLE b i hi

/-- **The Tor-dimension half of the direction (2) ⟹ (1) of Tag 03TT, at the flatness of the
étale stalks.** An object of `D(X_étale, Λ)` represented by a bounded complex of sheaves of
`Λ`-modules with flat étale stalks has image of locally finite Tor dimension over the constant
coefficient ringed site. -/
public theorem locallyHasFiniteTorDimension_of_flat_etaleModuleStalk
    (T : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))
    (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ) (a b : ℤ)
    (hGE : C.IsStrictlyGE a) (hLE : C.IsStrictlyLE b)
    (hC : ∀ (i : ℤ) (s : GeometricPoint X.obj),
      Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj (C.X i)))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    (e : DerivedCategory.Q.obj C ≅ K) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, w, r} B X Λ) T
      ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj K) :=
  Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_forall
    T _ fun V => ⟨a, b,
      hasTorAmplitude_derivedRestriction_of_flat_etaleModuleStalk.{u, w, r, d}
        B X Λ C a b hGE hLE hC K e T V⟩

variable
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]

/-- **The restriction to a slice of the image of an object represented by a bounded complex of
constructible flat sheaves has Tor amplitude in the interval the complex is concentrated in.** -/
public theorem hasTorAmplitude_derivedRestriction_of_constructibleFlatComplex
    (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ) (a b : ℤ)
    (hGE : C.IsStrictlyGE a) (hLE : C.IsStrictlyLE b)
    (hC : ∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (C.X i))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    (e : DerivedCategory.Q.obj C ≅ K)
    (T : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))
    (V : (constantCoefficientRingedSite.{u, w, r} B X Λ).C) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude (T V)
      ((RingedSite.derivedRestriction.{u + 1, u, max (u + 1) w r, d}
        (constantCoefficientRingedSite.{u, w, r} B X Λ) V).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj K))
      a b :=
  hasTorAmplitude_derivedRestriction_of_flat_etaleModuleStalk.{u, w, r, d} B X Λ C a b hGE hLE
    (fun i s =>
      have := etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf B X Λ (C.X i) (hC i) s
      Module.Flat.of_projective) K e T V

end Stacks.EtaleCohomology

end
