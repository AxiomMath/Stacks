module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientStalk
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.BoundedAboveShriekComplex
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatIsFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A bounded complex of constructible flat sheaves lies in `D_ctf`

This file proves the direction (2) ⟹ (1) of [Stacks, Tag 03TT]: an object of `D(X_étale, Λ)`
represented by a bounded complex of constructible flat sheaves of `Λ`-modules lies in the
category `D_ctf(X_étale, Λ)` of Tag 03TQ, i.e. it has constructible cohomology sheaves and, read
as an object of the derived category of modules over the constant coefficient ring sheaf, it
locally has finite Tor dimension.

## Main results

* `AlgebraicGeometry.isFlat_overFunctor_moduleSheafOverConstantCoefficients` — a sheaf of
  `Λ`-modules whose étale stalks are flat becomes, after restriction to any slice of the small
  étale site, a flat module over the restricted constant coefficient ring sheaf.

The following names are in the namespace `Stacks.EtaleCohomology`.

* `locallyHasFiniteTorDimension_of_isRepresentedByConstructibleFlatComplex_sliceStalks` — the
  Tor-dimension half of the direction (2) ⟹ (1) of Tag 03TT.
* `exists_constructibleFiniteTor_of_isRepresentedByConstructibleFlatComplex` — **the direction
  (2) ⟹ (1) of Tag 03TT**, as membership of the category of Tag 03TQ.

## Implementation notes

Locally finite Tor dimension is Tor amplitude on the slices of the ringed site, measured against
the given derived tensor products on the slices. On the slice over `V` the restriction of a bounded
complex of constructible flat sheaves is a bounded complex of flat modules, so it has Tor amplitude
in the interval of its degrees by Stacks 08G1. Restriction to a slice preserves flatness in general
(Stacks 0E8J); since the small étale site has its objects one universe above its morphisms,
flatness of the restriction is read here at the stalks, Stacks 05VC on the slice site: the lifts
`Ψ.over z` of the universe-lifted geometric points `Ψ` of `X` form a conservative family of points
of the slice site (`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.over`), and at
`Ψ.over z` the stalk of the restriction is the étale stalk of the sheaf of `Λ`-modules, through
Stacks 04H2 (`AlgebraicGeometry.moduleSheafOverConstantCoefficientsOverFiberIso`).

The coefficient universe is `max (u + 1) r`, the universe of the bounded above resolutions of
Tag 0960 and of the weak Serre property of Tag 03RZ (3) on which the constructible half rests.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r d

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

/-- **The restriction to a slice of a sheaf of modules with flat étale stalks is flat.** Let `F`
be a sheaf of `Λ`-modules on the small étale site of `X` whose stalk at every geometric point is
a flat `Λ`-module, and let `V` be an object of the site. The restriction to the slice over `V`
of the associated sheaf of modules over the constant coefficient ring sheaf is a flat module over
the restricted ring sheaf.

This is Stacks 05VC on the slice site, tested on the lifts `Ψ.over z` of the universe lifts `Ψ`
of the geometric points of `X`, which form a conservative family of points of the slice; at such
a lift the stalk is the étale stalk of `F`, by Stacks 04H2, the two module structures differing
by the identification `AlgebraicGeometry.constantCoefficientRingOverFiberEquiv` of the stalk of
the restricted ring sheaf with `Λ`. -/
public theorem isFlat_overFunctor_moduleSheafOverConstantCoefficients
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hF : ∀ s : GeometricPoint X.obj,
      Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj F))
    (V : SmallEtale B X.obj X.property) :
    Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) r, max (u + 1) r}
      (O := ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O)
      ((SheafOfModules.overFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) V).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ).obj F)) := by
  let P := ObjectProperty.ofObj (fun x : ↥X.obj =>
    (geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) r})
  have hP : P.IsConservativeFamilyOfPoints :=
    isConservativeFamilyOfPoints_uliftGeometricSitePoint.{u, max (u + 1) r, r} B X
  have : (SmallEtale.topology B X.obj X.property).WEqualsLocallyBijective
      (Type (max (u + 1) r)) :=
    GrothendieckTopology.wEqualsLocallyBijective_type _
  have : HasSheafify (SmallEtale.topology B X.obj X.property) (Type (max (u + 1) r)) :=
    Stacks.Sites.SheafSection.hasSheafify_type_of_essentiallySmall _
  have : HasSheafify ((SmallEtale.topology B X.obj X.property).over V)
      (Type (max (u + 1) r)) :=
    Stacks.Sites.SheafSection.hasSheafify_type_of_essentiallySmall _
  refine Stacks.isFlat_of_forall_isFlatModuleStalk.{max (u + 1) r, u, u + 1}
    ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O _
    (fun ψ : Σ (Φ : P.FullSubcategory), Φ.obj.fiber.obj V => ψ.1.obj.over ψ.2) (hP.over V) ?_
  rintro ⟨⟨Φ, hΦ⟩, z⟩
  obtain ⟨x⟩ := hΦ
  let e := constantCoefficientRingOverFiberEquiv.{u, max (u + 1) r, r} B X Λ _ z
  let g := (moduleSheafOverConstantCoefficientsOverFiberIso.{u, max (u + 1) r, r}
    B X Λ _ z F).toLinearEquiv
  have hflat : Module.Flat Λ ((upliftedEtaleFiberFunctor.{u, max (u + 1) r, r} B X Λ
      ((geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) r})).obj F) := by
    have := hF (.ofPoint X.obj x)
    have hL : Module.Flat Λ ↑((ModuleCat.uliftFunctor.{max (u + 1) r} Λ).obj
        ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ (.ofPoint X.obj x)).obj F)) :=
      Module.Flat.ulift (R := Λ)
        (M := (etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ (.ofPoint X.obj x)).obj F)
    exact Module.Flat.of_linearEquiv
      (upliftedEtaleFiberIso.{u, max (u + 1) r, r} B X Λ (.ofPoint X.obj x) F).toLinearEquiv
  refine flat_of_semilinear_equiv e.symm g.symm.toAddEquiv (fun c m => ?_)
  exact (congrArg g.symm (congrArg (· • m) (e.apply_symm_apply c).symm)).trans
    (g.symm.map_smul (e.symm c) m)

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
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

omit [IsNoetherianRing Λ] in
open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **Tag 03TT, the direction (2) ⟹ (1) for the Tor-dimension condition.** An object of
`D(X_étale, Λ)` represented by a bounded complex of constructible flat sheaves of `Λ`-modules,
read as an object of the derived category of modules over the constant coefficient ring sheaf,
locally has finite Tor dimension, for any choice `T` of derived tensor products on the slices.

On every slice, the restriction of the representing complex, concentrated in `[a, b]`, is a
complex of flat modules (`AlgebraicGeometry.isFlat_overFunctor_moduleSheafOverConstantCoefficients`
applied to the projective stalks of a constructible flat sheaf), so the restriction of the
object has Tor amplitude in `[a, b]` by Stacks 08G1; the maximal covering of each object then
witnesses Stacks 08FZ (3). -/
public theorem locallyHasFiniteTorDimension_of_isRepresentedByConstructibleFlatComplex_sliceStalks
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsRepresentedByConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ K) :
    LocallyHasFiniteTorDimension (X := constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)
      T ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ
        ).mapDerivedCategory.obj K) := by
  obtain ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩ := hK
  refine locallyHasFiniteTorDimension_of_forall T _ (fun V => ⟨a, b, ?_⟩)
  let Φ := moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ
  let ρ := SheafOfModules.overFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) V
  let C' := (ρ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
  refine hasTorAmplitude_of_flatRepresentative (T V) _ a b C' (fun i => ?_) (fun i hi => ?_) ?_
  · exact isFlat_overFunctor_moduleSheafOverConstantCoefficients B X Λ (C.X i)
      (fun s => by
        have := etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf B X Λ (C.X i) (hC i) s
        infer_instance) V
  · simp only [Set.mem_Icc, not_and_or, not_le] at hi
    refine ρ.map_isZero (Φ.map_isZero ?_)
    rcases hi with hi | hi
    · exact C.isZero_of_isStrictlyGE a i hi
    · exact C.isZero_of_isStrictlyLE b i hi
  · let : HasDerivedCategory.{d} (SheafOfModules.{max (u + 1) r}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).over V)) :=
      hSliceDerived V
    exact ((Functor.mapDerivedCategoryFactors.{d, d} ρ).app _).symm ≪≫
      (RingedSite.derivedRestriction.{u + 1, u, max (u + 1) r, d}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) V).mapIso
        (((Functor.mapDerivedCategoryFactors.{_, d} Φ).app C).symm ≪≫
          Φ.mapDerivedCategory.mapIso e)

/-- **Tag 03TT, the direction (2) ⟹ (1).** An object of `D(X_étale, Λ)` represented by a bounded
complex of constructible flat sheaves of `Λ`-modules lies in `D_ctf(X_étale, Λ)`, the category of
Tag 03TQ, for any choice `T` of derived tensor products on the slices: its cohomology sheaves are
constructible (`Stacks.EtaleCohomology.isConstructible_of_isRepresentedByConstructibleFlatComplex`
with the weak Serre property of Tag 03RZ (3)), and it locally has finite Tor dimension. No
hypothesis on `X` is needed. -/
@[sga "4½ Rapport 4.6" "partial"]
public theorem exists_constructibleFiniteTor_of_isRepresentedByConstructibleFlatComplex
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsRepresentedByConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ K) :
    ∃ L : ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B X Λ T,
      Nonempty (L.obj.obj ≅ K) :=
  ⟨⟨⟨K, isConstructible_of_isRepresentedByConstructibleFlatComplex B X Λ
      (isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ) K hK⟩,
    locallyHasFiniteTorDimension_of_isRepresentedByConstructibleFlatComplex_sliceStalks
      B X Λ T K hK⟩,
    ⟨Iso.refl _⟩⟩

end Stacks.EtaleCohomology
