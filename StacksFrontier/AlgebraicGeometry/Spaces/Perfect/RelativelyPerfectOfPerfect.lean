module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorStalkwise
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAtGeometricPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitudeGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummandsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksCore.Tactic.StacksAttribute

/-!
# Perfect objects are relatively perfect over a flat base

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is flat
and locally of finite presentation. A perfect object of `D(𝒪_X)` is then perfect relative to `Y`
in the sense of Stacks 0DKN: it is pseudo-coherent, and it locally has finite Tor dimension read
over `f⁻¹𝒪_Y`.

Pseudo-coherence is Stacks 08G8 and needs nothing from `f`. The Tor clause is where flatness of
`f` enters. A perfect object is, locally on the small étale site of `X`, quasi-isomorphic to a
strictly perfect complex `P`, which is bounded and whose terms are direct summands of finite free
`𝒪_X`-modules, hence flat; and `𝒪_X` is flat over `f⁻¹𝒪_Y`, so those terms stay flat when their
scalars are restricted to `f⁻¹𝒪_Y`. A bounded complex of flat modules representing an object
bounds its Tor amplitude, by Stacks 08G1.

That last flatness is proved here at the stalks. Flatness of a sheaf of modules on a site is a
condition on its stalks at a conservative family of points (Stacks 05VC); on a slice of the small
étale site the localizations of the geometric points are such a family, and the map of stalks
there is the map of stalks of `f⁻¹𝒪_Y ⟶ 𝒪_X` at the geometric point (Stacks 04H2), which is the
map on étale local rings of Stacks 04NG and is flat exactly when `f` is (Stacks 08EW). A module
flat over the étale local ring of `X` is then flat over that of `Y`, flatness being transitive.

## Main results

* `Stacks.RestrictScalarsFlat.isFlatModuleStalk_restrictScalars`: the stalk of a restriction of
  scalars along a map of structure sheaves whose stalk map is flat is a flat module.
* `Stacks.RestrictScalarsFlat.flat_restrictScalarsStalkRingHom_over`: flatness of the map of
  stalks of a map of structure sheaves passes to the slices of the site.
* `Stacks.RestrictScalarsFlat.isFlat_restrictScalars`: restriction of scalars along a stalkwise
  flat map of structure sheaves takes flat sheaves of modules to flat sheaves of modules.
* `AlgebraicGeometry.Space.flat_inverseImageStalkRingHom`: for a flat morphism of algebraic
  spaces the map of stalks of `f⁻¹𝒪_Y ⟶ 𝒪_X` at every geometric point is flat.
* `AlgebraicGeometry.Space.isFlat_restrictScalars_over`: for a flat morphism, restriction of
  scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X` preserves flatness on every slice of the small étale site.
* `AlgebraicGeometry.Space.isPerfectRelativeTo_of_isPerfect`: the first assertion of Stacks
  0DKS — a perfect object of `D(𝒪_X)` is `Y`-perfect.
* `AlgebraicGeometry.Space.isRelativelyPerfect_of_isPerfect`: the same, with relative
  perfectness spelled as `AlgebraicGeometry.Space.IsRelativelyPerfect` spells it.

## Implementation notes

The stalkwise route is taken because the two universe-insensitive alternatives are unavailable.
Stacks 073C, `AlgebraicGeometry.Space.isFlat_iff_smallEtaleRingedToposHom_isFlat`, reads flatness
of `f` as flatness of the morphism of small étale ringed topoi, whose own notion of flatness
(`Stacks.IsFlatMapULift`) is about sheaves of modules with sections one universe up, while the
module categories here have sections in the universe `u` of the schemes and
`Stacks.SheafOfModules.sheafULiftIsoId` does not bridge the two on the small étale site. And
Stacks 0E8J, the restriction of flatness to a slice, is not available in the library.

The flat representative on a slice is `P` with its scalars restricted along the restriction
`ψ'` of `f⁻¹𝒪_Y ⟶ 𝒪_X` to that slice, and `ψ'` is spelled as the image of the structure map
under `CategoryTheory.GrothendieckTopology.overPullback`. The spelling matters: with the
structure sheaf of the slice written as the slice of the structure sheaf, restriction of scalars
and restriction to a slice commute on the nose
(`AlgebraicGeometry.RingedSite.restrictScalars_comp_overFunctor`), so the complex of
`f⁻¹𝒪_Y|_V`-modules built from `P` and the restriction to `V` of the complex of `f⁻¹𝒪_Y`-modules
built from a global representative of `E` are the same complex, and the quasi-isomorphism between
them is the one `P` already carries.

The second assertion of Stacks 0DKS — that `K ⊗^{𝐋}_{𝒪_X} M` is `Y`-perfect when `K` is perfect
and `M` is `Y`-perfect — is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectDerivedTensor`, which also carries
the `@[stacks 0DKS]` registration of both assertions together.

## References

* [Stacks Project, Tag 0DKS](https://stacks.math.columbia.edu/tag/0DKS)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 08EW](https://stacks.math.columbia.edu/tag/08EW)
* [Stacks Project, Tag 09J9](https://stacks.math.columbia.edu/tag/09J9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u d e

namespace Stacks.RestrictScalarsFlat

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  {O₁ O₂ : Sheaf J CommRingCat.{w}}
  (ψ : Stacks.SheafOfModules.Tensor.ringSheaf O₁ ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O₂)

/-- The stalk of a restriction of scalars along a flat map of structure sheaves is flat. -/
theorem isFlatModuleStalk_restrictScalars (Ψ : J.Point.{w})
    (hψ : (Stacks.restrictScalarsStalkRingHom Ψ ψ).Flat)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (hM : Stacks.IsFlatModuleStalk Ψ O₂ M) :
    Stacks.IsFlatModuleStalk Ψ O₁ ((SheafOfModules.restrictScalars ψ).obj M) := by
  let alg : Algebra ((Ψ.presheafFiber (A := CommRingCat.{w})).obj O₁.obj)
      ((Ψ.presheafFiber (A := CommRingCat.{w})).obj O₂.obj) :=
    (Stacks.restrictScalarsStalkRingHom Ψ ψ).toAlgebra
  have h1 : Module.Flat ((Ψ.presheafFiber (A := CommRingCat.{w})).obj O₁.obj)
      ((Ψ.presheafFiber (A := CommRingCat.{w})).obj O₂.obj) := hψ
  have h2 : Module.Flat ((Ψ.presheafFiber (A := CommRingCat.{w})).obj O₂.obj)
      ((ModuleCat.restrictScalars (Stacks.restrictScalarsStalkRingHom Ψ ψ)).obj
        (Stacks.moduleStalk Ψ O₂ M)) := hM
  let : IsScalarTower ((Ψ.presheafFiber (A := CommRingCat.{w})).obj O₁.obj)
      ((Ψ.presheafFiber (A := CommRingCat.{w})).obj O₂.obj)
      ((ModuleCat.restrictScalars (Stacks.restrictScalarsStalkRingHom Ψ ψ)).obj
        (Stacks.moduleStalk Ψ O₂ M)) :=
    ⟨fun r s m => mul_smul (Stacks.restrictScalarsStalkRingHom Ψ ψ r) s
      (show Stacks.moduleStalk Ψ O₂ M from m)⟩
  have h3 : Module.Flat ((Ψ.presheafFiber (A := CommRingCat.{w})).obj O₁.obj)
      ((ModuleCat.restrictScalars (Stacks.restrictScalarsStalkRingHom Ψ ψ)).obj
        (Stacks.moduleStalk Ψ O₂ M)) :=
    Module.Flat.trans _ ((Ψ.presheafFiber (A := CommRingCat.{w})).obj O₂.obj) _
  exact Module.Flat.of_linearEquiv
    (Stacks.restrictScalarsModuleStalkIso Ψ ψ M).toLinearEquiv

end Stacks.RestrictScalarsFlat

namespace Stacks.RestrictScalarsFlat

open _root_.Stacks.AlgebraicGeometry

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  Stacks.SheafOfModules.DerivedTensorProduct.sliceLocallySmall

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  {O₁ O₂ : Sheaf J CommRingCat.{w}}
  (ψ : Stacks.SheafOfModules.Tensor.ringSheaf O₁ ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O₂)

/-- **Flatness of the map of stalks of `ψ` passes to the slices.** At the lift `Φ.over ξ` of a
point to the slice over `V`, the map of stalks of the restriction of `ψ` to that slice is
conjugate, through the comparison of Stacks 04H2, to the map of stalks of `ψ` at `Φ`; so the one
is flat as soon as the other is. The restriction is taken as a parameter together with the
assertion that it is the restriction, so that a consumer may hand over whichever spelling of it
it has. -/
theorem flat_restrictScalarsStalkRingHom_over (Φ : J.Point.{w}) {V : C} (ξ : Φ.fiber.obj V)
    (ψ' : Stacks.SheafOfModules.Tensor.ringSheaf (O₁.over V) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf (O₂.over V))
    (hψ' : ψ' = (J.overPullback RingCat.{w} V).map ψ)
    (hflat : (Stacks.restrictScalarsStalkRingHom Φ ψ).Flat) :
    (Stacks.restrictScalarsStalkRingHom (Φ.over ξ) ψ').Flat := by
  let i : ∀ O : Sheaf J CommRingCat.{w},
      ((Φ.over ξ).presheafFiber (A := CommRingCat.{w})).obj (O.over V).obj ≅
        (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj := fun O =>
    (GrothendieckTopology.Point.presheafFiberOverIso Φ ξ CommRingCat.{w}).app O.obj
  have hgerm : ∀ (O : Sheaf J CommRingCat.{w}) (W : Over V) (y : (Φ.over ξ).fiber.obj W)
      (a : (Stacks.SheafOfModules.Tensor.ringSheaf (O.over V)).obj.obj (op W)),
      (i O).hom.hom
          (Stacks.ringStalkGerm (Φ.over ξ) (O.over V) W y a) =
        Stacks.ringStalkGerm Φ O W.left y.val a := fun O W y a =>
    ConcreteCategory.congr_hom
      (_root_.AlgebraicGeometry.presheafFiberOverIso_hom_toPresheafFiber Φ ξ CommRingCat.{w}
        O.obj W y) a
  have key : (i O₂).hom.hom.comp (Stacks.restrictScalarsStalkRingHom (Φ.over ξ) ψ') =
      (Stacks.restrictScalarsStalkRingHom Φ ψ).comp (i O₁).hom.hom := by
    refine RingHom.ext fun r => ?_
    obtain ⟨W, y, a, rfl⟩ := Stacks.ringStalkGerm_jointly_surjective (Φ.over ξ) (O₁.over V) r
    have l1 := Stacks.restrictScalarsStalkRingHom_ringStalkGerm (Φ.over ξ) ψ' W y a
    have l2 := Stacks.restrictScalarsStalkRingHom_ringStalkGerm Φ ψ W.left y.val a
    rw [RingHom.comp_apply, RingHom.comp_apply, l1, hgerm O₂ W y, hgerm O₁ W y a, l2, hψ']
    rfl
  have hb₁ : Function.Bijective (CommRingCat.Hom.hom (i O₁).hom) :=
    ConcreteCategory.bijective_of_isIso (i O₁).hom
  have hb₂ : Function.Bijective (CommRingCat.Hom.hom (i O₂).hom) :=
    ConcreteCategory.bijective_of_isIso (i O₂).hom
  refine (RingHom.Flat.comp_iff_of_bijective_left hb₂).1 ?_
  rw [key]
  exact (RingHom.Flat.comp_iff_of_bijective_right hb₁).2 hflat

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Restriction of scalars along a stalkwise flat map of structure sheaves preserves
flatness.** If the map of stalks of `ψ` is flat at every point of a conservative family, then a
flat sheaf of `O₂`-modules is flat as a sheaf of `O₁`-modules. Flatness is a stalkwise condition
by Stacks 05VC, and a flat module over a flat algebra is flat over the base. -/
theorem isFlat_restrictScalars {t : Type*} (p : t → J.Point.{w})
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (hψ : ∀ i, (Stacks.restrictScalarsStalkRingHom (p i) ψ).Flat)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat (O := O₂) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := O₁)
      ((SheafOfModules.restrictScalars ψ).obj M) :=
  Stacks.isFlat_of_forall_isFlatModuleStalk O₁ _ p hp fun i =>
    isFlatModuleStalk_restrictScalars ψ (p i) (hψ i) M
      (Stacks.isFlatModuleStalk_of_hasLocalSingleRelationFactorizations (p i) O₂ M
        (Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse
          (O := O₂) (F := M) hM))

end Stacks.RestrictScalarsFlat

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The map of stalks of `f⁻¹𝒪_Y ⟶ 𝒪_X` at a geometric point of a flat morphism is flat.**
By Stacks 08EW and 04NG flatness of `f` is flatness of its maps on étale local rings, which are
the fibres of the inverse-image structure map at the geometric points. -/
theorem flat_inverseImageStalkRingHom (hflat : IsFlat B S hS f.hom)
    (x : GeometricPoint B S hS X.1) :
    (inverseImageStalkRingHom B S hS f x).Flat := by
  have he : inverseImageStalkRingHom B S hS f x =
      ((etaleSitePoint B S hS X.1 x X.2).presheafFiber.map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom).hom :=
    RingHom.ext (inverseImageStalkRingHom_eq_sheafFiber_map B S hS f x)
  rw [he]
  exact etaleLocalRingMap_flat_iff_stalkRingMap_flat.1
    ((isFlat_iff_forall_etaleLocalRingMap_flat B S hS f).1 hflat x)

/-- **Over a flat morphism, restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X` preserves flatness on
every slice of the small étale site.** Flatness of a sheaf of modules is a condition on its
stalks at a conservative family of points, by Stacks 05VC; the localizations of the geometric
points are such a family on a slice, and there the map of stalks is the map of stalks of
`f⁻¹𝒪_Y ⟶ 𝒪_X` at the geometric point, which is flat. The flat module over the étale local ring
of `X` is then flat over that of `Y`, flatness being transitive. -/
theorem isFlat_restrictScalars_over (hflat : IsFlat B S hS f.hom)
    (V : (inverseImageRingedSite B S hS f).C)
    (ψ' : (Stacks.SheafOfModules.Tensor.ringSheaf
        (inverseImageRingedSite B S hS f).O).over V ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).over V)
    (hψ' : ψ' = ((smallEtaleRingedSite B S hS X.1 X.2).J.overPullback RingCat.{u} V).map
      (inverseImageStructureMap B S hS f))
    (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).over V))
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (smallEtaleRingedSite B S hS X.1 X.2).O.over V) N) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (inverseImageRingedSite B S hS f).O.over V)
      ((SheafOfModules.restrictScalars ψ').obj N) :=
  Stacks.RestrictScalarsFlat.isFlat_restrictScalars
    (O₁ := (inverseImageRingedSite B S hS f).O.over V)
    (O₂ := (smallEtaleRingedSite B S hS X.1 X.2).O.over V) ψ'
    (fun ζ : Σ x : GeometricPoint B S hS X.1,
        (etaleSitePoint B S hS X.1 x X.2).fiber.obj V =>
      (etaleSitePoint B S hS X.1 ζ.1 X.2).over ζ.2)
    (isConservativeFamilyOfPoints_etaleSitePointOver B S hS X.2 V)
    (fun ζ => Stacks.RestrictScalarsFlat.flat_restrictScalarsStalkRingHom_over
      (inverseImageStructureMap B S hS f) _ ζ.2 ψ' hψ'
      (flat_inverseImageStalkRingHom B S hS f hflat ζ.1))
    N hN

variable [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f).C) M,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O).obj M).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f).C)
        (K L : CochainComplex
          (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor
          ((inverseImageRingedSite B S hS f).over U).O) (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

/-- **Stacks 0DKS, the first assertion.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S` which is flat and locally of finite presentation. A perfect object `E` of `D(𝒪_X)` is perfect
relative to `Y`, for every family `T` of derived tensor products on the slices of
`(X_étale, f⁻¹𝒪_Y)`.

Pseudo-coherence, the first clause, is Stacks 08G8 and uses nothing about `f`. For the second,
perfectness supplies, over each member `V` of a covering of each object of the small étale site, a
strictly perfect complex `P` of `𝒪_X|_V`-modules and a quasi-isomorphism `P ⟶ E|_V`. A strictly
perfect complex is bounded and its terms are direct summands of finite free modules, hence flat,
and flatness survives the restriction of scalars to `f⁻¹𝒪_Y|_V` because `f` is flat. So `E|_V`,
read over `f⁻¹𝒪_Y|_V`, is represented by a bounded complex of flat modules, which bounds its Tor
amplitude by Stacks 08G1. -/
theorem isPerfectRelativeTo_of_isPerfect
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) :
    IsPerfectRelativeTo B S hS f hflat hlfp T E := by
  refine ⟨RingedSite.isPseudoCoherent_of_isPerfect_general _ hE, ?_⟩
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  intro U
  obtain ⟨Sv, hSv, hmodels⟩ := hK U
  refine ⟨Sv, hSv, fun {V} g hg => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hmodels g hg
  have := hq
  let ψ' : (Stacks.SheafOfModules.Tensor.ringSheaf
        (inverseImageRingedSite B S hS f).O).over V ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).over V :=
    ((smallEtaleRingedSite B S hS X.1 X.2).J.overPullback RingCat.{u} V).map
      (inverseImageStructureMap B S hS f)
  let rs := SheafOfModules.restrictScalars.{u} ψ'
  have hrsA : rs.Additive := inferInstanceAs
    (SheafOfModules.restrictScalars.{u} ψ').Additive
  have hrsL : Limits.PreservesFiniteLimits rs := inferInstanceAs
    (Limits.PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} ψ'))
  have hrsC : Limits.PreservesFiniteColimits rs := inferInstanceAs
    (Limits.PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} ψ'))
  let : Limits.PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        (inverseImageRingedSite B S hS f).O) V) :=
    RingedSite.sliceRestrictionPreservesFiniteLimits (inverseImageRingedSite B S hS f) V
  let : Limits.PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        (inverseImageRingedSite B S hS f).O) V) :=
    RingedSite.sliceRestrictionPreservesFiniteColimits (inverseImageRingedSite B S hS f) V
  let : HasDerivedCategory.{e} (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        (inverseImageRingedSite B S hS f).O).over V)) :=
    inferInstanceAs (HasDerivedCategory.{e}
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over V)))
  let : HasDerivedCategory.{e} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((inverseImageRingedSite B S hS f).O.over V))) :=
    inferInstanceAs (HasDerivedCategory.{e}
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over V)))
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  obtain ⟨a, ha⟩ := hP.bounded.bddBelow
  have hzeroP : ∀ i : ℤ, i ∉ Set.Icc a b → IsZero (P.X i) := by
    intro i hi
    by_contra hc
    exact hi (Set.mem_Icc.2 ⟨ha hc, hb hc⟩)
  have hqi : QuasiIso ((rs.mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
    have : rs.PreservesHomology := Functor.preservesHomologyOfExact rs
    exact HomologicalComplex.quasiIso_map_of_preservesHomology q rs (hφ := hq)
  have hqQ : IsIso (DerivedCategory.Q.map
      ((rs.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hqi
  refine ⟨a, b, Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative
    (T V) _ a b ((rs.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (fun i => isFlat_restrictScalars_over B S hS f hflat V ψ' rfl (P.X i)
      (Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect_general
        (Y := (smallEtaleRingedSite B S hS X.1 X.2).over V) hP i))
    (fun i hi => rs.map_isZero (hzeroP i hi)) ?_⟩
  refine (@asIso _ _ _ _ _ hqQ) ≪≫ ?_
  refine ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
      (inverseImageRingedSite B S hS f).O) V).mapDerivedCategoryFactors.app
    (((scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫ ?_
  exact (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
      (inverseImageRingedSite B S hS f).O) V).mapDerivedCategory.mapIso
    (((derivedScalarRestrictionFactors B S hS f).app K).symm ≪≫
      (derivedScalarRestriction B S hS f).mapIso eK)

/-- **Stacks 0DKS, the first assertion, in the vocabulary of Stacks 0DKN.** A perfect object of
`D(𝒪_X)` is perfect relative to `Y`, relative perfectness being measured as
`AlgebraicGeometry.Space.IsRelativelyPerfect` does it, against the derived tensor products of
Stacks 06YU on the slices. -/
theorem isRelativelyPerfect_of_isPerfect
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) :
    IsRelativelyPerfect B S hS f hflat hlfp E :=
  (isRelativelyPerfect_iff_isPerfectRelativeTo B S hS f hflat hlfp
    (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct
      ((inverseImageRingedSite B S hS f).over U)) E).2
    (isPerfectRelativeTo_of_isPerfect B S hS f hflat hlfp _ E hE)

end AlgebraicGeometry.Space

end
