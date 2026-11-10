module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorStalkwise
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.AffineChartModel
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.Homology.RelativelyPerfect.TorAmplitudeAtGeometricPoint

/-!
# Tor amplitude of a geometric stalk over the base, read on an affine chart

Let `f : X ⟶ 𝒮` be a morphism of algebraic spaces, `x̄` a geometric point of `X` and `E` an object
of `D(𝒪_X)`. The second clause of relative perfectness is read at `x̄` on the geometric stalk
`E_x̄`, with its scalars restricted along the map of stalks `(f⁻¹𝒪_𝒮)_x̄ ⟶ 𝒪_{X, x̄}`
(`AlgebraicGeometry.Space.locallyHasFiniteTorDimension_derivedScalarRestriction_of_stalkBound`).
This file compares that map with the map of geometric stalks `𝒪_{𝒮, f(x̄)} ⟶ 𝒪_{X, x̄}` of the
structure map of Stacks 03G8 (`AlgebraicGeometry.Space.stalkStructureMap`).

## Main results

* `AlgebraicGeometry.Space.inverseImageStalkRingHom_eq_sheafFiber_map`: the map of stalks of
  `f⁻¹𝒪_𝒮 ⟶ 𝒪_X` is the fibre of the inverse-image structure map.
* `AlgebraicGeometry.Space.inverseImageStalkRingHom_fiberRingIso`: composed with the comparison
  `(f⁻¹𝒪_𝒮)_x̄ ≅ 𝒪_{𝒮, f(x̄)}` of Stacks 04K2 it is `AlgebraicGeometry.Space.stalkStructureMap`.
* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_geometricStalk_iff_hasTorAmplitudeAt`: for
  `𝒮 = Spec R`, an affine étale chart `Spec A ⟶ X` over `𝒮` and a complex `P` of `A`-modules
  modelling `E` on it, the Tor amplitude of `E_x̄` over `(f⁻¹𝒪_𝒮)_x̄` at the image `x̄` of a
  geometric point `ū` of the chart is the Tor amplitude of `P_q` over `R_{q ∩ R}`, `q` the prime
  under `ū`.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Lemma 76.54.5 (0DL5)](https://stacks.math.columbia.edu/tag/0DL5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w₁ w₂

namespace ModuleCat

variable {R R' : Type u} [CommRing R] [CommRing R'] (β : R →+* R') (hβ : Function.Bijective β)

include hβ in
/-- Along a bijective ring map, the unit `M ⟶ R' ⊗_R M` of extension and restriction of scalars
is bijective. -/
theorem bijective_extendRestrictScalarsAdj_unit_app (M : ModuleCat.{u} R) :
    Function.Bijective ((extendRestrictScalarsAdj.{u, u, u} β).unit.app M) := by
  let βₗ : R →ₗ[R] (restrictScalars β).obj (ModuleCat.of R' R') :=
    { toFun := β
      map_add' := β.map_add
      map_smul' := fun r x => show β (r * x) = β r * β x from map_mul β r x }
  let c := (TensorProduct.congr (LinearEquiv.ofBijective βₗ hβ).symm (LinearEquiv.refl R M)).trans
    (TensorProduct.lid R M)
  have hc : ∀ m : M, c ((extendRestrictScalarsAdj.{u, u, u} β).unit.app M m) = m := fun m => by
    have h1 : (LinearEquiv.ofBijective βₗ hβ).symm (1 : R') = 1 :=
      (LinearEquiv.ofBijective βₗ hβ).symm_apply_eq.2 (map_one β).symm
    refine (congrArg c (extendRestrictScalarsAdj_unit_app_apply β M m)).trans ?_
    change TensorProduct.lid R M ((LinearEquiv.ofBijective βₗ hβ).symm (1 : R') ⊗ₜ m) = m
    rw [h1, TensorProduct.lid_tmul, one_smul]
  exact ⟨Function.LeftInverse.injective hc, fun t => ⟨c t, c.injective (hc (c t))⟩⟩

/-- Along a bijective ring map, restriction of scalars after extension of scalars is the
identity of the derived category, for any models of the two derived categories. -/
def restrictScalarsExtendScalarsMapDerivedIso
    [HasDerivedCategory.{w₁} (ModuleCat.{u} R)] [HasDerivedCategory.{w₂} (ModuleCat.{u} R')]
    [Limits.PreservesFiniteLimits (extendScalars.{u, u, u} β)]
    (K : DerivedCategory (ModuleCat.{u} R)) :
    (restrictScalars.{u} β).mapDerivedCategory.obj
        ((extendScalars.{u, u, u} β).mapDerivedCategory.obj K) ≅ K :=
  let L := DerivedCategory.Q.objPreimage K
  let eL : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  haveI : ∀ M, IsIso ((extendRestrictScalarsAdj.{u, u, u} β).unit.app M) := fun M =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_extendRestrictScalarsAdj_unit_app β hβ M)
  let c : ((restrictScalars.{u} β).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((extendScalars.{u, u, u} β).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≅ L :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (asIso ((extendRestrictScalarsAdj.{u, u, u} β).unit.app (L.X i))).symm)
      (fun i j _ => by
        change inv _ ≫ _ = _ ≫ inv _
        rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
        exact (extendRestrictScalarsAdj.{u, u, u} β).unit.naturality (L.d i j))
  (restrictScalars.{u} β).mapDerivedCategory.mapIso
      ((extendScalars.{u, u, u} β).mapDerivedCategory.mapIso eL.symm ≪≫
        (extendScalars.{u, u, u} β).mapDerivedCategoryFactors.app L) ≪≫
    (restrictScalars.{u} β).mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso c ≪≫ eL

end ModuleCat

namespace AlgebraicGeometry.Space

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The map of stalks of `f⁻¹𝒪_Y ⟶ 𝒪_X` at a geometric point is the fibre of the inverse-image
structure map of the morphism of small étale ringed topoi: the two agree on germs. -/
theorem inverseImageStalkRingHom_eq_sheafFiber_map (x : GeometricPoint B S hS X.1)
    (w : ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
      (inverseImageRingedSite B S hS f).O.obj) :
    inverseImageStalkRingHom B S hS f x w =
      ((etaleSitePoint B S hS X.1 x X.2).presheafFiber.map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom).hom w := by
  obtain ⟨U, ξ, a, rfl⟩ := Stacks.ringStalkGerm_jointly_surjective
    (etaleSitePoint B S hS X.1 x X.2) (inverseImageRingedSite B S hS f).O w
  refine (Stacks.restrictScalarsStalkRingHom_ringStalkGerm _ _ U ξ a).trans ?_
  exact (ConcreteCategory.congr_hom ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_naturality
    (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom U ξ) a).symm

/-- **The map of stalks of `f⁻¹𝒪_Y ⟶ 𝒪_X`, read through Stacks 04K2, is the map of geometric
stalks of the structure map.** -/
theorem inverseImageStalkRingHom_fiberRingIso (x : GeometricPoint B S hS X.1)
    (z : ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber
      (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O) :
    inverseImageStalkRingHom B S hS f x
        (((smallEtaleInverseImageFiberRingIso B S hS f x).hom.app
          (smallEtaleRingedTopos B S hS Y).O).hom z) =
      (stalkStructureMap B S hS f x).hom z :=
  inverseImageStalkRingHom_eq_sheafFiber_map B S hS f x _

/-! ### The local ring at the point of an affine represented space under a geometric point -/

section ChartPoint

variable {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (g : B.obj hA ⟶ B.obj hS) (ū : GeometricPoint B S hS (yoneda.obj (specFppfOver B S hS hA g)))

/-- The point of `Spec A` under a geometric point of the algebraic space represented by `Spec A`,
read on the identity chart. -/
abbrev identityChartPrime : PrimeSpectrum A :=
  chartPoint B S hS (yoneda.obj (specFppfOver B S hS hA g))
    (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)

/-- The germ at a point of `Spec A` of the global function `a` is the image of `a` in the
stalk. -/
theorem germ_ΓSpecIso_inv (x : PrimeSpectrum A) (a : A) :
    (Spec (CommRingCat.of A)).presheaf.germ ⊤ x trivial
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = StructureSheaf.toStalk A x a :=
  rfl

/-- The local ring of the identity chart at the point under `ū`, as an `A`-algebra through the
germs of global functions. -/
instance algebraChartLocalRing :
    Algebra A (chartLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
    (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)) :=
  (StructureSheaf.toStalk A (identityChartPrime B S hS hA g ū)).hom.toAlgebra

/-- The local ring of the identity chart at the point under `ū` is the localization of `A` at
that point. -/
instance isLocalization_chartLocalRing :
    IsLocalization.AtPrime (chartLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
      (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū))
      (identityChartPrime B S hS hA g ū).asIdeal :=
  StructureSheaf.IsLocalization.to_stalk A (identityChartPrime B S hS hA g ū)

/-- The localization of `A` at the point under `ū` is the local ring of the identity chart. -/
def chartLocalRingEquiv :
    Localization.AtPrime (identityChartPrime B S hS hA g ū).asIdeal ≃ₐ[A]
      chartLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
        (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū) :=
  IsLocalization.algEquiv (identityChartPrime B S hS hA g ū).asIdeal.primeCompl _ _

/-- The map from the localization of `A` at the point under `ū` to the geometric stalk ring of
`h_{Spec A}` at `ū`: the local ring of the chart followed by its strict henselization, which is the
étale local ring (Stacks 04KF), read in the geometric stalk ring. -/
def chartLocalizationRingHom :
    Localization.AtPrime (identityChartPrime B S hS hA g ū).asIdeal →+*
      geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hA g),
        isAlgebraicSpace_yoneda B S hS _⟩) ū :=
  (pointStalkRingEquiv B S hS ⟨yoneda.obj (specFppfOver B S hS hA g),
      isAlgebraicSpace_yoneda B S hS _⟩ ū).symm.toRingHom.comp
    ((chartLocalRingToEtaleLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
        (isAlgebraicSpace_yoneda B S hS _)
        (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)).comp
      (chartLocalRingEquiv B S hS hA g ū).toRingEquiv.toRingHom)

/-- The map from the local ring of the identity chart to the étale local ring sends the image of an
element `a` of `A` to the germ of the global function `a`. -/
theorem chartLocalRingToEtaleLocalRing_algebraMap (a : A) :
    chartLocalRingToEtaleLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
        (isAlgebraicSpace_yoneda B S hS _) (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)
        (algebraMap A _ a) =
      etaleLocalRingGerm B S hS (yoneda.obj (specFppfOver B S hS hA g)) ū
        (op (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a : (Γ(chartScheme
          (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū).chart, ⊤))) := by
  change chartLocalRingToEtaleLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
      (isAlgebraicSpace_yoneda B S hS _) (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)
      ((StructureSheaf.toStalk A (identityChartPrime B S hS hA g ū)).hom a) = _
  rw [← germ_ΓSpecIso_inv]
  exact chartLocalRingToEtaleLocalRing_germ B S hS (yoneda.obj (specFppfOver B S hS hA g))
    (isAlgebraicSpace_yoneda B S hS _) (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)

/-- The map from the localization to the geometric stalk ring sends the image of an element of `A`
to its germ, read in the étale local ring. -/
theorem pointStalkRingEquiv_chartLocalizationRingHom_algebraMap (a : A) :
    pointStalkRingEquiv B S hS
        ⟨yoneda.obj (specFppfOver B S hS hA g), isAlgebraicSpace_yoneda B S hS _⟩ ū
        (chartLocalizationRingHom B S hS hA g ū (algebraMap A _ a)) =
      etaleLocalRingGerm B S hS (yoneda.obj (specFppfOver B S hS hA g)) ū
        (op (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a : (Γ(chartScheme
          (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū).chart, ⊤))) := by
  refine (RingEquiv.apply_symm_apply _ _).trans ?_
  refine (congrArg (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
    (isAlgebraicSpace_yoneda B S hS _) (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū))
      ((chartLocalRingEquiv B S hS hA g ū).commutes a)).trans ?_
  exact chartLocalRingToEtaleLocalRing_algebraMap B S hS hA g ū a

/-- The geometric stalk ring of `h_{Spec A}` at `ū` is faithfully flat over the localization of `A`
at the point under `ū`: the étale local ring is faithfully flat over the local ring of the chart
(Stacks 04KF). -/
theorem faithfullyFlat_chartLocalizationRingHom :
    letI := (chartLocalizationRingHom B S hS hA g ū).toAlgebra
    Module.FaithfullyFlat (Localization.AtPrime (identityChartPrime B S hS hA g ū).asIdeal)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hA g),
        isAlgebraicSpace_yoneda B S hS _⟩) ū) := by
  let L := chartLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
    (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)
  let κ := chartLocalRingToEtaleLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
    (isAlgebraicSpace_yoneda B S hS _) (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)
  let p := pointStalkRingEquiv B S hS ⟨yoneda.obj (specFppfOver B S hS hA g),
    isAlgebraicSpace_yoneda B S hS _⟩ ū
  let e := (chartLocalRingEquiv B S hS hA g ū).toRingEquiv
  let : Algebra L (etaleLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g)) ū) := κ.toAlgebra
  have h₁ :
      Module.FaithfullyFlat L (etaleLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g)) ū) :=
    faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
      (isAlgebraicSpace_yoneda B S hS _) (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)
  let : Algebra L (geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hA g),
      isAlgebraicSpace_yoneda B S hS _⟩) ū) := (p.symm.toRingHom.comp κ).toAlgebra
  have h₂ : Module.FaithfullyFlat L
      (geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hA g),
      isAlgebraicSpace_yoneda B S hS _⟩) ū) :=
    Module.FaithfullyFlat.of_linearEquiv L _
      { p.toAddEquiv with
        map_smul' := fun c y =>
          (map_mul p (p.symm (κ c)) y).trans (congrArg (· * p y) (p.apply_symm_apply (κ c))) }
  let : Algebra (Localization.AtPrime (identityChartPrime B S hS hA g ū).asIdeal) L :=
    e.toRingHom.toAlgebra
  have h₃ :
      Module.FaithfullyFlat (Localization.AtPrime (identityChartPrime B S hS hA g ū).asIdeal) L :=
    (RingHom.faithfullyFlat_algebraMap_iff).1 (RingHom.FaithfullyFlat.of_bijective e.bijective)
  let := (chartLocalizationRingHom B S hS hA g ū).toAlgebra
  have : IsScalarTower (Localization.AtPrime (identityChartPrime B S hS hA g ū).asIdeal) L
      (geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hA g),
        isAlgebraicSpace_yoneda B S hS _⟩) ū) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.FaithfullyFlat.trans _ L _

/-- **Flatness descends along the map from the localization to the geometric stalk ring**
(Stacks 05VL): a module over the geometric stalk ring of `h_{Spec A}` at `ū` is flat over it
exactly when it is flat over the localization of `A` at the point under `ū`, the geometric stalk
ring being a strict henselization of that local ring (Stacks 04KF). -/
theorem flat_chartLocalizationRingHom_iff (N : Type*) [AddCommGroup N]
    [Module (geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hA g),
      isAlgebraicSpace_yoneda B S hS _⟩) ū) N] :
    letI : Module (Localization.AtPrime (identityChartPrime B S hS hA g ū).asIdeal) N :=
      Module.compHom N (chartLocalizationRingHom B S hS hA g ū)
    Module.Flat (Localization.AtPrime (identityChartPrime B S hS hA g ū).asIdeal) N ↔
      Module.Flat (geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hA g),
        isAlgebraicSpace_yoneda B S hS _⟩) ū) N := by
  let L := chartLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA g))
    (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)
  let T := chartHenselizationTower B S hS (yoneda.obj (specFppfOver B S hS hA g))
    (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)
  let σ := chartStrictHenselizationEquiv B S hS (yoneda.obj (specFppfOver B S hS hA g))
    (isAlgebraicSpace_yoneda B S hS _) (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)
  let p := pointStalkRingEquiv B S hS ⟨yoneda.obj (specFppfOver B S hS hA g),
    isAlgebraicSpace_yoneda B S hS _⟩ ū
  let τ : T.strictHenselization ≃+* geometricStalkRing B S hS
      (X := ⟨yoneda.obj (specFppfOver B S hS hA g), isAlgebraicSpace_yoneda B S hS _⟩) ū :=
    σ.trans p.symm
  let e := (chartLocalRingEquiv B S hS hA g ū).toRingEquiv
  let : Module T.strictHenselization N := Module.compHom N τ.toRingHom
  let : Module T.henselization N :=
    Module.compHom N (algebraMap T.henselization T.strictHenselization)
  let : Module L N := Module.compHom N (algebraMap L T.strictHenselization)
  have h₁ : List.TFAE [Module.Flat L N, Module.Flat T.henselization N,
      Module.Flat T.strictHenselization N] :=
    flat_tfae_henselization (R := L) (Rh := T.henselization) (Rsh := T.strictHenselization)
      (K := separableClosure (IsLocalRing.ResidueField L)
        (chartGeometricPoint
          (yonedaIdentityNeighborhood (specFppfOver B S hS hA g) ū)).residueField)
      (Msh := N)
  exact (Module.Flat.compHom_ringEquiv_iff _ _ N e).trans
    ((h₁.out 1 3).trans (Module.Flat.compHom_ringEquiv_iff _ _ N τ))

end ChartPoint

/-! ### The Tor amplitude of a geometric stalk, read on an affine chart -/

section ChartTorAmplitude

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.hasSheafCompose_forget₂_commRingCat
-- `representedDerivedAssociatedModule`, the two geometric-stalk computations of
-- `DualizingComplexGeometricStalk.lean` and `StacksDraft.TorAmplitude.HasTorAmplitudeCanonical`
-- are stated at the standard model of the derived categories they involve.
attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] (hR : B.Contains (Spec (CommRingCat.of R)))
  (gR : B.obj hR ⟶ B.obj hS) {A : Type u} [CommRing A] [Algebra R A]
  (hA : B.Contains (Spec (CommRingCat.of A))) (gA : B.obj hA ⟶ B.obj hS)

variable {X : AlgebraicSpaces B S hS}
  (f : X ⟶ ⟨yoneda.obj (specFppfOver B S hS hR gR), isAlgebraicSpace_yoneda B S hS _⟩)
  (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
    AlgebraicSpaces B S hS) ⟶ X)
  (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    B.obj hA ⟶ B.obj hR) ≫ gR = gA)
  (hφf : yoneda.map (specFppfOverMap B S hS hR gR hA gA w) = φ.hom ≫ f.hom)
  (ū : GeometricPoint B S hS (yoneda.obj (specFppfOver B S hS hA gA)))

include hφf in
/-- The prime of `Spec R` under the image of `ū` in `𝒮 = Spec R` is the inverse image of the
prime of `Spec A` under `ū`. -/
theorem identityChartPrime_geometricPointMap :
    (identityChartPrime B S hS hR gR
      (geometricPointMap f.hom (geometricPointMap φ.hom ū))).asIdeal =
      (identityChartPrime B S hS hA gA ū).asIdeal.under R := by
  have h : geometricPointMap f.hom (geometricPointMap φ.hom ū) =
      geometricPointMap (yoneda.map (specFppfOverMap B S hS hR gR hA gA w)) ū := by
    rw [hφf]; rfl
  rw [h]
  rfl

include hφf in
/-- The canonical homomorphism of étale local rings of the composite `h_{Spec A} ⟶ X ⟶ 𝒮` sends the
germ of a function `r` on `Spec R` to the germ of its image in `A`. -/
theorem etaleLocalRingMap_comp_etaleLocalRingGerm (r : R) :
    etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS _) (φ.hom ≫ f.hom) ū
        (etaleLocalRingGerm B S hS (yoneda.obj (specFppfOver B S hS hR gR))
          (geometricPointMap (φ.hom ≫ f.hom) ū)
          (op (yonedaIdentityNeighborhood (specFppfOver B S hS hR gR)
            (geometricPointMap (φ.hom ≫ f.hom) ū)))
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r : (Γ(chartScheme
            (yonedaIdentityNeighborhood (specFppfOver B S hS hR gR)
              (geometricPointMap (φ.hom ≫ f.hom) ū)).chart, ⊤)))) =
      etaleLocalRingGerm B S hS (yoneda.obj (specFppfOver B S hS hA gA)) ū
        (op (yonedaIdentityNeighborhood (specFppfOver B S hS hA gA) ū))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap R A r) : (Γ(chartScheme
          (yonedaIdentityNeighborhood (specFppfOver B S hS hA gA) ū).chart, ⊤))) := by
  rw [← hφf]
  have key := RingHom.congr_fun (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing_yoneda B S hS
    (specFppfOverMap B S hS hR gR hA gA w) ū)
    (algebraMap R (chartLocalRing B S hS (yoneda.obj (specFppfOver B S hS hR gR))
      (yonedaIdentityNeighborhood (specFppfOver B S hS hR gR)
        (geometricPointMap (yoneda.map (specFppfOverMap B S hS hR gR hA gA w)) ū))) r)
  have hT := chartLocalRingToEtaleLocalRing_algebraMap B S hS hR gR
    (geometricPointMap (yoneda.map (specFppfOverMap B S hS hR gR hA gA w)) ū) r
  refine (congrArg (etaleLocalRingMap _ _ ū) hT).symm.trans (key.symm.trans ?_)
  refine (congrArg (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj (specFppfOver B S hS hA gA))
    (isAlgebraicSpace_yoneda B S hS _) (yonedaIdentityNeighborhood (specFppfOver B S hS hA gA) ū))
    (AlgebraicGeometry.stalkMap_toStalk_apply
      (CommRingCat.ofHom (algebraMap R A)) (identityChartPrime B S hS hA gA ū) r)).trans ?_
  exact chartLocalRingToEtaleLocalRing_algebraMap B S hS hA gA ū (algebraMap R A r)

/-- The stalk of `f⁻¹𝒪_𝒮` at the image in `X` of a geometric point `ū` of the chart. -/
abbrev chartImageInverseImageStalkRing : CommRingCat.{u} :=
  ((etaleSitePoint B S hS X.1 (geometricPointMap φ.hom ū) X.2).presheafFiber
    (A := CommRingCat.{u})).obj (inverseImageRingedSite B S hS f).O.obj

include hφf in
/-- The map from the local ring of `Spec R` at the point under `ū` to the stalk of `f⁻¹𝒪_𝒮` at
the image of `ū` in `X`: the local ring of the identity chart of `𝒮` at the image point, followed
by its strict henselization (Stacks 04KF) and the comparison of Stacks 04K2. -/
def baseLocalizationStalkRingHom :
    Localization.AtPrime ((identityChartPrime B S hS hA gA ū).asIdeal.under R) →+*
      chartImageInverseImageStalkRing B S hS hR gR hA gA f φ ū :=
  let e₀ : geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hR gR),
      isAlgebraicSpace_yoneda B S hS _⟩) (geometricPointMap f.hom (geometricPointMap φ.hom ū)) ≃+*
        chartImageInverseImageStalkRing B S hS hR gR hA gA f φ ū :=
    ((smallEtaleInverseImageFiberRingIso B S hS f (geometricPointMap φ.hom ū)).app
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj (specFppfOver B S hS hR gR),
        isAlgebraicSpace_yoneda B S hS _⟩).O).commRingCatIsoToRingEquiv
  let ℓ : Localization.AtPrime ((identityChartPrime B S hS hA gA ū).asIdeal.under R) ≃+*
      Localization.AtPrime (identityChartPrime B S hS hR gR
        (geometricPointMap f.hom (geometricPointMap φ.hom ū))).asIdeal :=
    IsLocalization.ringEquivOfRingEquiv
      (M := ((identityChartPrime B S hS hA gA ū).asIdeal.under R).primeCompl)
      (T := (identityChartPrime B S hS hR gR
        (geometricPointMap f.hom (geometricPointMap φ.hom ū))).asIdeal.primeCompl) _ _
      (RingEquiv.refl R)
      (by ext z; simp [identityChartPrime_geometricPointMap B S hS hR gR hA gA f φ w hφf ū])
  e₀.toRingHom.comp ((chartLocalizationRingHom B S hS hR gR
    (geometricPointMap f.hom (geometricPointMap φ.hom ū))).comp ℓ.toRingHom)

/-- The map from the stalk of `f⁻¹𝒪_𝒮` at the image of `ū` to the geometric stalk ring of the chart
at `ū`: the map of stalks of `f⁻¹𝒪_𝒮 ⟶ 𝒪_X`, followed by the isomorphism of geometric stalk rings
along the étale `φ`. -/
abbrev chartStalkRingHom :
    chartImageInverseImageStalkRing B S hS hR gR hA gA f φ ū →+*
      geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hA gA),
        isAlgebraicSpace_yoneda B S hS _⟩) ū :=
  (smallEtaleStalkPullbackRingMap B S hS φ ū).comp
    (inverseImageStalkRingHom B S hS f (geometricPointMap φ.hom ū))

/-- The identification of the localizations of `R` at the prime under `ū` and at the prime of the
image point. -/
private def baseLocalizationEquiv :
    Localization.AtPrime ((identityChartPrime B S hS hA gA ū).asIdeal.under R) ≃+*
      Localization.AtPrime (identityChartPrime B S hS hR gR
        (geometricPointMap f.hom (geometricPointMap φ.hom ū))).asIdeal :=
  IsLocalization.ringEquivOfRingEquiv
    (M := ((identityChartPrime B S hS hA gA ū).asIdeal.under R).primeCompl)
    (T := (identityChartPrime B S hS hR gR
      (geometricPointMap f.hom (geometricPointMap φ.hom ū))).asIdeal.primeCompl) _ _
    (RingEquiv.refl R)
    (by ext z; simp [identityChartPrime_geometricPointMap B S hS hR gR hA gA f φ w hφf ū])

/-- The comparison of the geometric stalk ring of `𝒮` at the image point with the stalk of
`f⁻¹𝒪_𝒮`. -/
private def geometricStalkRingEquivInverseImage :
    geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hR gR),
      isAlgebraicSpace_yoneda B S hS _⟩) (geometricPointMap f.hom (geometricPointMap φ.hom ū)) ≃+*
        chartImageInverseImageStalkRing B S hS hR gR hA gA f φ ū :=
  ((smallEtaleInverseImageFiberRingIso B S hS f (geometricPointMap φ.hom ū)).app
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj (specFppfOver B S hS hR gR),
      isAlgebraicSpace_yoneda B S hS _⟩).O).commRingCatIsoToRingEquiv

include hφf in
/-- The two maps out of the local ring of `Spec R` into the geometric stalk ring of the chart,
through the stalk of `f⁻¹𝒪_𝒮` and through the local ring of `Spec A`, agree (Stacks 04NG). -/
theorem chartStalkRingHom_comp_baseLocalizationStalkRingHom :
    letI : Algebra (Localization.AtPrime ((identityChartPrime B S hS hA gA ū).asIdeal.under R))
        (Localization.AtPrime (identityChartPrime B S hS hA gA ū).asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver _ _
    (chartStalkRingHom B S hS hR gR hA gA f φ ū).comp
        (baseLocalizationStalkRingHom B S hS hR gR hA gA f φ w hφf ū) =
      (chartLocalizationRingHom B S hS hA gA ū).comp
        (algebraMap (Localization.AtPrime ((identityChartPrime B S hS hA gA ū).asIdeal.under R))
          (Localization.AtPrime (identityChartPrime B S hS hA gA ū).asIdeal)) := by
  let : Algebra (Localization.AtPrime ((identityChartPrime B S hS hA gA ū).asIdeal.under R))
      (Localization.AtPrime (identityChartPrime B S hS hA gA ū).asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver _ _
  let V := specFppfOver B S hS hA gA
  let 𝒮 : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj (specFppfOver B S hS hR gR), isAlgebraicSpace_yoneda B S hS _⟩
  let x := geometricPointMap φ.hom ū
  let β := smallEtaleStalkPullbackRingMap B S hS φ ū
  let ι := inverseImageStalkRingHom B S hS f x
  refine IsLocalization.ringHom_ext
    ((identityChartPrime B S hS hA gA ū).asIdeal.under R).primeCompl (RingHom.ext fun r => ?_)
  apply (pointStalkRingEquiv B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS _⟩ ū).injective
  have hR' : ((chartLocalizationRingHom B S hS hA gA ū).comp
        (algebraMap (Localization.AtPrime ((identityChartPrime B S hS hA gA ū).asIdeal.under R))
          (Localization.AtPrime (identityChartPrime B S hS hA gA ū).asIdeal))).comp
        (algebraMap R _) r =
      chartLocalizationRingHom B S hS hA gA ū (algebraMap A _ (algebraMap R A r)) :=
    congrArg (chartLocalizationRingHom B S hS hA gA ū)
      (Localization.localRingHom_to_map _ _ _ _ r)
  let z' := chartLocalizationRingHom B S hS hR gR
    (geometricPointMap f.hom (geometricPointMap φ.hom ū)) (algebraMap R _ r)
  let w' := (stalkStructureMap B S hS f x).hom z'
  have hℓ : baseLocalizationEquiv B S hS hR gR hA gA f φ w hφf ū (algebraMap R _ r) =
      algebraMap R (Localization.AtPrime (identityChartPrime B S hS hR gR
        (geometricPointMap f.hom (geometricPointMap φ.hom ū))).asIdeal) r :=
    IsLocalization.ringEquivOfRingEquiv_eq _ r
  have hρ : baseLocalizationStalkRingHom B S hS hR gR hA gA f φ w hφf ū (algebraMap R _ r) =
      ((smallEtaleInverseImageFiberRingIso B S hS f x).hom.app
        (smallEtaleRingedTopos B S hS 𝒮).O).hom
        z' :=
    congrArg (fun z => ((smallEtaleInverseImageFiberRingIso B S hS f x).hom.app
      (smallEtaleRingedTopos B S hS 𝒮).O).hom (chartLocalizationRingHom B S hS hR gR
        (geometricPointMap f.hom (geometricPointMap φ.hom ū)) z)) hℓ
  have hL : ((chartStalkRingHom B S hS hR gR hA gA f φ ū).comp
      (baseLocalizationStalkRingHom B S hS hR gR hA gA f φ w hφf ū)).comp (algebraMap R _) r =
        β w' :=
    (congrArg (fun z => β (ι z)) hρ).trans
      (congrArg β (inverseImageStalkRingHom_fiberRingIso B S hS f x z'))
  have h₁ : pointStalkRingEquiv B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS _⟩ ū (β w') =
      etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS _) φ.hom ū
        (pointStalkRingEquiv B S hS X x w') :=
    RingHom.congr_fun (pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS φ ū) w'
  have h₂ : pointStalkRingEquiv B S hS X x w' =
      etaleLocalRingMap X.2 f.hom x
        (pointStalkRingEquiv B S hS 𝒮 (geometricPointMap f.hom (geometricPointMap φ.hom ū)) z') :=
    (congrArg (fun z => pointStalkRingEquiv B S hS X x ((stalkStructureMap B S hS f x).hom z))
      ((pointStalkRingEquiv B S hS 𝒮
        (geometricPointMap f.hom (geometricPointMap φ.hom ū))).symm_apply_apply z').symm).trans
      (RingHom.congr_fun (stalkStructureMapAsEtaleLocalRingMap_eq B S hS f x)
        (pointStalkRingEquiv B S hS 𝒮 (geometricPointMap f.hom (geometricPointMap φ.hom ū)) z'))
  rw [pointStalkRingEquiv_chartLocalizationRingHom_algebraMap] at h₂
  rw [hL]
  refine Eq.trans ?_ (congrArg _ hR'.symm)
  rw [pointStalkRingEquiv_chartLocalizationRingHom_algebraMap]
  refine h₁.trans ((congrArg (etaleLocalRingMap _ φ.hom ū) h₂).trans ?_)
  refine (RingHom.congr_fun (etaleLocalRingMap_comp _ _ φ.hom f.hom ū) _).trans ?_
  exact etaleLocalRingMap_comp_etaleLocalRingGerm B S hS hR gR hA gA f φ w hφf ū r

include hφf in
/-- **Flatness descends along the map from the local ring of `Spec R` to the stalk of `f⁻¹𝒪_𝒮`**
(Stacks 05VL): that stalk is a strict henselization of the local ring. -/
theorem flat_baseLocalizationStalkRingHom_iff
    (N : ModuleCat.{u} (chartImageInverseImageStalkRing B S hS hR gR hA gA f φ ū)) :
    Module.Flat (Localization.AtPrime ((identityChartPrime B S hS hA gA ū).asIdeal.under R))
        ((ModuleCat.restrictScalars
          (baseLocalizationStalkRingHom B S hS hR gR hA gA f φ w hφf ū)).obj
          N) ↔
      Module.Flat (chartImageInverseImageStalkRing B S hS hR gR hA gA f φ ū) N := by
  let e₀ := geometricStalkRingEquivInverseImage B S hS hR gR hA gA f φ ū
  let ℓ := baseLocalizationEquiv B S hS hR gR hA gA f φ w hφf ū
  let : Module (geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hR gR),
      isAlgebraicSpace_yoneda B S hS _⟩) (geometricPointMap f.hom (geometricPointMap φ.hom ū))) N :=
    Module.compHom N e₀.toRingHom
  let : Module (Localization.AtPrime (identityChartPrime B S hS hR gR
      (geometricPointMap f.hom (geometricPointMap φ.hom ū))).asIdeal) N :=
    Module.compHom N (chartLocalizationRingHom B S hS hR gR
      (geometricPointMap f.hom (geometricPointMap φ.hom ū)))
  exact (Module.Flat.compHom_ringEquiv_iff _ _ N ℓ).trans
    ((flat_chartLocalizationRingHom_iff B S hS hR gR
      (geometricPointMap f.hom (geometricPointMap φ.hom ū)) N).trans
      (Module.Flat.compHom_ringEquiv_iff _ _ N e₀))

variable (hφ : IsEtale B S hS φ.hom) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
  (P : CochainComplex (ModuleCat.{u} A) ℤ)
  (eP : letI := etaleModulePullback_additive.{u, u} B S hS φ hφ
    letI := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
    letI := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
    (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E ≅
      (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
        ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
          (Iso.refl ((BigFppfOver.toScheme B S hS).obj
            (specFppfOver B S hS hA gA))).hom).mapDerivedCategory.obj (DerivedCategory.Q.obj P)))

/-- The base change of a complex of `A`-modules to the geometric stalk ring of the chart at `ū`,
through the local ring of `Spec A` at the point under `ū`. -/
abbrev chartStalkComplex : CochainComplex (ModuleCat.{u} (geometricStalkRing B S hS
    (X := ⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩) ū)) ℤ :=
  (CochainComplex.extendScalars (chartLocalizationRingHom B S hS hA gA ū)).obj
    ((CochainComplex.extendScalars
      (algebraMap A (Localization.AtPrime (identityChartPrime B S hS hA gA ū).asIdeal))).obj P)

/-- The derived geometric stalk of `ε^*(P~)` at `ū` is `P ⊗_A 𝒪_{Spec A, ū}`. -/
theorem nonempty_geometricDerivedStalk_chartModel_iso :
    Nonempty ((geometricDerivedStalk B S hS
        (X := ⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩) ū).obj
        ((representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
          ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
            (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA))).hom
            ).mapDerivedCategory.obj (DerivedCategory.Q.obj P))) ≅
      DerivedCategory.Q.obj (chartStalkComplex B S hS hA gA ū P)) := by
  let V := specFppfOver B S hS hA gA
  let q := (identityChartPrime B S hS hA gA ū).asIdeal
  obtain ⟨γ, hγ, ⟨eF⟩⟩ := exists_representedAffineStalkRingHom_iso B S hS V (CommRingCat.of A)
    (Iso.refl _) ū
  let := preservesFiniteLimits_extendScalars_of_iso B S hS V (CommRingCat.of A) (Iso.refl _) ū γ eF
  obtain ⟨e₃⟩ := nonempty_geometricDerivedStalk_representedTilde_iso B S hS V (CommRingCat.of A)
    (Iso.refl _) ū γ eF (DerivedCategory.Q.obj P)
  have hγ' : γ = (chartLocalizationRingHom B S hS hA gA ū).comp
      (algebraMap A (Localization.AtPrime q)) := by
    refine RingHom.ext fun a => (pointStalkRingEquiv B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS _⟩ ū).injective ?_
    rw [hγ a, RingHom.comp_apply, pointStalkRingEquiv_chartLocalizationRingHom_algebraMap]
    rfl
  let c : ((ModuleCat.extendScalars.{u, u, u} γ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅
      chartStalkComplex B S hS hA gA ū P :=
    eqToIso (by rw [hγ']) ≪≫
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp
        (algebraMap A (Localization.AtPrime q)) (chartLocalizationRingHom B S hS hA gA ū))
        (ComplexShape.up ℤ)).app P
  exact ⟨e₃ ≪≫ (ModuleCat.extendScalars.{u, u, u} γ).mapDerivedCategoryFactors.app P ≪≫
    DerivedCategory.Q.mapIso c⟩

include eP in
/-- **The geometric stalk of `E` at the image of `ū`, transported to the chart**, is
`P ⊗_A 𝒪_{Spec A, ū}`: Stacks 05V5 along the étale `φ`, and the stalks of `ε^*(P~)`. -/
theorem nonempty_extendScalars_geometricDerivedStalk_iso :
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
        (smallEtaleStalkPullbackRingMap B S hS φ ū)) :=
      ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
        (RingHom.Flat.of_bijective (bijective_smallEtaleStalkPullbackRingMap B S hS φ hφ ū))
    Nonempty ((ModuleCat.extendScalars.{u, u, u}
        (smallEtaleStalkPullbackRingMap B S hS φ ū)).mapDerivedCategory.obj
        ((geometricDerivedStalk B S hS (geometricPointMap φ.hom ū)).obj E) ≅
      (geometricDerivedStalk B S hS
        (X := ⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩) ū).obj
        ((representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
          ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
            (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA))).hom
            ).mapDerivedCategory.obj (DerivedCategory.Q.obj P)))) := by
  let := etaleModulePullback_additive.{u, u} B S hS φ hφ
  let := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
  let := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
  obtain ⟨e₁⟩ := nonempty_geometricDerivedStalk_etaleModulePullback_iso B S hS φ hφ ū E
  exact ⟨e₁.symm ≪≫ (geometricDerivedStalk B S hS
    (X := ⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩) ū).mapIso eP⟩

include eP in
omit [Algebra R A] in
/-- **The geometric stalk of `E` at the image of `ū`, read over the stalk of `f⁻¹𝒪_𝒮`**, is
`P ⊗_A 𝒪_{Spec A, ū}` read over that stalk. -/
theorem nonempty_restrictScalars_geometricStalk_iso :
    Nonempty ((ModuleCat.restrictScalars.{u} (inverseImageStalkRingHom B S hS f
        (geometricPointMap φ.hom ū))).mapDerivedCategory.obj
        ((geometricStalkFunctor B S hS (geometricPointMap φ.hom ū)).mapDerivedCategory.obj E) ≅
      DerivedCategory.Q.obj ((CochainComplex.restrictScalars
        (chartStalkRingHom B S hS hR gR hA gA f φ ū)).obj
          (chartStalkComplex B S hS hA gA ū P))) := by
  let β := smallEtaleStalkPullbackRingMap B S hS φ ū
  have hβ : Function.Bijective β := bijective_smallEtaleStalkPullbackRingMap B S hS φ hφ ū
  let ι := inverseImageStalkRingHom B S hS f (geometricPointMap φ.hom ū)
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} β) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (RingHom.Flat.of_bijective hβ)
  obtain ⟨e₁⟩ := nonempty_extendScalars_geometricDerivedStalk_iso B S hS hA gA φ ū hφ E P eP
  obtain ⟨e₃⟩ := nonempty_geometricDerivedStalk_chartModel_iso B S hS hA gA ū P
  let e₅ := e₁ ≪≫ e₃
  let C := chartStalkComplex B S hS hA gA ū P
  let e₆ : (geometricStalkFunctor B S hS (geometricPointMap φ.hom ū)).mapDerivedCategory.obj E ≅
      DerivedCategory.Q.obj ((CochainComplex.restrictScalars β).obj C) :=
    (ModuleCat.restrictScalarsExtendScalarsMapDerivedIso β hβ _).symm ≪≫
      (ModuleCat.restrictScalars.{u} β).mapDerivedCategory.mapIso e₅ ≪≫
      (ModuleCat.restrictScalars.{u} β).mapDerivedCategoryFactors.app C
  let c' : (CochainComplex.restrictScalars ι).obj ((CochainComplex.restrictScalars β).obj C) ≅
      (CochainComplex.restrictScalars (chartStalkRingHom B S hS hR gR hA gA f φ ū)).obj C :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => ((ModuleCat.restrictScalarsComp.{u} ι β).app (C.X i)).symm)
      (fun i j _ => ((ModuleCat.restrictScalarsComp.{u} ι β).inv.naturality (C.d i j)).symm)
  exact ⟨(ModuleCat.restrictScalars.{u} ι).mapDerivedCategory.mapIso e₆ ≪≫
    (ModuleCat.restrictScalars.{u} ι).mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso c'⟩

include hφf eP in
/-- **The Tor amplitude of a geometric stalk, read on an affine chart.** Let `f : X ⟶ 𝒮` with
`𝒮 = Spec R`, let `φ : Spec A ⟶ X` be étale with `f ∘ φ` the structure map of the `R`-algebra `A`,
and let `P` be a complex of `A`-modules with `φ^*E ≅ ε^*(P~)`. At the image `x̄` of a geometric
point `ū` of `Spec A`, the geometric stalk `E_x̄`, read over the stalk of `f⁻¹𝒪_𝒮`, has Tor
amplitude in `[a, b]` exactly when `P_q` has Tor amplitude in `[a, b]` over `R_{q ∩ R}`, `q` the
prime under `ū`. -/
theorem hasTorAmplitudeCanonical_geometricStalk_iff_hasTorAmplitudeAt (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (chartImageInverseImageStalkRing B S hS hR gR hA gA f φ ū)
        ((ModuleCat.restrictScalars.{u} (inverseImageStalkRingHom B S hS f
          (geometricPointMap φ.hom ū))).mapDerivedCategory.obj
          ((geometricStalkFunctor B S hS (geometricPointMap φ.hom ū)).mapDerivedCategory.obj E))
        a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeAt R P (identityChartPrime B S hS hA gA ū).asIdeal
        a b := by
  let := (chartLocalizationRingHom B S hS hA gA ū).toAlgebra
  have := faithfullyFlat_chartLocalizationRingHom B S hS hA gA ū
  rw [PseudoCoherence.hasTorAmplitudeAt_iff_hasTorAmplitudeCanonical_restrictScalars
    (B := geometricStalkRing B S hS (X := ⟨yoneda.obj (specFppfOver B S hS hA gA),
      isAlgebraicSpace_yoneda B S hS _⟩) ū) _ P a b
    (baseLocalizationStalkRingHom B S hS hR gR hA gA f φ w hφf ū)
    (chartStalkRingHom B S hS hR gR hA gA f φ ū)
    (chartStalkRingHom_comp_baseLocalizationStalkRingHom B S hS hR gR hA gA f φ w hφf ū)
    (flat_baseLocalizationStalkRingHom_iff B S hS hR gR hA gA f φ w hφf ū)]
  obtain ⟨e⟩ := nonempty_restrictScalars_geometricStalk_iso B S hS hR gR hA gA f φ ū hφ E P eP
  exact ⟨fun h => AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b h,
    fun h => AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e.symm a b h⟩

end ChartTorAmplitude

end AlgebraicGeometry.Space

end
