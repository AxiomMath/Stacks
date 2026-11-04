module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentZariskiSchemeCase
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentHomDescentZariskiLeaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeGeometricStalks
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineSchemeTorDimension
public import StacksFrontier.Cotangent.Spaces.RepresentableStalkH1
public import
 StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentZariskiSchemeChartFlat

/-!
# Zariski Tor dimension on an affine model from the relative Tor clause on spaces

Let `p₀ : X₀ ⟶ Y₀` be a morphism of algebraic spaces and `L₀ ∈ D(𝒪_{X₀})` locally of finite Tor
dimension over `p₀⁻¹𝒪_{Y₀}` on the small étale site (the Tor clause of Stacks 0DKN). Let
`t' : Spec A ⟶ Spec R` be an affine model of an étale piece `U ⟶ X₀` over an étale piece
`V ⟶ Y₀`, and `L ∈ D(𝒪_{Spec A})` with quasi-coherent cohomology and `ε^*L ≅ La^*Lg^*L₀`. Then
`L`, read over `t'⁻¹𝒪_{Spec R}`, locally has finite Tor dimension on the Zariski site, which is
the Tor hypothesis of Stacks 0DI7 on `t'`.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `hasTorAmplitudeCanonical_extendScalars_of_bijectiveSquare`: Tor amplitude across a square of
  rings with bijective horizontal edges.
* `geometricStalkTorAmplitude_etaleModulePullback_of_etaleSquare`: the geometric-stalk Tor bound
  across a square of algebraic spaces with étale horizontal edges.
* `exists_geometricStalkTorAmplitude_of_hasLocallyFiniteTorDimensionAlong`: a uniform
  geometric-stalk bound on an affine étale chart, from the Tor clause.
* `hasTorAmplitudeCanonical_of_geometricStalkTorAmplitude_specFppfOverMap` and
  `locallyHasFiniteTorDimension_of_geometricStalkTorAmplitude_specFppfOverMap`: on
  `Spec A ⟶ Spec R`, a uniform bound on the geometric stalks gives Tor amplitude over `R` and the
  Zariski Tor clause.
* `locallyHasFiniteTorDimension_specFppfOverMap_of_hasLocallyFiniteTorDimensionAlong`: the
  statement above.
* `exists_specFppfOver_iso_of_isAffineSpace` and `exists_algebra_specFppfOverMap_eq`: an affine
  algebraic space is represented by a spectrum, and a morphism between spectra is the spectrum of
  a ring map.
* `RelativeDescentSituation.zariskiModelHomDescent_of_hasLocallyFiniteTorDimensionAlong`: the
  Zariski descent of morphisms on the affine model, from the Tor clause of `L₀`.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 05VL](https://stacks.math.columbia.edu/tag/05VL)
* [Stacks Project, Tag 0B67](https://stacks.math.columbia.edu/tag/0B67)
* [Stacks Project, Tag 0DHY](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open StacksDraft.TorAmplitude

universe u

/-! ### Tor amplitude across a square of rings with bijective horizontal edges -/

section BijectiveSquare

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Tor amplitude across a commutative square of rings whose horizontal edges are
bijective.**  Let `σ : R ⟶ A` and `e : R' ⟶ A'` be ring maps and `b : R ⟶ R'`, `c : A ⟶ A'`
bijective ones with `e ∘ b = c ∘ σ`.  If `K ∈ D(A)`, read over `R`, has Tor amplitude in
`[a, b]`, then so has `K ⊗_A A'`, read over `R'`. -/
theorem AlgebraicGeometry.Space.hasTorAmplitudeCanonical_extendScalars_of_bijectiveSquare
    {R R' A A' : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
    (σ : R →+* A) (e : R' →+* A') (b : R →+* R') (hb : Function.Bijective b)
    (c : A →+* A') (hc : Function.Bijective c) (h : e.comp b = c.comp σ)
    [hcl : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} c)]
    (K : DerivedCategory (ModuleCat.{u} A)) (a₀ b₀ : ℤ)
    (hK : HasTorAmplitudeCanonical R
      ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategory.obj K) a₀ b₀) :
    HasTorAmplitudeCanonical R'
      ((ModuleCat.restrictScalars.{u} e).mapDerivedCategory.obj
        ((ModuleCat.extendScalars.{u, u, u} c).mapDerivedCategory.obj K)) a₀ b₀ :=
  (AlgebraicGeometry.Space.hasTorAmplitudeCanonical_restrictScalars_iff_of_ringEquiv
    (RingEquiv.ofBijective b hb) e (c.comp σ) (h.symm.trans (RingHom.ext fun _ => rfl))
    _ a₀ b₀).2 (AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategory.mapIso
          (ModuleCat.restrictScalarsExtendScalarsMapDerivedIso c hc K).symm ≪≫
        (AlgebraicGeometry.Space.restrictScalarsMapDerivedCompIso σ c (c.comp σ) rfl _).symm)
      a₀ b₀ hK)

end BijectiveSquare

namespace AlgebraicGeometry.Space

/-! ### The geometric-stalk Tor bound across a square with étale horizontal edges -/

section EtaleSquare

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS}

/-- **The geometric-stalk Tor bound across a square with étale horizontal edges.**  Let
`φ ≫ f = f' ≫ ψ` with `φ : X' ⟶ X` and `ψ : Y' ⟶ Y` étale.  If the geometric stalk of
`E ∈ D(𝒪_X)` at the image `φ(x̄')` of a geometric point of `X'` has Tor amplitude in `[a, b]`
over the stalk of `f⁻¹𝒪_Y`, then the geometric stalk of `φ^*E` at `x̄'` has Tor amplitude in
`[a, b]` over the stalk of `f'⁻¹𝒪_{Y'}`. -/
theorem geometricStalkTorAmplitude_etaleModulePullback_of_etaleSquare (f : X ⟶ Y) (f' : X' ⟶ Y')
    (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom) (ψ : Y' ⟶ Y) (hψ : IsEtale B S hS ψ.hom)
    (sq : φ ≫ f = f' ≫ ψ) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (x' : GeometricPoint B S hS X'.1) (a b : ℤ)
    (h : GeometricStalkTorAmplitude B S hS f E (geometricPointMap φ.hom x') a b) :
    letI := etaleModulePullback_additive.{u, u} B S hS φ hφ
    letI := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
    letI := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
    GeometricStalkTorAmplitude B S hS f'
      ((etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E) x' a b := by
  let := etaleModulePullback_additive.{u, u} B S hS φ hφ
  let := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
  let := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
  have hcl : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (smallEtaleStalkPullbackRingMap B S hS φ x')) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
      (RingHom.Flat.of_bijective (bijective_smallEtaleStalkPullbackRingMap B S hS φ hφ x'))
  rw [stalkTorAmplitude_iff_stalkStructureMap] at h ⊢
  obtain ⟨e₁⟩ := nonempty_geometricDerivedStalk_etaleModulePullback_iso B S hS φ hφ x' E
  have hψb : Function.Bijective
      (stalkStructureMap B S hS ψ (geometricPointMap f'.hom x')).hom := by
    rw [stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap]
    exact bijective_smallEtaleStalkPullbackRingMap B S hS ψ hψ _
  have hb : Function.Bijective (geometricBaseStalkMap B S hS f ψ f' φ sq x').hom := by
    rw [geometricBaseStalkMap, CommRingCat.hom_comp]
    exact hψb.comp (ConcreteCategory.bijective_of_isIso _)
  have hsq := stalkStructureMap_square B S hS f ψ f' φ sq x'
  rw [stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap] at hsq
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((ModuleCat.restrictScalars.{u} (stalkStructureMap B S hS f' x').hom).mapDerivedCategory.mapIso
      e₁.symm) a b
    (hasTorAmplitudeCanonical_extendScalars_of_bijectiveSquare
      (stalkStructureMap B S hS f (geometricPointMap φ.hom x')).hom
      (stalkStructureMap B S hS f' x').hom (geometricBaseStalkMap B S hS f ψ f' φ sq x').hom hb
      (smallEtaleStalkPullbackRingMap B S hS φ x')
      (bijective_smallEtaleStalkPullbackRingMap B S hS φ hφ x') hsq.symm (hcl := hcl) _ a b h)

/-- The geometric-stalk Tor bound depends only on the isomorphism class of the object. -/
theorem geometricStalkTorAmplitude_of_iso (f : X ⟶ Y)
    {E E' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (e : E ≅ E')
    (x : GeometricPoint B S hS X.1) (a b : ℤ)
    (h : GeometricStalkTorAmplitude B S hS f E x a b) :
    GeometricStalkTorAmplitude B S hS f E' x a b :=
  AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((ModuleCat.restrictScalars.{u} (inverseImageStalkRingHom B S hS f x)).mapDerivedCategory.mapIso
      ((geometricStalkFunctor B S hS x).mapDerivedCategory.mapIso e)) a b h

end EtaleSquare

/-! ### The Zariski Tor clause from the geometric stalks on `Spec A ⟶ Spec R` -/

section SpecCore

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Étale restriction along the identity is the identity, on derived categories, objectwise. -/
def etaleModulePullbackIdDerivedObjIso (X : AlgebraicSpaces B S hS)
    (hid : IsEtale B S hS (𝟙 X : X ⟶ X).hom) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    letI := etaleModulePullback_additive.{u, u} B S hS (𝟙 X) hid
    letI := preservesFiniteLimits_etaleModulePullback B S hS (𝟙 X) hid
    letI := preservesFiniteColimits_etaleModulePullback B S hS (𝟙 X) hid
    (etaleModulePullback.{u, u} B S hS (𝟙 X) hid).mapDerivedCategory.obj E ≅ E :=
  letI := etaleModulePullback_additive.{u, u} B S hS (𝟙 X) hid
  letI := preservesFiniteLimits_etaleModulePullback B S hS (𝟙 X) hid
  letI := preservesFiniteColimits_etaleModulePullback B S hS (𝟙 X) hid
  let G : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
    etaleModulePullback.{u, u} B S hS (𝟙 X) hid
  let K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅ K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (etaleModulePullbackIdIso B S hS hid).app (K.X i))
      (fun i j _ => (etaleModulePullbackIdIso B S hS hid).hom.naturality (K.d i j))
  let e₁ : G.mapDerivedCategory.obj E ≅ G.mapDerivedCategory.obj (DerivedCategory.Q.obj K) :=
    G.mapDerivedCategory.mapIso eK.symm
  let e₂ : G.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    G.mapDerivedCategoryFactors.app K
  let e₃ : DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      DerivedCategory.Q.obj K :=
    DerivedCategory.Q.mapIso c
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ eK

variable {R : Type u} [CommRing R] (hR : B.Contains (Spec (CommRingCat.of R)))
  (gR : B.obj hR ⟶ B.obj hS) {A : Type u} [CommRing A] [Algebra R A]
  (hA : B.Contains (Spec (CommRingCat.of A))) (gA : B.obj hA ⟶ B.obj hS)
  (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    B.obj hA ⟶ B.obj hR) ≫ gR = gA)

/-- **The Tor amplitude over `R` of a complex of `A`-modules, from the geometric stalks.**  Let
`t : Spec A ⟶ Spec R` be the morphism of the site of an `R`-algebra `A`, and `E` an object of
`D(𝒪_{h_{Spec A}})` isomorphic to `ε^*(P~)`.  If one interval `[a, b]` contains the Tor amplitude
of every geometric stalk of `E` over the stalk of `t⁻¹𝒪_{h_{Spec R}}`, then `P`, read over `R`,
has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitudeCanonical_of_geometricStalkTorAmplitude_specFppfOverMap
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (specFppfOver B S hS hA gA))
      (isAlgebraicSpace_yoneda B S hS _)))
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (eP : E ≅ (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
      ((Functor.mapDerivedCategory (tilde.functor (CommRingCat.of A) ⋙
        Scheme.Modules.restrictFunctor
          (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA))).hom)).obj
        (DerivedCategory.Q.obj P)))
    (a b : ℤ)
    (h : ∀ ū : GeometricPoint B S hS (yoneda.obj (specFppfOver B S hS hA gA)),
      GeometricStalkTorAmplitude B S hS
        (representedSpaceMap B S hS (specFppfOverMap B S hS hR gR hA gA w)) E ū a b) :
    HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) a b := by
  rw [AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_restrictScalars_iff_forall_isPrime]
  intro q hq
  obtain ⟨ū, hū⟩ := exists_chartPoint_yonedaIdentityNeighborhood_eq B S hS
    (specFppfOver B S hS hA gA) (⟨q, hq⟩ : PrimeSpectrum A)
  let X : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩
  have hid : IsEtale B S hS (𝟙 X : X ⟶ X).hom := isEtale_of_isIso B S hS _
  have hφf : yoneda.map (specFppfOverMap B S hS hR gR hA gA w) =
      (𝟙 X : X ⟶ X).hom ≫ (representedSpaceMap B S hS (specFppfOverMap B S hS hR gR hA gA w)).hom :=
    (Category.id_comp _).symm
  have key := (hasTorAmplitudeCanonical_geometricStalk_iff_hasTorAmplitudeAt B S hS hR gR hA gA
    (representedSpaceMap B S hS (specFppfOverMap B S hS hR gR hA gA w)) (𝟙 X) w hφf ū hid E P
    (etaleModulePullbackIdDerivedObjIso B S hS X hid E ≪≫ eP) a b).1 (h _)
  exact (show _ = q from congrArg PrimeSpectrum.asIdeal hū) ▸ key

end SpecCore

section SpecZariski

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {R : Type u} [CommRing R] (hR : B.Contains (Spec (CommRingCat.of R)))
  (gR : B.obj hR ⟶ B.obj hS) {A : Type u} [CommRing A] [Algebra R A]
  (hA : B.Contains (Spec (CommRingCat.of A))) (gA : B.obj hA ⟶ B.obj hS)
  (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    B.obj hA ⟶ B.obj hR) ≫ gR = gA)

/-- **The Zariski Tor clause on `Spec A ⟶ Spec R`, from the geometric stalks.** Let
`t : Spec A ⟶ Spec R` be the morphism of the site of an `R`-algebra `A` and `L` an object of
`D(𝒪_{Spec A})` with quasi-coherent cohomology. If one interval `[a, b]` contains the Tor amplitude
of every geometric stalk of `ε^*L` over the stalk of `t⁻¹𝒪_{h_{Spec R}}`, then `L`, read over
`t⁻¹𝒪_{Spec R}`, locally has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_of_geometricStalkTorAmplitude_specFppfOverMap
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).toRingedSpace)))
    (hLqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).Modules n).obj
        L).IsQuasicoherent)
    (a b : ℤ)
    (h : ∀ ū : GeometricPoint B S hS (yoneda.obj (specFppfOver B S hS hA gA)),
      GeometricStalkTorAmplitude B S hS
        (representedSpaceMap B S hS (specFppfOverMap B S hS hR gR hA gA w))
        ((zariskiEtaleDerived B S hS _).obj L) ū a b) :
    AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension
      (AlgebraicGeometry.RingedSpace.inverseImage
        ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hR gR)).toRingedSpace
        ((BigFppfOver.toScheme B S hS).map (specFppfOverMap B S hS hR gR hA gA w)).base)
      (AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction
        ((BigFppfOver.toScheme B S hS).map (specFppfOverMap B S hS hR gR hA gA w))).obj L) := by
  obtain ⟨M, ⟨eM⟩⟩ := AlgebraicGeometry.exists_tildeComplex_iso (CommRingCat.of A) L hLqc
  let T : ModuleCat.{u} A ⥤
      ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).Modules :=
    tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
      (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA))).hom
  let c : (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ≅
      ((tilde.functor (CommRingCat.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (Scheme.Modules.restrictFunctorId (X := Spec (CommRingCat.of A))).app
        ((tilde.functor (CommRingCat.of A)).obj (M.X i)))
      (fun i j _ => (Scheme.Modules.restrictFunctorId (X := Spec (CommRingCat.of A))).hom.naturality
        ((tilde.functor (CommRingCat.of A)).map (M.d i j)))
  let eT : T.mapDerivedCategory.obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (((tilde.functor (CommRingCat.of A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) :=
    T.mapDerivedCategoryFactors.app M ≪≫ DerivedCategory.Q.mapIso c
  have hamp := hasTorAmplitudeCanonical_of_geometricStalkTorAmplitude_specFppfOverMap B S hS hR gR
    hA gA w ((zariskiEtaleDerived B S hS _).obj L) M
    ((zariskiEtaleDerived B S hS _).mapIso (eM ≪≫ eT.symm)) a b h
  have hfin := (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical R
    (DerivedCategory.Q.obj (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M))).2 ⟨a, b, hamp⟩
  exact Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_iso
    ((Scheme.Hom.derivedScalarRestriction
      (AlgebraicGeometry.AffineRelativeTorAmplitude.specMap R A)).mapIso eM.symm)
    ((AlgebraicGeometry.AffinePerfectDescent.locallyHasFiniteTorDimension_tildeObj_iff
      R A M).2 hfin)

end SpecZariski

/-! ### A uniform geometric-stalk bound on an affine étale chart -/

section ChartBound

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **A uniform bound at the geometric stalks over an affine étale chart, from the Tor clause.**
Let `E ∈ D(𝒪_X)` locally have finite Tor dimension over `f⁻¹𝒪_Y`, and let `φ : h_T ⟶ X` be an
étale chart with `T` affine.  Then one interval `[a, b]` contains the Tor amplitude of the
geometric stalk of `E` over the stalk of `f⁻¹𝒪_Y` at the image of every geometric point of
`h_T`. -/
theorem exists_geometricStalkTorAmplitude_of_hasLocallyFiniteTorDimensionAlong
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (E : derivedModules B S hS X)
    (hE : HasLocallyFiniteTorDimensionAlong f E) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (φ : yoneda.obj T ⟶ X.1)
    (hφ : IsEtale B S hS φ) :
    ∃ a b : ℤ, ∀ y : GeometricPoint B S hS (yoneda.obj T),
      GeometricStalkTorAmplitude B S hS f E (geometricPointMap φ y) a b := by
  let U : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk φ, (isEtale_iff_presheaf_of_yoneda B S hS φ).1 hφ⟩
  obtain ⟨ι, -, V, g, a, b, hcov, hamp⟩ :=
    exists_finite_covering_hasTorAmplitude_of_locallyHasFiniteTorDimension
      (canonicalSliceDerivedTensorProduct B S hS f) _ hE U
      (isQuasiCompactObject_of_isAffine B S hS X.1 U hT)
  refine ⟨a, b, fun y ↦ ?_⟩
  let x := geometricPointMap φ y
  let Φ : (inverseImageRingedSite B S hS f).J.Point.{u} := etaleSitePoint B S hS X.1 x X.2
  let ξ : Φ.fiber.obj U := ⟨y.val.value, rfl⟩
  obtain ⟨W, k, ⟨W', h, k', ⟨i⟩, -⟩, ζ, -⟩ := Φ.jointly_surjective _ hcov ξ
  let ξ' : Φ.fiber.obj (V i) := Φ.fiber.map h ζ
  let Ψ : ((inverseImageRingedSite B S hS f).over (V i)).J.Point.{u} := Φ.over ξ'
  have h₁ := hasTorAmplitudeCanonical_derivedModuleFiber.{u + 1, u, u, u + 1}
    (canonicalSliceDerivedTensorProduct B S hS f (V i)) _ a b (hamp i) Ψ
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    (Iso.refl _ ≪≫ derivedScalarRestrictionStalkIso B S hS f x E) a b
    ((RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff Φ ξ' _ a b).1 h₁)

end ChartBound

/-! ### The Zariski Tor clause on the affine model from the Tor clause on spaces -/

section Translation

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : Type u} [CommRing R] {hR : B.Contains (Spec (CommRingCat.of R))}
  {gR : B.obj hR ⟶ B.obj hS} {A : Type u} [CommRing A] [Algebra R A]
  {hA : B.Contains (Spec (CommRingCat.of A))} {gA : B.obj hA ⟶ B.obj hS}

/-- **The Zariski Tor clause on an affine model, from the Tor clause on spaces.** Let `p : X ⟶ Y`
be a morphism of algebraic spaces and `L₀ ∈ D(𝒪_X)` locally of finite Tor dimension over `p⁻¹𝒪_Y`.
Let `g ≫ p = t ≫ v` with `g : U ⟶ X` and `v : V ⟶ Y` étale, and let `a : h_{Spec A} ⟶ U` and
`c : h_{Spec R} ⟶ V` be étale with `a ≫ t = h_{t'} ≫ c`, where `t' : Spec A ⟶ Spec R` is the
morphism of the site of an `R`-algebra `A`. If `L ∈ D(𝒪_{Spec A})` has quasi-coherent cohomology
and `ε^*L ≅ La^*Lg^*L₀`, then `L`, read over `t'⁻¹𝒪_{Spec R}`, locally has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_specFppfOverMap_of_hasLocallyFiniteTorDimensionAlong
    {X Y U V : AlgebraicSpaces B S hS} (p : X ⟶ Y) (L₀ : derivedModules B S hS X)
    (hL₀ : HasLocallyFiniteTorDimensionAlong p L₀)
    (g : U ⟶ X) (hg : IsEtale B S hS g.hom) (v : V ⟶ Y) (hv : IsEtale B S hS v.hom)
    (t : U ⟶ V) (ht : g ≫ p = t ≫ v)
    (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) ≫ gR = gA)
    (a : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ U) (ha : IsEtale B S hS a.hom)
    (c : (⟨yoneda.obj (specFppfOver B S hS hR gR), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ V) (hc : IsEtale B S hS c.hom)
    (hac : a ≫ t = representedSpaceMap B S hS (specFppfOverMap B S hS hR gR hA gA w) ≫ c)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).toRingedSpace)))
    (hLqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).Modules n).obj
        L).IsQuasicoherent)
    (b : (zariskiEtaleDerived B S hS _).obj L ≅ (smallEtaleDerivedModulePullback B S hS a).obj
      ((smallEtaleDerivedModulePullback B S hS g).obj L₀)) :
    AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension
      (AlgebraicGeometry.RingedSpace.inverseImage
        ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hR gR)).toRingedSpace
        ((BigFppfOver.toScheme B S hS).map (specFppfOverMap B S hS hR gR hA gA w)).base)
      (AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction
        ((BigFppfOver.toScheme B S hS).map (specFppfOverMap B S hS hR gR hA gA w))).obj L) := by
  obtain ⟨a₀, b₀, hbound⟩ := exists_geometricStalkTorAmplitude_of_hasLocallyFiniteTorDimensionAlong
    p L₀ hL₀ (specFppfOver B S hS hA gA) (inferInstanceAs (IsAffine (Spec (CommRingCat.of A))))
    (a.hom ≫ g.hom) (isEtale_comp B S hS ha hg)
  let := etaleModulePullback_additive.{u, u} B S hS g hg
  let := preservesFiniteLimits_etaleModulePullback B S hS g hg
  let := preservesFiniteColimits_etaleModulePullback B S hS g hg
  let := etaleModulePullback_additive.{u, u} B S hS a ha
  let := preservesFiniteLimits_etaleModulePullback B S hS a ha
  let := preservesFiniteColimits_etaleModulePullback B S hS a ha
  let eL : (smallEtaleDerivedModulePullback B S hS a).obj
      ((smallEtaleDerivedModulePullback B S hS g).obj L₀) ≅
      (etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.obj
        ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj L₀) :=
    (smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app _ ≪≫
      (etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.mapIso
        ((smallEtaleDerivedModulePullbackIsoEtale B S hS g hg).app L₀)
  refine locallyHasFiniteTorDimension_of_geometricStalkTorAmplitude_specFppfOverMap B S hS hR gR
    hA gA w L hLqc a₀ b₀ fun y ↦ ?_
  have h₁ := geometricStalkTorAmplitude_etaleModulePullback_of_etaleSquare B S hS p t g hg v hv ht
    L₀ (geometricPointMap a.hom y) a₀ b₀ (hbound y)
  have h₂ := geometricStalkTorAmplitude_etaleModulePullback_of_etaleSquare B S hS t
    (representedSpaceMap B S hS (specFppfOverMap B S hS hR gR hA gA w)) a ha c hc hac _ y a₀ b₀ h₁
  exact geometricStalkTorAmplitude_of_iso B S hS _ (b ≪≫ eL).symm y a₀ b₀ h₂

end Translation

/-! ### Spec models of the affine pieces -/

section SpecModels

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The object `Spec A` of the big fppf site, as an object of the big affine fppf site. -/
abbrev specAffineFppf {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (gA : B.obj hA ⟶ B.obj hS) : BigAffineFppf B S hS :=
  ⟨specFppfOver B S hS hA gA, inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))⟩

/-- **An affine algebraic space is represented by the spectrum of a ring**, as an object of the
big fppf site. -/
theorem exists_specFppfOver_iso_of_isAffineSpace {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU₀ : IsAffineSpace B S hS U₀) :
    ∃ (A : Type u) (_ : CommRing A) (hA : B.Contains (Spec (CommRingCat.of A)))
      (gA : B.obj hA ⟶ B.obj hS), Nonempty (yoneda.obj (specFppfOver B S hS hA gA) ≅ U₀) := by
  obtain ⟨T, hT, ⟨eT⟩⟩ := hU₀
  let e := ((BigFppfOver.toScheme B S hS).obj T).isoSpec
  have hA : B.Contains (Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact e.inv) T.left.2
  let gA : B.obj hA ⟶ B.obj hS := ObjectProperty.homMk e.inv ≫ T.hom
  let eV : specFppfOver B S hS hA gA ≅ T :=
    Over.isoMk (B.inclusion.preimageIso e.symm) (B.inclusion.map_injective (by
      rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      rfl))
  exact ⟨_, inferInstance, hA, gA, ⟨yoneda.mapIso eV ≪≫ eT.symm⟩⟩

/-- **A morphism of the site between spectra is the spectrum of a ring map**: every
`t : Spec A ⟶ Spec R` over `S` is `specFppfOverMap` for an `R`-algebra structure on `A`. -/
theorem exists_algebra_specFppfOverMap_eq {R : Type u} [CommRing R]
    {hR : B.Contains (Spec (CommRingCat.of R))} {gR : B.obj hR ⟶ B.obj hS} {A : Type u}
    [CommRing A] {hA : B.Contains (Spec (CommRingCat.of A))} {gA : B.obj hA ⟶ B.obj hS}
    (t : specFppfOver B S hS hA gA ⟶ specFppfOver B S hS hR gR) :
    ∃ (_ : Algebra R A) (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
        B.obj hA ⟶ B.obj hR) ≫ gR = gA), specFppfOverMap B S hS hR gR hA gA w = t := by
  let c : CommRingCat.of R ⟶ CommRingCat.of A := Spec.preimage ((BigFppfOver.toScheme B S hS).map t)
  let := c.hom.toAlgebra
  have hm : Spec.map (CommRingCat.ofHom (algebraMap R A)) = (BigFppfOver.toScheme B S hS).map t :=
    Spec.map_preimage _
  have hl : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) = t.left := B.inclusion.map_injective hm
  have w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) ≫ gR = gA := hl ▸ Over.w t
  exact ⟨c.hom.toAlgebra, w, Over.OverMorphism.ext hl⟩

end SpecModels

/-! ### Zariski descent of morphisms on the affine model from the Tor clause -/

section LeafConsumer

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] RelativeDescentSituation.isDirected_laterIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : RelativeDescentSituation B S hS hZ I}

/-- **Zariski descent of morphisms on the affine model, from the Tor clause.**  Let
`g : U₀ ⟶ X₀` and `w : V ⟶ Y₀` be étale with `t ≫ w = g ≫ p₀`, with Spec models
`e₀ : Spec A ≅ U₀` and `eV : Spec R ≅ V` compatible with `t`. For a pseudo-coherent `K` and an
`L` with quasi-coherent cohomology on `Spec A` such that `ε^*L ≅ L(e₀)^*Lg^*L₀` for an object
`L₀ ∈ D(𝒪_{X₀})` locally of finite Tor dimension over `p₀⁻¹𝒪_{Y₀}`,
`RelativeDescentSituation.ZariskiModelHomDescent Rep K L` holds. -/
theorem RelativeDescentSituation.zariskiModelHomDescent_of_hasLocallyFiniteTorDimensionAlong
    (hD : D.IsSchemeLimit) {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.X₀)
    (hg : IsEtale B S hS g) (hgflat : IsFlat B S hS g) (hgfp : IsFinitePresentation B S hS g)
    {V : AlgebraicSpaces B S hS} (w : V ⟶ D.initialTarget) (t : U₀ ⟶ V.1)
    (hw : IsEtale B S hS w.hom) (ht : t ≫ w.hom = g ≫ D.p₀)
    {R : Type u} [CommRing R] {hR : B.Contains (Spec (CommRingCat.of R))}
    {gR : B.obj hR ⟶ B.obj hS} {A : Type u} [CommRing A] [Algebra R A]
    {hA : B.Contains (Spec (CommRingCat.of A))} {gA : B.obj hA ⟶ B.obj hS}
    (wA : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) ≫ gR = gA)
    (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specAffineFppf hA gA)) ≅ U₀)
    (eV : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specAffineFppf hR gR)) ≅ V.1)
    (ht' : yoneda.map (specFppfOverMap B S hS hR gR hA gA wA) ≫ eV.hom = e₀.hom ≫ t)
    (Rep : (D.restrict hU₀ g hgflat hgfp).AffineBaseChangeRepresentation (specAffineFppf hA gA)
      (e₀.hom ≫ (D.restrict hU₀ g hgflat hgfp).p₀))
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).toRingedSpace)))
    (hK : AlgebraicGeometry.RingedSpace.IsPseudoCoherent
      (X := ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).toRingedSpace) K)
    (hLqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).Modules n).obj
        L).IsQuasicoherent)
    (L₀ : derivedModules B S hS D.initialSource)
    (hL₀ : HasLocallyFiniteTorDimensionAlong D.initialStructure L₀)
    (b : (zariskiEtaleDerived B S hS _).obj L ≅
      (smallEtaleDerivedModulePullback B S hS
        (RelativeDescentSituation.modelInitialHom (D := D.restrict hU₀ g hgflat hgfp) e₀)).obj
        ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀ g hgflat hgfp)).obj L₀)) :
    RelativeDescentSituation.ZariskiModelHomDescent Rep K L := by
  exact RelativeDescentSituation.zariskiModelHomDescent_of_etale_factorization hD hU₀ g hg
    hgflat hgfp w t hw ht e₀ eV (specFppfOverMap B S hS hR gR hA gA wA) ht' Rep K L hK hLqc
    (locallyHasFiniteTorDimension_specFppfOverMap_of_hasLocallyFiniteTorDimensionAlong
      D.initialStructure L₀ hL₀ (D.restrictInitial hU₀ g hgflat hgfp) hg w hw
      (ObjectProperty.homMk t) ((ObjectProperty.ι _).map_injective ht.symm) wA
      (ObjectProperty.homMk e₀.hom) (isEtale_of_isIso B S hS e₀.hom)
      (ObjectProperty.homMk eV.hom) (isEtale_of_isIso B S hS eV.hom)
      ((ObjectProperty.ι _).map_injective ht'.symm) L hLqc b)

end LeafConsumer

end AlgebraicGeometry.Space

end
