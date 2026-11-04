module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeGeometricStalks
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeDerivedStalks
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleConservativeFamilyOfImages
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.StalksCanonical
import StacksCore.Tactic.StacksAttribute

/-!
# Fpqc descent of relative Tor amplitude on algebraic spaces

Let `{g_i : Y_i ⟶ Y}` be an fpqc covering of algebraic spaces over a scheme `S`, let `f : X ⟶ Y`
be a morphism of algebraic spaces and let `X_i = Y_i ×_Y X`, with projections `f_i : X_i ⟶ Y_i`
and `g'_i : X_i ⟶ X`.  Stacks 0DL2 says that an object `E` of `D_QCoh(𝒪_X)` has Tor amplitude in
`[a, b]` as an object of `D(f⁻¹𝒪_Y)` if and only if every `L(g'_i)^*E` has Tor amplitude in
`[a, b]` as an object of `D(f_i⁻¹𝒪_{Y_i})`.

Here `E` is read in `D(f⁻¹𝒪_Y)` through restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`
(`AlgebraicGeometry.Space.derivedScalarRestriction`), Tor amplitude is measured against the
derived tensor product of Stacks 06YU on `(X_étale, f⁻¹𝒪_Y)`, and `L(g'_i)^*` is the derived
pullback of Stacks 06YY (`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`).

## Main results

* `AlgebraicGeometry.Space.hasTorAmplitude_derivedScalarRestriction_iff_forall_of_isFpqcCovering`:
  `E` has Tor amplitude in `[a, b]` over `f⁻¹𝒪_Y` if and only if every `L(g'_i)^*E` has Tor
  amplitude in `[a, b]` over `f_i⁻¹𝒪_{Y_i}`.
* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_iff`
  and `hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_pullback_iff`: the derived
  stalks at a geometric point of `E` read over `f⁻¹𝒪_Y`, and of `L(g')^*E` read over
  `f'⁻¹𝒪_{Y'}`, in terms of the geometric stalk complex of `E`.
* `AlgebraicGeometry.Space.isFpqcCovering_of_isPullback` and
  `AlgebraicGeometry.Space.exists_geometricPointMap_image_eq_of_isPullback`: the base change of an
  fpqc covering is an fpqc covering, so every geometric point of `X` lies over the same point as
  a geometric point coming from some `X_i`.

## References

* [Stacks Project, Tag 0DL2](https://stacks.math.columbia.edu/tag/0DL2)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 068S](https://stacks.math.columbia.edu/tag/068S)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Stalks

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- Canonical Tor amplitude transports along isomorphisms on both sides of an equivalence. -/
private theorem hasTorAmplitudeCanonical_iff_of_iso {R R' : Type u} [CommRing R] [CommRing R']
    {A B : DerivedCategory (ModuleCat.{u} R)} {C D : DerivedCategory (ModuleCat.{u} R')}
    (e₁ : A ≅ B) (e₂ : C ≅ D) (a b : ℤ)
    (h : HasTorAmplitudeCanonical R B a b ↔ HasTorAmplitudeCanonical R' C a b) :
    HasTorAmplitudeCanonical R A a b ↔ HasTorAmplitudeCanonical R' D a b :=
  ⟨fun hA ↦ AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₂ a b
      (h.1 (AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₁ a b hA)),
    fun hD ↦ AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₁.symm a b
      (h.2 (AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₂.symm a b
        hD))⟩

/-- The fibre of the structure map of `f` at `x̄` is the fibre comparison of Stacks 04K2 (4)
followed by the fibre of `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
theorem stalkStructureMap_hom_eq_comp :
    (stalkStructureMap B S hS f x).hom =
      (Stacks.SitePointBaseChange.stalkRingHom
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom
          (etaleSitePoint B S hS X.1 x X.2)).comp
        ((smallEtaleInverseImageFiberRingIso B S hS f x).app
          (smallEtaleRingedTopos B S hS Y).O).commRingCatIsoToRingEquiv.toRingHom :=
  rfl

/-- For a complex
`K` of `𝒪_X`-modules, the derived stalk at `x̄` of `K` read in `D(f⁻¹𝒪_Y)` has Tor amplitude in
`[a, b]` over the fibre of `f⁻¹𝒪_Y` exactly when the stalk complex `K_x̄` has Tor amplitude in
`[a, b]` over `𝒪_{Y,f(x̄)}` through the fibre of the structure map. -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_iff
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (a b : ℤ) :
    HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS f).O.obj)
        ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
          (inverseImageRingedSite B S hS f).O).obj
          ((derivedScalarRestriction B S hS f).obj (DerivedCategory.Q.obj K))) a b ↔
      HasTorAmplitudeCanonical (geometricStalkRing B S hS (geometricPointMap f.hom x))
        (DerivedCategory.Q.obj ((CochainComplex.restrictScalars
          (stalkStructureMap B S hS f x).hom).obj
          (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))) a b := by
  let ι := ((smallEtaleInverseImageFiberRingIso B S hS f x).app
    (smallEtaleRingedTopos B S hS Y).O).commRingCatIsoToRingEquiv
  let ρ := Stacks.SitePointBaseChange.stalkRingHom
    (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom (etaleSitePoint B S hS X.1 x X.2)
  let M := ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have e₁ := derivedStalkScalarRestrictionIso B S hS f x K
  have hρι : (stalkStructureMap B S hS f x).hom = ρ.comp ι.toRingHom :=
    stalkStructureMap_hom_eq_comp B S hS f x
  have e₂ : (ModuleCat.restrictScalars ι.toRingHom).mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars ρ).obj M)) ≅
      DerivedCategory.Q.obj ((CochainComplex.restrictScalars
        (stalkStructureMap B S hS f x).hom).obj M) :=
    (ModuleCat.restrictScalars ι.toRingHom).mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
        (fun n ↦ (ModuleCat.restrictScalarsComp'App.{u} ι.toRingHom ρ _ hρι (M.X n)).symm)
        (fun i j _ ↦ by ext; rfl))
  exact hasTorAmplitudeCanonical_iff_of_iso e₁ e₂ a b
    (AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff
      ι _ a b).symm

end Stalks

section PullbackStalks

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

/-- For a flat morphism
`g : X' ⟶ X`, a morphism `f' : X' ⟶ Y'` and a complex `K` of `𝒪_X`-modules, the derived stalk at
`x̄'` of `Lg^*K` read in `D(f'⁻¹𝒪_{Y'})` has Tor amplitude in `[a, b]` exactly when
`K_{g(x̄')} ⊗_{𝒪_{X,g(x̄')}} 𝒪_{X',x̄'}` has Tor amplitude in `[a, b]` over `𝒪_{Y',f'(x̄')}`. -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_pullback_iff
    {X' X Y' : AlgebraicSpaces B S hS} (g : X' ⟶ X) (hg : IsFlat B S hS g.hom) (f' : X' ⟶ Y')
    (x' : GeometricPoint B S hS X'.1) (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (a b : ℤ) :
    HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS X'.1 x' X'.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS f').O.obj)
        ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
          (inverseImageRingedSite B S hS f').O).obj
          ((derivedScalarRestriction B S hS f').obj
            ((smallEtaleDerivedModulePullback B S hS g).obj (DerivedCategory.Q.obj K)))) a b ↔
      HasTorAmplitudeCanonical (geometricStalkRing B S hS (geometricPointMap f'.hom x'))
        (DerivedCategory.Q.obj ((CochainComplex.restrictScalars
          (stalkStructureMap B S hS f' x').hom).obj
          ((CochainComplex.extendScalars (stalkStructureMap B S hS g x').hom).obj
            (((Stacks.sheafModuleFiberOfCommRing
              (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
              (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)))) a b := by
  let K' : CochainComplex (Modules.{u, u} B S hS X'.1 X'.2) ℤ :=
    ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
  have e₀ : ((smallEtaleDerivedModulePullback B S hS g).obj (DerivedCategory.Q.obj K) :
      DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2)) ≅ DerivedCategory.Q.obj K' :=
    derivedPullbackObjIsoOfIsFlat B S hS g hg K
  have e₁ := (Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
    (inverseImageRingedSite B S hS f').O).mapIso ((derivedScalarRestriction B S hS f').mapIso e₀)
  have hβ : Stacks.Sheaves.StalkPullback.stalkRingMap
      (smallEtaleRingedToposHom B S hS g).toModulesHom
      (etaleSitePoint B S hS X'.1 x' X'.2)
      (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
      (smallEtaleInverseImageFiberIso B S hS g x') = (stalkStructureMap B S hS g x').hom :=
    (stalkRingMap_toModulesHom_eq B S hS g x').trans
      (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap B S hS g x').symm
  have e₂ := DerivedCategory.Q.mapIso ((CochainComplex.restrictScalars
    (stalkStructureMap B S hS f' x').hom).mapIso (stalkComplexPullbackIso B S hS g x' K))
  rw [hβ] at e₂
  exact hasTorAmplitudeCanonical_iff_of_iso e₁ e₂ a b
    (hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_iff B S hS f' x' K' a b)

end PullbackStalks

section Descent

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open Stacks.SheafOfModules.DerivedTensorProduct

variable {I : Type v} {Y : AlgebraicSpaces B S hS} {Yi : I → AlgebraicSpaces B S hS}
  (g : ∀ i, Yi i ⟶ Y) (hg : IsFpqcCovering B S hS fun i => (g i).hom)
  {X : AlgebraicSpaces B S hS} (f : X ⟶ Y) {Xi : I → AlgebraicSpaces B S hS}
  (f' : ∀ i, Xi i ⟶ Yi i) (g' : ∀ i, Xi i ⟶ X) (hpb : ∀ i, IsPullback (g' i) (f' i) f (g i))

include hg hpb in
/-- The base change of an fpqc covering along a morphism, presented by given cartesian squares,
is an fpqc covering. -/
theorem isFpqcCovering_of_isPullback : IsFpqcCovering B S hS fun i => (g' i).hom := by
  have h₁ := isFpqcCovering_pullback_fst B S hS Yi g hg X f
  have h₂ := isFpqcCovering_isoComp B S hS (fun i ↦ ((hpb i).isoPullback.hom).hom)
    (fun i ↦ (pullback.fst f (g i)).hom) h₁
  convert h₂ using 2 with i
  exact congrArg (fun k : Xi i ⟶ X ↦ k.hom) (hpb i).isoPullback_hom_fst.symm

include hg hpb in
/-- Every geometric point of `X` lies over the same point of `|X|` as the image of a geometric
point of some `X_i`. -/
theorem exists_geometricPointMap_image_eq_of_isPullback (x : GeometricPoint B S hS X.1) :
    ∃ k : Σ i, GeometricPoint B S hS (Xi i).1,
      (geometricPointMap (g' k.1).hom k.2).image = x.image := by
  obtain ⟨i, z, hz⟩ := (isJointlySurjective_iff B S hS _ _).1
    (isJointlySurjective_of_isFpqcCovering B S hS (fun i ↦ (g' i).hom)
      (isFpqcCovering_of_isPullback B S hS g hg f f' g' hpb)) x.image
  obtain ⟨x', hx'⟩ := exists_geometricRepresentative B S hS (Xi i).1 z
  exact ⟨⟨i, x'⟩, by rw [geometricPointMap_image, hx', hz]⟩

attribute [local instance 10000] HasDerivedCategory.standard

include hg hpb in
/-- Let `{g_i : Y_i ⟶ Y}` be an fpqc covering of
algebraic spaces over `S`, let `f : X ⟶ Y` be a morphism of algebraic spaces and let
`X_i = Y_i ×_Y X`, with projections `f_i : X_i ⟶ Y_i` and `g'_i : X_i ⟶ X`.  An object `E` of
`D(𝒪_X)` has Tor amplitude in `[a, b]` as an object of `D(f⁻¹𝒪_Y)` if and only if every
`L(g'_i)^* E` has Tor amplitude in `[a, b]` as an object of `D(f_i⁻¹𝒪_{Y_i})`, both measured
against the derived tensor product of Stacks 06YU. -/
@[stacks 0DL2 "tor amplitude in [a, b]"]
theorem hasTorAmplitude_derivedScalarRestriction_iff_forall_of_isFpqcCovering
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a b : ℤ) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
          (inverseImageRingedSite B S hS f)) ((derivedScalarRestriction B S hS f).obj E) a b ↔
      ∀ i, Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
          (inverseImageRingedSite B S hS (f' i)))
        ((derivedScalarRestriction B S hS (f' i)).obj
          ((smallEtaleDerivedModulePullback B S hS (g' i)).obj E)) a b := by
  have hflat : ∀ i, IsFlat B S hS (g i).hom := hg.1
  have hflat' : ∀ i, IsFlat B S hS (g' i).hom := fun i ↦
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback (hpb i).flip (hflat i)
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hE : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        (inverseImageRingedSite B S hS f)) ((derivedScalarRestriction B S hS f).obj E) a b ↔
      Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        (inverseImageRingedSite B S hS f))
        ((derivedScalarRestriction B S hS f).obj (DerivedCategory.Q.obj K)) a b :=
    ⟨fun h ↦ h.of_iso ((derivedScalarRestriction B S hS f).mapIso e.symm),
      fun h ↦ h.of_iso ((derivedScalarRestriction B S hS f).mapIso e)⟩
  have hEi : ∀ i, Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        (inverseImageRingedSite B S hS (f' i)))
        ((derivedScalarRestriction B S hS (f' i)).obj
          ((smallEtaleDerivedModulePullback B S hS (g' i)).obj E)) a b ↔
      Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        (inverseImageRingedSite B S hS (f' i)))
        ((derivedScalarRestriction B S hS (f' i)).obj
          ((smallEtaleDerivedModulePullback B S hS (g' i)).obj (DerivedCategory.Q.obj K))) a b :=
    fun i ↦ ⟨fun h ↦ h.of_iso ((derivedScalarRestriction B S hS (f' i)).mapIso
        ((smallEtaleDerivedModulePullback B S hS (g' i)).mapIso e.symm)),
      fun h ↦ h.of_iso ((derivedScalarRestriction B S hS (f' i)).mapIso
        ((smallEtaleDerivedModulePullback B S hS (g' i)).mapIso e))⟩
  simp only [hE, hEi]
  constructor
  · intro h i
    refine hasTorAmplitude_of_forall_derivedModuleFiber_family.{u + 1, u, u, u + 1}
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        (inverseImageRingedSite B S hS (f' i))) _ a b
      (fun x' : GeometricPoint B S hS (Xi i).1 ↦ etaleSitePoint B S hS (Xi i).1 x' (Xi i).2)
      (isConservativeFamilyOfPoints_etaleSitePoint B S hS (Xi i).1 (Xi i).2) fun x' ↦ ?_
    refine (hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_pullback_iff B S hS
      (g' i) (hflat' i) (f' i) x' K a b).2 ?_
    refine hasTorAmplitudeCanonical_geometricStalk_baseChange B S hS (g' i) (f' i) f (g i)
      (hpb i) (hflat i) x' _ a b ?_
    refine (hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_iff B S hS f
      (geometricPointMap (g' i).hom x') K a b).1 ?_
    exact hasTorAmplitudeCanonical_derivedModuleFiber.{u + 1, u, u, u + 1} _ _ a b h
      (etaleSitePoint B S hS X.1 (geometricPointMap (g' i).hom x') X.2)
  · intro h
    refine hasTorAmplitude_of_forall_derivedModuleFiber_family.{u + 1, u, u, u + 1}
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        (inverseImageRingedSite B S hS f)) _ a b
      (fun k : Σ i, GeometricPoint B S hS (Xi i).1 ↦
        etaleSitePoint B S hS X.1 (geometricPointMap (g' k.1).hom k.2) X.2)
      (isConservativeFamilyOfPoints_etaleSitePoint_of_forall_image B S hS X.1 X.2
        (fun k : Σ i, GeometricPoint B S hS (Xi i).1 ↦ geometricPointMap (g' k.1).hom k.2)
        (exists_geometricPointMap_image_eq_of_isPullback B S hS g hg f f' g' hpb))
      fun ⟨i, x'⟩ ↦ ?_
    refine (hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_iff B S hS f
      (geometricPointMap (g' i).hom x') K a b).2 ?_
    refine hasTorAmplitudeCanonical_geometricStalk_of_baseChange B S hS (g' i) (f' i) f (g i)
      (hpb i) (hflat i) x' _ a b ?_
    refine (hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_pullback_iff B S hS
      (g' i) (hflat' i) (f' i) x' K a b).1 ?_
    exact hasTorAmplitudeCanonical_derivedModuleFiber.{u + 1, u, u, u + 1} _ _ a b (h i)
      (etaleSitePoint B S hS (Xi i).1 x' (Xi i).2)

end Descent

end AlgebraicGeometry.Space

end
