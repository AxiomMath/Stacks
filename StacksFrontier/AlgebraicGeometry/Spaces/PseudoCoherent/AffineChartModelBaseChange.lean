module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.AffineChartModel
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullbackComputation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExistence
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeComplexes
public import StacksFrontier.Homology.KFlat.Flat
public import
StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical

/-!
# The affine chart model under a morphism of affine charts

Let `A → A₀` be a ring map and `g : Spec A₀ ⟶ Spec A` the induced morphism of the big fppf site,
and let `P` be a bounded above complex of finite free `A`-modules. The derived pullback along
`h_g : h_{Spec A₀} ⟶ h_{Spec A}` of the model `ε^*(P~)` of
`AlgebraicGeometry.Space.exists_isBoundedAboveFiniteFree_etaleModulePullback_iso` is the model
`ε^*((A₀ ⊗_A P)~)`.

## Main results

* `AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_chartModel_iso`: the derived
  pullback of `ε^*(P~)` along `h_{Spec A₀} ⟶ h_{Spec A}` is `ε^*((A₀ ⊗_A P)~)`.
* `AlgebraicGeometry.Space.nonempty_etaleModulePullback_derivedPullback_chartModel_iso`: for an
  étale chart `φ₀ : h_{Spec A₀} ⟶ X₀` lying over an étale chart `φ : h_{Spec A} ⟶ X` along
  `i : X₀ ⟶ X`, the model `ε^*(P~)` of `E` on `φ` gives the model `ε^*((A₀ ⊗_A P)~)` of `Li^*E`
  on `φ₀`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- `representedDerivedAssociatedModule` and the model of
-- `exists_isBoundedAboveFiniteFree_etaleModulePullback_iso` are stated at the standard model of
-- the derived categories they involve.
attribute [local instance 10000] HasDerivedCategory.standard

/-- The model `ε^*(P~)` of a chart, read on the degreewise sheafification of `P`. -/
def chartModelTildeIso {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (g : B.obj hA ⟶ B.obj hS) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
        (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA g))).hom
        ).mapDerivedCategory.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((tilde.functor (CommRingCat.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  ((Stacks.DerivedGlueing.mapDerivedCategoryCongr
      ((Functor.rightUnitor (tilde.functor (CommRingCat.of A))).symm ≪≫
        Functor.isoWhiskerLeft (tilde.functor (CommRingCat.of A))
          Scheme.Modules.restrictFunctorId.symm)).app _).symm ≪≫
    (tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors.app P

/-- For a ring map `A → A₀` and a bounded above complex `P` of finite free `A`-modules, the
derived pullback of `ε^*(P~)` along `h_{Spec A₀} ⟶ h_{Spec A}` is `ε^*((A₀ ⊗_A P)~)`. -/
theorem nonempty_smallEtaleDerivedModulePullback_chartModel_iso {A A₀ : Type u} [CommRing A]
    [CommRing A₀] [Algebra A A₀] (hA : B.Contains (Spec (CommRingCat.of A)))
    (gA : B.obj hA ⟶ B.obj hS) (hA₀ : B.Contains (Spec (CommRingCat.of A₀)))
    (gA₀ : B.obj hA₀ ⟶ B.obj hS)
    (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A A₀))) :
      B.obj hA₀ ⟶ B.obj hA) ≫ gA = gA₀)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P) :
    haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
      (representedSpaceMap B S hS (specFppfOverMap B S hS hA gA hA₀ gA₀ w))
    Nonempty ((smallEtaleDerivedModulePullback B S hS
        (representedSpaceMap B S hS (specFppfOverMap B S hS hA gA hA₀ gA₀ w))).obj
        ((representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
          ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
            (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA))).hom
            ).mapDerivedCategory.obj (DerivedCategory.Q.obj P))) ≅
      (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA₀ gA₀)).obj
        ((tilde.functor (CommRingCat.of A₀) ⋙ Scheme.Modules.restrictFunctor
          (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA₀ gA₀))).hom
          ).mapDerivedCategory.obj (DerivedCategory.Q.obj
            ((CochainComplex.extendScalars (algebraMap A A₀)).obj P)))) := by
  let T := specFppfOver B S hS hA gA
  let T₀ := specFppfOver B S hS hA₀ gA₀
  let g := specFppfOverMap B S hS hA gA hA₀ gA₀ w
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
    (representedSpaceMap B S hS g)
  let r := ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom
  let tP := ((tilde.functor (CommRingCat.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  obtain ⟨K, k, hK, hKf, hk, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution
    ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace tP
  have : IsIso (DerivedCategory.Q.map k) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ k).2 hk
  let eK : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj tP := asIso (DerivedCategory.Q.map k)
  obtain ⟨b, hb⟩ := hP.upperBound
  have := hb
  have : ∀ i, Module.Flat A (P.X i) := fun i =>
    have := (hP.finiteFree i).2
    inferInstance
  have htP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex
      ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace tP :=
    Stacks.TildeStalk.kFlatComplex_tilde (CommRingCat.of A) P
      (CochainComplex.KFlat.kFlat_of_flat.{u, u} P b)
  obtain ⟨e₃⟩ := nonempty_smallEtaleDerivedModulePullback_representedAssociatedModule_iso B S hS g
    K hK hKf
  let eSch := (Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat r K hK).symm ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback r).mapIso eK ≪≫
    Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat r tP htP ≪≫
    DerivedCategory.Q.mapIso ((tildePullbackComplexIso (CommRingCat.of A) (CommRingCat.of A₀)
      (CommRingCat.ofHom (algebraMap A A₀))).app P)
  exact ⟨(smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).mapIso
      ((representedDerivedAssociatedModule B S hS T).mapIso
        (chartModelTildeIso B S hS hA gA P ≪≫ eK.symm) ≪≫
      ((representedAssociatedModule B S hS T
        (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategoryFactors.app K)) ≪≫ e₃ ≪≫
    ((representedAssociatedModule B S hS T₀
      (isAlgebraicSpace_yoneda B S hS T₀)).mapDerivedCategoryFactors.app _).symm ≪≫
    (representedDerivedAssociatedModule B S hS T₀).mapIso
      (eSch ≪≫ (chartModelTildeIso B S hS hA₀ gA₀ _).symm)⟩

variable {B S hS} in
/-- The étale pullback of an object of `D(𝒪_X)` along an étale morphism is its derived pullback
(Stacks 03LW). -/
theorem nonempty_etaleModulePullback_mapDerivedCategory_iso {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsEtale B S hS f.hom) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    letI := etaleModulePullback_additive.{u, u} B S hS f hf
    letI := preservesFiniteLimits_etaleModulePullback B S hS f hf
    letI := preservesFiniteColimits_etaleModulePullback B S hS f hf
    haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS f
    Nonempty ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.obj E ≅
      (smallEtaleDerivedModulePullback B S hS f).obj E) := by
  let := etaleModulePullback_additive.{u, u} B S hS f hf
  let := preservesFiniteLimits_etaleModulePullback B S hS f hf
  let := preservesFiniteColimits_etaleModulePullback B S hS f hf
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS f
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_iso_etaleModulePullback B S hS f hf K
  exact ⟨(etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.mapIso eK.symm ≪≫
    (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategoryFactors.app K ≪≫ e.symm ≪≫
    (smallEtaleDerivedModulePullback B S hS f).mapIso eK⟩

/-- Let `i : X₀ ⟶ X`, let `φ : h_{Spec A} ⟶ X` and `φ₀ : h_{Spec A₀} ⟶ X₀` be étale with
`φ₀ ≫ i = h_g ≫ φ` for the morphism `g` of the structure map of an `A`-algebra `A₀`, and let `P`
be a bounded above complex of finite free `A`-modules with `φ^*E ≅ ε^*(P~)`. Then
`φ₀^*(Li^*E) ≅ ε^*((A₀ ⊗_A P)~)`. -/
theorem nonempty_etaleModulePullback_derivedPullback_chartModel_iso {X X₀ : AlgebraicSpaces B S hS}
    (i : X₀ ⟶ X) {A A₀ : Type u} [CommRing A] [CommRing A₀] [Algebra A A₀]
    (hA : B.Contains (Spec (CommRingCat.of A))) (gA : B.obj hA ⟶ B.obj hS)
    (hA₀ : B.Contains (Spec (CommRingCat.of A₀))) (gA₀ : B.obj hA₀ ⟶ B.obj hS)
    (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A A₀))) :
      B.obj hA₀ ⟶ B.obj hA) ≫ gA = gA₀)
    (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (φ₀ : (⟨yoneda.obj (specFppfOver B S hS hA₀ gA₀), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ X₀) (hφ₀ : IsEtale B S hS φ₀.hom)
    (hcomm : φ₀ ≫ i = representedSpaceMap B S hS (specFppfOverMap B S hS hA gA hA₀ gA₀ w) ≫ φ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (eP : letI := etaleModulePullback_additive.{u, u} B S hS φ hφ
      letI := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
      letI := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
      (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E ≅
        (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
          ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
            (Iso.refl ((BigFppfOver.toScheme B S hS).obj
              (specFppfOver B S hS hA gA))).hom).mapDerivedCategory.obj
            (DerivedCategory.Q.obj P))) :
    letI := etaleModulePullback_additive.{u, u} B S hS φ₀ hφ₀
    letI := preservesFiniteLimits_etaleModulePullback B S hS φ₀ hφ₀
    letI := preservesFiniteColimits_etaleModulePullback B S hS φ₀ hφ₀
    haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS i
    Nonempty ((etaleModulePullback.{u, u} B S hS φ₀ hφ₀).mapDerivedCategory.obj
        ((smallEtaleDerivedModulePullback B S hS i).obj E) ≅
      (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA₀ gA₀)).obj
        ((tilde.functor (CommRingCat.of A₀) ⋙ Scheme.Modules.restrictFunctor
          (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA₀ gA₀))).hom
          ).mapDerivedCategory.obj (DerivedCategory.Q.obj
            ((CochainComplex.extendScalars (algebraMap A A₀)).obj P)))) := by
  let rg := representedSpaceMap B S hS (specFppfOverMap B S hS hA gA hA₀ gA₀ w)
  have := @hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
  obtain ⟨e₁⟩ := nonempty_etaleModulePullback_mapDerivedCategory_iso φ₀ hφ₀
    ((smallEtaleDerivedModulePullback B S hS i).obj E)
  obtain ⟨e₅⟩ := nonempty_etaleModulePullback_mapDerivedCategory_iso φ hφ E
  obtain ⟨e₆⟩ := nonempty_smallEtaleDerivedModulePullback_chartModel_iso B S hS hA gA hA₀ gA₀ w P hP
  exact ⟨e₁ ≪≫ (smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS φ₀ i).app E ≪≫
    eqToIso (by rw [hcomm]) ≪≫
    ((smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS rg φ).app E).symm ≪≫
    (smallEtaleDerivedModulePullback B S hS rg).mapIso (e₅.symm ≪≫ eP) ≪≫ e₆⟩

end AlgebraicGeometry.Space

end
