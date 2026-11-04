module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherent.Characterization
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineHomToStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedZariskiPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPushforwardSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackCompAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.AlgebraicGeometry.UniformTwistBound.Basic

/-!
# Pseudo-coherence on projective space over `A`, read on the small étale site

Let `A` be a ring and `P = ℙⁿ_A`, the algebraic space represented by projective space over
`Spec A`. For `M ∈ D_QCoh(𝒪_P)` on the small étale site, if `RΓ(P, M ⊗^𝐋 𝒪(d))` is a
pseudo-coherent object of `D(A)` for `0 ≤ d ≤ n`, then `M` is pseudo-coherent. This is
(5) ⟹ (1) of Stacks 0CSG, carried from the Zariski site of the model `Proj A[T₀, …, Tₙ]` to the
small étale site of `P` along the comparison `ε` of Stacks 071Q and the isomorphism of the two
models of projective space.

## Main definitions

* `AlgebraicGeometry.Space.projModelSiteObj`: `Proj A[T₀, …, Tₙ]` as an object of the site.
* `AlgebraicGeometry.Space.projModelSpaceIso`: its algebraic space is the one of `ℙⁿ_A`.
* `AlgebraicGeometry.Space.projectiveSpaceSiteTwist`: `𝒪(d)` on the small étale site of `ℙⁿ_A`.

## Main results

* `AlgebraicGeometry.Space.nonempty_representedZariskiDerivedPullback_projModelZariskiTensor_iso`:
  `Lε^*(Z ⊗^𝐋 𝒪(d)) ≅ Lε^*Z ⊗^𝐋 Lε^*𝒪(d)`.
* `AlgebraicGeometry.Space.isPseudoCoherent_of_isPseudoCoherent_twist_projectiveSpace`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  isGrothendieckAbelian_ringedToposStructureRingSheaf

section Iso

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- Derived pullback along an isomorphism of algebraic spaces is an equivalence, with
quasi-inverse the derived pullback along the inverse. -/
def smallEtaleDerivedModulePullbackModulesEquivalence (e : X ≅ Y) :
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ≌
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
  CategoryTheory.Equivalence.mk (smallEtaleDerivedModulePullback B S hS e.hom)
    (smallEtaleDerivedModulePullback B S hS e.inv)
    ((smallEtaleDerivedModulePullbackIdIso B S hS Y).symm ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS e.inv_hom_id.symm ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS e.inv e.hom).symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS e.hom e.inv ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS e.hom_inv_id ≪≫
      smallEtaleDerivedModulePullbackIdIso B S hS X)

/-- Pseudo-coherence on the small étale site pulls back along an isomorphism in the derived
category. -/
private theorem isPseudoCoherent_of_iso_smallEtale {M N : DerivedCategory (Modules.{u, u} B S hS
      X.1 X.2)} (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent N) (e : M ≅ N) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent M :=
  (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ M).2 fun m =>
    RingedSite.isPseudoCoherentFrom_of_iso _ m
      ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 h m) e

/-- Pseudo-coherence descends along derived pullback by an isomorphism of algebraic spaces. -/
theorem isPseudoCoherent_of_smallEtaleDerivedModulePullback_iso (e : X ≅ Y)
    (M : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
      ((smallEtaleDerivedModulePullback B S hS e.hom).obj M)) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent M := by
  have h' := isPseudoCoherent_smallEtaleDerivedModulePullback e.inv _ h
  exact isPseudoCoherent_of_iso_smallEtale h'
    ((smallEtaleDerivedModulePullbackModulesEquivalence e).unitIso.app M)

/-- `R(e ≫ g)_* Le^* N ≅ Rg_* N` for an isomorphism `e`. -/
def derivedModulePushforwardCompPullbackIso (e : X ≅ Y) (g : Y ⟶ Z)
    (N : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    (derivedModulePushforward B S hS (e.hom ≫ g)).obj
        ((smallEtaleDerivedModulePullback B S hS e.hom).obj N) ≅
      (derivedModulePushforward B S hS g).obj N :=
  ((smallEtaleDerivedPushforwardCompIsoToposHom B S hS e.hom g).app _).symm ≪≫
    (derivedModulePushforward B S hS g).mapIso
      ((Adjunction.rightAdjointUniq (smallEtaleDerivedModuleAdjunction B S hS e.hom)
        (smallEtaleDerivedModulePullbackModulesEquivalence e).toAdjunction).app _ ≪≫
        ((smallEtaleDerivedModulePullbackModulesEquivalence e).unitIso.app N).symm)

end Iso

section Model

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (n : ℕ)

include hA in
/-- `Proj A[T₀, …, Tₙ]` lies in every big fppf site containing `Spec A`. -/
theorem contains_proj_polyGrading : B.Contains (Proj (polyGrading A n)) :=
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff A n
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (projToSpecCoeff A n) hA

/-- `Proj A[T₀, …, Tₙ]` with its structure morphism, as an object of the big fppf site over
`Spec A`. -/
abbrev projModelSiteObj : BigFppfOver B (Spec (CommRingCat.of A)) hA :=
  siteObject B _ hA (contains_proj_polyGrading B hA n) (projToSpecCoeff A n)

/-- The structure morphism of `Proj A[T₀, …, Tₙ]`, in the site. -/
def projModelSiteObjToBase : projModelSiteObj B hA n ⟶ baseSiteObj B _ hA :=
  Over.homMk (projModelSiteObj B hA n).hom (Category.comp_id _)

/-- The two models of `ℙⁿ_A` are isomorphic over `Spec A`, as objects of the site. -/
def projModelSiteObjIso (hP : B.Contains (projectiveSpaceOver n (Spec (CommRingCat.of A)))) :
    projModelSiteObj B hA n ≅ projectiveSpaceSiteObj B _ hA n hP :=
  Over.isoMk (ObjectProperty.isoMk _ (Stacks.ProjectiveCohomology.projModelIso A n)) (by
    ext1
    exact (Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism A n).trans
      (Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec A n).symm)

variable {B hA}

/-- The canonical derived tensor product on the Zariski ringed topos of `Proj A[T₀, …, Tₙ]`. -/
abbrev projModelZariskiTensor : Stacks.SheafOfModules.DerivedTensorProduct
    (Proj (polyGrading A n)).zariskiRingedTopos.toRingedSite :=
  Stacks.SheafOfModules.canonicalDerivedTensorProduct
    (Proj (polyGrading A n)).zariskiRingedTopos.toRingedSite

/-- `Z ⊗^𝐋 𝒪(d) ≅ Z(d)` for the Zariski derived tensor product of the model. -/
theorem nonempty_projModelZariskiTensor_twistingSheaf_iso (d : ℤ)
    (Z : DerivedCategory (Proj (polyGrading A n)).Modules) :
    Nonempty ((((projModelZariskiTensor (A := A) n).tensor.obj Z).obj
          ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d))) ≅
      (Stacks.AlgebraicGeometry.ProjTwistFunctor.twistModules A n d).mapDerivedCategory.obj Z) :=
  have : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Proj (polyGrading A n)).zariskiRingedTopos.toRingedSite.O).Additive :=
    Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} _
  have : ∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Proj (polyGrading A n)).zariskiRingedTopos.toRingedSite.O).obj M).Additive :=
    fun M => Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} _ M
  have : ∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u}
      (Proj (polyGrading A n)).zariskiRingedTopos.toRingedSite) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (Proj (polyGrading A n)).zariskiRingedTopos.toRingedSite.O) (ComplexShape.up ℤ) :=
    fun K L => Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u, u, u, u, u} _ K L
  ⟨Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleRightIsoOfExact.{u} _
    (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
      (projModelZariskiTensor (A := A) n))
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)
    (Stacks.AlgebraicGeometry.ProjTwistFunctor.twistModules A n d)
    (hFa := inferInstanceAs
      (Stacks.AlgebraicGeometry.ProjTwistFunctor.twistModules A n d).Additive)
    (hFl := inferInstanceAs
      (PreservesFiniteLimits (Stacks.AlgebraicGeometry.ProjTwistFunctor.twistModules A n d)))
    (hFc := inferInstanceAs
      (PreservesFiniteColimits (Stacks.AlgebraicGeometry.ProjTwistFunctor.twistModules A n d)))
    rfl Z⟩

/-- **Stacks 07A4 for `ε`** at `Z` and `𝒪(d)`: `Lε^*(Z ⊗^𝐋 𝒪(d)) ≅ Lε^*Z ⊗^𝐋 Lε^*𝒪(d)`. -/
theorem nonempty_representedZariskiDerivedPullback_projModelZariskiTensor_iso (d : ℤ)
    (Z : DerivedCategory (Proj (polyGrading A n)).Modules) :
    Nonempty ((representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).obj
        (((projModelZariskiTensor (A := A) n).tensor.obj Z).obj
          ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d))) ≅
      ((smallEtaleDerivedTensor B _ hA (representedSpace (projModelSiteObj B hA n))).obj
        ((representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).obj Z)).obj
        ((representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).obj
          ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)))) :=
  ⟨(Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B _ hA
      (projModelSiteObj B hA n))
    (smallEtaleDerivedTensorProduct B _ hA (representedSpace (projModelSiteObj B hA n)))
    (projModelZariskiTensor (A := A) n)).app
      (Z, (DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d))⟩

variable (B hA) (hP : B.Contains (projectiveSpaceOver n (Spec (CommRingCat.of A))))

/-- The algebraic space of `Proj A[T₀, …, Tₙ]` is the one of `ℙⁿ_A`. -/
def projModelSpaceIso : representedSpace (projModelSiteObj B hA n) ≅
    schemeSpace (projectiveSpaceSiteObj B _ hA n hP) :=
  ObjectProperty.isoMk _ (yoneda.mapIso (projModelSiteObjIso B hA n hP))

/-- `𝒪(d)` on the small étale site of `ℙⁿ_A`: the twisting sheaf of the model, carried by `ε` and
the isomorphism of the two models. -/
abbrev projectiveSpaceSiteTwist (d : ℤ) :
    DerivedCategory (Modules.{u, u} B _ hA (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)).1
      (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)).2) :=
  (smallEtaleDerivedModulePullback B _ hA (projModelSpaceIso B hA n hP).inv).obj
    ((representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).obj
      ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d)))

/-- The isomorphism of the two models is a morphism over `Spec A`. -/
theorem projModelSpaceIso_hom_comp :
    (projModelSpaceIso B hA n hP).hom ≫
        schemeSpaceMap (projectiveSpaceSiteObjToBase B _ hA n hP) =
      representedSpaceMap B _ hA (projModelSiteObjToBase B hA n) :=
  ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
    (congrArg yoneda.map (Over.mkIdTerminal.hom_ext _ _)))

/-- Along the isomorphism of the two models, `R(Proj A[T] → Spec A)_* ∘ Lψ^*` is
`R(ℙⁿ_A → Spec A)_*`. -/
theorem nonempty_derivedModulePushforward_projModelSpaceIso_iso
    (W : DerivedCategory (Modules.{u, u} B _ hA
      (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)).1
      (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)).2)) :
    Nonempty ((derivedModulePushforward B _ hA
        (representedSpaceMap B _ hA (projModelSiteObjToBase B hA n))).obj
          ((smallEtaleDerivedModulePullback B _ hA (projModelSpaceIso B hA n hP).hom).obj W) ≅
      (derivedModulePushforward B _ hA
        (schemeSpaceMap (projectiveSpaceSiteObjToBase B _ hA n hP))).obj W) := by
  rw [← projModelSpaceIso_hom_comp B hA n hP]
  exact ⟨derivedModulePushforwardCompPullbackIso _ _ W⟩

/-- `Lψ^*(M ⊗^𝐋 W) ≅ Lψ^*M ⊗^𝐋 Lψ^*W` along the isomorphism of the two models. -/
theorem nonempty_smallEtaleDerivedModulePullback_projModelSpaceIso_tensor_iso
    (M W : DerivedCategory (Modules.{u, u} B _ hA
      (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)).1
      (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)).2)) :
    Nonempty ((smallEtaleDerivedModulePullback B _ hA (projModelSpaceIso B hA n hP).hom).obj
        (((smallEtaleDerivedTensor B _ hA (schemeSpace (projectiveSpaceSiteObj B _ hA n hP))).obj
          M).obj W) ≅
      ((smallEtaleDerivedTensor B _ hA (representedSpace (projModelSiteObj B hA n))).obj
        ((smallEtaleDerivedModulePullback B _ hA (projModelSpaceIso B hA n hP).hom).obj M)).obj
        ((smallEtaleDerivedModulePullback B _ hA (projModelSpaceIso B hA n hP).hom).obj W)) :=
  ⟨(smallEtaleDerivedPullbackTensorIso (projModelSpaceIso B hA n hP).hom).app (M, W)⟩

/-- The twist `𝒪(d)` of `ℙⁿ_A` pulls back to `Lε^*𝒪(d)` on the model. -/
theorem nonempty_smallEtaleDerivedModulePullback_projectiveSpaceSiteTwist_iso (d : ℤ) :
    Nonempty ((smallEtaleDerivedModulePullback B _ hA (projModelSpaceIso B hA n hP).hom).obj
        (projectiveSpaceSiteTwist B hA n hP d) ≅
      (representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).obj
        ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d))) :=
  ⟨(smallEtaleDerivedModulePullbackModulesEquivalence
    (projModelSpaceIso B hA n hP)).counitIso.app _⟩

/-- Pseudo-coherence of `RΓ(Spec A, Rπ_* -)` on the model is invariant under isomorphism. -/
private theorem isPseudoCoherent_sections_pushforward_projModel_of_iso
    {P Q : DerivedCategory (Modules.{u, u} B _ hA
      (representedSpace (projModelSiteObj B hA n)).1
      (representedSpace (projModelSiteObj B hA n)).2)}
    (h : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
        ((derivedModulePushforward B _ hA
          (representedSpaceMap B _ hA (projModelSiteObjToBase B hA n))).obj P)))
    (e : P ≅ Q) : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
        ((derivedModulePushforward B _ hA
          (representedSpaceMap B _ hA (projModelSiteObjToBase B hA n))).obj Q)) :=
  h.ofIso ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).mapIso
    ((derivedModulePushforward B _ hA
      (representedSpaceMap B _ hA (projModelSiteObjToBase B hA n))).mapIso e))

/-- The test functors on the model `Proj A[T₀, …, Tₙ]` are pseudo-coherent at `Z` as soon as the
étale `RΓ(Spec A, -)` of `Lε^*Z ⊗^𝐋 Lε^*𝒪(d)` is. -/
theorem isPseudoCoherent_testFunctor_of_isPseudoCoherent_representedZariskiDerivedPullback
    (Z : DerivedCategory (Proj (polyGrading A n)).Modules)
    (hZ : ProjectiveSpacePseudoCoherent.quasicoherentObject A n Z) (d : ℤ)
    (h : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
        ((derivedModulePushforward B _ hA
          (representedSpaceMap B _ hA (projModelSiteObjToBase B hA n))).obj
          (((smallEtaleDerivedTensor B _ hA (representedSpace (projModelSiteObj B hA n))).obj
            ((representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).obj Z)).obj
            ((representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).obj
              ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
                (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d))))))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((ProjectiveSpacePseudoCoherent.testFunctor A n d).obj Z) := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff A n
  have hfqc : IsQuasiCompact B _ hA
      (representedSpaceMap B _ hA (projModelSiteObjToBase B hA n)).hom :=
    isQuasiCompact_of_presheaf_quasiCompact B _ hA
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B _ hA _ _).2
        (inferInstanceAs (QuasiCompact (projToSpecCoeff A n))))
  have hfqs : IsQuasiSeparated B _ hA
      (representedSpaceMap B _ hA (projModelSiteObjToBase B hA n)).hom :=
    (isQuasiSeparated_yoneda_map_iff B _ hA _).2
      (inferInstanceAs (QuasiSeparated (projToSpecCoeff A n)))
  have hZd : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj
      ((Stacks.AlgebraicGeometry.ProjTwistFunctor.twistModules A n d).mapDerivedCategory.obj
        Z)).IsQuasicoherent := fun q =>
    (SheafOfModules.isQuasicoherent _).prop_of_iso
      (((Stacks.AlgebraicGeometry.ProjTwistFunctor.twistModules A n d).mapDerivedCategoryHomologyIso
          q).app Z).symm
      (Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.isQuasicoherent_twistSheafOfModules
        (polyGrading A n) _ (hZ q) d)
  refine (isPseudoCoherent_representedAffineDerivedSections_pushforward_iff_of_eq
    (projModelSiteObjToBase B hA n) (projToSpecCoeff A n) rfl hfqc hfqs _ hZd).1 ?_
  exact isPseudoCoherent_sections_pushforward_projModel_of_iso B hA n h
    (((representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).mapIso
        (nonempty_projModelZariskiTensor_twistingSheaf_iso (A := A) n d Z).some.symm ≪≫
      (nonempty_representedZariskiDerivedPullback_projModelZariskiTensor_iso (B := B) (hA := hA)
        n d Z).some).symm)

/-- The previous lemma for all the test functors at once. -/
theorem testPseudoCoherent_of_isPseudoCoherent_representedZariskiDerivedPullback
    (Z : DerivedCategory (Proj (polyGrading A n)).Modules)
    (hZ : ProjectiveSpacePseudoCoherent.quasicoherentObject A n Z)
    (h : ∀ d : Fin (n + 1), StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
        ((derivedModulePushforward B _ hA
          (representedSpaceMap B _ hA (projModelSiteObjToBase B hA n))).obj
          (((smallEtaleDerivedTensor B _ hA (representedSpace (projModelSiteObj B hA n))).obj
            ((representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).obj Z)).obj
            ((representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).obj
              ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
                (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d))))))) :
    ProjectiveSpacePseudoCoherent.testPseudoCoherent A n Z := by
  intro d
  exact isPseudoCoherent_testFunctor_of_isPseudoCoherent_representedZariskiDerivedPullback B hA n
    Z hZ d (h d)

/-- **(5) ⟹ (1) of Stacks 0CSG on the algebraic space of `Proj A[T₀, …, Tₙ]`.** -/
theorem isPseudoCoherent_of_isPseudoCoherent_twist_projModel
    (N : DerivedCategory (Modules.{u, u} B _ hA
      (representedSpace (projModelSiteObj B hA n)).1
      (representedSpace (projModelSiteObj B hA n)).2))
    (hN : QcohDerived B _ hA (representedSpace (projModelSiteObj B hA n)) N)
    (h5 : ∀ d : Fin (n + 1), StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
        ((derivedModulePushforward B _ hA
          (representedSpaceMap B _ hA (projModelSiteObjToBase B hA n))).obj
          (((smallEtaleDerivedTensor B _ hA
            (representedSpace (projModelSiteObj B hA n))).obj N).obj
            ((representedZariskiDerivedPullback B _ hA (projModelSiteObj B hA n)).obj
              ((DerivedCategory.singleFunctor (Proj (polyGrading A n)).Modules 0).obj
                (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d))))))) :
    (smallEtaleRingedSite B _ hA (representedSpace (projModelSiteObj B hA n)).1
      (representedSpace (projModelSiteObj B hA n)).2).IsPseudoCoherent N := by
  have := isIso_representedZariskiDerivedAdjunction_counit_app B _ hA
    (projModelSiteObj B hA n) N hN
  have hZ := isQuasicoherent_homology_representedZariskiDerivedPushforward_obj B _ hA
    (projModelSiteObj B hA n) N hN
  have hY : ProjectiveSpacePseudoCoherent.testPseudoCoherent A n
      ((representedZariskiDerivedPushforward B _ hA (projModelSiteObj B hA n)).obj N) :=
    testPseudoCoherent_of_isPseudoCoherent_representedZariskiDerivedPullback B hA n
      ((representedZariskiDerivedPushforward B _ hA (projModelSiteObj B hA n)).obj N) hZ fun d =>
        isPseudoCoherent_sections_pushforward_projModel_of_iso B hA n (h5 d)
          (((smallEtaleDerivedTensor B _ hA (representedSpace (projModelSiteObj B hA n))).mapIso
            (asIso ((representedZariskiDerivedAdjunction B _ hA
              (projModelSiteObj B hA n)).counit.app N)).symm).app _)
  have hZpc := ProjectiveSpacePseudoCoherent.isPseudoCoherent_of_testPseudoCoherent A n
    ((representedZariskiDerivedPushforward B _ hA (projModelSiteObj B hA n)).obj N) hZ hY
  have hLZ := (isPseudoCoherent_representedZariskiDerivedPullback_iff (projModelSiteObj B hA n)
    ((representedZariskiDerivedPushforward B _ hA (projModelSiteObj B hA n)).obj N)).2 hZpc
  exact isPseudoCoherent_of_iso_smallEtale hLZ
    (asIso ((representedZariskiDerivedAdjunction B _ hA
      (projModelSiteObj B hA n)).counit.app N)).symm

/-- **(5) ⟹ (1) of Stacks 0CSG on `ℙⁿ_A`, read on the small étale site.** Let
`M ∈ D_QCoh(𝒪_{ℙⁿ_A})` with `RΓ(ℙⁿ_A, M ⊗^𝐋 𝒪(d))` pseudo-coherent in `D(A)` for `0 ≤ d ≤ n`.
Then `M` is pseudo-coherent. -/
theorem isPseudoCoherent_of_isPseudoCoherent_twist_projectiveSpace
    (M : DerivedCategory (Modules.{u, u} B _ hA
      (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)).1
      (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)).2))
    (hM : QcohDerived B _ hA (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)) M)
    (h5 : ∀ d : Fin (n + 1), StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
        ((derivedModulePushforward B _ hA
          (schemeSpaceMap (projectiveSpaceSiteObjToBase B _ hA n hP))).obj
          (((smallEtaleDerivedTensor B _ hA (schemeSpace (projectiveSpaceSiteObj B _ hA n hP))).obj
            M).obj (projectiveSpaceSiteTwist B hA n hP d))))) :
    (smallEtaleRingedSite B _ hA (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)).1
      (schemeSpace (projectiveSpaceSiteObj B _ hA n hP)).2).IsPseudoCoherent M := by
  refine isPseudoCoherent_of_smallEtaleDerivedModulePullback_iso (projModelSpaceIso B hA n hP) M ?_
  refine isPseudoCoherent_of_isPseudoCoherent_twist_projModel B hA n
    ((smallEtaleDerivedModulePullback B _ hA (projModelSpaceIso B hA n hP).hom).obj M)
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ M hM) fun d => ?_
  have h₁ := (h5 d).ofIso ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).mapIso
    (nonempty_derivedModulePushforward_projModelSpaceIso_iso B hA n hP _).some.symm)
  have h₂ := isPseudoCoherent_sections_pushforward_projModel_of_iso B hA n h₁
    (nonempty_smallEtaleDerivedModulePullback_projModelSpaceIso_tensor_iso B hA n hP M
      (projectiveSpaceSiteTwist B hA n hP d)).some
  exact isPseudoCoherent_sections_pushforward_projModel_of_iso B hA n h₂
    (((smallEtaleDerivedTensor B _ hA (representedSpace (projModelSiteObj B hA n))).obj
      ((smallEtaleDerivedModulePullback B _ hA (projModelSpaceIso B hA n hP).hom).obj M)).mapIso
      (nonempty_smallEtaleDerivedModulePullback_projectiveSpaceSiteTwist_iso B hA n hP d).some)

end Model

end AlgebraicGeometry.Space

end
