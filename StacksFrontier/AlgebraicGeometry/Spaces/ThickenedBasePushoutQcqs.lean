module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingInverseImageKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverAffineFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraExtensionPushoutQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsTerminalBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheafMapSurjective
public import StacksFrontier.Deformation.AlgebraExtension.PushoutSiteEquivalence
public import StacksFrontier.Deformation.ToposThickening.KernelPushoutAlgebraExtension

/-!
# Pushout of solutions over a thickened base, on a qcqs algebraic space

Let `f : X ⟶ D` be a morphism of algebraic spaces with `X` quasi-compact and quasi-separated,
`i : D ⟶ D'` a first order thickening, and `S` a square-zero extension problem of the small
étale ringed topoi over `f` whose thickened base is `i⁻¹𝒪_{D'}`. This file reduces
[Stacks Project, Tag 0D3Q] for `S` to [Stacks Project, Tag 0D3P] for the composite `X ⟶ D'`, as
the source's proof does: the solutions of `S` are the extensions of `(f ≫ i)⁻¹𝒪_{D'}`-algebras
inducing the prescribed map on the base ideal.

## Main results

* `AlgebraicGeometry.Space.thickenedBaseIso`: `(f ≫ i)⁻¹𝒪_{D'} ≅ f⁻¹(i⁻¹𝒪_{D'})`, over `𝒪_X`.
* `AlgebraicGeometry.Space.isEquivalence_of_isKernelPushoutFunctor_of_injective`: pushout of
  solutions is an equivalence once `Hom(f⁻¹𝒥, ℱ) ⟶ Hom(f⁻¹𝒥, 𝒢)` is injective.

## References

* [Stacks Project, Tag 0D3Q](https://stacks.math.columbia.edu/tag/0D3Q)
* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.AlgebraExtension
open Deformation.ToposThickening
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
attribute [local instance] HasDerivedCategory.standard

/-- Sheafification of sheaves of abelian groups on the small étale site of an algebraic space,
at the universe of its rings of sections: the site is essentially small. -/
local instance smallEtaleHasSheafifyAddCommGrpCat (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u, _, _} _

/-- On the small étale site of an algebraic space, the weak equivalences of presheaves of abelian
groups at the universe of its rings of sections are the locally bijective morphisms. -/
local instance smallEtaleWEqualsLocallyBijectiveAddCommGrpCat (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (SmallEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _

/-- Products of presheaves of sets, stated directly: instance search for them times out on the
small étale site. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_ThickenedBasePushoutQcqs
    {C : Type*} [Category C] (J : Type u) : HasLimitsOfShape (Discrete J) (C ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- Products of sheaves of sets, stated directly: instance search for them times out on the
small étale site. -/
local instance (priority := high) hasLimitsOfShape_discrete_sheaf_ThickenedBasePushoutQcqs
    {C : Type*} [Category C] (T : GrothendieckTopology C) (J : Type u) :
    HasLimitsOfShape (Discrete J) (Sheaf T (Type u)) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf T (Type u))

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X D D': AlgebraicSpaces B S hS} (f : X ⟶ D) (i : D ⟶ D')

/-- **The base ring of the composite**: `(f ≫ i)⁻¹𝒪_{D'} ≅ f⁻¹𝒜` for a sheaf of rings `𝒜` on `D`
identified with `i⁻¹𝒪_{D'}`. -/
def thickenedBaseIso {𝒜 : Sheaf (SmallEtale.topology B S hS D.1) CommRingCat.{u}}
    (e : 𝒜 ≅ (smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS D').O) :
    inverseImageBase B S hS (f ≫ i) ≅ (smallEtaleInverseImageRing B S hS f).obj 𝒜 :=
  ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS f i).app
      (smallEtaleRingedTopos B S hS D').O).symm ≪≫
    (smallEtaleInverseImageRing B S hS f).mapIso e.symm

/-- If `r : 𝒜 ⟶ 𝒪_D` corresponds under `e` to the comorphism `i⁻¹𝒪_{D'} ⟶ 𝒪_D`, then
`thickenedBaseIso` followed by `f⁻¹r` and the comorphism `f⁻¹𝒪_D ⟶ 𝒪_X` is the comorphism
`(f ≫ i)⁻¹𝒪_{D'} ⟶ 𝒪_X`. -/
theorem thickenedBaseIso_hom_comp {𝒜 : Sheaf (SmallEtale.topology B S hS D.1) CommRingCat.{u}}
    (e : 𝒜 ≅ (smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS D').O)
    (r : 𝒜 ⟶ (smallEtaleRingedTopos B S hS D).O)
    (hr : e.hom ≫ (smallEtaleRingedToposHom B S hS i).fSharpInverseImage = r) :
    (thickenedBaseIso B S hS f i e).hom ≫ (smallEtaleInverseImageRing B S hS f).map r ≫
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage =
      inverseImageBaseMap B S hS (f ≫ i) := by
  have hr' : e.inv ≫ r = (smallEtaleRingedToposHom B S hS i).fSharpInverseImage := by
    rw [← hr, Iso.inv_hom_id_assoc]
  show (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS f i).inv.app _) ≫
      (smallEtaleInverseImageRing B S hS f).map e.inv) ≫ _ = _
  rw [Category.assoc, ← Category.assoc ((smallEtaleInverseImageRing B S hS f).map e.inv),
    ← Functor.map_comp, hr', ← smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage,
    ← Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app, Category.id_comp]

/-- The inverse image of a locally surjective morphism of sheaves of rings on `D` is locally
surjective, read on the underlying sheaves of (not necessarily commutative) rings. -/
theorem isLocallySurjective_inverseImage_map {𝒜 𝒜' : Sheaf (SmallEtale.topology B S hS D.1)
      CommRingCat.{u}} (r : 𝒜 ⟶ 𝒜')
    (hr : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS D.1) r.hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((smallEtaleInverseImageRing B S hS f).map r)).hom := by
  have : Epi ((sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).map r) :=
    (Sheaf.isLocallySurjective_iff_epi _).1
      ((Presheaf.isLocallySurjective_iff_whisker_forget _ r.hom).1 hr)
  have := Functor.preservesEpimorphisms_of_adjunction
    (smallEtaleRingedToposHom B S hS f).toToposHom.adj
  have e := Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap
    (SmallEtale.topology B S hS X.1) (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage r
  set ψ := (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
    ((smallEtaleInverseImageRing B S hS f).map r)
  have : Epi ψ := by
    show Epi ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
      (Stacks.Sheaves.ToposPullback.pullbackCommRingSheafMap _
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage r))
    rw [e]
    exact Functor.map_epi _ _
  have := (Sheaf.isLocallySurjective_iff_epi ψ).2 inferInstance
  exact ⟨fun {_V} y => Presheaf.imageSieve_mem (SmallEtale.topology B S hS X.1) ψ.hom y⟩

/-- A quasi-coherent module in degree zero lies in `D_QCoh(𝒪_X)`. -/
theorem qcohDerivedProp_singleFunctor_obj (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    qcohDerivedProp B S hS X ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
      M) := by
  intro n
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (DerivedCategory.isZero_of_isGE (C := Modules.{u, u} B S hS X.1 X.2)
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj M) 0 n h)
  · exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (Modules.{u, u} B S hS X.1 X.2) 0).app M).symm hM
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (DerivedCategory.isZero_of_isLE (C := Modules.{u, u} B S hS X.1 X.2)
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj M) 0 n h)

/-- **Maps out of a quasi-coherent module do not see a map inverted by `DQ_X`**: if
`DQ_X(ℱ) ⟶ DQ_X(𝒢)` is an isomorphism, post-composition with `φ : ℱ ⟶ 𝒢` is bijective on maps
out of a quasi-coherent module. -/
theorem bijective_comp_of_isIso_coherator_map (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXc : IsQuasiCompactSpace B S hS X.1) (hXs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (hDQ : letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
      IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)))
    {Q : Modules.{u, u} B S hS X.1 X.2} (hQ : Q.IsQuasicoherentOnSite) :
    Function.Bijective (fun g : Q ⟶ M => g ≫ φ) := by
  let := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
  let L := DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0
  have := hDQ
  exact (Functor.FullyFaithful.ofFullyFaithful L).bijective_comp_of_arrowIso
    φ (L.map φ) (Iso.refl _)
    ((qcohDerivedProp B S hS X).bijective_comp_of_isIso_rightAdjoint_map
      (qcohDerivedProp_singleFunctor_obj B S hS Q hQ) (L.map φ))

/-- **Maps out of an inverse image are maps out of the pullback**: for an `𝒪_D`-module `𝒦` and an
`𝒪_X`-module `ℳ`, `Hom_{f⁻¹𝒪_D}(f⁻¹𝒦, ℳ) ≅ Hom_{𝒪_D}(𝒦, f_*ℳ) ≅ Hom_{𝒪_X}(f^*𝒦, ℳ)`. -/
def inverseImageHomEquiv (𝒦 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D).O))
    (M : Modules.{u, u} B S hS X.1 X.2) :
    ((Stacks.Sheaves.RingedToposModules.inverseImageModules
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D).O)).obj 𝒦 ⟶
      (SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).obj M) ≃
      ((modulePullback B S hS f).obj 𝒦 ⟶ M) :=
  ((Stacks.Sheaves.RingedToposModules.inverseImageAdjDirectImageModules
      (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D).O)).homEquiv 𝒦
    ((SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).obj M)).trans
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).homEquiv 𝒦 M).symm

/-- `inverseImageHomEquiv` is natural in the target module: it commutes with post-composition by
a morphism `φ : ℳ ⟶ ℳ'` of `𝒪_X`-modules. -/
theorem inverseImageHomEquiv_comp (𝒦 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D).O))
    {M M' : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ M')
    (d : (Stacks.Sheaves.RingedToposModules.inverseImageModules
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D).O)).obj 𝒦 ⟶
      (SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).obj M) :
    inverseImageHomEquiv B S hS f 𝒦 M' (d ≫ (SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map φ) =
      inverseImageHomEquiv B S hS f 𝒦 M d ≫ φ :=
  (congrArg ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).homEquiv 𝒦 M').symm
    ((Stacks.Sheaves.RingedToposModules.inverseImageAdjDirectImageModules
      (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS D).O)).homEquiv_naturality_right
        d _)).trans
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).homEquiv_naturality_right_symm _ φ)

/-- **Maps out of an inverse image of a quasi-coherent module do not see a map inverted by
`DQ_X`**: if `𝒦` is a quasi-coherent `𝒪_D`-module and `DQ_X(ℱ) ⟶ DQ_X(𝒢)` is an isomorphism, then
post-composition with `φ : ℱ ⟶ 𝒢` is injective on the maps `f⁻¹𝒦 ⟶ ℱ` of `f⁻¹𝒪_D`-modules. -/
theorem inverseImage_comp_injective_of_isIso_coherator_map (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXc : IsQuasiCompactSpace B S hS X.1) (hXs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (hDQ : letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
      IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)))
    (𝒦 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D).O))
    (h𝒦 : 𝒦.IsQuasicoherentOnSite)
    (e₁ e₂ : (Stacks.Sheaves.RingedToposModules.inverseImageModules
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS D).O)).obj 𝒦 ⟶
      (SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).obj M)
    (h : e₁ ≫ (SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map φ =
        e₂ ≫ (SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map φ) :
    e₁ = e₂ := by
  have h2 : inverseImageHomEquiv B S hS f 𝒦 M e₁ ≫ φ =
      inverseImageHomEquiv B S hS f 𝒦 M e₂ ≫ φ :=
    (inverseImageHomEquiv_comp B S hS f 𝒦 φ e₁).symm.trans
      ((congrArg (inverseImageHomEquiv B S hS f 𝒦 N) h).trans
        (inverseImageHomEquiv_comp B S hS f 𝒦 φ e₂))
  exact (inverseImageHomEquiv B S hS f 𝒦 M).injective
    ((bijective_comp_of_isIso_coherator_map B S hS hZ hXc hXs φ hDQ
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f 𝒦 h𝒦)).1 h2)

/-- **[Stacks Project, Tag 0D3Q], with the injectivity of `Hom(f⁻¹𝒥, ℱ) ⟶ Hom(f⁻¹𝒥, 𝒢)` as an
input.** Pushout of solutions over the thickened base `i⁻¹𝒪_{D'}` is an equivalence when
`DQ_X(ℱ) ⟶ DQ_X(𝒢)` is an isomorphism and post-composition with `φ` is injective on the maps
from the base ideal: by [Stacks Project, Tag 0D3P] for `X ⟶ D'`, applied to the pushout functor
`AlgebraExtension.sitePushoutFunctor` of all extensions, restricted to the solutions. -/
theorem isEquivalence_of_isKernelPushoutFunctor_of_injective
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXc : IsQuasiCompactSpace B S hS X.1) (hXs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (P : RingedToposExtensionProblem (smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedTopos B S hS D))
    (hPf : P.f = smallEtaleRingedToposHom B S hS f)
    (eBase : P.baseExtension ≅
      (smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS D').O)
    (heBase : eBase.hom ≫ (smallEtaleRingedToposHom B S hS i).fSharpInverseImage =
      P.baseReduction)
    {N : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    (φ : P.G ⟶ N)
    {FT : P.CompatibleFirstOrderThickening ⥤
      (RingedToposExtensionProblem.changeKernel P φ).CompatibleFirstOrderThickening}
    (hFT : RingedToposExtensionProblem.IsKernelPushoutFunctor.{u, u + 1, u, u, u + 1, u}
      (S := P) φ FT)
    (hDQ : letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
      IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)))
    (hinj : ∀ d₁ d₂ : P.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose
        (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
          P.f.fSharpInverseImage)).obj P.G,
      d₁ ≫ (SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map P.f.fSharpInverseImage)).map φ =
        d₂ ≫ (SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map P.f.fSharpInverseImage)).map φ →
        d₁ = d₂) :
    FT.IsEquivalence := by
  cases P with
  | mk Pf baseExt red hred hsq I G incl c hzero huniv =>
  subst hPf
  let a₁ := inverseImageBaseMap B S hS (f ≫ i)
  let hF := isPushoutFunctor_sitePushoutFunctor (smallEtaleModelTopology B S hS X.1)
    (modelEquiv B S hS X) a₁ φ
  have : (sitePushoutFunctor (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X) a₁
      φ).IsEquivalence :=
    isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map_of_qcqs B S hS (f ≫ i) hZ hXc hXs
      φ hF hDQ
  have := isLocallySurjective_inverseImage_map B S hS f red hred
  obtain ⟨j, hj, -⟩ := hFT
  have : (SmallEtale.topology B S hS X.1).HasSheafCompose (forget CommRingCat.{u}) :=
    inferInstance
  exact RingedToposExtensionProblem.isEquivalence_of_isPushoutFunctor.{u, u + 1, u, u, u + 1, u}
    (A := inverseImageBase B S hS (f ≫ i)) (a := a₁) (N := N)
    (F := sitePushoutFunctor (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X) a₁ φ)
    (FT := FT) (X := smallEtaleRingedTopos B S hS X) (B := smallEtaleRingedTopos B S hS D)
    ⟨smallEtaleRingedToposHom B S hS f, baseExt, red, hred, hsq, I, G, incl, c, hzero, huniv⟩
    (thickenedBaseIso B S hS f i eBase) (thickenedBaseIso_hom_comp B S hS f i eBase red heBase)
    φ hF j hj hinj

end AlgebraicGeometry.Space

end
