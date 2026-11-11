module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.ModuleEquivalences
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.EquivalenceOfIso
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.AffineTensor

/-!
# Gabriel–Rosenberg reconstruction for affine schemes

Let `X` and `Y` be affine schemes and let `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` be an equivalence of
their categories of quasi-coherent modules.  Then there are an isomorphism of schemes
`f : Y ≅ X` and an invertible sheaf `L` of `𝒪_Y`-modules such that `F` is inverse image along
`f` followed by `- ⊗_{𝒪_Y} L`.  The same statement is also recorded with the invertible object
read as a `Γ(Y, ⊤)`-module.

## Main definitions

* `AlgebraicGeometry.affineQuasicoherentModulesEquiv` — for `X` affine, the equivalence
  `ModuleCat Γ(X, ⊤) ≌ QCoh(𝒪_X)` given by the tilde construction on `Spec Γ(X, ⊤)` and
  transport along `X.isoSpec`.
* `AlgebraicGeometry.schemeIsoOfΓRingEquiv` — the isomorphism of affine schemes attached to an
  isomorphism of their rings of global sections.
* `AlgebraicGeometry.affineTensorFunctor` — tensoring with a `Γ(Y, ⊤)`-module, read as an
  endofunctor of `QCoh(𝒪_Y)` through `AlgebraicGeometry.affineQuasicoherentModulesEquiv`.
* `AlgebraicGeometry.pullbackTensorFunctor` — inverse image of a quasi-coherent module along a
  morphism of schemes, tensored with a fixed sheaf of modules on the source.
* `AlgebraicGeometry.tildeTensorFunctorIso` — the isomorphism of functors
  `(- ⊗_R L₀)^~ ≅ L₀^~ ⊗_{𝒪_{Spec R}} (-)^~`.
* `AlgebraicGeometry.tensorLeftFunctorCompPullback` — the isomorphism of functors
  `f^*(Λ ⊗ -) ≅ f^*Λ ⊗ f^*(-)` for a fixed sheaf of modules `Λ`.

## Main results

* `AlgebraicGeometry.exists_schemeIso_invertibleSheaf_of_quasicoherentEquivalence` — an
  equivalence of the categories of quasi-coherent modules of two affine schemes is inverse image
  along an isomorphism of schemes followed by tensoring with an invertible sheaf of
  `𝒪_Y`-modules.
* `AlgebraicGeometry.exists_schemeIso_invertible_of_quasicoherentEquivalence` — the same, with
  the invertible object a `Γ(Y, ⊤)`-module and the tensoring read on `ModuleCat Γ(Y, ⊤)`.
* `AlgebraicGeometry.isInvertible_tilde` — the associated sheaf of an invertible module is an
  invertible sheaf.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 56.6.1 (Tag 0GP0)](https://stacks.math.columbia.edu/tag/0GP0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry

/-- **For an affine scheme `X`, modules over `Γ(X, ⊤)` are the quasi-coherent
`𝒪_X`-modules.** This is the tilde equivalence on `Spec Γ(X, ⊤)` followed by transport along
the isomorphism `X.isoSpec`. -/
noncomputable def affineQuasicoherentModulesEquiv (X : Scheme.{u}) [IsAffine X] :
    ModuleCat.{u} Γ(X, ⊤) ≌ (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  tildeEquiv.trans (quasicoherentModulesEquivOfSchemeIso X.isoSpec).symm

/-- Forgetting quasi-coherence, the affine comparison is the tilde functor followed by
restriction along `X.isoSpec.hom`. -/
lemma affineQuasicoherentModulesEquiv_functor_comp_ι (X : Scheme.{u}) [IsAffine X] :
    (affineQuasicoherentModulesEquiv X).functor ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) =
      tilde.functor Γ(X, ⊤) ⋙
        Scheme.Modules.restrictFunctor (f := X.isoSpec.hom) := rfl

/-- Forgetting quasi-coherence, the affine comparison is the tilde functor followed by inverse
image along `X.isoSpec.hom`. -/
noncomputable def affineQuasicoherentModulesEquivCompι (X : Scheme.{u}) [IsAffine X] :
    (affineQuasicoherentModulesEquiv X).functor ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ≅
      tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.pullback X.isoSpec.hom :=
  eqToIso (affineQuasicoherentModulesEquiv_functor_comp_ι X) ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.hom)

/-- Forgetting quasi-coherence, the inverse of the equivalence attached to an isomorphism of
schemes `f : Y ≅ X` is restriction along `f.hom`. -/
lemma quasicoherentModulesEquivOfSchemeIso_symm_functor_comp_ι {X Y : Scheme.{u}} (f : Y ≅ X) :
    (quasicoherentModulesEquivOfSchemeIso f).symm.functor ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) =
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Scheme.Modules.restrictFunctor (f := f.hom) := rfl

/-- Forgetting quasi-coherence, the inverse of the equivalence attached to an isomorphism of
schemes `f : Y ≅ X` is inverse image along `f.hom`. -/
noncomputable def quasicoherentPullbackIsoCompι {X Y : Scheme.{u}} (f : Y ≅ X) :
    (quasicoherentModulesEquivOfSchemeIso f).symm.functor ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Scheme.Modules.pullback f.hom :=
  eqToIso (quasicoherentModulesEquivOfSchemeIso_symm_functor_comp_ι f) ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback f.hom)

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

/-- An isomorphism of the rings of global sections, read as an isomorphism in `CommRingCat`. -/
@[simps]
noncomputable def ΓIsoOfRingEquiv (e : Γ(X, ⊤) ≃+* Γ(Y, ⊤)) : Γ(X, ⊤) ≅ Γ(Y, ⊤) where
  hom := CommRingCat.ofHom (e : Γ(X, ⊤) →+* Γ(Y, ⊤))
  inv := CommRingCat.ofHom (e.symm : Γ(Y, ⊤) →+* Γ(X, ⊤))
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

/-- **An isomorphism of the rings of global sections of two affine schemes induces an
isomorphism of the schemes**, namely `Y ≅ Spec Γ(Y, ⊤) ≅ Spec Γ(X, ⊤) ≅ X`. -/
noncomputable def schemeIsoOfΓRingEquiv (e : Γ(X, ⊤) ≃+* Γ(Y, ⊤)) : Y ≅ X :=
  Y.isoSpec ≪≫ asIso (Spec.map (ΓIsoOfRingEquiv e).hom) ≪≫ X.isoSpec.symm

/-- `AlgebraicGeometry.schemeIsoOfΓRingEquiv` is, after the two comparisons with spectra, the
morphism of spectra induced by the ring isomorphism. -/
lemma schemeIsoOfΓRingEquiv_hom_comp (e : Γ(X, ⊤) ≃+* Γ(Y, ⊤)) :
    (schemeIsoOfΓRingEquiv e).hom ≫ X.isoSpec.hom =
      Y.isoSpec.hom ≫ Spec.map (ΓIsoOfRingEquiv e).hom := by
  simp [schemeIsoOfΓRingEquiv]

open Stacks.Descent in
/-- **Extension of scalars along a ring isomorphism is inverse image along the induced
isomorphism of affine schemes**, on modules rather than on quasi-coherent modules.  The
comparison is `Stacks.Descent.extendScalarsCompTildeIso` on `Spec`, conjugated by the two
comparisons of the affine equivalence with the tilde functor. -/
noncomputable def pullbackCompAffineQuasicoherentEquiv (e : Γ(X, ⊤) ≃+* Γ(Y, ⊤)) :
    ((affineQuasicoherentModulesEquiv X).functor ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)) ⋙
        Scheme.Modules.pullback (schemeIsoOfΓRingEquiv e).hom ≅
      ModuleCat.extendScalars (ΓIsoOfRingEquiv e).hom.hom ⋙
        (affineQuasicoherentModulesEquiv Y).functor ⋙
          ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) :=
  Functor.isoWhiskerRight (affineQuasicoherentModulesEquivCompι X)
      (Scheme.Modules.pullback (schemeIsoOfΓRingEquiv e).hom) ≪≫
    Functor.isoWhiskerLeft (tilde.functor Γ(X, ⊤))
      (Scheme.Modules.pullbackComp (schemeIsoOfΓRingEquiv e).hom X.isoSpec.hom) ≪≫
    Functor.isoWhiskerLeft (tilde.functor Γ(X, ⊤))
      (Scheme.Modules.pullbackCongr (schemeIsoOfΓRingEquiv_hom_comp e)) ≪≫
    Functor.isoWhiskerLeft (tilde.functor Γ(X, ⊤))
      (Scheme.Modules.pullbackComp Y.isoSpec.hom (Spec.map (ΓIsoOfRingEquiv e).hom)).symm ≪≫
    Functor.isoWhiskerRight (extendScalarsCompTildeIso (ΓIsoOfRingEquiv e).hom).symm
      (Scheme.Modules.pullback Y.isoSpec.hom) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars (ΓIsoOfRingEquiv e).hom.hom)
      (affineQuasicoherentModulesEquivCompι Y).symm

/-- **Extension of scalars along a ring isomorphism is inverse image of quasi-coherent modules
along the induced isomorphism of affine schemes.**  This is
`AlgebraicGeometry.pullbackCompAffineQuasicoherentEquiv` with quasi-coherence restored. -/
noncomputable def extendScalarsCompAffineQuasicoherentEquiv (e : Γ(X, ⊤) ≃+* Γ(Y, ⊤)) :
    (affineQuasicoherentModulesEquiv X).functor ⋙
        (quasicoherentModulesEquivOfSchemeIso (schemeIsoOfΓRingEquiv e)).symm.functor ≅
      ModuleCat.extendScalars (ΓIsoOfRingEquiv e).hom.hom ⋙
        (affineQuasicoherentModulesEquiv Y).functor :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (affineQuasicoherentModulesEquiv X).functor
        (quasicoherentPullbackIsoCompι (schemeIsoOfΓRingEquiv e)) ≪≫
      pullbackCompAffineQuasicoherentEquiv e)

/-- **Tensoring with a `Γ(Y, ⊤)`-module `L`, read as an endofunctor of the quasi-coherent
`𝒪_Y`-modules** through `AlgebraicGeometry.affineQuasicoherentModulesEquiv`. -/
noncomputable def affineTensorFunctor (Y : Scheme.{u}) [IsAffine Y] (L : ModuleCat.{u} Γ(Y, ⊤)) :
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
  (affineQuasicoherentModulesEquiv Y).inverse ⋙
    (tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L ⋙
      (affineQuasicoherentModulesEquiv Y).functor

/-- If `X` and `Y` are affine schemes and
`F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` is an equivalence, then there are an isomorphism of schemes
`f : Y ≅ X` and an invertible `Γ(Y, ⊤)`-module `L` such that `F` is inverse image along `f`
followed by tensoring with `L`. -/
theorem exists_schemeIso_invertible_of_quasicoherentEquivalence
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) [F.IsEquivalence] :
    ∃ (f : Y ≅ X) (L : ModuleCat.{u} Γ(Y, ⊤)), Module.Invertible Γ(Y, ⊤) L ∧
      Nonempty (F ≅ (quasicoherentModulesEquivOfSchemeIso f).symm.functor ⋙
        affineTensorFunctor Y L) := by
  have hE : ((affineQuasicoherentModulesEquiv X).functor ⋙ F ⋙
      (affineQuasicoherentModulesEquiv Y).inverse).IsEquivalence := inferInstance
  obtain ⟨e, L, hL, ⟨i⟩⟩ :=
    ModuleCat.exists_ringEquiv_invertible_iso_extensionTensorFunctor Γ(X, ⊤) Γ(Y, ⊤)
      ((affineQuasicoherentModulesEquiv X).functor ⋙ F ⋙
        (affineQuasicoherentModulesEquiv Y).inverse)
  refine ⟨schemeIsoOfΓRingEquiv e, L, hL, ⟨?_⟩⟩
  have h1 : (affineQuasicoherentModulesEquiv X).functor ⋙ F ≅
      ((affineQuasicoherentModulesEquiv X).functor ⋙ F ⋙
          (affineQuasicoherentModulesEquiv Y).inverse) ⋙
        (affineQuasicoherentModulesEquiv Y).functor :=
    (Functor.isoWhiskerLeft ((affineQuasicoherentModulesEquiv X).functor ⋙ F)
        (affineQuasicoherentModulesEquiv Y).counitIso).symm
  have h2 : ((affineQuasicoherentModulesEquiv X).functor ⋙ F ⋙
        (affineQuasicoherentModulesEquiv Y).inverse) ⋙
        (affineQuasicoherentModulesEquiv Y).functor ≅
      (ModuleCat.extendScalars (ΓIsoOfRingEquiv e).hom.hom ⋙
        (tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L) ⋙
          (affineQuasicoherentModulesEquiv Y).functor :=
    Functor.isoWhiskerRight i (affineQuasicoherentModulesEquiv Y).functor
  have h3 : (ModuleCat.extendScalars (ΓIsoOfRingEquiv e).hom.hom ⋙
        (tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L) ⋙
        (affineQuasicoherentModulesEquiv Y).functor ≅
      (ModuleCat.extendScalars (ΓIsoOfRingEquiv e).hom.hom ⋙
        (affineQuasicoherentModulesEquiv Y).functor) ⋙
        (affineQuasicoherentModulesEquiv Y).inverse ⋙
          (tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L ⋙
            (affineQuasicoherentModulesEquiv Y).functor :=
    Functor.associator (ModuleCat.extendScalars (ΓIsoOfRingEquiv e).hom.hom)
        ((tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L)
        (affineQuasicoherentModulesEquiv Y).functor ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars (ΓIsoOfRingEquiv e).hom.hom)
        ((Functor.leftUnitor ((tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L ⋙
              (affineQuasicoherentModulesEquiv Y).functor)).symm ≪≫
          Functor.isoWhiskerRight (affineQuasicoherentModulesEquiv Y).unitIso
            ((tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L ⋙
              (affineQuasicoherentModulesEquiv Y).functor) ≪≫
          Functor.associator (affineQuasicoherentModulesEquiv Y).functor
            (affineQuasicoherentModulesEquiv Y).inverse
            ((tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L ⋙
              (affineQuasicoherentModulesEquiv Y).functor)) ≪≫
      (Functor.associator (ModuleCat.extendScalars (ΓIsoOfRingEquiv e).hom.hom)
        (affineQuasicoherentModulesEquiv Y).functor
        ((affineQuasicoherentModulesEquiv Y).inverse ⋙
          (tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L ⋙
            (affineQuasicoherentModulesEquiv Y).functor)).symm
  have h4 : (ModuleCat.extendScalars (ΓIsoOfRingEquiv e).hom.hom ⋙
        (affineQuasicoherentModulesEquiv Y).functor) ⋙
        (affineQuasicoherentModulesEquiv Y).inverse ⋙
          (tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L ⋙
            (affineQuasicoherentModulesEquiv Y).functor ≅
      (affineQuasicoherentModulesEquiv X).functor ⋙
        (quasicoherentModulesEquivOfSchemeIso (schemeIsoOfΓRingEquiv e)).symm.functor ⋙
          affineTensorFunctor Y L :=
    Functor.isoWhiskerRight (extendScalarsCompAffineQuasicoherentEquiv e).symm
      ((affineQuasicoherentModulesEquiv Y).inverse ⋙
        (tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L ⋙
          (affineQuasicoherentModulesEquiv Y).functor)
  exact ((affineQuasicoherentModulesEquiv X).invFunIdAssoc F).symm ≪≫
    Functor.isoWhiskerLeft (affineQuasicoherentModulesEquiv X).inverse
      (h1 ≪≫ h2 ≪≫ h3 ≪≫ h4) ≪≫
    (affineQuasicoherentModulesEquiv X).invFunIdAssoc _

section SheafLevel

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-- Inverse image along a morphism of ringed spaces `f : S ⟶ T` turns tensoring with a sheaf of
`𝒪_T`-modules `Λ` into tensoring with `f^*Λ`: `f^*(Λ ⊗_{𝒪_T} -) ≅ f^*Λ ⊗_{𝒪_S} f^*(-)`,
naturally in the second argument, with components those of
`Stacks.RingedSpace.comparisonBifunctorIso`. -/
noncomputable def tensorLeftFunctorCompPullback {S T : RingedSpace.{u, u}} (f : S ⟶ T)
    (hS : Presheaf.IsSheaf (Opens.grothendieckTopology S.carrier)
      (structureRingPresheaf S.presheaf))
    (hT : Presheaf.IsSheaf (Opens.grothendieckTopology T.carrier)
      (structureRingPresheaf T.presheaf))
    (Λ : SheafOfModules.{u} (structureSheaf T.presheaf hT)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨T.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ T.presheaf (forget₂ CommRingCat RingCat)
          hT⟩).obj Λ ⋙ Stacks.RingedSpace.pullbackFunctor f ≅
      Stacks.RingedSpace.pullbackFunctor f ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
            (forget₂ CommRingCat RingCat) hS⟩).obj
          ((Stacks.RingedSpace.pullbackFunctor f).obj Λ) :=
  NatIso.ofComponents (fun N => (Stacks.RingedSpace.comparisonBifunctorIso f).app (Λ, N)) (by
    intro N N' φ
    have h := (Stacks.RingedSpace.comparisonBifunctorIso f).hom.naturality
      (X := (Λ, N)) (Y := (Λ, N')) (𝟙 Λ, φ)
    have hT' := (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u}
        ⟨T.presheaf, T.IsSheaf⟩ (𝟙 Λ) φ).trans
      (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map.{u, u, u, u, u}
        ⟨T.presheaf, T.IsSheaf⟩ Λ φ).symm
    have hS' := (congrArg (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u,
        u, u} ⟨S.presheaf, S.IsSheaf⟩)).map
        (Prod.ext ((Stacks.RingedSpace.pullbackFunctor f).map_id Λ) rfl :
          ((Stacks.RingedSpace.pullbackFunctor f).prod (Stacks.RingedSpace.pullbackFunctor f)).map
            ((𝟙 Λ, φ) : (Λ, N) ⟶ (Λ, N')) =
            (𝟙 ((Stacks.RingedSpace.pullbackFunctor f).obj Λ),
              (Stacks.RingedSpace.pullbackFunctor f).map φ))).trans
      ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u}
          ⟨S.presheaf, S.IsSheaf⟩ (𝟙 ((Stacks.RingedSpace.pullbackFunctor f).obj Λ))
          ((Stacks.RingedSpace.pullbackFunctor f).map φ)).trans
        (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map.{u, u, u, u, u}
          ⟨S.presheaf, S.IsSheaf⟩ ((Stacks.RingedSpace.pullbackFunctor f).obj Λ)
          ((Stacks.RingedSpace.pullbackFunctor f).map φ)).symm)
    exact (congrArg (fun t => (Stacks.RingedSpace.pullbackFunctor f).map t ≫
        (Stacks.RingedSpace.comparisonBifunctorIso f).hom.app (Λ, N')) hT').symm.trans
      (h.trans (congrArg (fun t => (Stacks.RingedSpace.comparisonBifunctorIso f).hom.app (Λ, N) ≫
        t) hS')))

/-- On `Spec R`, the associated sheaf of `- ⊗_R L₀` is the tensor product of sheaves with
`L₀^~`: `(- ⊗_R L₀)^~ ≅ L₀^~ ⊗_{𝒪_{Spec R}} (-)^~`, with components the braiding of
`ModuleCat R` followed by `AlgebraicGeometry.tildeTensorIso`. -/
noncomputable def tildeTensorFunctorIso (R : CommRingCat.{u}) (L₀ : ModuleCat.{u} R) :
    (tensoringRight (ModuleCat.{u} R)).obj L₀ ⋙ tilde.functor R ≅
      tilde.functor R ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(Spec R).presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Spec R).presheaf
          (forget₂ CommRingCat RingCat) (isSheaf_specStructureRingPresheaf R)⟩).obj
        (tilde L₀) :=
  NatIso.ofComponents
    (fun M => (tilde.functor R).mapIso (β_ M L₀) ≪≫ tildeTensorIso R L₀ M) (by
      intro M M' φ
      have hb : φ ▷ L₀ ≫ (β_ M' L₀).hom = (β_ M L₀).hom ≫ L₀ ◁ φ :=
        BraidedCategory.braiding_naturality_left φ L₀
      have hn : tilde.map (L₀ ◁ φ) ≫ (tildeTensorIso R L₀ M').hom =
          (tildeTensorIso R L₀ M).hom ≫ tildeTensorSheafMap R (𝟙 L₀) φ := by
        rw [← MonoidalCategory.id_tensorHom]
        exact tildeTensorIso_natural R (𝟙 L₀) φ
      have hid : tildeTensorSheafMap R (𝟙 L₀) φ =
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(Spec R).presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Spec R).presheaf
              (forget₂ CommRingCat RingCat) (isSheaf_specStructureRingPresheaf R)⟩).obj
            (tilde L₀)).map (tilde.map φ) := by
        dsimp only [tildeTensorSheafMap]
        rw [tilde.map_id]
        rfl
      have key : tilde.map (φ ▷ L₀) ≫
            (tilde.map (β_ M' L₀).hom ≫ (tildeTensorIso R L₀ M').hom) =
          (tilde.map (β_ M L₀).hom ≫ (tildeTensorIso R L₀ M).hom) ≫
            tildeTensorSheafMap R (𝟙 L₀) φ := by
        rw [← Category.assoc, ← tilde.map_comp, hb, tilde.map_comp, Category.assoc, hn]
        exact (Category.assoc _ _ _).symm
      exact key.trans (congrArg (fun t => (tilde.map (β_ M L₀).hom ≫
        (tildeTensorIso R L₀ M).hom) ≫ t) hid))

/-- **The associated sheaf of an invertible module is an invertible sheaf.**  If `L₀` is an
invertible `R`-module then `L₀^~` is an invertible sheaf of `𝒪_{Spec R}`-modules in the sense of
Tag 01CS. -/
theorem isInvertible_tilde (R : CommRingCat.{u}) (L₀ : ModuleCat.{u} R)
    [Module.Invertible R L₀] :
    Stacks.SheafOfModules.IsInvertible (Spec R).presheaf
      (isSheaf_specStructureRingPresheaf R) (tilde L₀) := by
  refine (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).mpr
    ⟨tilde (ModuleCat.of R (Module.Dual R L₀)), ⟨?_⟩⟩
  refine (tildeTensorIso R L₀ (ModuleCat.of R (Module.Dual R L₀))).symm ≪≫ ?_
  exact (tilde.functor R).mapIso
    (((TensorProduct.comm R L₀ (Module.Dual R L₀)).trans
      (Module.Invertible.linearEquiv R L₀)).toModuleIso)

/-- `AlgebraicGeometry.affineQuasicoherentModulesEquivCompι` with the inverse image typed as the
module pullback of the underlying morphism of ringed spaces. -/
noncomputable def affineQuasicoherentModulesEquivCompModulePullback (Y : Scheme.{u})
    [IsAffine Y] :
    (affineQuasicoherentModulesEquiv Y).functor ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ≅
      tilde.functor Γ(Y, ⊤) ⋙
        Stacks.RingedSpace.pullbackFunctor Y.isoSpec.hom.toLRSHom.toShHom :=
  affineQuasicoherentModulesEquivCompι Y

/-- **Tensoring with a `Γ(Y, ⊤)`-module is tensoring with the corresponding invertible sheaf.**
Forgetting quasi-coherence, `AlgebraicGeometry.affineTensorFunctor Y L₀` is
`- ⊗_{𝒪_Y} L`, where `L` is the inverse image along `Y ≅ Spec Γ(Y, ⊤)` of the associated sheaf
of `L₀`. -/
noncomputable def affineTensorFunctorCompι (Y : Scheme.{u}) [IsAffine Y]
    (L₀ : ModuleCat.{u} Γ(Y, ⊤)) :
    affineTensorFunctor Y L₀ ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
            (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).obj
          ((Stacks.RingedSpace.pullbackFunctor
            Y.isoSpec.hom.toLRSHom.toShHom).obj (tilde L₀)) :=
  let E := affineQuasicoherentModulesEquiv Y
  let incl := ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
  let til := tilde.functor Γ(Y, ⊤)
  let pb := Stacks.RingedSpace.pullbackFunctor Y.isoSpec.hom.toLRSHom.toShHom
  let tr := (tensoringRight (ModuleCat.{u} Γ(Y, ⊤))).obj L₀
  let tenSpec := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(Spec Γ(Y, ⊤)).presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Spec Γ(Y, ⊤)).presheaf
      (forget₂ CommRingCat RingCat) (isSheaf_specStructureRingPresheaf Γ(Y, ⊤))⟩).obj (tilde L₀)
  let tenY := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
      (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).obj (pb.obj (tilde L₀))
  let inner : (tr ⋙ E.functor) ⋙ incl ≅ E.functor ⋙ (incl ⋙ tenY) :=
    Functor.associator tr E.functor incl ≪≫
    Functor.isoWhiskerLeft tr (affineQuasicoherentModulesEquivCompModulePullback Y) ≪≫
    (Functor.associator tr til pb).symm ≪≫
    Functor.isoWhiskerRight (tildeTensorFunctorIso Γ(Y, ⊤) L₀) pb ≪≫
    Functor.associator til tenSpec pb ≪≫
    Functor.isoWhiskerLeft til (tensorLeftFunctorCompPullback
      Y.isoSpec.hom.toLRSHom.toShHom Y.ringCatSheaf.2
      (isSheaf_specStructureRingPresheaf Γ(Y, ⊤)) (tilde L₀)) ≪≫
    (Functor.associator til pb tenY).symm ≪≫
    Functor.isoWhiskerRight (affineQuasicoherentModulesEquivCompModulePullback Y).symm tenY ≪≫
    Functor.associator E.functor incl tenY
  Functor.associator E.inverse (tr ⋙ E.functor) incl ≪≫
  Functor.isoWhiskerLeft E.inverse inner ≪≫
  (Functor.associator E.inverse E.functor (incl ⋙ tenY)).symm ≪≫
  Functor.isoWhiskerRight E.counitIso (incl ⋙ tenY) ≪≫
  Functor.leftUnitor (incl ⋙ tenY)

/-- **Inverse image of a quasi-coherent module along `f`, tensored with a fixed sheaf `L` of
`𝒪_Y`-modules**, as a functor into all `𝒪_Y`-modules. -/
noncomputable def pullbackTensorFunctor {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : SheafOfModules.{u} Y.ringCatSheaf) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} Y.ringCatSheaf :=
  ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
    Scheme.Modules.pullback f ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
          (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).obj L

/-- If `X` and `Y` are affine schemes and `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` is an equivalence, then there
are an isomorphism of schemes `f : Y ≅ X` and an invertible sheaf `L` of `𝒪_Y`-modules such
that `F` is inverse image along `f` followed by `- ⊗_{𝒪_Y} L`. -/
theorem exists_schemeIso_invertibleSheaf_of_quasicoherentEquivalence
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) [F.IsEquivalence] :
    ∃ (f : Y ≅ X) (L : SheafOfModules.{u} Y.ringCatSheaf),
      Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L ∧
        Nonempty (F ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ≅
          pullbackTensorFunctor f.hom L) := by
  obtain ⟨f, L₀, hL₀, ⟨i⟩⟩ := exists_schemeIso_invertible_of_quasicoherentEquivalence F
  have : Module.Invertible Γ(Y, ⊤) L₀ := hL₀
  refine ⟨f, (Stacks.RingedSpace.pullbackFunctor
    Y.isoSpec.hom.toLRSHom.toShHom).obj (tilde L₀), ?_, ⟨?_⟩⟩
  · exact @Stacks.RingedSpace.modulePullback_isInvertible _ _
      Y.isoSpec.hom.toLRSHom.toShHom (tilde L₀) (isInvertible_tilde _ _)
  · exact Functor.isoWhiskerRight i
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (quasicoherentModulesEquivOfSchemeIso f).symm.functor
        (affineTensorFunctorCompι Y L₀) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (quasicoherentPullbackIsoCompι f) _ ≪≫
      Functor.associator _ _ _

end SheafLevel

end AlgebraicGeometry

end
