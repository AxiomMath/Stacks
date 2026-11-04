module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Module.Injective.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineReconstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedLiftTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Étale restriction of an injective quasi-coherent module on a Noetherian affine space

Let `U` be the algebraic space represented by an affine scheme `W` with Noetherian ring of
global functions, and let `𝒥` be an injective object of `QCoh(𝒪_U)`.  For every affine algebraic
space `V` with an étale morphism `e : V ⟶ U`, the restriction `𝒥|_V` is again an injective object
of `QCoh(𝒪_V)`.

On the Zariski side this is the algebra of
`StacksFrontier/Algebra/Module/Injective/EtaleBaseChange.lean`: a quasi-coherent module on an affine
scheme is `M~` for its module of global sections, pulling `M~` back along a morphism of affine
schemes gives the module associated to the base change, and the base change of an injective
module along an étale ring map with Noetherian source is injective.  The passage between the
small étale site of a representable algebraic space and the Zariski site of the representing
scheme is `AlgebraicGeometry.Space.representedZariskiModule`, which on quasi-coherent modules is a
quasi-inverse of the equivalence of Descent, Proposition 03DX (2)
(`AlgebraicGeometry.Space.representedZariskiModuleQuasicoherentSchemeIso`) and commutes with
inverse images (`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`).

## Main results

* `AlgebraicGeometry.Space.exists_injective_iso_pullback_of_etale`: the Zariski statement.
* `AlgebraicGeometry.Space.injective_etaleModulePullback_of_isAffineSpace`: the statement on the
  small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-- **Zariski form.**  Let `f : X ⟶ Y` be an étale morphism of affine schemes with `Γ(Y, 𝒪_Y)`
Noetherian.  The pullback along `f` of an injective quasi-coherent `𝒪_Y`-module is (isomorphic
to) an injective quasi-coherent `𝒪_X`-module. -/
theorem exists_injective_iso_pullback_of_etale {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    [IsNoetherianRing Γ(Y, ⊤)] (f : X ⟶ Y) [Etale f]
    (G : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) [Injective G] :
    ∃ G' : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory, Injective G' ∧
      Nonempty ((Scheme.Modules.pullback f).obj G.obj ≅ G'.obj) := by
  let eY := affineQuasicoherentModulesEquiv Y
  let eX := affineQuasicoherentModulesEquiv X
  let I := eY.inverse.obj G
  have hI : Injective I := eY.inverse.injective_obj G
  let := f.appTop.hom.toAlgebra
  have : Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) :=
    RingHom.etale_algebraMap.1 (HasRingHomProperty.appTop @Etale f ‹_›)
  have : Module.Injective Γ(Y, ⊤) I := Module.injective_module_of_injective_object _ _
  let I' := (ModuleCat.extendScalars f.appTop.hom).obj I
  have : Module.Injective Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(Y, ⊤)] I) :=
    Module.Injective.tensorProduct_of_formallyUnramified Γ(X, ⊤) I
  have hI'' : Injective (ModuleCat.of Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(Y, ⊤)] I)) :=
    Module.injective_object_of_injective_module _ _
  have hI' : Injective I' := hI''
  exact ⟨eX.functor.obj I', eX.functor.injective_obj I', ⟨(Scheme.Modules.pullback f).mapIso
      ((ObjectProperty.ι _).mapIso (eY.counitIso.app G).symm ≪≫
        (affineQuasicoherentModulesEquivCompι Y).app I) ≪≫
    Stacks.AlgebraicGeometry.AffineTilde.tildeOfPullbackIsoApp f I ≪≫
    ((affineQuasicoherentModulesEquivCompι X).app I').symm⟩⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object of a full subcategory which is isomorphic to an injective one is injective. -/
private theorem injective_of_iso_obj {C : Type*} [Category C] {P : ObjectProperty C}
    {F G : P.FullSubcategory} [Injective G] (e : F.obj ≅ G.obj) : Injective F :=
  Injective.of_iso ((ObjectProperty.fullyFaithfulι _).preimageIso e).symm ‹_›

/-- The Zariski reading of a quasi-coherent module `F` on a representable algebraic space is
isomorphic to the underlying module of the corresponding quasi-coherent module on the scheme. -/
private def representedZariskiModuleIsoInverseObj (T : BigFppfOver B S hS)
    (F : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    representedZariskiModule B S hS T F.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS T).inverse.obj F).obj :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
    ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso
      ((ObjectProperty.ι _).mapIso
        ((representedQuasicoherentSchemeEquivalence B S hS T).counitIso.app F).symm)) ≪≫
    representedZariskiModuleQuasicoherentSchemeIso B S hS T _

/-- An injective quasi-coherent module on a representable algebraic space has an injective
quasi-coherent module on the representing scheme as its Zariski reading. -/
theorem exists_injective_iso_representedZariskiModule (T : BigFppfOver B S hS)
    (F : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hF : Injective F) :
    ∃ G : (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory,
      Injective G ∧ Nonempty (representedZariskiModule B S hS T F.obj ≅ G.obj) :=
  ⟨_, (representedQuasicoherentSchemeEquivalence B S hS T).inverse.injective_obj_of_injective hF,
    ⟨representedZariskiModuleIsoInverseObj B S hS T F⟩⟩

/-- A quasi-coherent module on a representable algebraic space whose Zariski reading is an
injective quasi-coherent module on the representing scheme is injective. -/
theorem injective_of_iso_representedZariskiModule (T : BigFppfOver B S hS)
    (F : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (G : (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory) (hG₀ : Injective G)
    (e : representedZariskiModule B S hS T F.obj ≅ G.obj) : Injective F :=
  have : Injective ((representedQuasicoherentSchemeEquivalence B S hS T).inverse.obj F) :=
    injective_of_iso_obj (G := G) ((representedZariskiModuleIsoInverseObj B S hS T F).symm ≪≫ e)
  Injective.of_iso ((representedQuasicoherentSchemeEquivalence B S hS T).counitIso.app F)
    ((representedQuasicoherentSchemeEquivalence B S hS T).functor.injective_obj_of_injective this)

/-- Étale restriction along an isomorphism of algebraic spaces is an equivalence of the
categories of quasi-coherent modules. -/
def quasicoherentEtaleModulePullbackEquivalence {Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y') :
    QuasicoherentSheaves.{u, u} B S hS Y'.1 Y'.2 ≌ QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 :=
  (etaleModulePullbackEquivalence B S hS e).congrFullSubcategory (by
    funext M
    refine propext ⟨fun h => ?_, fun h => isQuasicoherentOnSite_etaleModulePullback B S hS e.hom
      (isEtale_of_isIso B S hS e.hom.hom) M h⟩
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((etaleModulePullbackEquivalence B S hS e).unitIso.app M).symm
      (isQuasicoherentOnSite_etaleModulePullback B S hS e.inv
        (isEtale_of_isIso B S hS e.inv.hom) _ h))

/-- **Étale restriction of an injective quasi-coherent module on a Noetherian affine space.**  Let
`W` be an object of the big fppf site whose underlying scheme is affine with Noetherian ring of
global functions, and let `𝒥` be an injective object of `QCoh(𝒪_W)`.  For every affine algebraic
space `V` with an étale morphism `e : V ⟶ W`, the restriction `𝒥|_V` is an injective object of
`QCoh(𝒪_V)`. -/
theorem injective_etaleModulePullback_of_isAffineSpace (W : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)]
    (J : QuasicoherentSheaves.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2)
    (hJ : Injective J) {V : AlgebraicSpaces B S hS} (hV : IsAffineSpace B S hS V.1)
    (e : V ⟶ schemeSpace W) (he : IsEtale B S hS e.hom) :
    Injective (⟨(etaleModulePullback.{u, u} B S hS e he).obj J.obj,
      isQuasicoherentOnSite_etaleModulePullback B S hS e he J.obj J.2⟩ :
        QuasicoherentSheaves.{u, u} B S hS V.1 V.2) := by
  obtain ⟨T, hT, ⟨ψ⟩⟩ := hV
  let ψ' : schemeSpace T ≅ V := ObjectProperty.isoMk _ ψ.symm
  let φ : schemeSpace T ⟶ schemeSpace W := ψ'.hom ≫ e
  have hφ : IsEtale B S hS φ.hom := isEtale_comp B S hS (isEtale_of_isIso B S hS ψ'.hom.hom) he
  let g : T ⟶ W := yoneda.preimage φ.hom
  have hgp : yoneda.map g = φ.hom := yoneda.map_preimage _
  have hgφ : representedSpaceMap B S hS g = φ := by
    ext1
    exact hgp
  obtain ⟨G, hG, ⟨eG⟩⟩ := exists_injective_iso_representedZariskiModule B S hS W J hJ
  have : IsAffine (Over.left T).obj := hT
  have : IsAffine (Over.left W).obj := ‹IsAffine ((BigFppfOver.toScheme B S hS).obj W)›
  have : IsNoetherianRing Γ((Over.left W).obj, ⊤) :=
    ‹IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)›
  have : Etale (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) :=
    (presheaf_yoneda_map_etale_iff B S hS g).1 (hgp ▸ presheaf_etale_of_isEtale B S hS hφ)
  obtain ⟨G', hG', ⟨eG'⟩⟩ := exists_injective_iso_pullback_of_etale
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) G
  let F₀ : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
    ⟨(modulePullback B S hS (representedSpaceMap B S hS g)).obj J.obj,
      isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g
        (relativelyRepresentable_yoneda_map B S hS g) J.obj J.2⟩
  have hF₀ : Injective F₀ := injective_of_iso_representedZariskiModule B S hS T F₀ G' hG'
    ((representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
      J.obj J.2).symm ≪≫ (Scheme.Modules.pullback _).mapIso eG ≪≫ eG')
  let F : QuasicoherentSheaves.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2 := F₀
  have hF : Injective F := hF₀
  let EQ := quasicoherentEtaleModulePullbackEquivalence B S hS ψ'
  let X : QuasicoherentSheaves.{u, u} B S hS V.1 V.2 :=
    ⟨(etaleModulePullback.{u, u} B S hS e he).obj J.obj,
      isQuasicoherentOnSite_etaleModulePullback B S hS e he J.obj J.2⟩
  let χ : (EQ.functor.obj X).obj ≅ F.obj :=
    (etaleModulePullbackFactorIso B S hS ψ'.hom e (isEtale_of_isIso B S hS ψ'.hom.hom) he rfl
      hφ).app J.obj ≪≫ ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app J.obj).symm ≪≫
      eqToIso (congrArg (fun m : schemeSpace T ⟶ schemeSpace W =>
        (modulePullback B S hS m).obj J.obj) hgφ.symm)
  have hX : Injective (EQ.functor.obj X) :=
    injective_of_iso_obj (G := F) χ
  exact Injective.of_iso (EQ.unitIso.app X).symm (EQ.inverse.injective_obj_of_injective hX)

end AlgebraicGeometry.Space

end
