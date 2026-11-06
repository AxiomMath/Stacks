module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentMayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism

/-!
# Extension by zero and the conclusion of Stacks 0DKV

In Situation 0DKU let `u : U₀ ⟶ X₀` be étale, and restrict the situation along `u`
(`AlgebraicGeometry.Space.RelativeDescentSituation.restrict`), so that its stages are
`Uᵢ = Xᵢ ×_{X₀} U₀` and `U = X ×_{X₀} U₀`.  For `A ∈ D(𝒪_{U₀})` and `L ∈ D(𝒪_{X₀})` this file
compares the conclusion of Stacks 0DKV for the pair `(u_!A, L)` in the situation with its
conclusion for the pair `(A, Lu^*L)` in the restricted situation.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoOfIsEtale`: along an étale
  morphism the derived pullback `Lu^*` is the functor induced on derived categories by étale
  restriction of modules.
* `AlgebraicGeometry.Space.etaleDerivedLowerShriekAdjunction`: `u_! ⊣ Lu^*` on unbounded
  derived categories, with `u_!` induced by extension by zero.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

/-- Pullbacks of presheaves on the big fppf site of `S`, supplied directly: since Lean v4.35.0
instance search times out finding them through the functor-category limit instances. -/
local instance (priority := high)
    hasLimit_cospan_presheaf_RelativelyPerfectHomDescentLocalization (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/- The abelian structure of the modules is taken to be `SheafOfModules.instAbelian`, and their
preadditive structure the one it induces, which is how `DerivedCategory.Qh` reads it: with one
spelling of these instances throughout, the statements below unify with those of the derived
pullback and of the homotopy category without unfolding. -/
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

section Adjunction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Étale restriction of modules, in the spelling of the sheaves of rings of the small étale
ringed topoi that the derived pullback is indexed by. -/
abbrev etaleRestriction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) :=
  etaleModulePullback.{u, u} B S hS f hf

/-- Extension by zero, in the spelling of `AlgebraicGeometry.Space.etaleRestriction`. -/
abbrev etaleExtensionByZero {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) :=
  etaleModuleLowerShriek B S hS f hf

/-- Étale restriction of modules is additive. -/
instance additive_etaleRestriction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) : (etaleRestriction B S hS f hf).Additive :=
  etaleModulePullback_additive B S hS f hf

/-- Étale restriction of modules preserves finite limits. -/
instance preservesFiniteLimits_etaleRestriction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) : PreservesFiniteLimits (etaleRestriction B S hS f hf) :=
  preservesFiniteLimits_etaleModulePullback B S hS f hf

/-- Étale restriction of modules preserves finite colimits. -/
instance preservesFiniteColimits_etaleRestriction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) : PreservesFiniteColimits (etaleRestriction B S hS f hf) :=
  preservesFiniteColimits_etaleModulePullback B S hS f hf

/-- Extension by zero along an étale morphism is additive. -/
instance additive_etaleExtensionByZero {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) : (etaleExtensionByZero B S hS f hf).Additive :=
  etaleModuleLowerShriek_additive B S hS f hf

/-- Extension by zero along an étale morphism preserves finite limits. -/
instance preservesFiniteLimits_etaleExtensionByZero {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) : PreservesFiniteLimits (etaleExtensionByZero B S hS f hf) :=
  preservesFiniteLimits_etaleModuleLowerShriek B S hS f hf

/-- Extension by zero along an étale morphism preserves finite colimits. -/
instance preservesFiniteColimits_etaleExtensionByZero {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    PreservesFiniteColimits (etaleExtensionByZero B S hS f hf) :=
  preservesFiniteColimits_etaleModuleLowerShriek B S hS f hf

/-- Pullback of modules along the morphism of small étale ringed topoi of an étale morphism is
étale restriction: Stacks 03LW read in the spelling the derived pullback is built from. -/
def pullbackModulesIsoEtaleRestriction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ≅
      etaleRestriction B S hS f hf :=
  eqToIso (pullbackModules_eq_modulePullback B S hS f) ≪≫
    modulePullbackIsoEtaleModulePullback B S hS f hf

/- The derived pullback `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` is stated for
the standard model of the derived category, so the declarations below are stated at it too. -/
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Along an étale morphism the derived pullback is étale restriction.**  Étale restriction is
exact, so the functor it induces on derived categories is a left derived functor of degreewise
pullback followed by localization, as `Lu^*` is. -/
def smallEtaleDerivedModulePullbackIsoOfIsEtale {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    smallEtaleDerivedModulePullback B S hS f ≅
      (etaleRestriction B S hS f hf).mapDerivedCategory :=
  letI := Functor.isLeftDerivedFunctor_of_inverts (smallEtaleModuleQuasiIso B S hS Y)
    (etaleRestriction B S hS f hf).mapDerivedCategory
    (etaleRestriction B S hS f hf).mapDerivedCategoryFactorsh
  Functor.leftDerivedNatIso (smallEtaleDerivedModulePullback B S hS f) _
    (smallEtaleDerivedModulePullbackComparison B S hS f)
    (etaleRestriction B S hS f hf).mapDerivedCategoryFactorsh.hom
    (smallEtaleModuleQuasiIso B S hS Y)
    (Functor.isoWhiskerRight
      (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso
        (pullbackModulesIsoEtaleRestriction B S hS f hf) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- **Extension by zero is left adjoint to the derived pullback along an étale morphism**, on
unbounded derived categories: the adjunction of Stacks 03DJ induced on derived categories,
read through `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoOfIsEtale`. -/
def etaleDerivedLowerShriekAdjunction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    (etaleExtensionByZero B S hS f hf).mapDerivedCategory ⊣
      smallEtaleDerivedModulePullback B S hS f :=
  (Adjunction.mapDerivedCategory (F := etaleExtensionByZero B S hS f hf)
      (G := etaleRestriction B S hS f hf)
      (etaleModuleLowerShriekAdjunction B S hS f hf)).ofNatIsoRight
    (smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS f hf).symm

end Adjunction

namespace DerivedPullbackComposition

/- The derived pullback `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` is stated for
the standard model of the derived category, so the declarations below are stated at it too. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (P : DerivedPullbackComposition B S hS)

/-- A factorisation `f ≫ g = k` induces maps on derived homomorphisms that only depend on `f`
through its value. -/
theorem factorHom_congr {X Y Z : AlgebraicSpaces B S hS} {f f' : X ⟶ Y} (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k) (h' : f' ≫ g = k) (hf : f = f')
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (φ : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L) :
    P.factorHom f g k h K L φ = P.factorHom f' g k h' K L φ := by
  subst hf
  rfl

/-- **Change of base** along a factorisation `t ≫ u = k`: conjugation by
`Lu^* ⋙ Lt^* ≅ Lk^*` identifies `Hom(Lk^*M, Lk^*N)` with `Hom(Lt^*(Lu^*M), Lt^*(Lu^*N))`. -/
def baseChangeHomEquiv {T U Z : AlgebraicSpaces B S hS} (t : T ⟶ U) (u : U ⟶ Z) (k : T ⟶ Z)
    (h : t ≫ u = k)
    (M N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    ((smallEtaleDerivedModulePullback B S hS k).obj M ⟶
        (smallEtaleDerivedModulePullback B S hS k).obj N) ≃
      ((smallEtaleDerivedModulePullback B S hS t).obj
          ((smallEtaleDerivedModulePullback B S hS u).obj M) ⟶
        (smallEtaleDerivedModulePullback B S hS t).obj
          ((smallEtaleDerivedModulePullback B S hS u).obj N)) :=
  (((P.iso t u k h).app M).homCongr ((P.iso t u k h).app N)).symm

/-- Change of base commutes with the maps induced by factorisations: this is the cocycle
identity of the composition isomorphisms. -/
theorem baseChangeHomEquiv_factorHom {T' T U Z : AlgebraicSpaces B S hS} (b : T' ⟶ T)
    (t : T ⟶ U) (t' : T' ⟶ U) (u : U ⟶ Z) (k : T ⟶ Z) (k' : T' ⟶ Z) (hb : b ≫ t = t')
    (h : t ≫ u = k) (h' : t' ≫ u = k') (hbk : b ≫ k = k')
    (M N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (ψ : (smallEtaleDerivedModulePullback B S hS k).obj M ⟶
      (smallEtaleDerivedModulePullback B S hS k).obj N) :
    P.baseChangeHomEquiv t' u k' h' M N (P.factorHom b k k' hbk M N ψ) =
      P.factorHom b t t' hb _ _ (P.baseChangeHomEquiv t u k h M N ψ) := by
  have hM := congrArg Iso.hom (P.iso_assoc b t u k t' k' h hb h' hbk M)
  have hN := congrArg Iso.inv (P.iso_assoc b t u k t' k' h hb h' hbk N)
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv] at hM hN
  have hM' : ((P.iso t' u k' h').app M).hom ≫ ((P.iso b k k' hbk).app M).inv =
      ((P.iso b t t' hb).app ((smallEtaleDerivedModulePullback B S hS u).obj M)).inv ≫
        (smallEtaleDerivedModulePullback B S hS b).map ((P.iso t u k h).app M).hom := by
    rw [Iso.comp_inv_eq, Category.assoc, ← hM, Iso.inv_hom_id_assoc]
  have hN' : ((P.iso b k k' hbk).app N).hom ≫ ((P.iso t' u k' h').app N).inv =
      (smallEtaleDerivedModulePullback B S hS b).map ((P.iso t u k h).app N).inv ≫
        ((P.iso b t t' hb).app ((smallEtaleDerivedModulePullback B S hS u).obj N)).hom := by
    have e := congrArg (fun x ↦ ((P.iso b k k' hbk).app N).hom ≫ x ≫
      ((P.iso b t t' hb).app ((smallEtaleDerivedModulePullback B S hS u).obj N)).hom) hN
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc] using e
  simp only [baseChangeHomEquiv, factorHom, Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hM', hN']

/-- **The localization map** attached to a commutative square `u' ≫ t = t' ≫ u` with `u` étale:
`Hom(Lt^*(u_!A), Lt^*L) ⟶ Hom(Lt'^*A, Lt'^*(Lu^*L))`, apply `Lu'^*`, identify
`Lu'^* ∘ Lt^*` with `Lt'^* ∘ Lu^*`, and precompose with `Lt'^*` of the unit `A ⟶ Lu^*(u_!A)` of
extension by zero. -/
def localizationHom {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T) (t : T ⟶ Z)
    (t' : T' ⟶ U) (u : U ⟶ Z) (hu : IsEtale B S hS u.hom) (h : u' ≫ t = t' ≫ u)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U)))
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (χ : (smallEtaleDerivedModulePullback B S hS t).obj
        ((etaleExtensionByZero B S hS u hu).mapDerivedCategory.obj A) ⟶
      (smallEtaleDerivedModulePullback B S hS t).obj L) :
    (smallEtaleDerivedModulePullback B S hS t').obj A ⟶
      (smallEtaleDerivedModulePullback B S hS t').obj
        ((smallEtaleDerivedModulePullback B S hS u).obj L) :=
  (smallEtaleDerivedModulePullback B S hS t').map
      ((etaleDerivedLowerShriekAdjunction B S hS u hu).unit.app A) ≫
    P.baseChangeHomEquiv t' u (u' ≫ t) h.symm _ L (P.factorHom u' t (u' ≫ t) rfl _ L χ)

/-- **The localization maps are compatible with the maps induced by factorisations**: for a
morphism of commutative squares `(a, b)` over the étale `u`, applying `La^*` and then localizing
is localizing and then applying `Lb^*`. -/
theorem localizationHom_factorHom {Tᵢ Tⱼ Tᵢ' Tⱼ' U Z : AlgebraicSpaces B S hS}
    (uᵢ : Tᵢ' ⟶ Tᵢ) (uⱼ : Tⱼ' ⟶ Tⱼ) (tᵢ : Tᵢ ⟶ Z) (tⱼ : Tⱼ ⟶ Z) (tᵢ' : Tᵢ' ⟶ U)
    (tⱼ' : Tⱼ' ⟶ U) (u : U ⟶ Z) (hu : IsEtale B S hS u.hom) (hᵢ : uᵢ ≫ tᵢ = tᵢ' ≫ u)
    (hⱼ : uⱼ ≫ tⱼ = tⱼ' ≫ u) (a : Tⱼ ⟶ Tᵢ) (b : Tⱼ' ⟶ Tᵢ') (ha : a ≫ tᵢ = tⱼ)
    (hb : b ≫ tᵢ' = tⱼ') (hab : b ≫ uᵢ = uⱼ ≫ a)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U)))
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (χ : (smallEtaleDerivedModulePullback B S hS tᵢ).obj
        ((etaleExtensionByZero B S hS u hu).mapDerivedCategory.obj A) ⟶
      (smallEtaleDerivedModulePullback B S hS tᵢ).obj L) :
    P.localizationHom uⱼ tⱼ tⱼ' u hu hⱼ A L (P.factorHom a tᵢ tⱼ ha _ L χ) =
      P.factorHom b tᵢ' tⱼ' hb A _ (P.localizationHom uᵢ tᵢ tᵢ' u hu hᵢ A L χ) := by
  have hc : (uⱼ ≫ a) ≫ tᵢ = uⱼ ≫ tⱼ := by rw [Category.assoc, ha]
  have hpb : b ≫ uᵢ ≫ tᵢ = uⱼ ≫ tⱼ := by rw [← Category.assoc, hab, Category.assoc, ha]
  unfold localizationHom
  rw [P.factorHom_precomp]
  congr 1
  rw [P.factorHom_comp uⱼ a tᵢ tⱼ (uⱼ ≫ a) (uⱼ ≫ tⱼ) ha rfl hc rfl,
    P.factorHom_congr tᵢ (uⱼ ≫ tⱼ) hc (by rw [Category.assoc]; exact hpb) hab.symm,
    ← P.factorHom_comp b uᵢ tᵢ (uᵢ ≫ tᵢ) (b ≫ uᵢ) (uⱼ ≫ tⱼ) rfl rfl _ hpb]
  exact P.baseChangeHomEquiv_factorHom b tᵢ' tⱼ' u (uᵢ ≫ tᵢ) (uⱼ ≫ tⱼ) hb hᵢ.symm hⱼ.symm hpb _ L _

/-- The identification `Lt'^*(Lu^*M) ≅ Lu'^*(Lt^*M)` attached to a commutative square
`u' ≫ t = t' ≫ u`. -/
def squareIso {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T) (t : T ⟶ Z) (t' : T' ⟶ U)
    (u : U ⟶ Z) (h : u' ≫ t = t' ≫ u) :
    smallEtaleDerivedModulePullback B S hS u ⋙ smallEtaleDerivedModulePullback B S hS t' ≅
      smallEtaleDerivedModulePullback B S hS t ⋙ smallEtaleDerivedModulePullback B S hS u' :=
  P.iso t' u (u' ≫ t) h.symm ≪≫ (P.iso u' t (u' ≫ t) rfl).symm

/-- **The base change map for extension by zero**, `u'_!(Lt'^*A) ⟶ Lt^*(u_!A)`, attached to a
commutative square `u' ≫ t = t' ≫ u` with `u` and `u'` étale: the mate of
`AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso` under `u_! ⊣ Lu^*` and
`u'_! ⊣ Lu'^*`. -/
def extensionByZeroBaseChange {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T) (t : T ⟶ Z)
    (t' : T' ⟶ U) (u : U ⟶ Z) (hu : IsEtale B S hS u.hom) (hu' : IsEtale B S hS u'.hom)
    (h : u' ≫ t = t' ≫ u) :
    smallEtaleDerivedModulePullback B S hS t' ⋙
        (etaleExtensionByZero B S hS u' hu').mapDerivedCategory ⟶
      (etaleExtensionByZero B S hS u hu).mapDerivedCategory ⋙
        smallEtaleDerivedModulePullback B S hS t :=
  ((mateEquiv (etaleDerivedLowerShriekAdjunction B S hS u hu)
    (etaleDerivedLowerShriekAdjunction B S hS u' hu')).symm
      (TwoSquare.mk _ _ _ _ (P.squareIso u' t t' u h).hom)).natTrans

/-- The component at `A` of the base change map for extension by zero is `u'_!` of `Lt'^*` of the
unit `A ⟶ Lu^*(u_!A)` followed by the identification of the square, composed with the counit of
`u'_! ⊣ Lu'^*` at `Lt^*(u_!A)`. -/
theorem extensionByZeroBaseChange_app {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T)
    (t : T ⟶ Z) (t' : T' ⟶ U) (u : U ⟶ Z) (hu : IsEtale B S hS u.hom)
    (hu' : IsEtale B S hS u'.hom) (h : u' ≫ t = t' ≫ u)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U))) :
    (P.extensionByZeroBaseChange u' t t' u hu hu' h).app A =
      (etaleExtensionByZero B S hS u' hu').mapDerivedCategory.map
          ((smallEtaleDerivedModulePullback B S hS t').map
              ((etaleDerivedLowerShriekAdjunction B S hS u hu).unit.app A) ≫
            (P.squareIso u' t t' u h).hom.app
              ((etaleExtensionByZero B S hS u hu).mapDerivedCategory.obj A)) ≫
        (etaleDerivedLowerShriekAdjunction B S hS u' hu').counit.app
          ((smallEtaleDerivedModulePullback B S hS t).obj
            ((etaleExtensionByZero B S hS u hu).mapDerivedCategory.obj A)) := by
  simp [extensionByZeroBaseChange, mateEquiv]

/-- The localization map is adjunction transposition of precomposition with the base change map
for extension by zero, followed by the identification of the square. -/
theorem localizationHom_eq {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T) (t : T ⟶ Z)
    (t' : T' ⟶ U) (u : U ⟶ Z) (hu : IsEtale B S hS u.hom) (hu' : IsEtale B S hS u'.hom)
    (h : u' ≫ t = t' ≫ u)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U)))
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (χ : (smallEtaleDerivedModulePullback B S hS t).obj
        ((etaleExtensionByZero B S hS u hu).mapDerivedCategory.obj A) ⟶
      (smallEtaleDerivedModulePullback B S hS t).obj L) :
    P.localizationHom u' t t' u hu h A L χ =
      (etaleDerivedLowerShriekAdjunction B S hS u' hu').homEquiv _ _
          ((P.extensionByZeroBaseChange u' t t' u hu hu' h).app A ≫ χ) ≫
        (P.squareIso u' t t' u h).inv.app L := by
  rw [Adjunction.homEquiv_unit, extensionByZeroBaseChange_app]
  simp only [Functor.map_comp, Category.assoc, Adjunction.unit_naturality_assoc]
  simp [localizationHom, baseChangeHomEquiv, factorHom, squareIso]

/-- **The localization map is bijective as soon as the base change map for extension by zero is
invertible.** -/
theorem bijective_localizationHom {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T)
    (t : T ⟶ Z) (t' : T' ⟶ U) (u : U ⟶ Z) (hu : IsEtale B S hS u.hom)
    (hu' : IsEtale B S hS u'.hom) (h : u' ≫ t = t' ≫ u)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U)))
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    [IsIso ((P.extensionByZeroBaseChange u' t t' u hu hu' h).app A)] :
    Function.Bijective (P.localizationHom u' t t' u hu h A L) := by
  have e : P.localizationHom u' t t' u hu h A L =
      (fun ψ ↦ ψ ≫ (P.squareIso u' t t' u h).inv.app L) ∘
        (etaleDerivedLowerShriekAdjunction B S hS u' hu').homEquiv _ _ ∘
          (fun χ ↦ (P.extensionByZeroBaseChange u' t t' u hu hu' h).app A ≫ χ) :=
    funext fun χ ↦ P.localizationHom_eq u' t t' u hu hu' h A L χ
  rw [e]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp (Equiv.bijective _) ?_)
  · exact ((P.squareIso u' t t' u h).app L).symm.homToEquiv.bijective
  · exact
    (asIso ((P.extensionByZeroBaseChange u' t t' u hu hu' h).app A)).symm.homFromEquiv.bijective

end DerivedPullbackComposition

namespace RelativeDescentSituation

/- The conclusion of Stacks 0DKV,
`AlgebraicGeometry.Space.RelativeDescentSituation.HomDescent`, and the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` it is built from are stated for the
standard model of the derived category, so the declarations below are stated at it too. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I) (P : DerivedPullbackComposition B S hS)
  {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.X₀)
  (hgflat : IsFlat B S hS g) (hgfp : IsFinitePresentation B S hS g)

/-- The morphism `g : U₀ ⟶ X₀` along which the situation is restricted, as a morphism of
algebraic spaces from the space of the restricted situation. -/
abbrev restrictInitial : (D.restrict hU₀ g hgflat hgfp).initialSource ⟶ D.initialSource :=
  ObjectProperty.homMk g

/-- The projection `Xᵢ ×_{X₀} U₀ ⟶ Xᵢ` from a stage of the restricted situation. -/
abbrev restrictStage (i : D.LaterIndex) :
    (D.restrict hU₀ g hgflat hgfp).stageSource i ⟶ D.stageSource i :=
  ObjectProperty.homMk (pullback.fst (D.toX₀ i.1 i.2) g)

/-- The projection `X ×_{X₀} U₀ ⟶ X` from the limit of the restricted situation. -/
abbrev restrictLimit : (D.restrict hU₀ g hgflat hgfp).limitSource ⟶ D.limitSource :=
  ObjectProperty.homMk (pullback.fst D.toInitial g)

/-- The square formed by a stage `Xᵢ ×_{X₀} U₀` of the restricted situation over `Xᵢ`, `U₀` and
`X₀` commutes. -/
theorem restrictStage_comp_stageToInitial (i : D.LaterIndex) :
    D.restrictStage hU₀ g hgflat hgfp i ≫ D.stageToInitial i =
      (D.restrict hU₀ g hgflat hgfp).stageToInitial i ≫ D.restrictInitial hU₀ g hgflat hgfp :=
  ObjectProperty.hom_ext _ pullback.condition

/-- The square formed by the limit `X ×_{X₀} U₀` of the restricted situation over `X`, `U₀` and
`X₀` commutes. -/
theorem restrictLimit_comp_limitToInitial :
    D.restrictLimit hU₀ g hgflat hgfp ≫ D.limitToInitial =
      (D.restrict hU₀ g hgflat hgfp).limitToInitial ≫ D.restrictInitial hU₀ g hgflat hgfp :=
  ObjectProperty.hom_ext _ pullback.condition

/-- The projections from the stages of the restricted situation commute with the transition
morphisms. -/
theorem sourceTransition_comp_restrictStage {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    (D.restrict hU₀ g hgflat hgfp).sourceTransition (i := i) (j := j) h ≫
        D.restrictStage hU₀ g hgflat hgfp i =
      D.restrictStage hU₀ g hgflat hgfp j ≫ D.sourceTransition h :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- The projections from the stages and the limit of the restricted situation commute with the
projections from the limit to the stages. -/
theorem sourceProjection_comp_restrictStage (i : D.LaterIndex) :
    (D.restrict hU₀ g hgflat hgfp).sourceProjection i ≫ D.restrictStage hU₀ g hgflat hgfp i =
      D.restrictLimit hU₀ g hgflat hgfp ≫ D.sourceProjection i :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- Pullback of complexes of modules along `g : U₀ ⟶ X₀` has a left derived functor with respect to
quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_restrictInitial :
    (smallEtaleModulePullbackOnHomotopy B S hS
      (D.restrictInitial hU₀ g hgflat hgfp)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS D.initialSource) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- Pullback of complexes of modules along the projection `Xᵢ ×_{X₀} U₀ ⟶ Xᵢ` has a left derived
functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_restrictStage (i : D.LaterIndex) :
    (smallEtaleModulePullbackOnHomotopy B S hS
      (D.restrictStage hU₀ g hgflat hgfp i)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS (D.stageSource i)) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- Pullback of complexes of modules along the projection `X ×_{X₀} U₀ ⟶ X` has a left derived
functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_restrictLimit :
    (smallEtaleModulePullbackOnHomotopy B S hS
      (D.restrictLimit hU₀ g hgflat hgfp)).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS D.limitSource) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

variable (hg : IsEtale B S hS g)

/-- Étale restriction of modules along an étale `g : U₀ ⟶ X₀` is additive. -/
instance additive_etaleRestriction_restrictInitial :
    (etaleRestriction B S hS (D.restrictInitial hU₀ g hgflat hgfp) hg).Additive :=
  additive_etaleRestriction B S hS _ hg

/-- Étale restriction of modules along an étale `g : U₀ ⟶ X₀` preserves finite limits. -/
instance preservesFiniteLimits_etaleRestriction_restrictInitial :
    PreservesFiniteLimits (etaleRestriction B S hS (D.restrictInitial hU₀ g hgflat hgfp) hg) :=
  preservesFiniteLimits_etaleRestriction B S hS _ hg

/-- Étale restriction of modules along an étale `g : U₀ ⟶ X₀` preserves finite colimits. -/
instance preservesFiniteColimits_etaleRestriction_restrictInitial :
    PreservesFiniteColimits (etaleRestriction B S hS (D.restrictInitial hU₀ g hgflat hgfp) hg) :=
  preservesFiniteColimits_etaleRestriction B S hS _ hg

/-- Extension by zero along an étale `g : U₀ ⟶ X₀` is additive. -/
instance additive_etaleExtensionByZero_restrictInitial :
    (etaleExtensionByZero B S hS (D.restrictInitial hU₀ g hgflat hgfp) hg).Additive :=
  additive_etaleExtensionByZero B S hS _ hg

/-- Extension by zero along an étale `g : U₀ ⟶ X₀` preserves finite limits. -/
instance preservesFiniteLimits_etaleExtensionByZero_restrictInitial :
    PreservesFiniteLimits
      (etaleExtensionByZero B S hS (D.restrictInitial hU₀ g hgflat hgfp) hg) :=
  preservesFiniteLimits_etaleExtensionByZero B S hS _ hg

/-- Extension by zero along an étale `g : U₀ ⟶ X₀` preserves finite colimits. -/
instance preservesFiniteColimits_etaleExtensionByZero_restrictInitial :
    PreservesFiniteColimits
      (etaleExtensionByZero B S hS (D.restrictInitial hU₀ g hgflat hgfp) hg) :=
  preservesFiniteColimits_etaleExtensionByZero B S hS _ hg

/-- The localization map at a stage, from the system of `(u_!A, L)` to that of `(A, Lu^*L)`. -/
abbrev stageLocalizationHom (A : (D.restrict hU₀ g hgflat hgfp).InitialDerived)
    (L : D.InitialDerived) (i : D.LaterIndex) :=
  P.localizationHom (D.restrictStage hU₀ g hgflat hgfp i) (D.stageToInitial i)
    ((D.restrict hU₀ g hgflat hgfp).stageToInitial i) (D.restrictInitial hU₀ g hgflat hgfp) hg
    (D.restrictStage_comp_stageToInitial hU₀ g hgflat hgfp i) A L

/-- The localization map at the limit. -/
abbrev limitLocalizationHom (A : (D.restrict hU₀ g hgflat hgfp).InitialDerived)
    (L : D.InitialDerived) :=
  P.localizationHom (D.restrictLimit hU₀ g hgflat hgfp) D.limitToInitial
    (D.restrict hU₀ g hgflat hgfp).limitToInitial (D.restrictInitial hU₀ g hgflat hgfp) hg
    (D.restrictLimit_comp_limitToInitial hU₀ g hgflat hgfp) A L

/-- **Extension by zero and the conclusion of Stacks 0DKV.**  Let `u : U₀ ⟶ X₀` be étale.  If the
localization maps are bijective at every stage and at the limit, then the conclusion of the tag
for `(A, Lu^*L)` in the situation restricted along `u` gives it for `(u_!A, L)`. -/
theorem homDescent_extensionByZero_of_restrict
    (A : (D.restrict hU₀ g hgflat hgfp).InitialDerived) (L : D.InitialDerived)
    (hτ : ∀ i, Function.Bijective (D.stageLocalizationHom P hU₀ g hgflat hgfp hg A L i))
    (hτ' : Function.Bijective (D.limitLocalizationHom P hU₀ g hgflat hgfp hg A L))
    (hA : (D.restrict hU₀ g hgflat hgfp).HomDescent P A
      ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀ g hgflat hgfp)).obj L)) :
    D.HomDescent P
      ((etaleExtensionByZero B S hS (D.restrictInitial hU₀ g hgflat hgfp) hg).mapDerivedCategory.obj
        A) L := by
  have hT : ∀ {i j : D.LaterIndex} (h : i.1 ≤ j.1) χ,
      D.stageLocalizationHom P hU₀ g hgflat hgfp hg A L j (D.homTransition P _ L h χ) =
        (D.restrict hU₀ g hgflat hgfp).homTransition P A _ h
          (D.stageLocalizationHom P hU₀ g hgflat hgfp hg A L i χ) := fun h χ ↦
    P.localizationHom_factorHom _ _ _ _ _ _ _ hg _ _ _ _ _ _
      (D.sourceTransition_comp_restrictStage hU₀ g hgflat hgfp h) A L χ
  have hC : ∀ (i : D.LaterIndex) χ,
      D.limitLocalizationHom P hU₀ g hgflat hgfp hg A L (D.homComparison P _ L i χ) =
        (D.restrict hU₀ g hgflat hgfp).homComparison P A _ i
          (D.stageLocalizationHom P hU₀ g hgflat hgfp hg A L i χ) := fun i χ ↦
    P.localizationHom_factorHom _ _ _ _ _ _ _ hg _ _ _ _ _ _
      (D.sourceProjection_comp_restrictStage hU₀ g hgflat hgfp i) A L χ
  refine ⟨fun ψ ↦ ?_, fun i φ φ' hφ ↦ ?_⟩
  · obtain ⟨i, φ, hφ⟩ := hA.1 (D.limitLocalizationHom P hU₀ g hgflat hgfp hg A L ψ)
    obtain ⟨χ, rfl⟩ := (hτ i).2 φ
    exact ⟨i, χ, hτ'.1 ((hC i χ).trans hφ)⟩
  · obtain ⟨j, hij, hj⟩ := hA.2 i _ _
      (((hC i φ).symm.trans (congrArg _ hφ)).trans (hC i φ'))
    exact ⟨j, hij, (hτ j).1 (((hT hij φ).trans hj).trans (hT hij φ').symm)⟩

include hg in
/-- The projection from a stage of the restricted situation is étale, as a base change of `u`. -/
theorem isEtale_restrictStage (i : D.LaterIndex) :
    IsEtale B S hS (D.restrictStage hU₀ g hgflat hgfp i).hom :=
  isEtale_of_isPullback B S hS ((D.restrict hU₀ g hgflat hgfp).stageToInitial i)
    (D.restrictStage hU₀ g hgflat hgfp i) (D.restrictInitial hU₀ g hgflat hgfp)
    (D.stageToInitial i)
    (IsPullback.of_map_of_faithful (F := ObjectProperty.ι _)
      (IsPullback.of_hasPullback (D.toX₀ i.1 i.2) g).flip) hg

include hg in
/-- The projection from the limit of the restricted situation is étale, as a base change of
`u`. -/
theorem isEtale_restrictLimit : IsEtale B S hS (D.restrictLimit hU₀ g hgflat hgfp).hom :=
  isEtale_of_isPullback B S hS (D.restrict hU₀ g hgflat hgfp).limitToInitial
    (D.restrictLimit hU₀ g hgflat hgfp) (D.restrictInitial hU₀ g hgflat hgfp) D.limitToInitial
    (IsPullback.of_map_of_faithful (F := ObjectProperty.ι _)
      (IsPullback.of_hasPullback D.toInitial g).flip) hg

/-- The base change map for extension by zero at a stage of the restricted situation. -/
abbrev stageExtensionByZeroBaseChange (i : D.LaterIndex) :=
  P.extensionByZeroBaseChange (D.restrictStage hU₀ g hgflat hgfp i) (D.stageToInitial i)
    ((D.restrict hU₀ g hgflat hgfp).stageToInitial i) (D.restrictInitial hU₀ g hgflat hgfp) hg
    (D.isEtale_restrictStage hU₀ g hgflat hgfp hg i)
    (D.restrictStage_comp_stageToInitial hU₀ g hgflat hgfp i)

/-- The base change map for extension by zero at the limit of the restricted situation. -/
abbrev limitExtensionByZeroBaseChange :=
  P.extensionByZeroBaseChange (D.restrictLimit hU₀ g hgflat hgfp) D.limitToInitial
    (D.restrict hU₀ g hgflat hgfp).limitToInitial (D.restrictInitial hU₀ g hgflat hgfp) hg
    (D.isEtale_restrictLimit hU₀ g hgflat hgfp hg)
    (D.restrictLimit_comp_limitToInitial hU₀ g hgflat hgfp)

/-- **The conclusion of Stacks 0DKV for `u_!(u^*K₀)` from its conclusion in the situation
restricted along `u`**, for an étale `u : U₀ ⟶ X₀`, as soon as the base change maps for
extension by zero are invertible at every stage and at the limit. -/
theorem shiftedHomDescent_extendRestrict_of_restrict (K₀ L₀ : D.InitialDerived)
    (hβ : ∀ (i : D.LaterIndex) (A : (D.restrict hU₀ g hgflat hgfp).InitialDerived),
      IsIso ((D.stageExtensionByZeroBaseChange P hU₀ g hgflat hgfp hg i).app A))
    (hβ' : ∀ A : (D.restrict hU₀ g hgflat hgfp).InitialDerived,
      IsIso ((D.limitExtensionByZeroBaseChange P hU₀ g hgflat hgfp hg).app A))
    (hE : (D.restrict hU₀ g hgflat hgfp).ShiftedHomDescent P
      ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀ g hgflat hgfp)).obj K₀)
      ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀ g hgflat hgfp)).obj L₀)) :
    D.ShiftedHomDescent P (D.extendRestrictObj (D.restrictInitial hU₀ g hgflat hgfp) hg K₀) L₀ := by
  intro n
  let A := ((smallEtaleDerivedModulePullback B S hS
    (D.restrictInitial hU₀ g hgflat hgfp)).obj K₀)⟦n⟧
  have h := D.homDescent_extensionByZero_of_restrict P hU₀ g hgflat hgfp hg A L₀
    (fun i ↦ have := hβ i A; P.bijective_localizationHom _ _ _ _ hg _ _ A L₀)
    (have := hβ' A; P.bijective_localizationHom _ _ _ _ hg _ _ A L₀) (hE n)
  refine homDescent_of_iso P ?_ h
  exact ((etaleExtensionByZero B S hS (D.restrictInitial hU₀ g hgflat hgfp)
      hg).mapDerivedCategory.commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso
      ((etaleExtensionByZero B S hS (D.restrictInitial hU₀ g hgflat hgfp)
          hg).mapDerivedCategory.mapIso
        ((smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS
          (D.restrictInitial hU₀ g hgflat hgfp) hg).app K₀) ≪≫
      ((Dualizing.mapDerivedCategoryComp
        (etaleRestriction B S hS (D.restrictInitial hU₀ g hgflat hgfp) hg)
        (etaleExtensionByZero B S hS (D.restrictInitial hU₀ g hgflat hgfp) hg)).app K₀).symm)

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
