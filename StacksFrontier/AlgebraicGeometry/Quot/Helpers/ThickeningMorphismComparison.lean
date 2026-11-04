module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorObstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraSquareMapCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompMate

/-!
# Comparing the deformation data of two thickenings related by a morphism

In Situation 082M let `h₂ : T ⟶ T₂` and `g : T₂ ⟶ T₁` be morphisms of test schemes over `Y`,
and write `h₁ = h₂ ≫ g`. This file compares the reductions `F_{Tₖ} ⟶ (X_{hₖ})_*F_T` of the two
base changes along the comparison `F_{T₁} ⟶ (X_g)_*F_{T₂}`.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation.reductionComparison`: the map
  `F_{T₁} ⟶ (X_g)_*F_{T₂}`, adjoint to `F_{T₁}|_{X_{T₂}} ≅ F_{T₂}`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_map_of_cocycle`: the map adjoint to
  a base-change identification along a composite, through those along the factors.

## Implementation notes

Helpers for the naturality of the deformation theory of quotients (Stacks 0CZU, 0CZV) in the
thickening, used for Stacks 0CZW, axiom [5]. No declaration here carries a `@[stacks]`
attribute.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-- **Transport of a factorization of reductions along isomorphisms of the direct images.** Let
`ι₁ : t₁ ≅ m₁`, `ι₂ : t₂ ≅ m₂`, `ιg : tg ≅ mg` be isomorphisms of functors and
`Cm : m₂ ⋙ mg ≅ m₁`. If maps `rₖ : Fₖ ⟶ tₖ F₀` (and `rg : F₁ ⟶ tg F₂`) are carried by the `ι`
to maps `r'ₖ` with `r'₁ = r'g ≫ mg(r'₂) ≫ Cm`, then `r₁` followed by the transported comparison
`t₁ ≅ t₂ ⋙ tg` is `rg ≫ tg(r₂)`. -/
theorem transport_reduction_comp {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {t₁ m₁ : C₀ ⥤ C₁} {t₂ m₂ : C₀ ⥤ C₂} {tg mg : C₂ ⥤ C₁} (ι₁ : t₁ ≅ m₁) (ι₂ : t₂ ≅ m₂)
    (ιg : tg ≅ mg) (Cm : m₂ ⋙ mg ≅ m₁) {F₀ : C₀} {F₁ : C₁} {F₂ : C₂}
    (r₁ : F₁ ⟶ t₁.obj F₀) (r₂ : F₂ ⟶ t₂.obj F₀) (rg : F₁ ⟶ tg.obj F₂)
    (r'₁ : F₁ ⟶ m₁.obj F₀) (r'₂ : F₂ ⟶ m₂.obj F₀) (r'g : F₁ ⟶ mg.obj F₂)
    (h₁ : r₁ ≫ ι₁.hom.app F₀ = r'₁) (h₂ : r₂ ≫ ι₂.hom.app F₀ = r'₂) (hg : rg ≫ ιg.hom.app F₂ = r'g)
    (h : r'₁ = r'g ≫ mg.map r'₂ ≫ Cm.hom.app F₀) :
    r₁ ≫ (ι₁ ≪≫ Cm.symm ≪≫ Functor.isoWhiskerRight ι₂.symm mg ≪≫
      Functor.isoWhiskerLeft t₂ ιg.symm).hom.app F₀ = rg ≫ tg.map r₂ := by
  subst h₁ h₂ hg
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    ιg.inv.naturality, Iso.hom_inv_id_app_assoc]

/-- A map `π` carried to `U` by an isomorphism `ι : t ≅ m` of functors, followed by `t(R)`, is
carried to `U ≫ m(R)`. -/
theorem transport_comp_map {C₀ C₁ : Type*} [Category C₀] [Category C₁] {t m : C₀ ⥤ C₁}
    (ι : t ≅ m) {F : C₁} {X Y : C₀} (π : F ⟶ t.obj X) (U : F ⟶ m.obj X) (R : X ⟶ Y)
    (h : π ≫ ι.hom.app X = U) : (π ≫ t.map R) ≫ ι.hom.app Y = U ≫ m.map R := by
  rw [Category.assoc, ι.hom.naturality, ← Category.assoc, h]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The unit of an adjunction transported along a composite of two isomorphisms of its right
adjoint is the unit transported along the first, followed by the second. -/
theorem _root_.CategoryTheory.Adjunction.unit_app_ofNatIsoRight_trans {C D : Type*} [Category C]
    [Category D] {F : C ⥤ D} {G H K : D ⥤ C} (A : F ⊣ G) (e₁ : G ≅ H) (e₂ : H ≅ K) (Z : C) :
    (A.ofNatIsoRight (e₁ ≪≫ e₂)).unit.app Z =
      (A.ofNatIsoRight e₁).unit.app Z ≫ e₂.hom.app (F.obj Z) := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.trans_hom, Category.assoc]

/-- **The unit of `f^* ⊣ f_*` is the unit of the Stacks 03D7 adjunction of the small étale
ringed topoi**, read through the identification of the two direct images of modules. -/
theorem viaComparison_unit_app_comp_pushforwardModulesIsoModulePushforward
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (smallEtaleRingedToposHom B S hS f).pullbackAdjPushforwardModulesViaComparison.unit.app M ≫
        (pushforwardModulesIsoModulePushforward B S hS f).hom.app
          ((modulePullback B S hS f).obj M) =
      (modulePullbackAdjunction B S hS f).unit.app M :=
  (Adjunction.unit_app_ofNatIsoRight_trans
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f))
    (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso
    (pushforwardModulesIsoModulePushforward B S hS f) M).symm

section Composite

variable {X₀ X₂ X₁ : AlgebraicSpaces B S hS} (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁)

/-- **The reduction of a composite, through the reductions of the factors.** Let
`R_b : b^*F₁ ≅ F₂`, `R_a : a^*F₂ ≅ F₀` and `R : (a ≫ b)^*F₁ ≅ F₀` satisfy the cocycle condition
`R = (a^*b^* ≅ (a ≫ b)^*)⁻¹ ≫ a^*R_b ≫ R_a`. Then the map `F₁ ⟶ (a ≫ b)_*F₀` adjoint to `R` is the
map `F₁ ⟶ b_*F₂` adjoint to `R_b` followed by the direct image along `b` of the map
`F₂ ⟶ a_*F₀` adjoint to `R_a`, read through `b_* ∘ a_* ≅ (a ≫ b)_*`. -/
theorem modulePullbackAdjunction_unit_comp_map_of_cocycle
    {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} {F₂ : Modules.{u, u} B S hS X₂.1 X₂.2}
    {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2} (Rb : (modulePullback B S hS b).obj F₁ ≅ F₂)
    (Ra : (modulePullback B S hS a).obj F₂ ≅ F₀) (R : (modulePullback B S hS (a ≫ b)).obj F₁ ≅ F₀)
    (hR : R.hom = (modulePullbackCompIso B S hS a b).inv.app F₁ ≫
      (modulePullback B S hS a).map Rb.hom ≫ Ra.hom) :
    (modulePullbackAdjunction B S hS (a ≫ b)).unit.app F₁ ≫
        (modulePushforward B S hS (a ≫ b)).map R.hom =
      (modulePullbackAdjunction B S hS b).unit.app F₁ ≫
        (modulePushforward B S hS b).map (Rb.hom ≫
          (modulePullbackAdjunction B S hS a).unit.app F₂ ≫
            (modulePushforward B S hS a).map Ra.hom) ≫
        (modulePushforwardCompIso B S hS a b).hom.app F₀ := by
  rw [← unit_comp_map_modulePullbackCompIso_hom_app_assoc B S hS a b F₁, hR]
  have e₁ : (modulePushforward B S hS (a ≫ b)).map ((modulePullbackCompIso B S hS a b).hom.app F₁) ≫
      (modulePushforward B S hS (a ≫ b)).map ((modulePullbackCompIso B S hS a b).inv.app F₁ ≫
        (modulePullback B S hS a).map Rb.hom ≫ Ra.hom) =
      (modulePushforward B S hS (a ≫ b)).map ((modulePullback B S hS a).map Rb.hom ≫ Ra.hom) := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  have e₂ : (modulePushforwardCompIso B S hS a b).hom.app
        ((modulePullback B S hS b ⋙ modulePullback B S hS a).obj F₁) ≫
        (modulePushforward B S hS (a ≫ b)).map ((modulePullback B S hS a).map Rb.hom ≫ Ra.hom) =
      (modulePushforward B S hS b).map ((modulePushforward B S hS a).map
        ((modulePullback B S hS a).map Rb.hom ≫ Ra.hom)) ≫
        (modulePushforwardCompIso B S hS a b).hom.app F₀ :=
    ((modulePushforwardCompIso B S hS a b).hom.naturality
      (show (modulePullback B S hS b ⋙ modulePullback B S hS a).obj F₁ ⟶ F₀ from
        (modulePullback B S hS a).map Rb.hom ≫ Ra.hom)).symm
  have hu : (modulePullbackAdjunction B S hS a).unit.app ((modulePullback B S hS b).obj F₁) ≫
      (modulePushforward B S hS a).map ((modulePullback B S hS a).map Rb.hom) =
        Rb.hom ≫ (modulePullbackAdjunction B S hS a).unit.app F₂ :=
    ((modulePullbackAdjunction B S hS a).unit.naturality Rb.hom).symm
  have e₃ : (modulePushforward B S hS b).map
        ((modulePullbackAdjunction B S hS a).unit.app ((modulePullback B S hS b).obj F₁)) ≫
      (modulePushforward B S hS b).map ((modulePushforward B S hS a).map
        ((modulePullback B S hS a).map Rb.hom ≫ Ra.hom)) =
      (modulePushforward B S hS b).map (Rb.hom ≫
        (modulePullbackAdjunction B S hS a).unit.app F₂ ≫
          (modulePushforward B S hS a).map Ra.hom) := by
    rw [← Functor.map_comp, Functor.map_comp (modulePushforward B S hS a), ← Category.assoc, hu,
      Category.assoc]
  simp only [Category.assoc]
  rw [e₁, e₂, ← Category.assoc
    ((modulePushforward B S hS b).map ((modulePullbackAdjunction B S hS a).unit.app _)), e₃]

/-- `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_map_of_cocycle` for a morphism
`k` equal to the composite, the cocycle condition being read through
`AlgebraicGeometry.Space.modulePullbackTriangle`. -/
theorem modulePullbackAdjunction_unit_map_of_triangle {k : X₀ ⟶ X₁} (e : a ≫ b = k)
    {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} {F₂ : Modules.{u, u} B S hS X₂.1 X₂.2}
    {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2} (Rb : (modulePullback B S hS b).obj F₁ ≅ F₂)
    (Ra : (modulePullback B S hS a).obj F₂ ≅ F₀) (R : (modulePullback B S hS k).obj F₁ ≅ F₀)
    (hR : R.hom = (modulePullbackTriangle B S hS e).hom.app F₁ ≫
      (modulePullback B S hS a).map Rb.hom ≫ Ra.hom) :
    (modulePullbackAdjunction B S hS k).unit.app F₁ ≫ (modulePushforward B S hS k).map R.hom =
      (modulePullbackAdjunction B S hS b).unit.app F₁ ≫
        (modulePushforward B S hS b).map (Rb.hom ≫
          (modulePullbackAdjunction B S hS a).unit.app F₂ ≫
            (modulePushforward B S hS a).map Ra.hom) ≫
        (modulePushforwardCompIso B S hS a b ≪≫
          eqToIso (congrArg (modulePushforward B S hS) e)).hom.app F₀ := by
  subst e
  have hR' : R.hom = (modulePullbackCompIso B S hS a b).inv.app F₁ ≫
      (modulePullback B S hS a).map Rb.hom ≫ Ra.hom := by
    rw [hR, modulePullbackTriangle_eq, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
      Category.id_comp, Iso.symm_hom]
  rw [modulePullbackAdjunction_unit_comp_map_of_cocycle a b Rb Ra R hR', Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- **A cocycle of natural isomorphisms, read on an object.** If `β : P₀ ≅ P₁ ⋙ k^*` is the
composite of `βa : P₀ ≅ P₂ ⋙ a^*` and `βb : P₂ ≅ P₁ ⋙ b^*` read through `a^* ∘ b^* ≅ k^*` for
`a ≫ b = k`, then on an object its inverse is the comparison followed by `a^*` of the inverse of
`βb` and the inverse of `βa`. -/
theorem modulePullbackTriangle_inv_app_of_cocycle {k : X₀ ⟶ X₁} (e : a ≫ b = k) {C : Type*}
    {_ : Category C} (P₁ : C ⥤ Modules.{u, u} B S hS X₁.1 X₁.2)
    (P₂ : C ⥤ Modules.{u, u} B S hS X₂.1 X₂.2) (P₀ : C ⥤ Modules.{u, u} B S hS X₀.1 X₀.2)
    (βb : P₂ ≅ P₁ ⋙ modulePullback B S hS b) (βa : P₀ ≅ P₂ ⋙ modulePullback B S hS a)
    (β : P₀ ≅ P₁ ⋙ modulePullback B S hS k)
    (hβ : β = (βa ≪≫ Functor.isoWhiskerRight βb (modulePullback B S hS a) ≪≫
      Functor.associator P₁ (modulePullback B S hS b) (modulePullback B S hS a)) ≪≫
        (Functor.isoWhiskerLeft P₁ (modulePullbackTriangle B S hS e)).symm) (F : C) :
    β.inv.app F = (modulePullbackTriangle B S hS e).hom.app (P₁.obj F) ≫
      (modulePullback B S hS a).map (βb.inv.app F) ≫ βa.inv.app F := by
  subst hβ
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Category.id_comp, Category.assoc]

/-- `AlgebraicGeometry.Space.modulePullbackTriangle_inv_app_of_cocycle` for isomorphisms
`R`, `Rb`, `Ra` of the iterated inverse images whose forward maps are the inverses of the
components of the natural isomorphisms. -/
theorem modulePullbackTriangle_hom_of_cocycle {k : X₀ ⟶ X₁} (e : a ≫ b = k) {C : Type*}
    {_ : Category C} (P₁ : C ⥤ Modules.{u, u} B S hS X₁.1 X₁.2)
    (P₂ : C ⥤ Modules.{u, u} B S hS X₂.1 X₂.2) (P₀ : C ⥤ Modules.{u, u} B S hS X₀.1 X₀.2)
    (βb : P₂ ≅ P₁ ⋙ modulePullback B S hS b) (βa : P₀ ≅ P₂ ⋙ modulePullback B S hS a)
    (β : P₀ ≅ P₁ ⋙ modulePullback B S hS k)
    (hβ : β = (βa ≪≫ Functor.isoWhiskerRight βb (modulePullback B S hS a) ≪≫
      Functor.associator P₁ (modulePullback B S hS b) (modulePullback B S hS a)) ≪≫
        (Functor.isoWhiskerLeft P₁ (modulePullbackTriangle B S hS e)).symm) (F : C)
    (Rb : (modulePullback B S hS b).obj (P₁.obj F) ≅ P₂.obj F)
    (Ra : (modulePullback B S hS a).obj (P₂.obj F) ≅ P₀.obj F)
    (R : (modulePullback B S hS k).obj (P₁.obj F) ≅ P₀.obj F)
    (hRb : Rb.hom = βb.inv.app F) (hRa : Ra.hom = βa.inv.app F) (hR : R.hom = β.inv.app F) :
    R.hom = (modulePullbackTriangle B S hS e).hom.app (P₁.obj F) ≫
      (modulePullback B S hS a).map Rb.hom ≫ Ra.hom := by
  rw [hR, hRb, hRa]
  exact modulePullbackTriangle_inv_app_of_cocycle a b e P₁ P₂ P₀ βb βa β hβ F

end Composite

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-- `X_{h₂ ≫ g} = X_{h₂} ≫ X_g`, in the spelling through `relativeMap`. -/
theorem relativeMap_comp {T T₂ T₁ : SchemesOver D.Y} (h₂ : T ⟶ T₂) (g : T₂ ⟶ T₁) :
    D.relativeMap h₂ ≫ D.relativeMap g = D.relativeMap (h₂ ≫ g) :=
  (baseChangeMap_comp D.f h₂ g).symm

/-- The comparison of Stacks 03LU for `X_{h₂ ≫ g} = X_{h₂} ≫ X_g`, spelled through `relativeMap`,
is the one spelled through `baseChangeMap`. -/
theorem relativeMapTriangle_eq {T T₂ T₁ : SchemesOver D.Y} (h₂ : T ⟶ T₂) (g : T₂ ⟶ T₁) :
    modulePullbackTriangle B S hS (f := D.relativeMap h₂) (g := D.relativeMap g)
        (k := D.relativeMap (h₂ ≫ g)) (D.relativeMap_comp h₂ g) =
      modulePullbackTriangle B S hS (baseChangeMap_comp D.f h₂ g).symm :=
  rfl

/-- `F_{T'}|_{X_T} ≅ F_T` is the inverse of the comparison of the two base changes. -/
theorem restrictBaseChangeModuleIso_hom {T T' : SchemesOver D.Y} (h : T ⟶ T') :
    (D.restrictBaseChangeModuleIso h).hom = (D.baseChangeComparison h).inv.app D.F := by
  rw [restrictBaseChangeModuleIso, Iso.symm_hom, Iso.app_inv]

/-- **The comparison `F_{T₁} ⟶ (X_g)_*F_{T₂}`** for a morphism `g : T₂ ⟶ T₁` of test schemes:
the map adjoint to the identification `F_{T₁}|_{X_{T₂}} ≅ F_{T₂}` of Stacks 082N. -/
def reductionComparison {T₂ T₁ : SchemesOver D.Y} (g : T₂ ⟶ T₁) :
    D.baseChangeModule T₁ ⟶
      (modulePushforward B S hS (D.relativeMap g)).obj (D.baseChangeModule T₂) :=
  (modulePullbackAdjunction B S hS (D.relativeMap g)).unit.app (D.baseChangeModule T₁) ≫
    (modulePushforward B S hS (D.relativeMap g)).map (D.restrictBaseChangeModuleIso g).hom

/-- The comparison `(X_g)_* ∘ (X_{h₂})_* ≅ (X_{h₂ ≫ g})_*` of direct images of modules
(Stacks 03LU), read through `X_{h₂ ≫ g} = X_{h₂} ≫ X_g`. -/
def relativeMapPushforwardCompIso {T T₂ T₁ : SchemesOver D.Y} (h₂ : T ⟶ T₂) (g : T₂ ⟶ T₁) :
    modulePushforward B S hS (D.relativeMap h₂) ⋙ modulePushforward B S hS (D.relativeMap g) ≅
      modulePushforward B S hS (D.relativeMap (h₂ ≫ g)) :=
  modulePushforwardCompIso B S hS (D.relativeMap h₂) (D.relativeMap g) ≪≫
    eqToIso (congrArg (modulePushforward B S hS) (D.relativeMap_comp h₂ g))

/-- **The cocycle condition for `F_{T'}|_{X_T} ≅ F_T`** along a composite of test schemes
(Stacks 082N): it is the cocycle condition of the comparison of the two base changes. -/
theorem restrictBaseChangeModuleIso_comp_hom {T T₂ T₁ : SchemesOver D.Y} (h₂ : T ⟶ T₂)
    (g : T₂ ⟶ T₁) :
    (D.restrictBaseChangeModuleIso (h₂ ≫ g)).hom =
      (modulePullbackTriangle B S hS (f := D.relativeMap h₂) (g := D.relativeMap g)
          (k := D.relativeMap (h₂ ≫ g)) (D.relativeMap_comp h₂ g)).hom.app
          ((modulePullback B S hS (D.sourceProjection T₁)).obj D.F) ≫
        (modulePullback B S hS (D.relativeMap h₂)).map (D.restrictBaseChangeModuleIso g).hom ≫
        (D.restrictBaseChangeModuleIso h₂).hom := by
  have key := D.baseChangeComparison_comp (modulePushforwardCoherence B S hS) h₂ g
  rw [← D.relativeMapTriangle_eq h₂ g] at key
  refine modulePullbackTriangle_hom_of_cocycle (k := D.relativeMap (h₂ ≫ g))
    (D.relativeMap h₂) (D.relativeMap g) (D.relativeMap_comp h₂ g)
    (modulePullback B S hS (D.sourceProjection T₁))
    (modulePullback B S hS (D.sourceProjection T₂)) (modulePullback B S hS (D.sourceProjection T))
    (D.baseChangeComparison g) (D.baseChangeComparison h₂) (D.baseChangeComparison (h₂ ≫ g))
    key D.F (D.restrictBaseChangeModuleIso g) (D.restrictBaseChangeModuleIso h₂)
    (D.restrictBaseChangeModuleIso (h₂ ≫ g)) ?_ ?_ ?_
  · exact D.restrictBaseChangeModuleIso_hom g
  · exact D.restrictBaseChangeModuleIso_hom h₂
  · exact D.restrictBaseChangeModuleIso_hom (h₂ ≫ g)

/-- **The reduction along a composite of test schemes, through the reductions of the factors.**
For `h₂ : T ⟶ T₂` and `g : T₂ ⟶ T₁`, the map `F_{T₁} ⟶ (X_{h₂ ≫ g})_*F_T` adjoint to
`F_{T₁}|_{X_T} ≅ F_T` is the map `F_{T₁} ⟶ (X_g)_*F_{T₂}` adjoint to `F_{T₁}|_{X_{T₂}} ≅ F_{T₂}`
followed by the direct image of the map `F_{T₂} ⟶ (X_{h₂})_*F_T` adjoint to
`F_{T₂}|_{X_T} ≅ F_T`, read through `(X_g)_* ∘ (X_{h₂})_* ≅ (X_{h₂ ≫ g})_*`. -/
theorem unit_comp_restrictBaseChangeModuleIso_comp {T T₂ T₁ : SchemesOver D.Y} (h₂ : T ⟶ T₂)
    (g : T₂ ⟶ T₁) :
    (modulePullbackAdjunction B S hS (D.relativeMap (h₂ ≫ g))).unit.app
          ((modulePullback B S hS (D.sourceProjection T₁)).obj D.F) ≫
        (modulePushforward B S hS (D.relativeMap (h₂ ≫ g))).map
          (D.restrictBaseChangeModuleIso (h₂ ≫ g)).hom =
      (modulePullbackAdjunction B S hS (D.relativeMap g)).unit.app
          ((modulePullback B S hS (D.sourceProjection T₁)).obj D.F) ≫
        (modulePushforward B S hS (D.relativeMap g)).map ((D.restrictBaseChangeModuleIso g).hom ≫
          (modulePullbackAdjunction B S hS (D.relativeMap h₂)).unit.app
            ((modulePullback B S hS (D.sourceProjection T₂)).obj D.F) ≫
            (modulePushforward B S hS (D.relativeMap h₂)).map
              (D.restrictBaseChangeModuleIso h₂).hom) ≫
        (modulePushforwardCompIso B S hS (D.relativeMap h₂) (D.relativeMap g) ≪≫
          eqToIso (congrArg (modulePushforward B S hS) (D.relativeMap_comp h₂ g))).hom.app
          ((modulePullback B S hS (D.sourceProjection T)).obj D.F) :=
  modulePullbackAdjunction_unit_map_of_triangle (k := D.relativeMap (h₂ ≫ g))
    (F₁ := (modulePullback B S hS (D.sourceProjection T₁)).obj D.F)
    (F₂ := (modulePullback B S hS (D.sourceProjection T₂)).obj D.F)
    (F₀ := (modulePullback B S hS (D.sourceProjection T)).obj D.F)
    (D.relativeMap h₂) (D.relativeMap g) (D.relativeMap_comp h₂ g)
    (D.restrictBaseChangeModuleIso g) (D.restrictBaseChangeModuleIso h₂)
    (D.restrictBaseChangeModuleIso (h₂ ≫ g)) (D.restrictBaseChangeModuleIso_comp_hom h₂ g)

end QuotientSituation

end AlgebraicGeometry.Space

end
