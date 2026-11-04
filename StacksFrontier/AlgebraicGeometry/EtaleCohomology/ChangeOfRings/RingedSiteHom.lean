module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.DirectImage
public import StacksFrontier.CategoryTheory.Sites.Modules.CoefficientChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ChangeOfRings.Restriction

/-!
# Change of coefficient rings on the constant ringed small étale site

Let `φ : Λ₁ ⟶ Λ₂` be a homomorphism of commutative rings and let `X` be a scheme. The map of
constant sheaves of rings `Λ̲₁ ⟶ Λ̲₂` on the small model `Stacks.EtaleCohomology.etaleRingedSite`
of `X_étale` presents a morphism of ringed topoi `(X_étale, Λ̲₂) ⟶ (X_étale, Λ̲₁)` over the
identity of the site (`AlgebraicGeometry.RingedToposSiteHom.coefficientChange`). Its pushforward
of sheaves of modules is, read through the identifications
`Stacks.EtaleCohomology.etaleModulesEquivalence` of sheaves of `Λ̲ᵢ`-modules with sheaves of
`Λᵢ`-modules, the restriction of scalars `Stacks.EtaleCohomology.ChangeOfRings.restrictScalars`.

## Main definitions

* `Stacks.EtaleCohomology.ChangeOfRings.ringMap`: the map `Λ̲₁ ⟶ Λ̲₂` induced by `φ`.
* `Stacks.EtaleCohomology.ChangeOfRings.coefficientChangeHom`: the morphism of ringed topoi.
* `Stacks.EtaleCohomology.ChangeOfRings.pushforwardIso`: the comparison of its pushforward with
  restriction of scalars.

## Main results

* `Stacks.EtaleCohomology.ChangeOfRings.ringMap_constantRingedSiteRingMap`: `ringMap` sends the
  constant `a` to the constant `φ a`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u r

namespace Stacks.EtaleCohomology.ChangeOfRings

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂) (X : Scheme.{u})

/-- `φ` on the lifts of the two rings to the coefficient universe. -/
abbrev uliftRingHom : ULift.{max (u + 1) r} Λ₁ →+* ULift.{max (u + 1) r} Λ₂ :=
  (ULift.ringEquiv : ULift.{max (u + 1) r} Λ₂ ≃+* Λ₂).symm.toRingHom.comp
    (φ.comp (ULift.ringEquiv : ULift.{max (u + 1) r} Λ₁ ≃+* Λ₁).toRingHom)

/-- The presheaf map `Λ₁ ⟶ Γ(-, Λ̲₂)` sending a constant `a` to the constant `φ a`. -/
abbrev presheafRingMap :
    (Functor.const (AsSmall.{max (u + 1) r} X.Etale)ᵒᵖ).obj
        (CommRingCat.of (ULift.{max (u + 1) r} Λ₁)) ⟶
      (etaleRingedSite.{u, r} Λ₂ X).O.obj :=
  (Functor.const _).map (CommRingCat.ofHom (uliftRingHom.{u, r} φ)) ≫
    toSheafify (etaleSmallModelTopology.{u, r} X)
      ((Functor.const (AsSmall.{max (u + 1) r} X.Etale)ᵒᵖ).obj
        (CommRingCat.of (ULift.{max (u + 1) r} Λ₂)))

/-- The map `Λ̲₁ ⟶ Λ̲₂` of constant sheaves of rings induced by `φ`. -/
def ringMap : (etaleRingedSite.{u, r} Λ₁ X).O ⟶ (etaleRingedSite.{u, r} Λ₂ X).O :=
  ObjectProperty.homMk (sheafifyLift (etaleSmallModelTopology.{u, r} X)
    (presheafRingMap.{u, r} φ X) (etaleRingedSite.{u, r} Λ₂ X).O.property)

/-- `ringMap` restricted to the constant presheaf is the map sending a constant to its image. -/
theorem toSheafify_ringMap :
    toSheafify (etaleSmallModelTopology.{u, r} X)
        ((Functor.const (AsSmall.{max (u + 1) r} X.Etale)ᵒᵖ).obj
          (CommRingCat.of (ULift.{max (u + 1) r} Λ₁))) ≫ (ringMap.{u, r} φ X).hom =
      presheafRingMap.{u, r} φ X :=
  toSheafify_sheafifyLift _ _ _

/-- The change of coefficient rings `(X_étale, Λ̲₂) ⟶ (X_étale, Λ̲₁)` along `φ`, a morphism of
ringed topoi over the identity of the small étale site. -/
abbrev coefficientChangeHom :=
  RingedToposSiteHom.coefficientChange.{max (u + 1) r, max (u + 1) r, max (u + 1) r}
    (etaleSmallModelTopology.{u, r} X) (ringMap.{u, r} φ X)

/-- **`ringMap` sends the constant `a` to the constant `φ a`**, read through the maps out of the
constant presheaves of rings. -/
theorem ringMap_constantRingedSiteRingMap (V : (AsSmall.{max (u + 1) r} X.Etale)ᵒᵖ)
    (a : ULift.{max (u + 1) r} Λ₁) :
    ((ringMap.{u, r} φ X).hom.app V).hom
        (((Stacks.ConstantRingModules.constantRingedSiteRingMap (etaleSmallModelTopology.{u, r} X)
          (ULift.{max (u + 1) r} Λ₁)).app V).hom a) =
      ((Stacks.ConstantRingModules.constantRingedSiteRingMap (etaleSmallModelTopology.{u, r} X)
          (ULift.{max (u + 1) r} Λ₂)).app V).hom (uliftRingHom.{u, r} φ a) := by
  rw [constantRingedSiteRingMap_app_apply, constantRingedSiteRingMap_app_apply]
  exact congrArg (fun ψ => (ψ.app V).hom a) (toSheafify_ringMap.{u, r} φ X)

/-- The sections over `V` of the restriction of scalars of a sheaf of `Λ̲₂`-modules `M` along
`ringMap`, read as a `Λ₁`-module. -/
abbrev pushforwardSections (M : EtaleRingedModules.{u, r} Λ₂ X) (V : X.Etaleᵒᵖ) :
    ModuleCat.{max (u + 1) r} Λ₁ :=
  ((etaleModulesEquivalence.{u, r} Λ₁ X).inverse.obj
    ((coefficientChangeHom.{u, r} φ X).pushforwardTopos.obj M)).obj.obj V

/-- The sections over `V` of the restriction of scalars along `φ` of the sheaf of
`Λ₂`-modules underlying `M`. -/
abbrev restrictSections (M : EtaleRingedModules.{u, r} Λ₂ X) (V : X.Etaleᵒᵖ) :
    ModuleCat.{max (u + 1) r} Λ₁ :=
  ((restrictScalars φ X).obj ((etaleModulesEquivalence.{u, r} Λ₂ X).inverse.obj M)).obj.obj V

/-- The two actions of `Λ₁` on the sections of `M` agree. -/
theorem pushforward_smul (M : EtaleRingedModules.{u, r} Λ₂ X) (V : X.Etaleᵒᵖ) (a : Λ₁)
    (x : pushforwardSections.{u, r} φ X M V) :
    (a • x : pushforwardSections.{u, r} φ X M V) =
      (a • (show restrictSections.{u, r} φ X M V from x) : restrictSections.{u, r} φ X M V) := by
  have h := ringMap_constantRingedSiteRingMap.{u, r} φ X
    (op ((AsSmall.up : X.Etale ⥤ AsSmall.{max (u + 1) r} X.Etale).obj V.unop)) (ULift.up a)
  exact congrArg (fun (s : (Stacks.SheafOfModules.Tensor.ringSheaf
      (etaleRingedSite.{u, r} Λ₂ X).O).obj.obj
        (op ((AsSmall.up : X.Etale ⥤ AsSmall.{max (u + 1) r} X.Etale).obj V.unop))) =>
    s • (show M.val.obj
      (op ((AsSmall.up : X.Etale ⥤ AsSmall.{max (u + 1) r} X.Etale).obj V.unop)) from x)) h

/-- The identity of the sections of `M`, as a `Λ₁`-linear map. -/
def pushforwardSectionsLinear (M : EtaleRingedModules.{u, r} Λ₂ X) (V : X.Etaleᵒᵖ) :
    pushforwardSections.{u, r} φ X M V →ₗ[Λ₁] restrictSections.{u, r} φ X M V where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' a x := pushforward_smul.{u, r} φ X M V a x

/-- The inverse of `pushforwardSectionsLinear`. -/
def restrictSectionsLinear (M : EtaleRingedModules.{u, r} Λ₂ X) (V : X.Etaleᵒᵖ) :
    restrictSections.{u, r} φ X M V →ₗ[Λ₁] pushforwardSections.{u, r} φ X M V where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' a x := (pushforward_smul.{u, r} φ X M V a x).symm

/-- **Restriction of scalars along the change of coefficient rings is restriction of scalars of
sheaves of modules**, read through the identifications of sheaves of `Λ̲ᵢ`-modules with sheaves
of `Λᵢ`-modules. -/
def pushforwardIso :
    (coefficientChangeHom.{u, r} φ X).pushforwardTopos ⋙
        (etaleModulesEquivalence.{u, r} Λ₁ X).inverse ≅
      (etaleModulesEquivalence.{u, r} Λ₂ X).inverse ⋙ restrictScalars φ X :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      (NatIso.ofComponents (fun V =>
        { hom := ModuleCat.homEquiv.symm (pushforwardSectionsLinear.{u, r} φ X M V)
          inv := ModuleCat.homEquiv.symm (restrictSectionsLinear.{u, r} φ X M V)
          hom_inv_id := rfl
          inv_hom_id := rfl })
        (fun _ => by ext; rfl)))
    (fun _ => by ext; rfl)

end Stacks.EtaleCohomology.ChangeOfRings

end
