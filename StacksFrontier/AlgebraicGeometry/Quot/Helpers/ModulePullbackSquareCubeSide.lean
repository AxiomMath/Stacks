module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ThickeningCubeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroUnderivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PullRestrictionTranspose

/-!
# The comparison of iterated inverse images around a square, in the two spellings

For a commuting square `i ≫ f = k = p ≫ t` of morphisms of algebraic spaces, the comparison
`f^* ⋙ i^* ≅ t^* ⋙ p^*` of iterated inverse images of modules of Stacks 03LU is written in two
ways in the development: `AlgebraicGeometry.Space.modulePullbackSquare`, through the inverse
image `AlgebraicGeometry.Space.modulePullback` of the modules development, and
`Deformation.ToposThickening.cubeSideIso` at the adjunctions
`AlgebraicGeometry.Space.spaceModuleAdj` of the morphisms of small étale ringed topoi. The two
inverse images are equal functors
(`AlgebraicGeometry.Space.pullbackModules_toModulesHom_eq_modulePullback`), and the two
comparisons agree up to the identifications of the objects this equality gives
(`AlgebraicGeometry.Space.modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app`).

This module is a helper and carries no `@[stacks]` attribute.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

-- The instance search of `AlgebraicGeometry.Space.homEquiv_thickeningIdealMap`'s file, so that the
-- instance terms of the small étale sites agree with it.
attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]

/-- Retyping the left adjoint of an adjunction along the identity equality changes nothing. -/
private theorem ofNatIsoLeft_eqToIso_rfl {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (a : L ⊣ R) :
    a.ofNatIsoLeft (eqToIso rfl) = a :=
  Adjunction.ext (NatTrans.ext (funext fun X => by simp [Adjunction.ofNatIsoLeft]))

/-- **A comparison of left adjoints is unchanged by retyping the left adjoints along equalities
of functors**, up to the identifications of the objects these equalities give. -/
theorem leftAdjointCompIso_hom_app_of_eq_ofNatIsoLeft_eqToIso {L₁ L₁' : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀}
    {L₂ L₂' : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁} {L₃ L₃' : C₀ ⥤ C₂} {R₃ : C₂ ⥤ C₀} (a₁ : L₁ ⊣ R₁)
    (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₁' : L₁' ⊣ R₁) (a₂' : L₂' ⊣ R₂) (a₃' : L₃' ⊣ R₃)
    (h₁ : L₁ = L₁') (h₂ : L₂ = L₂') (h₃ : L₃ = L₃')
    (ha₁ : a₁' = a₁.ofNatIsoLeft (eqToIso h₁)) (ha₂ : a₂' = a₂.ofNatIsoLeft (eqToIso h₂))
    (ha₃ : a₃' = a₃.ofNatIsoLeft (eqToIso h₃)) (e : R₂ ⋙ R₁ ≅ R₃) (X : C₀) :
    (leftAdjointCompIso a₁' a₂' a₃' e).hom.app X =
      eqToHom (congrArg (fun F => F.obj X) (congrArg₂ (· ⋙ ·) h₁ h₂)).symm ≫
        (leftAdjointCompIso a₁ a₂ a₃ e).hom.app X ≫
        eqToHom (congrArg (fun F => F.obj X) h₃) := by
  subst h₁ h₂ h₃ ha₁ ha₂ ha₃
  rw [ofNatIsoLeft_eqToIso_rfl, ofNatIsoLeft_eqToIso_rfl, ofNatIsoLeft_eqToIso_rfl]
  simp

end CategoryTheory.Adjunction

namespace Deformation.ToposThickening

/-- **A comparison around a square given by two triangles is the comparison of left adjoints
around the square.** If two isomorphisms `τ₁ : M_k ≅ M_f ⋙ M_i` and `τ₂ : M_k ≅ M_t ⋙ M_p`,
between functors equal to the left adjoints, have inverses the comparisons of left adjoints of
the two triangles, then `τ₁⁻¹ ≫ τ₂` at an object is `Deformation.ToposThickening.cubeSideIso`,
between the identifications of the objects. -/
theorem inv_app_comp_hom_app_eq_cubeSideIso_hom_app {𝒱 𝒴 𝒯 𝒯' : Type*} [Category* 𝒱]
    [Category* 𝒴] [Category* 𝒯] [Category* 𝒯'] {Li : 𝒴 ⥤ 𝒱} {Ri : 𝒱 ⥤ 𝒴} (ai : Li ⊣ Ri)
    {Lf : 𝒯' ⥤ 𝒴} {Rf : 𝒴 ⥤ 𝒯'} (af : Lf ⊣ Rf) {Lt : 𝒯' ⥤ 𝒯} {Rt : 𝒯 ⥤ 𝒯'} (at' : Lt ⊣ Rt)
    {Lp : 𝒯 ⥤ 𝒱} {Rp : 𝒱 ⥤ 𝒯} (ap : Lp ⊣ Rp) {Lk : 𝒯' ⥤ 𝒱} {Rk : 𝒱 ⥤ 𝒯'} (ak : Lk ⊣ Rk)
    (a : Ri ⋙ Rf ≅ Rk) (b : Rp ⋙ Rt ≅ Rk) {Mi : 𝒴 ⥤ 𝒱} {Mf : 𝒯' ⥤ 𝒴} {Mt : 𝒯' ⥤ 𝒯}
    {Mp : 𝒯 ⥤ 𝒱} {Mk : 𝒯' ⥤ 𝒱} (hi : Li = Mi) (hf : Lf = Mf) (ht : Lt = Mt) (hp : Lp = Mp)
    (hk : Lk = Mk) (τ₁ : Mk ≅ Mf ⋙ Mi) (τ₂ : Mk ≅ Mt ⋙ Mp) (N : 𝒯')
    (h₁ : τ₁.inv.app N =
      eqToHom (congrArg (fun F => F.obj N) (congrArg₂ (· ⋙ ·) hf hi)).symm ≫
        (Adjunction.leftAdjointCompIso af ai ak a).hom.app N ≫
        eqToHom (congrArg (fun F => F.obj N) hk))
    (h₂ : τ₂.inv.app N =
      eqToHom (congrArg (fun F => F.obj N) (congrArg₂ (· ⋙ ·) ht hp)).symm ≫
        (Adjunction.leftAdjointCompIso at' ap ak b).hom.app N ≫
        eqToHom (congrArg (fun F => F.obj N) hk)) :
    τ₁.inv.app N ≫ τ₂.hom.app N =
      eqToHom (congrArg (fun F => F.obj N) (congrArg₂ (· ⋙ ·) hf hi)).symm ≫
        (cubeSideIso ap ai af at' ak a b).hom.app N ≫
        eqToHom (congrArg (fun F => F.obj N) (congrArg₂ (· ⋙ ·) ht hp)) := by
  subst hi hf ht hp hk
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h₁ h₂ ⊢
  have e := (Iso.inv_eq_inv (τ₂.app N)
    ((Adjunction.leftAdjointCompIso at' ap ak b).app N).symm).1 h₂
  simp only [Iso.app_hom, Iso.symm_hom, Iso.app_inv] at e
  simp only [cubeSideIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, h₁, e]

end Deformation.ToposThickening

namespace Stacks.Sheaves.RingedToposModules

universe v u w v' u' w'

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The Stacks 03D7 adjunction at two equal four-field morphisms of ringed topoi**, each with
its right adjoint retyped to a common functor `R` along compatible isomorphisms: the second is
the first with its left adjoint retyped along the equality of the two pullbacks. -/
theorem pullbackAdjPushforwardModules_ofNatIsoRight_eq_ofNatIsoLeft {φ φ' : RingedToposHom X Y}
    (h : φ = φ') {R : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (α : pushforwardModules φ ≅ R) (β : pushforwardModules φ' ≅ R)
    (hαβ : eqToIso (congrArg (fun ψ ↦ pushforwardModules ψ) h) ≪≫ β = α) :
    (pullbackAdjPushforwardModules φ').ofNatIsoRight β =
      ((pullbackAdjPushforwardModules φ).ofNatIsoRight α).ofNatIsoLeft
        (eqToIso (congrArg (fun ψ ↦ RingedToposHom.pullbackModules ψ) h)) := by
  subst h hαβ
  exact Adjunction.ext (NatTrans.ext (funext fun M => by
    simp [Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft]))

end Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The pullback of modules along the morphism of small étale ringed topoi of a morphism of
algebraic spaces is the inverse image of modules of Stacks 03LU. -/
theorem pullbackModules_toModulesHom_eq_modulePullback (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules = modulePullback B S hS f :=
  congrArg (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
    (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) ↦ ψ.pullbackModules)
      (smallEtaleRingedToposHom B S hS f).toModulesHom_eq_toRingedToposModulesHom

/-- The adjunction of the morphism of small étale ringed topoi through the four-field reading
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` is the one through
`AlgebraicGeometry.RingedToposHom.toModulesHom`, with its left adjoint retyped along the equality
of the two pullbacks. -/
theorem etaleModuleAdjunction_eq_spaceModuleAdj_ofNatIsoLeft (f : X ⟶ Y) :
    etaleModuleAdjunction f = (spaceModuleAdj f).ofNatIsoLeft
      (eqToIso (pullbackModules_toModulesHom_eq_modulePullback f)) :=
  Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules_ofNatIsoRight_eq_ofNatIsoLeft
    (smallEtaleRingedToposHom B S hS f).toModulesHom_eq_toRingedToposModulesHom _ _
    (RingedToposHom.eqToIso_trans_pushforwardModulesIso (smallEtaleRingedToposHom B S hS f))

/-- **The comparison `g^* ⋙ f^* ≅ (f ≫ g)^*` of Stacks 03LU in the two spellings**, at an
object: it is the comparison of left adjoints of the adjunctions
`AlgebraicGeometry.Space.spaceModuleAdj`, between the identifications of the two spellings of
the iterated inverse images. -/
theorem modulePullbackCompIso_hom_app_eq_leftAdjointCompIso_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackCompIso B S hS f g).hom.app N =
      eqToHom (congrArg (fun F => F.obj N)
          (congrArg₂ (· ⋙ ·) (pullbackModules_toModulesHom_eq_modulePullback g)
            (pullbackModules_toModulesHom_eq_modulePullback f))).symm ≫
        (Adjunction.leftAdjointCompIso (spaceModuleAdj g) (spaceModuleAdj f)
          (spaceModuleAdj (f ≫ g)) (modulePushforwardCompIso' B S hS f g)).hom.app N ≫
        eqToHom (congrArg (fun F => F.obj N)
          (pullbackModules_toModulesHom_eq_modulePullback (f ≫ g))) := by
  rw [← pushforwardModulesCompAt_eq_modulePushforwardCompIso']
  exact (congrArg (fun i => i.hom.app N)
    (modulePullbackCompIso_eq_leftAdjointCompIso_etale f g)).trans
    (Adjunction.leftAdjointCompIso_hom_app_of_eq_ofNatIsoLeft_eqToIso _ _ _ _ _ _
      (pullbackModules_toModulesHom_eq_modulePullback g)
      (pullbackModules_toModulesHom_eq_modulePullback f)
      (pullbackModules_toModulesHom_eq_modulePullback (f ≫ g))
      (etaleModuleAdjunction_eq_spaceModuleAdj_ofNatIsoLeft g)
      (etaleModuleAdjunction_eq_spaceModuleAdj_ofNatIsoLeft f)
      (etaleModuleAdjunction_eq_spaceModuleAdj_ofNatIsoLeft (f ≫ g)) _ N)

/-- **The comparison `k^* ≅ g^* ⋙ f^*` of Stacks 03LU for `f ≫ g = k` in the two spellings**, at an
object. -/
theorem modulePullbackTriangle_inv_app_eq_leftAdjointCompIso_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (hk : f ≫ g = k) (N : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackTriangle B S hS hk).inv.app N =
      eqToHom (congrArg (fun F => F.obj N)
          (congrArg₂ (· ⋙ ·) (pullbackModules_toModulesHom_eq_modulePullback g)
            (pullbackModules_toModulesHom_eq_modulePullback f))).symm ≫
        (Adjunction.leftAdjointCompIso (spaceModuleAdj g) (spaceModuleAdj f)
          (spaceModuleAdj k) (modulePushforwardCompIsoOfEq f g k hk)).hom.app N ≫
        eqToHom (congrArg (fun F => F.obj N)
          (pullbackModules_toModulesHom_eq_modulePullback k)) := by
  subst hk
  have hc :
      modulePushforwardCompIsoOfEq f g (f ≫ g) rfl = modulePushforwardCompIso' B S hS f g := by
    simp [modulePushforwardCompIsoOfEq]
  rw [modulePullbackTriangle_rfl, Iso.symm_inv, hc]
  exact modulePullbackCompIso_hom_app_eq_leftAdjointCompIso_hom_app f g N

/-- `AlgebraicGeometry.Space.modulePullbackSquare` at an object, as the composite of its two
triangles. -/
theorem modulePullbackSquare_hom_app_eq_comp {V W T T' : AlgebraicSpaces B S hS}
    {p : V ⟶ T} {i : V ⟶ W} {f : W ⟶ T'} {t : T ⟶ T'} {kk : V ⟶ T'} (hf : i ≫ f = kk)
    (ht : p ≫ t = kk) (N : Modules.{u, u} B S hS T'.1 T'.2) :
    (modulePullbackSquare B S hS hf ht).hom.app N =
      (modulePullbackTriangle B S hS hf).inv.app N ≫ (modulePullbackTriangle B S hS ht).hom.app N :=
  rfl

/-- **The comparison of iterated inverse images around a commuting square `i ≫ f = k = p ≫ t`
in the two spellings**: `AlgebraicGeometry.Space.modulePullbackSquare` is
`Deformation.ToposThickening.cubeSideIso` of the adjunctions
`AlgebraicGeometry.Space.spaceModuleAdj` (the body of `AlgebraicGeometry.Space.spaceCubeSideIso`)
between the identifications of the two spellings of the iterated inverse images. -/
theorem modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app {V W T T' : AlgebraicSpaces B S hS}
    (p : V ⟶ T) (i : V ⟶ W) (f : W ⟶ T') (t : T ⟶ T') (kk : V ⟶ T') (hf : i ≫ f = kk)
    (ht : p ≫ t = kk) (N : Modules.{u, u} B S hS T'.1 T'.2) :
    (modulePullbackSquare B S hS hf ht).hom.app N =
      eqToHom (congrArg (fun F => F.obj N)
          (congrArg₂ (· ⋙ ·) (pullbackModules_toModulesHom_eq_modulePullback f)
            (pullbackModules_toModulesHom_eq_modulePullback i))).symm ≫
        (Deformation.ToposThickening.cubeSideIso (spaceModuleAdj p) (spaceModuleAdj i)
          (spaceModuleAdj f) (spaceModuleAdj t) (spaceModuleAdj kk)
          (modulePushforwardCompIsoOfEq i f kk hf)
          (modulePushforwardCompIsoOfEq p t kk ht)).hom.app N ≫
        eqToHom (congrArg (fun F => F.obj N)
          (congrArg₂ (· ⋙ ·) (pullbackModules_toModulesHom_eq_modulePullback t)
            (pullbackModules_toModulesHom_eq_modulePullback p))) := by
  have k₁ := modulePullbackTriangle_inv_app_eq_leftAdjointCompIso_hom_app i f kk hf N
  have k₂ := modulePullbackTriangle_inv_app_eq_leftAdjointCompIso_hom_app p t kk ht N
  have k := Deformation.ToposThickening.inv_app_comp_hom_app_eq_cubeSideIso_hom_app
    (spaceModuleAdj i) (spaceModuleAdj f) (spaceModuleAdj t) (spaceModuleAdj p) (spaceModuleAdj kk)
    (modulePushforwardCompIsoOfEq i f kk hf) (modulePushforwardCompIsoOfEq p t kk ht)
    (pullbackModules_toModulesHom_eq_modulePullback i)
    (pullbackModules_toModulesHom_eq_modulePullback f)
    (pullbackModules_toModulesHom_eq_modulePullback t)
    (pullbackModules_toModulesHom_eq_modulePullback p)
    (pullbackModules_toModulesHom_eq_modulePullback kk)
    (modulePullbackTriangle B S hS hf) (modulePullbackTriangle B S hS ht) N k₁ k₂
  rw [modulePullbackSquare_hom_app_eq_comp]
  exact k

end AlgebraicGeometry.Space
