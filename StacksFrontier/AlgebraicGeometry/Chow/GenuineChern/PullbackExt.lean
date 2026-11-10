module

public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Epi
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafCorepresentable

/-!
# Morphisms out of the pullback of a quasi-coherent module are determined over an affine open

Let `f : Y ⟶ X` be a morphism of schemes mapping into an affine open `U` of `X`, and let `ℰ` be a
quasi-coherent `𝒪_X`-module. A morphism `f^*ℰ ⟶ 𝒩` is determined by its values on the pullbacks
`f^*x` of the sections `x ∈ Γ(U, ℰ)`.

The adjoint transposes `ℰ ⟶ f_*𝒩` of two such morphisms agree on `Γ(U, ℰ)`; over a basic open
`D(g) ⊆ U` the sections of `ℰ` are the localization of `Γ(U, ℰ)` at `g`, and `g` acts invertibly
on `Γ(f⁻¹D(g), 𝒩)`, so the transposes agree there; and the preimages of those basic opens cover
the preimage of every open of `X`.

## Main results

* `Stacks.Chow.GenuineChern.pullback_hom_ext_of_isAffineOpen`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne

universe u

namespace Stacks.Chow.GenuineChern

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
  (hfU : f ⁻¹ᵁ U = ⊤) (E : X.Modules) [E.IsQuasicoherent] {N : Y.Modules}

omit [E.IsQuasicoherent] in
/-- The adjoint transpose of a morphism out of a pullback, read on sections. -/
theorem homEquiv_app_apply (φ : (Scheme.Modules.pullback f).obj E ⟶ N) (V : X.Opens)
    (x : Γ(E, V)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E N φ).val.app (op V)) x =
      φ.val.app (op (f ⁻¹ᵁ V)) (unitSection f E V x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

include hU in
/-- Over a basic open of `U`, two morphisms `ℰ ⟶ f_*𝒩` agreeing on `Γ(U, ℰ)` agree. -/
theorem app_basicOpen_eq {t₁ t₂ : E ⟶ (Scheme.Modules.pushforward f).obj N}
    (h : ∀ x : Γ(E, U), t₁.app U x = t₂.app U x) (g : Γ(X, U))
    (z : Γ(E, X.basicOpen g)) :
    t₁.app (X.basicOpen g) z = t₂.app (X.basicOpen g) z := by
  let : Module Γ(X, U) Γ(E, X.basicOpen g) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen g) Γ(E, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let ρ : Γ(E, U) →ₗ[Γ(X, U)] Γ(E, X.basicOpen g) :=
    { toFun a := E.presheaf.map (homOfLE (X.basicOpen_le g)).op a
      map_add' a b := map_add _ a b
      map_smul' r a := Scheme.Modules.map_smul E (homOfLE (X.basicOpen_le g)) r a }
  have hloc : IsLocalizedModule (Submonoid.powers g) ρ :=
    isLocalizedModule_restrict_basicOpen E hU g ρ fun _ => rfl
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := hloc.surj z
  -- `g ^ n • z` is the restriction of `x`
  have hx' : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ n) • z =
      E.presheaf.map (homOfLE (X.basicOpen_le g)).op x := hx
  have key : ∀ t : E ⟶ (Scheme.Modules.pushforward f).obj N,
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ n) •
          t.app (X.basicOpen g) z =
        ((Scheme.Modules.pushforward f).obj N).presheaf.map (homOfLE (X.basicOpen_le g)).op
          (t.app U x) := by
    intro t
    rw [← Scheme.Modules.Hom.app_smul t]
    refine (congrArg (fun w => t.app (X.basicOpen g) w) hx').trans ?_
    exact (PresheafOfModules.naturality_apply t.val (homOfLE (X.basicOpen_le g)).op x)
  have hunit : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ n)) := by
    rw [map_pow]
    exact (X.toRingedSpace.isUnit_res_basicOpen g).pow n
  obtain ⟨w, hw⟩ := hunit
  have e₁ := key t₁
  have e₂ := key t₂
  rw [h x, ← e₂, ← hw] at e₁
  have := congrArg (fun m => (↑w⁻¹ : Γ(X, X.basicOpen g)) • m) e₁
  simpa only [smul_smul, Units.inv_mul, one_smul] using this

include hU hfU in
/-- **A morphism out of the pullback of a quasi-coherent module along a morphism into an affine
open `U` is determined by its values on the pulled-back sections over `U`.** -/
theorem pullback_hom_ext_of_isAffineOpen {φ ψ : (Scheme.Modules.pullback f).obj E ⟶ N}
    (h : ∀ x : Γ(E, U), φ.val.app (op (f ⁻¹ᵁ U)) (unitSection f E U x) =
      ψ.val.app (op (f ⁻¹ᵁ U)) (unitSection f E U x)) :
    φ = ψ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E N).injective
  set t₁ := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E N φ
  set t₂ := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E N ψ
  have hU' : ∀ x : Γ(E, U), t₁.app U x = t₂.app U x := fun x => by
    change t₁.val.app (op U) x = t₂.val.app (op U) x
    rw [homEquiv_app_apply, homEquiv_app_apply]
    exact h x
  have hUW : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ U := hfU.ge
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext y
  refine Stacks.Smooth.section_ext_of_restrict_basicOpen f N hU hUW V _ _ fun g hg => ?_
  have n₁ := PresheafOfModules.naturality_apply t₁.val (homOfLE hg).op y
  have n₂ := PresheafOfModules.naturality_apply t₂.val (homOfLE hg).op y
  change ((Scheme.Modules.pushforward f).obj N).presheaf.map (homOfLE hg).op
      (t₁.app V y) =
    ((Scheme.Modules.pushforward f).obj N).presheaf.map (homOfLE hg).op (t₂.app V y)
  exact n₁.symm.trans ((app_basicOpen_eq f hU E hU' g _).trans n₂)

end Stacks.Chow.GenuineChern

end
