module

public import StacksFrontier.AlgebraicGeometry.Discriminant.BaseLocalization
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingComposition.Trace
public import StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization
public import StacksFrontier.RingTheory.TraceElement.BaseLocalization

/-!
# Transport of relative dualizing modules along target isomorphisms and Tag 0BT2

Let `A → B` be a quasi-finite algebra and `σ : B ≃ C` an isomorphism of `A`-algebras. Transport
of relative dualizing modules along `σ` (`Stacks.Discriminant.dualizingModule.retargetDualizingMap`)
commutes with the two localization identifications of Tag 0BT2: localizing the base
(part (1)) and localizing the target (part (2)).

## Main results

* `Stacks.Discriminant.retargetDualizingMap_dualizingModule_equiv_of_isLocalization_away`:
  compatibility with part (1).
* `Stacks.Discriminant.retargetDualizingMap_dualizingModuleEquiv_locFact`: compatibility with
  the canonical localization map of part (2).
* `Stacks.Discriminant.localizationMap_eq_of_localizedModule_dualizingModule_equiv_eq_id`: a
  normalized localization map of part (2) is that canonical map.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public section

universe u v w x y z

namespace Stacks.Discriminant

open scoped TensorProduct

attribute [local instance] algebraDualModule

/-- Transporting a functional along an isomorphism of the intermediate algebras commutes with the
comparison isomorphisms of dualizing modules. -/
private theorem dualizingModuleEquiv_tmul_of_equiv
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C] [IsNoetherianRing A]
    (X : FiniteOpenFactorization.{u, v, x} A C) (Y : FiniteOpenFactorization.{u, v, y} A C)
    (Z : FiniteOpenFactorization.{u, v, z} A C) (e : X.middle ≃ₐ[A] Y.middle)
    (he : ∀ c : X.middle, algebraMap Y.middle C (e c) = algebraMap X.middle C c)
    (φ : Module.Dual A Y.middle) (c : C) :
    dualizingModuleEquiv Y Z (dualizingModule.tmul Y φ c) =
      dualizingModuleEquiv X Z (dualizingModule.tmul X (φ.comp e.toLinearMap) c) := by
  rw [← comparison_restrict_of_equiv X Y e he, ← LinearEquiv.trans_apply,
    dualizingModuleEquiv_trans]

/-- Transport along an isomorphism of the target commutes with the base-localization
identification of Tag 0BT2 part (1). -/
theorem retargetDualizingMap_dualizingModule_equiv_of_isLocalization_away
    {A : Type u} {B : Type v} {C : Type z} {Af : Type w}
    [CommRing A] [CommRing B] [CommRing C] [CommRing Af]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    [Algebra A C] [Algebra Af C] [IsScalarTower A Af C]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    [IsNoetherianRing C] [Algebra.QuasiFinite A C]
    (f : A) [IsLocalization.Away f Af]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{w, v, y} Af B)
    (σ : B ≃ₐ[A] C) (σf : B ≃ₐ[Af] C) (hσ : ∀ b, σf b = σ b) (m : dualizingModule F) :
    letI : IsNoetherianRing Af :=
      IsLocalization.isNoetherianRing (Submonoid.powers f) Af inferInstance
    dualizingModule.retargetDualizingMap G σf
        (dualizingModule_equiv_of_isLocalization_away f F G m) =
      dualizingModule_equiv_of_isLocalization_away f (dualizingModule.retargetFactorization F σ)
        (dualizingModule.retargetFactorization G σf)
        (dualizingModule.retargetDualizingMap F σ m) := by
  let : IsNoetherianRing Af :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) Af inferInstance
  induction m using dualizingModule.induction_on F with
  | zero => simp only [map_zero]
  | add m n hm hn => simp only [map_add, hm, hn]
  | tmul φ b =>
    rw [dualizingModule_equiv_of_isLocalization_away_formula,
      dualizingModule.retargetDualizingMap_tmul,
      dualizingModule_equiv_of_isLocalization_away_formula,
      dualizingModule.retargetDualizingMap_naturality]
    refine (congrArg (dualizingModuleEquiv _ _)
      (dualizingModule.retargetDualizingMap_tmul _ σf _ b)).trans ?_
    let : Algebra C (Af ⊗[A] C) := Algebra.TensorProduct.rightAlgebra
    let : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    let : IsScalarTower Af B (Af ⊗[A] B) := isScalarTower_tensorProduct_of_isLocalizationAway f
    let : IsScalarTower Af C (Af ⊗[A] C) := isScalarTower_tensorProduct_of_isLocalizationAway f
    rw [hσ]
    let X := retargetFactorization ((dualizingModule.retargetFactorization F σ).baseChange Af)
      (AlgEquiv.restrictScalars Af (baseChangeTargetEquiv f))
    let Y := dualizingModule.retargetFactorization (retargetFactorization (F.baseChange Af)
      (AlgEquiv.restrictScalars Af (baseChangeTargetEquiv f))) σf
    have hE : ∀ c : Af ⊗[A] F.middle, algebraMap Y.middle C c = algebraMap X.middle C c := by
      intro c
      induction c using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | add c d hc hd =>
        exact (map_add _ c d).trans ((congrArg₂ (· + ·) hc hd).trans (map_add _ c d).symm)
      | tmul a m =>
        show σf (baseChangeTargetAlgEquiv f (a ⊗ₜ[A] algebraMap F.middle B m)) =
          baseChangeTargetAlgEquiv f (a ⊗ₜ[A] σ (algebraMap F.middle B m))
        rw [baseChangeTargetAlgEquiv_tmul, baseChangeTargetAlgEquiv_tmul, map_mul,
          AlgEquiv.commutes, hσ]
    exact dualizingModuleEquiv_tmul_of_equiv X Y _ AlgEquiv.refl hE _ _

/-- Transport along compatible isomorphisms of a target and of its away localization commutes
with the canonical localization map `ω_F → ω_G` of Tag 0BT2 part (2). -/
theorem retargetDualizingMap_dualizingModuleEquiv_locFact
    {A : Type u} {B : Type v} {Bg : Type w} {C : Type y} {Cg : Type z}
    [CommRing A] [CommRing B] [CommRing Bg] [CommRing C] [CommRing Cg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [Algebra A C] [Algebra C Cg] [Algebra A Cg] [IsScalarTower A C Cg]
    [IsNoetherianRing A]
    (g : B) [IsLocalization.Away g Bg] (σ : B ≃ₐ[A] C) (σg : Bg ≃ₐ[A] Cg)
    [IsLocalization.Away (σ g) Cg]
    (hσ : ∀ b, σg (algebraMap B Bg b) = algebraMap C Cg (σ b))
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{u, w, x} A Bg) (m : dualizingModule F) :
    dualizingModule.retargetDualizingMap G σg (dualizingModuleEquiv (locFact (Bg := Bg) g F) G
        (dualizingTensorLocalizationEquiv (Bg := Bg) g F
          (targetLocalizationMap (Bg := Bg) g F m))) =
      dualizingModuleEquiv (locFact (Bg := Cg) (σ g) (dualizingModule.retargetFactorization F σ))
        (dualizingModule.retargetFactorization G σg)
        (dualizingTensorLocalizationEquiv (Bg := Cg) (σ g)
          (dualizingModule.retargetFactorization F σ)
          (targetLocalizationMap (Bg := Cg) (σ g) (dualizingModule.retargetFactorization F σ)
            (dualizingModule.retargetDualizingMap F σ m))) := by
  induction m using dualizingModule.induction_on F with
  | zero => simp only [map_zero]
  | add m n hm hn => simp only [map_add, hm, hn]
  | tmul φ b =>
    rw [dualizingTensorLocalizationEquiv_tmul, dualizingModule.retargetDualizingMap_tmul,
      dualizingTensorLocalizationEquiv_tmul, dualizingModule.retargetDualizingMap_naturality]
    refine (congrArg (dualizingModuleEquiv _ _)
      (dualizingModule.retargetDualizingMap_tmul _ σg _ _)).trans ?_
    rw [hσ]
    exact dualizingModuleEquiv_tmul_of_equiv
      (locFact (Bg := Cg) (σ g) (dualizingModule.retargetFactorization F σ))
      (dualizingModule.retargetFactorization (locFact (Bg := Bg) g F) σg) _
      AlgEquiv.refl (fun c => hσ _) _ _

/-- A localization map whose induced comparison of Tag 0BT2 part (2) is the identity is the
canonical localization map `ω_F → ω_{F_g} ≅ ω_G`. -/
theorem localizationMap_eq_of_localizedModule_dualizingModule_equiv_eq_id
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{u, w, y} A Bg)
    [Module B (dualizingModule G)] [IsScalarTower B Bg (dualizingModule G)]
    (r : dualizingModule F →ₗ[B] dualizingModule G)
    (hr : IsLocalizedModule (Submonoid.powers g) r)
    (h : ∀ m, localizedModule_dualizingModule_equiv g F G r hr m = m) (m : dualizingModule F) :
    r m = dualizingModuleEquiv (locFact (Bg := Bg) g F) G
      (dualizingTensorLocalizationEquiv (Bg := Bg) g F (targetLocalizationMap (Bg := Bg) g F m)) :=
  (h (r m)).symm.trans (localizedModule_dualizingModule_equiv_apply g F G r hr m)

end Stacks.Discriminant
