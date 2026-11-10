module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleLocalization

/-!
# Localizing the relative dualizing module in the target

Let `A → B` be a quasi-finite map of Noetherian rings and `g` an element of `B`. The relative
dualizing module of the localization `B_g` over `A` is the localization of the relative
dualizing module of `B` over `A` away from `g`. This file constructs that identification for an
arbitrary model of the localized module, computes it on pure tensors, and shows that it does not
depend on either of the two finite-open factorizations involved.

## Main definitions

* `Stacks.Discriminant.localizedModule_dualizingModule_equiv` identifies a localization of the
  relative dualizing module away from `g` with the relative dualizing module of `B_g`.

## Main results

* `Stacks.Discriminant.localizedModule_dualizingModule_equiv_tmul` characterizes the
  identification on a pure tensor.
* `Stacks.Discriminant.localizedModule_dualizingModule_equiv_natural` and
  `Stacks.Discriminant.localizedModule_dualizingModule_equiv_natural_in_source` are its
  naturality in the factorization of `B_g`, and in both factorizations at once.

## Implementation notes

The localized module is taken as an abstract `IsLocalizedModule` over the powers of `g`, so the
statements apply to any model of it; the identification is obtained by comparing that model with
the concrete scalar extension `B_g ⊗[B] ω` of `Stacks.Discriminant.targetLocalizationMap`.

Because a map out of a localized module is determined by its composite with the localization
map, both naturality statements are reduced to an identity between maps out of the relative
dualizing module itself, and then to pure tensors.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public section

namespace Stacks.Discriminant

universe u v w x y z t q s

open Topology
open scoped TensorProduct

attribute [local instance] algebraDualModule

/-- **Stacks Project, Tag 0BT2, part (2).** Localizing the relative dualizing module away from
an element of the target gives the relative dualizing module of the localized target. -/
@[stacks 0BT2 "part (2)"]
public noncomputable def localizedModule_dualizingModule_equiv
    {A : Type u} {B : Type v} {Bg : Type w} {M : Type x}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, y} A B)
    (G : FiniteOpenFactorization.{u, w, z} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (localizationMap : dualizingModule F →ₗ[B] M)
    (hM : IsLocalizedModule (Submonoid.powers g) localizationMap) :
    M ≃ₗ[Bg] dualizingModule G := by
  let FLoc : FiniteOpenFactorization.{u, w, y} A Bg := locFact (Bg := Bg) g F
  let locMap := targetLocalizationMap (Bg := Bg) g F
  letI : IsLocalizedModule (Submonoid.powers g) locMap :=
    targetLocalizationMap_isLocalized g F
  let eLocB := IsLocalizedModule.linearEquiv
    (Submonoid.powers g) localizationMap locMap
  let e₁ := LinearEquiv.extendScalarsOfIsLocalization
    (Submonoid.powers g) Bg eLocB
  exact (e₁.trans (dualizingTensorLocalizationEquiv (Bg := Bg) g F)).trans
    (dualizingModuleEquiv FLoc G)

/-- The target-localization identification, computed on the image of the localization map
through the explicit factorization used to construct it. -/
theorem localizedModule_dualizingModule_equiv_apply
    {A : Type u} {B : Type v} {Bg : Type w} {M : Type x}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, y} A B)
    (G : FiniteOpenFactorization.{u, w, z} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (localizationMap : dualizingModule F →ₗ[B] M)
    (hM : IsLocalizedModule (Submonoid.powers g) localizationMap)
    (m : dualizingModule F) :
    localizedModule_dualizingModule_equiv g F G localizationMap hM
        (localizationMap m) =
      dualizingModuleEquiv (locFact (Bg := Bg) g F) G
        (dualizingTensorLocalizationEquiv (Bg := Bg) g F
          (targetLocalizationMap (Bg := Bg) g F m)) := by
  classical
  simp only [localizedModule_dualizingModule_equiv, LinearEquiv.trans_apply,
    LinearEquiv.extendScalarsOfIsLocalization_apply,
    IsLocalizedModule.linearEquiv_apply]

/-- On compatible finite-open factorizations, the target-localization map sends a pure tensor
to the tensor obtained by localizing its coefficient in the target. -/
@[stacks 0BT2 "part (2), characterization"]
public theorem localizedModule_dualizingModule_equiv_tmul
    {A : Type u} {B : Type v} {Bg : Type w} {M : Type x}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, y} A B)
    (G : FiniteOpenFactorization.{u, w, z} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (localizationMap : dualizingModule F →ₗ[B] M)
    (hM : IsLocalizedModule (Submonoid.powers g) localizationMap)
    (r : G.middle ≃ₐ[A] F.middle)
    (hr : ∀ c : G.middle,
      algebraMap B Bg (F.algebraTarget.algebraMap (r c)) =
        G.algebraTarget.algebraMap c)
    (φ : Module.Dual A F.middle) (b : B) :
    localizedModule_dualizingModule_equiv g F G localizationMap hM
        (localizationMap (dualizingModule.tmul F φ b)) =
      dualizingModule.tmul G (φ.comp r.toLinearMap) (algebraMap B Bg b) := by
  rw [localizedModule_dualizingModule_equiv_apply, dualizingTensorLocalizationEquiv_tmul]
  exact (comparison_restrict_of_local_annihilation (F := G)
    (H := locFact (Bg := Bg) g F) r.toAlgHom hr
    (locFact_local_annihilation (g := g) F G r hr) φ (algebraMap B Bg b)).trans (by congr 1)

/-- Two `B_g`-linear maps out of a localization of the dualizing module into the dualizing module
of `B_g` agree if they agree on the image of the localization map. -/
private theorem linearMap_ext_dualizingModule_localizedModule
    {A : Type u} {B : Type v} {Bg : Type w} {M : Type x}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, y} A B)
    (G' : FiniteOpenFactorization.{u, w, z} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (localizationMap : dualizingModule F →ₗ[B] M)
    (hM : IsLocalizedModule (Submonoid.powers g) localizationMap)
    {f₁ f₂ : M →ₗ[Bg] dualizingModule G'}
    (h : ∀ x, f₁ (localizationMap x) = f₂ (localizationMap x)) : f₁ = f₂ := by
  let : Module B (dualizingModule G') := Module.compHom _ (algebraMap B Bg)
  have : IsScalarTower B Bg (dualizingModule G') :=
    IsScalarTower.of_compHom (R := B) (A := Bg) (M := dualizingModule G')
  let eB := (localizedModule_dualizingModule_equiv g F G' localizationMap hM).restrictScalars B
  have := hM
  have : IsLocalizedModule (Submonoid.powers g) (eB.toLinearMap ∘ₗ localizationMap) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers g) localizationMap eB
  ext m
  exact LinearMap.congr_fun (IsLocalizedModule.linearMap_ext (Submonoid.powers g)
    localizationMap (eB.toLinearMap ∘ₗ localizationMap)
    (g := f₁.restrictScalars B) (g' := f₂.restrictScalars B) (LinearMap.ext h)) m

/-- The target-localization identification is natural in the finite-open factorization of the
localized algebra. -/
@[stacks 0BT2 "part (2), naturality"]
public theorem localizedModule_dualizingModule_equiv_natural
    {A : Type u} {B : Type v} {Bg : Type w} {M : Type x}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, y} A B)
    (G : FiniteOpenFactorization.{u, w, z} A Bg)
    (G' : FiniteOpenFactorization.{u, w, t} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (localizationMap : dualizingModule F →ₗ[B] M)
    (hM : IsLocalizedModule (Submonoid.powers g) localizationMap) (m : M) :
    dualizingModuleEquiv G G'
        (localizedModule_dualizingModule_equiv g F G localizationMap hM m) =
      localizedModule_dualizingModule_equiv g F G' localizationMap hM m := by
  refine LinearMap.congr_fun
    (linearMap_ext_dualizingModule_localizedModule g F G' localizationMap hM
    (f₁ := (dualizingModuleEquiv G G').toLinearMap ∘ₗ
      (localizedModule_dualizingModule_equiv g F G localizationMap hM).toLinearMap)
    (f₂ := (localizedModule_dualizingModule_equiv g F G' localizationMap hM).toLinearMap)
    fun x => ?_) m
  change dualizingModuleEquiv G G'
      (localizedModule_dualizingModule_equiv g F G localizationMap hM (localizationMap x)) =
    localizedModule_dualizingModule_equiv g F G' localizationMap hM (localizationMap x)
  rw [localizedModule_dualizingModule_equiv_apply, localizedModule_dualizingModule_equiv_apply,
    ← dualizingModuleEquiv_trans (F := locFact (Bg := Bg) g F) (G := G) (H := G')]
  rfl

/-- The comparison from a refinement `H` of `F` sends a pure tensor of `H` to the restricted
pure tensor of `F`. -/
private theorem dualizingModuleEquiv_tmul_refinement
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, x} A B) (H : FiniteOpenFactorization.{u, v, y} A B)
    (hinj : Function.Injective (algebraMap H.middle B)) (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (φ : Module.Dual A H.middle) (b : B) :
    dualizingModuleEquiv H F (dualizingModule.tmul H φ b) =
      dualizingModule.tmul F (φ.comp r.toLinearMap) b := by
  simpa only [AlgHom.toLinearMap_id, LinearMap.comp_id] using
    dualizingModuleEquiv_tmul H F H hinj (AlgHom.id A H.middle) r (fun _ => rfl) hr φ b

/-- Comparing a localized pure tensor of `F` with the localized pure tensor of a refinement `H`
of `F`, through any factorization `G'` of the localized algebra. -/
private theorem dualizingModuleEquiv_locFact_tmul_refinement
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B) (H : FiniteOpenFactorization.{u, v, y} A B)
    (G' : FiniteOpenFactorization.{u, w, z} A Bg)
    (hinj : Function.Injective (algebraMap H.middle B)) (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (φ : Module.Dual A H.middle) (b : B) :
    dualizingModuleEquiv (locFact (Bg := Bg) g F) G'
        (dualizingModule.tmul (locFact (Bg := Bg) g F) (φ.comp r.toLinearMap)
          (algebraMap B Bg b)) =
      dualizingModuleEquiv (locFact (Bg := Bg) g H) G'
        (dualizingModule.tmul (locFact (Bg := Bg) g H) φ (algebraMap B Bg b)) := by
  refine (congrArg (dualizingModuleEquiv (locFact (Bg := Bg) g F) G')
    (comparison_restrict_of_local_annihilation (locFact (Bg := Bg) g F)
      (locFact (Bg := Bg) g H) r (fun c => congrArg (algebraMap B Bg) (hr c))
      (locFact_refinement_local_annihilation (Bg := Bg) (g := g) F H r hr hinj)
      φ (algebraMap B Bg b)).symm).trans ?_
  rw [← dualizingModuleEquiv_trans (locFact (Bg := Bg) g H) (locFact (Bg := Bg) g F) G']
  rfl

/-- Localization commutes with the canonical comparison of two factorizations of the original
algebra, as well as with the comparison of factorizations after localization.  A map between
abstract localized modules is specified by its action on their localization maps. -/
@[stacks 0BT2 "part (2), naturality in both factorizations"]
public theorem localizedModule_dualizingModule_equiv_natural_in_source
    {A : Type u} {B : Type v} {Bg : Type w} {M : Type x} {M' : Type y}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, z} A B)
    (F' : FiniteOpenFactorization.{u, v, t} A B)
    (G : FiniteOpenFactorization.{u, w, q} A Bg)
    (G' : FiniteOpenFactorization.{u, w, s} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    [AddCommGroup M'] [Module B M'] [Module Bg M'] [IsScalarTower B Bg M']
    (localizationMap : dualizingModule F →ₗ[B] M)
    (hM : IsLocalizedModule (Submonoid.powers g) localizationMap)
    (localizationMap' : dualizingModule F' →ₗ[B] M')
    (hM' : IsLocalizedModule (Submonoid.powers g) localizationMap')
    (comparison : M →ₗ[Bg] M')
    (hcomparison : ∀ m : dualizingModule F,
      comparison (localizationMap m) =
        localizationMap' (dualizingModuleEquiv F F' m))
    (m : M) :
    dualizingModuleEquiv G G'
        (localizedModule_dualizingModule_equiv g F G localizationMap hM m) =
      localizedModule_dualizingModule_equiv g F' G' localizationMap' hM'
        (comparison m) := by
  refine LinearMap.congr_fun
    (linearMap_ext_dualizingModule_localizedModule g F G' localizationMap hM
      (f₁ := (dualizingModuleEquiv G G').toLinearMap ∘ₗ
        (localizedModule_dualizingModule_equiv g F G localizationMap hM).toLinearMap)
      (f₂ := (localizedModule_dualizingModule_equiv g F' G' localizationMap' hM').toLinearMap ∘ₗ
        comparison) fun x => ?_) m
  obtain ⟨H, rF, rF', hinj, hF, hF'⟩ := exists_common_finite_open_factorization F F'
  let eHF : dualizingModule H ≃ₗ[B] dualizingModule F := dualizingModuleEquiv H F
  obtain ⟨t, rfl⟩ := eHF.surjective x
  induction t using dualizingModule.induction_on with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul φ b =>
    have hcompare : dualizingModuleEquiv F F' (eHF (dualizingModule.tmul H φ b)) =
        dualizingModuleEquiv H F' (dualizingModule.tmul H φ b) := by
      rw [← dualizingModuleEquiv_trans H F F']
      rfl
    change dualizingModuleEquiv G G'
        (localizedModule_dualizingModule_equiv g F G localizationMap hM
          (localizationMap (eHF (dualizingModule.tmul H φ b)))) =
      localizedModule_dualizingModule_equiv g F' G' localizationMap' hM'
        (comparison (localizationMap (eHF (dualizingModule.tmul H φ b))))
    rw [hcomparison, hcompare, dualizingModuleEquiv_tmul_refinement F H hinj rF hF,
      dualizingModuleEquiv_tmul_refinement F' H hinj rF' hF',
      localizedModule_dualizingModule_equiv_apply, localizedModule_dualizingModule_equiv_apply,
      dualizingTensorLocalizationEquiv_tmul, dualizingTensorLocalizationEquiv_tmul]
    exact (congrArg (fun e => e (dualizingModule.tmul (locFact (Bg := Bg) g F)
        (φ.comp rF.toLinearMap) (algebraMap B Bg b))) (dualizingModuleEquiv_trans _ G G')).trans
      ((dualizingModuleEquiv_locFact_tmul_refinement (Bg := Bg) g F H G' hinj rF hF φ b).trans
        (dualizingModuleEquiv_locFact_tmul_refinement (Bg := Bg) g F' H G' hinj rF' hF' φ b).symm)

end Stacks.Discriminant
