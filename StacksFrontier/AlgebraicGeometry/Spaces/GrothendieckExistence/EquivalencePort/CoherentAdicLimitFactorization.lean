module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CoherentAdicAffineSectionTower
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.AdicSectionsAffineDescent

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Factoring through a comparison which is bijective on limits of affine sections

Let `G` and `P` be coherent `𝓘`-adic systems on an algebraic space with locally Noetherian étale
charts, `D` an inverse system of modules, `c : P ⟶ D` and `γ : G ⟶ D` morphisms of inverse
systems. If for every affine étale chart `V` the map `lim_n P_n(V) ⟶ lim_n D_n(V)` induced by
`c` is bijective, then `γ` factors uniquely as `α ≫ c` with `α : G ⟶ P`.

## Main definitions

* `AlgebraicGeometry.Space.C1573.adicSectionLimit`: the inverse limit `lim_n X_n(V)` of the
  sections of an inverse system over a chart.
* `AlgebraicGeometry.Space.C1573.adicSectionLimitMap`: the map of these limits induced by a
  morphism of inverse systems.
* `AlgebraicGeometry.Space.C1573.factorThroughLimitBijective`: the morphism `α : G ⟶ P` with
  `α ≫ c = γ`.

## Main results

* `AlgebraicGeometry.Space.C1573.factorThroughLimitBijective_comp`: `α ≫ c = γ`.
* `AlgebraicGeometry.Space.C1573.eq_factorThroughLimitBijective`: `α` is the only morphism
  `G ⟶ P` with `α ≫ c = γ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

section TowerMaps

variable {X Y Z : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (V : (smallEtaleRingedSite B S hS F hF).C)

/-- The inverse limit `lim_n X_n(V)` of the sections over a chart. -/
abbrev C1573.adicSectionLimit (X : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) :
    Submodule (chartRing B S hS F hF V) (∀ k, adicSectionTower B S hS F hF X V k) :=
  invLimit (adicSectionTower B S hS F hF X V) (adicSectionTransition B S hS F hF X V)

/-- A morphism of inverse systems on the shifted towers of sections. -/
def C1573.adicSectionTowerMap (φ : X ⟶ Y) (k : ℕ) :
    adicSectionTower B S hS F hF X V k →ₗ[chartRing B S hS F hF V]
      adicSectionTower B S hS F hF Y V k :=
  match k with
  | 0 => 0
  | k + 1 => ((φ.app (op k)).val.app (op V)).hom

/-- `adicSectionTowerMap` commutes with the transition maps of the towers. -/
theorem C1573.adicSectionTowerMap_transition (φ : X ⟶ Y) (k : ℕ)
    (x : adicSectionTower B S hS F hF X V (k + 1)) :
    adicSectionTransition B S hS F hF Y V k (adicSectionTowerMap B S hS F hF V φ (k + 1) x) =
      adicSectionTowerMap B S hS F hF V φ k (adicSectionTransition B S hS F hF X V k x) := by
  cases k with
  | zero => rfl
  | succ k =>
    exact (congrArg (fun t ↦ t.val.app (op V) x)
      (φ.naturality (homOfLE (Nat.le_add_right k 1)).op)).symm

/-- The map of inverse limits of sections over a chart induced by a morphism of inverse
systems. -/
def C1573.adicSectionLimitMap (φ : X ⟶ Y) :
    adicSectionLimit B S hS F hF V X →ₗ[chartRing B S hS F hF V]
      adicSectionLimit B S hS F hF V Y where
  toFun x := ⟨fun k ↦ adicSectionTowerMap B S hS F hF V φ k (x.1 k), fun k ↦
    (adicSectionTowerMap_transition B S hS F hF V φ k (x.1 (k + 1))).trans
      (congrArg _ (x.2 k))⟩
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ ↦ map_smul _ _ _)

/-- The component in degree `k + 1` of `adicSectionLimitMap φ x` is the image under `φ` of that
of `x`. -/
theorem C1573.adicSectionLimitMap_apply (φ : X ⟶ Y) (x : adicSectionLimit B S hS F hF V X)
    (k : ℕ) :
    (adicSectionLimitMap B S hS F hF V φ x).1 (k + 1) =
      (φ.app (op k)).val.app (op V) (x.1 (k + 1)) :=
  rfl

/-- `adicSectionLimitMap` takes a composite of morphisms of inverse systems to the composite. -/
theorem C1573.adicSectionLimitMap_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (x : adicSectionLimit B S hS F hF V X) :
    adicSectionLimitMap B S hS F hF V (φ ≫ ψ) x =
      adicSectionLimitMap B S hS F hF V ψ (adicSectionLimitMap B S hS F hF V φ x) :=
  Subtype.ext (funext fun k ↦ by cases k <;> rfl)

/-- Restriction of a compatible family of sections along a morphism of charts. -/
def C1573.adicSectionLimitRes {V' : (smallEtaleRingedSite B S hS F hF).C} (g : V' ⟶ V)
    (x : adicSectionLimit B S hS F hF V X) : adicSectionLimit B S hS F hF V' X :=
  ⟨fun k ↦ match k with
    | 0 => (0 : Fin 0 → chartRing B S hS F hF V')
    | k + 1 => (X.obj (op k)).val.map g.op (x.1 (k + 1)), fun k ↦ by
      cases k with
      | zero => rfl
      | succ k =>
        change ((X.map (homOfLE (Nat.le_add_right k 1)).op).val.app (op V'))
            ((X.obj (op (k + 1))).val.map g.op (x.1 (k + 1 + 1))) =
          (X.obj (op k)).val.map g.op (x.1 (k + 1))
        rw [← x.2 (k + 1)]
        exact PresheafOfModules.naturality_apply
          (X.map (homOfLE (Nat.le_add_right k 1)).op).val g.op (x.1 (k + 1 + 1))⟩

/-- Restriction along a morphism of charts commutes with `adicSectionLimitMap`. -/
theorem C1573.adicSectionLimitRes_map (φ : X ⟶ Y) {V' : (smallEtaleRingedSite B S hS F hF).C}
    (g : V' ⟶ V) (x : adicSectionLimit B S hS F hF V X) :
    adicSectionLimitRes B S hS F hF V g (adicSectionLimitMap B S hS F hF V φ x) =
      adicSectionLimitMap B S hS F hF V' φ (adicSectionLimitRes B S hS F hF V g x) := by
  refine Subtype.ext (funext fun k ↦ ?_)
  cases k with
  | zero => rfl
  | succ k => exact (PresheafOfModules.naturality_apply (φ.app (op k)).val g.op (x.1 (k + 1))).symm

end TowerMaps

section AffineExt

/-- Two morphisms of `𝒪_F`-modules agreeing on the sections over every affine chart are equal. -/
theorem C1573.modules_hom_ext_of_isAffine {M N : Modules.{u, u} B S hS F hF} {φ ψ : M ⟶ N}
    (h : ∀ (V : (smallEtaleRingedSite B S hS F hF).C), IsAffine (chartScheme V) →
      ∀ x : M.val.obj (op V), φ.val.app (op V) x = ψ.val.app (op V) x) : φ = ψ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
  obtain ⟨U⟩ := U
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  refine SmallEtale.C1573.eq_of_forall_isAffine B S hS F hF
    (Stacks.SheafOfModules.ImageSubsheaf.isSheaf_forget N) fun V g hV ↦ ?_
  exact (PresheafOfModules.naturality_apply φ.val g.op x).symm.trans
    ((h V hV _).trans (PresheafOfModules.naturality_apply ψ.val g.op x))

/-- The restrictions of a section of an `𝒪_F`-module along `a₁ ≫ g₁` and along `a₂ ≫ g₂` agree
when `a₁ ≫ g₁ = a₂ ≫ g₂`. -/
theorem C1573.modules_map_map_eq (M : Modules.{u, u} B S hS F hF)
    {U V₁ V₂ W : (smallEtaleRingedSite B S hS F hF).C} (g₁ : V₁ ⟶ U) (g₂ : V₂ ⟶ U) (a₁ : W ⟶ V₁)
    (a₂ : W ⟶ V₂) (h : a₁ ≫ g₁ = a₂ ≫ g₂) (y : M.val.obj (op U)) :
    M.val.map a₁.op (M.val.map g₁.op y) = M.val.map a₂.op (M.val.map g₂.op y) := by
  have hop : g₁.op ≫ a₁.op = g₂.op ≫ a₂.op := by rw [← op_comp, ← op_comp, h]
  exact (PresheafOfModules.map_comp_apply M.val g₁.op a₁.op y).symm.trans
    ((PresheafOfModules.congr_map_apply M.val hop y).trans
      (PresheafOfModules.map_comp_apply M.val g₂.op a₂.op y))

/-- The underlying presheaf of sets of an `𝒪_F`-module is a sheaf for the étale topology. -/
theorem C1573.isSheaf_forget_factor (M : Modules.{u, u} B S hS F hF) :
    Presieve.IsSheaf (SmallEtale.topology B S hS F)
      (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    (GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf)

end AffineExt

section Factor

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
  (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
  {G P : CoherentAdicSystems B S hS F hF 𝓘} {D : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
  (c : P.obj ⟶ D) (γ : G.obj ⟶ D)
  (hc : ∀ V : (smallEtaleRingedSite B S hS F hF).C, IsAffine (chartScheme V) →
    Function.Bijective (adicSectionLimitMap B S hS F hF V c))

include hc in
/-- The composite `lim_n G_n(V) ⟶ lim_n D_n(V) ≅ lim_n P_n(V) ⟶ P_k(V)` over an affine chart. -/
def C1573.affineFactorAux {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (k : ℕ) :
    adicSectionLimit B S hS F hF V G.obj →ₗ[chartRing B S hS F hF V]
      (P.obj.obj (op k)).val.obj (op V) :=
  (invLimit.proj (adicSectionTower B S hS F hF P.obj V) (adicSectionTransition B S hS F hF P.obj V)
      (k + 1)).comp
    ((LinearEquiv.ofBijective (adicSectionLimitMap B S hS F hF V c) (hc V hV)).symm.toLinearMap.comp
      (adicSectionLimitMap B S hS F hF V γ))

/-- Over an affine chart the ideal of sections of `𝓘` is finitely generated. -/
theorem C1573.fg_chartSectionIdeal {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) :
    (chartSectionIdeal B S hS F hF 𝓘 V).FG :=
  have : IsNoetherianRing (chartRing B S hS F hF V) :=
    isNoetherianRing_chartRing_of_isAffine (hX := hF) Fact.out hV
  (IsNoetherian.noetherian _)

include hI in
/-- The kernel of the projection `lim_n G_n(V) ⟶ G_k(V)` is contained in the kernel of
`affineFactorAux`. -/
theorem C1573.ker_proj_le_ker_affineFactorAux {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (k : ℕ) :
    LinearMap.ker (invLimit.proj (adicSectionTower B S hS F hF G.obj V)
        (adicSectionTransition B S hS F hF G.obj V) (k + 1)) ≤
      LinearMap.ker (affineFactorAux B S hS F hF 𝓘 c γ hc hV k) := by
  intro x hx
  have hx' := ((adicSectionInverseSystem hI G.property hV).ker_proj
    (fg_chartSectionIdeal B S hS F hF 𝓘 hV) (k + 1)).le hx
  have hann := (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (k + 1) _).1 (P.property.2.1 k)
  rw [LinearMap.mem_ker]
  refine Submodule.smul_induction_on hx' (fun r hr y _ ↦ ?_) (fun y y' hy hy' ↦ ?_)
  · exact ((affineFactorAux B S hS F hF 𝓘 c γ hc hV k).map_smul r y).trans (hann V r hr _)
  · exact ((affineFactorAux B S hS F hF 𝓘 c γ hc hV k).map_add y y').trans
      ((congrArg₂ (· + ·) hy hy').trans (add_zero 0))

/-- The component `G_k(V) ⟶ P_k(V)` over an affine chart `V` of the factorization of `γ`
through `c`. -/
def C1573.affineFactor {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (k : ℕ) :
    (G.obj.obj (op k)).val.obj (op V) →ₗ[chartRing B S hS F hF V]
      (P.obj.obj (op k)).val.obj (op V) :=
  ((LinearMap.ker (invLimit.proj (adicSectionTower B S hS F hF G.obj V)
      (adicSectionTransition B S hS F hF G.obj V) (k + 1))).liftQ
      (affineFactorAux B S hS F hF 𝓘 c γ hc hV k)
      (ker_proj_le_ker_affineFactorAux B S hS F hF 𝓘 hI c γ hc hV k)).comp
    ((invLimit.proj (adicSectionTower B S hS F hF G.obj V)
      (adicSectionTransition B S hS F hF G.obj V) (k + 1)).quotKerEquivOfSurjective
      ((adicSectionInverseSystem hI G.property hV).proj_surjective (k + 1))).symm.toLinearMap

/-- `affineFactor` applied to the degree-`k` component of a compatible family `x` is
`affineFactorAux` applied to `x`. -/
theorem C1573.affineFactor_proj {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (k : ℕ) (x : adicSectionLimit B S hS F hF V G.obj) :
    affineFactor B S hS F hF 𝓘 hI c γ hc hV k (x.1 (k + 1)) =
      affineFactorAux B S hS F hF 𝓘 c γ hc hV k x := by
  have h : ((invLimit.proj (adicSectionTower B S hS F hF G.obj V)
      (adicSectionTransition B S hS F hF G.obj V) (k + 1)).quotKerEquivOfSurjective
      ((adicSectionInverseSystem hI G.property hV).proj_surjective (k + 1))).symm (x.1 (k + 1)) =
        Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  exact (congrArg ((LinearMap.ker (invLimit.proj (adicSectionTower B S hS F hF G.obj V)
      (adicSectionTransition B S hS F hF G.obj V) (k + 1))).liftQ
      (affineFactorAux B S hS F hF 𝓘 c γ hc hV k)
      (ker_proj_le_ker_affineFactorAux B S hS F hF 𝓘 hI c γ hc hV k)) h).trans
    (Submodule.liftQ_apply _ _ _)

/-- `affineFactor` applied to the degree-`k` component of `x` is the degree-`k` component of the
preimage of `γ x` under the bijection induced by `c`. -/
private theorem affineFactor_proj_eq_limitInv {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (k : ℕ) (x : adicSectionLimit B S hS F hF V G.obj) :
    affineFactor B S hS F hF 𝓘 hI c γ hc hV k (x.1 (k + 1)) =
      ((LinearEquiv.ofBijective (adicSectionLimitMap B S hS F hF V c) (hc V hV)).symm
        (adicSectionLimitMap B S hS F hF V γ x)).1 (k + 1) :=
  affineFactor_proj B S hS F hF 𝓘 hI c γ hc hV k x

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))] in
include hI in
/-- Over an affine chart every section of `G_k` is the degree-`k` component of a compatible
family of sections. -/
theorem C1573.exists_adicSectionLimit_lift {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (k : ℕ) (y : (G.obj.obj (op k)).val.obj (op V)) :
    ∃ x : adicSectionLimit B S hS F hF V G.obj, x.1 (k + 1) = y :=
  (adicSectionInverseSystem hI G.property hV).proj_surjective (k + 1) y

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))] in
/-- Restriction along a morphism of affine charts commutes with the inverse of the bijection
`lim_n P_n(V) ⟶ lim_n D_n(V)` induced by `c`. -/
theorem C1573.adicSectionLimitRes_limitInv {V V' : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (hV' : IsAffine (chartScheme V')) (g : V' ⟶ V)
    (z : adicSectionLimit B S hS F hF V D) :
    adicSectionLimitRes B S hS F hF V g
        ((LinearEquiv.ofBijective (adicSectionLimitMap B S hS F hF V c) (hc V hV)).symm z) =
      (LinearEquiv.ofBijective (adicSectionLimitMap B S hS F hF V' c) (hc V' hV')).symm
        (adicSectionLimitRes B S hS F hF V g z) := by
  rw [LinearEquiv.eq_symm_apply]
  change adicSectionLimitMap B S hS F hF V' c (adicSectionLimitRes B S hS F hF V g _) = _
  rw [← adicSectionLimitRes_map]
  congr 1
  exact (LinearEquiv.ofBijective (adicSectionLimitMap B S hS F hF V c) (hc V hV)).apply_symm_apply z

/-- The affine components are natural along morphisms of affine charts. -/
theorem C1573.affineFactor_res {V V' : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (hV' : IsAffine (chartScheme V')) (g : V' ⟶ V) (k : ℕ)
    (y : (G.obj.obj (op k)).val.obj (op V)) :
    (P.obj.obj (op k)).val.map g.op (affineFactor B S hS F hF 𝓘 hI c γ hc hV k y) =
      affineFactor B S hS F hF 𝓘 hI c γ hc hV' k ((G.obj.obj (op k)).val.map g.op y) := by
  obtain ⟨x, rfl⟩ := exists_adicSectionLimit_lift B S hS F hF 𝓘 hI hV k y
  have h1 : (G.obj.obj (op k)).val.map g.op (x.1 (k + 1)) =
      (adicSectionLimitRes B S hS F hF V g x).1 (k + 1) := rfl
  rw [affineFactor_proj_eq_limitInv, h1, affineFactor_proj_eq_limitInv,
    ← adicSectionLimitRes_map, ← adicSectionLimitRes_limitInv B S hS F hF 𝓘 c hc hV hV' g]
  rfl

/-- The affine components are compatible with the transition maps. -/
theorem C1573.affineFactor_transition {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (k : ℕ) (y : (G.obj.obj (op (k + 1))).val.obj (op V)) :
    (P.obj.map (homOfLE (Nat.le_add_right k 1)).op).val.app (op V)
        (affineFactor B S hS F hF 𝓘 hI c γ hc hV (k + 1) y) =
      affineFactor B S hS F hF 𝓘 hI c γ hc hV k
        ((G.obj.map (homOfLE (Nat.le_add_right k 1)).op).val.app (op V) y) := by
  obtain ⟨x, rfl⟩ := exists_adicSectionLimit_lift B S hS F hF 𝓘 hI hV (k + 1) y
  have h1 : (G.obj.map (homOfLE (Nat.le_add_right k 1)).op).val.app (op V) (x.1 (k + 1 + 1)) =
      x.1 (k + 1) := x.2 (k + 1)
  rw [affineFactor_proj_eq_limitInv, h1, affineFactor_proj_eq_limitInv]
  exact ((LinearEquiv.ofBijective (adicSectionLimitMap B S hS F hF V c) (hc V hV)).symm
    (adicSectionLimitMap B S hS F hF V γ x)).2 (k + 1)

/-- The affine components factor `γ` through `c`. -/
theorem C1573.affineFactor_comp {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (k : ℕ) (y : (G.obj.obj (op k)).val.obj (op V)) :
    (c.app (op k)).val.app (op V) (affineFactor B S hS F hF 𝓘 hI c γ hc hV k y) =
      (γ.app (op k)).val.app (op V) y := by
  obtain ⟨x, rfl⟩ := exists_adicSectionLimit_lift B S hS F hF 𝓘 hI hV k y
  rw [affineFactor_proj_eq_limitInv]
  exact congrArg (fun z : adicSectionLimit B S hS F hF V D ↦ z.1 (k + 1))
    ((LinearEquiv.ofBijective (adicSectionLimitMap B S hS F hF V c) (hc V hV)).apply_symm_apply _)

/-- For a section `y` over `U` and affine charts `V₁ ⟶ U`, `V₂ ⟶ U`, the affine components of
the restrictions of `y` agree on an affine chart `W` mapping to both compatibly. -/
theorem C1573.gluedFactor_compat (k : ℕ) (U : (smallEtaleRingedSite B S hS F hF).C)
    (y : (G.obj.obj (op k)).val.obj (op U))
    (V₁ V₂ : (smallEtaleRingedSite B S hS F hF).C) (g₁ : V₁ ⟶ U) (g₂ : V₂ ⟶ U)
    (h₁ : IsAffine (chartScheme V₁)) (h₂ : IsAffine (chartScheme V₂))
    (W : (smallEtaleRingedSite B S hS F hF).C) (hW : IsAffine (chartScheme W)) (a₁ : W ⟶ V₁)
    (a₂ : W ⟶ V₂) (hcomm : a₁ ≫ g₁ = a₂ ≫ g₂) :
    (P.obj.obj (op k)).val.map a₁.op
        (affineFactor B S hS F hF 𝓘 hI c γ hc h₁ k ((G.obj.obj (op k)).val.map g₁.op y)) =
      (P.obj.obj (op k)).val.map a₂.op
        (affineFactor B S hS F hF 𝓘 hI c γ hc h₂ k ((G.obj.obj (op k)).val.map g₂.op y)) := by
  have e₁ := affineFactor_res B S hS F hF 𝓘 hI c γ hc h₁ hW a₁ k
    ((G.obj.obj (op k)).val.map g₁.op y)
  have e₂ := affineFactor_res B S hS F hF 𝓘 hI c γ hc h₂ hW a₂ k
    ((G.obj.obj (op k)).val.map g₂.op y)
  have m := modules_map_map_eq B S hS F hF (G.obj.obj (op k)) g₁ g₂ a₁ a₂ hcomm y
  exact e₁.trans ((congrArg (affineFactor B S hS F hF 𝓘 hI c γ hc hW k) m).trans e₂.symm)

/-- For a section `y` of `G_k` over a chart `U` there is a section of `P_k` over `U` whose
restriction to every affine chart `V ⟶ U` is the affine component of the restriction of `y`. -/
theorem C1573.exists_gluedFactor (k : ℕ) (U : (smallEtaleRingedSite B S hS F hF).C)
    (y : (G.obj.obj (op k)).val.obj (op U)) :
    ∃ z : (P.obj.obj (op k)).val.obj (op U), ∀ (V : (smallEtaleRingedSite B S hS F hF).C)
      (g : V ⟶ U) (hV : IsAffine (chartScheme V)), (P.obj.obj (op k)).val.map g.op z =
        affineFactor B S hS F hF 𝓘 hI c γ hc hV k ((G.obj.obj (op k)).val.map g.op y) := by
  let tV : ∀ (V : (smallEtaleRingedSite B S hS F hF).C) (_ : V ⟶ U),
      IsAffine (chartScheme V) → (P.obj.obj (op k)).val.obj (op V) :=
    fun V g hV ↦ affineFactor B S hS F hF 𝓘 hI c γ hc hV k ((G.obj.obj (op k)).val.map g.op y)
  exact SmallEtale.C1573.exists_eq_of_forall_isAffine B S hS F hF
    (isSheaf_forget_factor B S hS F hF (P.obj.obj (op k))) (fun V g hV ↦ tV V g hV)
    fun V₁ V₂ g₁ g₂ h₁ h₂ W hW a₁ a₂ ha ↦
      gluedFactor_compat B S hS F hF 𝓘 hI c γ hc k U y V₁ V₂ g₁ g₂ h₁ h₂ W hW a₁ a₂ ha

/-- The glued component over an arbitrary chart. -/
def C1573.gluedFactorFun (k : ℕ) (U : (smallEtaleRingedSite B S hS F hF).C)
    (y : (G.obj.obj (op k)).val.obj (op U)) :
    (P.obj.obj (op k)).val.obj (op U) :=
  (exists_gluedFactor B S hS F hF 𝓘 hI c γ hc k U y).choose

/-- The restriction of `gluedFactorFun y` to an affine chart `V ⟶ U` is the affine component of
the restriction of `y`. -/
theorem C1573.gluedFactorFun_spec (k : ℕ) (U : (smallEtaleRingedSite B S hS F hF).C)
    (y : (G.obj.obj (op k)).val.obj (op U)) (V : (smallEtaleRingedSite B S hS F hF).C) (g : V ⟶ U)
    (hV : IsAffine (chartScheme V)) :
    (P.obj.obj (op k)).val.map g.op (gluedFactorFun B S hS F hF 𝓘 hI c γ hc k U y) =
      affineFactor B S hS F hF 𝓘 hI c γ hc hV k ((G.obj.obj (op k)).val.map g.op y) :=
  (exists_gluedFactor B S hS F hF 𝓘 hI c γ hc k U y).choose_spec V g hV

/-- A section whose restrictions to the affine charts are the affine components of the
restrictions of `y` is `gluedFactorFun y`. -/
theorem C1573.gluedFactorFun_eq_of_forall (k : ℕ) (U : (smallEtaleRingedSite B S hS F hF).C)
    (y : (G.obj.obj (op k)).val.obj (op U)) (z : (P.obj.obj (op k)).val.obj (op U))
    (hz : ∀ (V : (smallEtaleRingedSite B S hS F hF).C) (g : V ⟶ U) (hV : IsAffine (chartScheme V)),
      (P.obj.obj (op k)).val.map g.op z =
        affineFactor B S hS F hF 𝓘 hI c γ hc hV k ((G.obj.obj (op k)).val.map g.op y)) :
    gluedFactorFun B S hS F hF 𝓘 hI c γ hc k U y = z :=
  SmallEtale.C1573.eq_of_forall_isAffine B S hS F hF
    (isSheaf_forget_factor B S hS F hF (P.obj.obj (op k))) fun V g hV ↦
      (gluedFactorFun_spec B S hS F hF 𝓘 hI c γ hc k U y V g hV).trans (hz V g hV).symm

/-- The glued component as a linear map. -/
def C1573.gluedFactorLinear (k : ℕ) (U : (smallEtaleRingedSite B S hS F hF).C) :
    (G.obj.obj (op k)).val.obj (op U) →ₗ[chartRing B S hS F hF U]
      (P.obj.obj (op k)).val.obj (op U) where
  toFun := gluedFactorFun B S hS F hF 𝓘 hI c γ hc k U
  map_add' y y' := by
    refine gluedFactorFun_eq_of_forall B S hS F hF 𝓘 hI c γ hc k U _ _ fun V g hV ↦ ?_
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·)
      (gluedFactorFun_spec B S hS F hF 𝓘 hI c γ hc k U y V g hV)
      (gluedFactorFun_spec B S hS F hF 𝓘 hI c γ hc k U y' V g hV)).trans
      ((map_add (affineFactor B S hS F hF 𝓘 hI c γ hc hV k) _ _).symm.trans
        (congrArg (affineFactor B S hS F hF 𝓘 hI c γ hc hV k) (map_add _ _ _).symm)))
  map_smul' r y := by
    refine gluedFactorFun_eq_of_forall B S hS F hF 𝓘 hI c γ hc k U _ _ fun V g hV ↦ ?_
    exact (PresheafOfModules.map_smul _ g.op r _).trans
      ((congrArg (_ • ·) (gluedFactorFun_spec B S hS F hF 𝓘 hI c γ hc k U y V g hV)).trans
      ((map_smul (affineFactor B S hS F hF 𝓘 hI c γ hc hV k) _ _).symm.trans
        (congrArg (affineFactor B S hS F hF 𝓘 hI c γ hc hV k)
          (PresheafOfModules.map_smul _ g.op r y).symm)))

/-- `gluedFactorFun` commutes with restriction along morphisms of charts. -/
theorem C1573.gluedFactorFun_res (k : ℕ) {U U' : (smallEtaleRingedSite B S hS F hF).C} (h : U' ⟶ U)
    (y : (G.obj.obj (op k)).val.obj (op U)) :
    (P.obj.obj (op k)).val.map h.op (gluedFactorFun B S hS F hF 𝓘 hI c γ hc k U y) =
      gluedFactorFun B S hS F hF 𝓘 hI c γ hc k U' ((G.obj.obj (op k)).val.map h.op y) := by
  symm
  refine gluedFactorFun_eq_of_forall B S hS F hF 𝓘 hI c γ hc k U' _ _ fun V g hV ↦ ?_
  exact (PresheafOfModules.map_comp_apply _ h.op g.op _).symm.trans
    ((gluedFactorFun_spec B S hS F hF 𝓘 hI c γ hc k U y V (g ≫ h) hV).trans
      (congrArg (affineFactor B S hS F hF 𝓘 hI c γ hc hV k)
        (PresheafOfModules.map_comp_apply _ h.op g.op y)))

/-- Over an affine chart `gluedFactorFun` is the affine component. -/
theorem C1573.gluedFactorFun_of_isAffine (k : ℕ) {U : (smallEtaleRingedSite B S hS F hF).C}
    (hU : IsAffine (chartScheme U)) (y : (G.obj.obj (op k)).val.obj (op U)) :
    gluedFactorFun B S hS F hF 𝓘 hI c γ hc k U y = affineFactor B S hS F hF 𝓘 hI c γ hc hU k y := by
  have h := gluedFactorFun_spec B S hS F hF 𝓘 hI c γ hc k U y U (𝟙 U) hU
  rwa [op_id, PresheafOfModules.map_id_apply, PresheafOfModules.map_id_apply] at h

/-- The glued component, as a morphism of `𝒪_F`-modules. -/
def C1573.gluedFactorHom (k : ℕ) : G.obj.obj (op k) ⟶ P.obj.obj (op k) :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom (gluedFactorLinear B S hS F hF 𝓘 hI c γ hc k U.unop)
     naturality := fun {U U'} h ↦ by
       ext y
       exact (gluedFactorFun_res B S hS F hF 𝓘 hI c γ hc k h.unop y).symm }⟩

/-- Over an affine chart `gluedFactorHom k` is the affine component. -/
theorem C1573.gluedFactorHom_app_of_isAffine (k : ℕ) {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (y : (G.obj.obj (op k)).val.obj (op V)) :
    (gluedFactorHom B S hS F hF 𝓘 hI c γ hc k).val.app (op V) y =
      affineFactor B S hS F hF 𝓘 hI c γ hc hV k y :=
  gluedFactorFun_of_isAffine B S hS F hF 𝓘 hI c γ hc k hV y

/-- The factorization of `γ` through `c`, as a morphism of coherent adic systems. -/
def C1573.factorThroughLimitBijective : G ⟶ P :=
  ObjectProperty.homMk (NatTrans.ofOpSequence (fun k ↦ gluedFactorHom B S hS F hF 𝓘 hI c γ hc k)
    fun k ↦ modules_hom_ext_of_isAffine B S hS F hF fun V hV y ↦ by
      change (gluedFactorHom B S hS F hF 𝓘 hI c γ hc k).val.app (op V)
          ((G.obj.map (homOfLE (Nat.le_add_right k 1)).op).val.app (op V) y) =
        (P.obj.map (homOfLE (Nat.le_add_right k 1)).op).val.app (op V)
          ((gluedFactorHom B S hS F hF 𝓘 hI c γ hc (k + 1)).val.app (op V) y)
      rw [gluedFactorHom_app_of_isAffine B S hS F hF 𝓘 hI c γ hc k hV,
        gluedFactorHom_app_of_isAffine B S hS F hF 𝓘 hI c γ hc (k + 1) hV]
      exact (affineFactor_transition B S hS F hF 𝓘 hI c γ hc hV k y).symm)

/-- The factorization `α` of `γ` through `c` satisfies `α ≫ c = γ`. -/
theorem C1573.factorThroughLimitBijective_comp :
    (factorThroughLimitBijective B S hS F hF 𝓘 hI c γ hc).hom ≫ c = γ := by
  refine NatTrans.ext (funext fun k ↦ ?_)
  obtain ⟨k⟩ := k
  refine modules_hom_ext_of_isAffine B S hS F hF fun V hV y ↦ ?_
  change (c.app (op k)).val.app (op V)
      ((gluedFactorHom B S hS F hF 𝓘 hI c γ hc k).val.app (op V) y) =
        (γ.app (op k)).val.app (op V) y
  rw [gluedFactorHom_app_of_isAffine B S hS F hF 𝓘 hI c γ hc k hV]
  exact affineFactor_comp B S hS F hF 𝓘 hI c γ hc hV k y

/-- Every morphism `α : G ⟶ P` with `α ≫ c = γ` is `factorThroughLimitBijective`. -/
theorem C1573.eq_factorThroughLimitBijective (α : G ⟶ P) (hα : α.hom ≫ c = γ) :
    α = factorThroughLimitBijective B S hS F hF 𝓘 hI c γ hc := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun k ↦ ?_))
  obtain ⟨k⟩ := k
  refine modules_hom_ext_of_isAffine B S hS F hF fun V hV y ↦ ?_
  change (α.hom.app (op k)).val.app (op V) y =
    (gluedFactorHom B S hS F hF 𝓘 hI c γ hc k).val.app (op V) y
  rw [gluedFactorHom_app_of_isAffine B S hS F hF 𝓘 hI c γ hc k hV]
  obtain ⟨x, rfl⟩ := exists_adicSectionLimit_lift B S hS F hF 𝓘 hI hV k y
  rw [affineFactor_proj_eq_limitInv]
  have hlim : adicSectionLimitMap B S hS F hF V α.hom x =
      (LinearEquiv.ofBijective (adicSectionLimitMap B S hS F hF V c) (hc V hV)).symm
        (adicSectionLimitMap B S hS F hF V γ x) := by
    rw [LinearEquiv.eq_symm_apply]
    change adicSectionLimitMap B S hS F hF V c (adicSectionLimitMap B S hS F hF V α.hom x) = _
    rw [← adicSectionLimitMap_comp, hα]
  exact congrArg (fun z : adicSectionLimit B S hS F hF V P.obj ↦ z.1 (k + 1)) hlim

end Factor

end AlgebraicGeometry.Space

end
