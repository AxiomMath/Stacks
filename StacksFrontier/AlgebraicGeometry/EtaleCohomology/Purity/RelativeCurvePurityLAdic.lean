module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerClassTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePuritySupportTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.InverseImageIsoOfStalksOver
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.TwistNegOneInverseImageInput
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerLocalEquation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TwistNegOneOp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IotaRealizableSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageRealizable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveFirstBaseChange

/-!
# The tower form of cohomological purity along an étale divisor of a smooth relative curve

Let `g : U ⟶ W` be smooth of relative dimension one over `W` smooth over a field `k`, `i : Z ⟶ U`
a closed immersion with `Z = V(f)` and `Z ⟶ W` finite étale, `j : U₀ ⟶ U` the open complement,
`ℓ` invertible in `k`, and `G` a lisse ℓ-adic sheaf on `U`. The tower `n ↦ R¹ j_*(j⁻¹ Gₙ)` is
`i_*` of the tower of levels of the Tate twist `(i⁻¹ G)(-1)`
(`Stacks.EtaleCohomology.Purity.relativeCurvePurityLAdicInput_of_isIsoStalksOver`):

* `R¹ j_*(j⁻¹ Gₙ) ⟶ i_* i⁻¹ R¹ j_*(j⁻¹ Gₙ)` is an isomorphism, `R¹ j_*` being supported on `Z`
  (`Stacks.EtaleCohomology.Purity.isIso_unit_rightDerived_directImage_of_nsmul_id_eq_zero`);
* the purity maps `𝓗om(μ_{ℓⁿ⁺¹}, Gₙ) ⟶ R¹ j_*(j⁻¹ Gₙ)`, `α ↦ α_* s`, form a morphism of towers
  (`Stacks.EtaleCohomology.Purity.purityTowerMap`), invertible after `i⁻¹` as soon as the purity
  maps are invertible on the stalks over `Z`;
* `i⁻¹ 𝓗om(μ, Gₙ) ≅ 𝓗om(μ, i⁻¹ Gₙ)` compatibly with the transitions (the proposition
  `Stacks.EtaleCohomology.Purity.TwistNegOneTowerInverseImageInput`);
* the tower of `𝓗om(μ_{ℓⁿ⁺¹}, (i⁻¹ G)ₙ)` is the tower of levels of the twist
  (`Stacks.EtaleCohomology.LAdicSheaf.padicTowerTwistNegOneOpIso`).

This is the ℓ-adic tower form `(P1)` of relative cohomological purity
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), with the stalkwise purity of the class map
and the compatibility of the twist with inverse images as hypotheses.

## Main results

* `Stacks.EtaleCohomology.Purity.IsIsoStalksOver.comp_of_isIso`.
* `Stacks.EtaleCohomology.Purity.relativeCurvePurityLAdicInput_of_isIsoStalksOver`.
* `Stacks.EtaleCohomology.Purity.relativeCurvePurityInput_of_isIsoStalksOver`.

## Main definitions

* `Stacks.EtaleCohomology.Purity.PurityClassMapStalkIsoInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology.Purity

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

attribute [local instance] neZero_pow_of_fact_prime

/-- **Invertibility on the stalks over `T` is stable under composition with an isomorphism.** -/
theorem IsIsoStalksOver.comp_of_isIso {S : Scheme.{u}} {T : Set S}
    {A B C : Sheaf (smallEtaleTopology S) Ab.{u + 1}} {σ : A ⟶ B} (hσ : IsIsoStalksOver T σ)
    (e : B ⟶ C) [IsIso e] : IsIsoStalksOver T (σ ≫ e) := by
  intro Ω _ _ x hx
  have := hσ x hx
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- **Stalkwise purity of the class map, as one proposition**: for `g : U ⟶ W` smooth of relative
dimension one over `W` smooth over a field `k`, a closed immersion `i : Z ⟶ U` with `Z ⟶ W` étale,
`j : U₀ ⟶ U` the open complement, `N` invertible in `k` and `H` a locally constant sheaf of finite
type of `ℤ/N`-modules on `U`, the purity map `𝓗om(μ_N, H) ⟶ R¹ j_*(j⁻¹ H)`, `α ↦ α_* s`
(`Stacks.EtaleCohomology.Purity.kummerClassMapAb`), is invertible on the stalks at the geometric
points over `Z`. -/
def PurityClassMapStalkIsoInput : Prop :=
  ∀ (k : Type u) [Field k] (N : ℕ) [NeZero N], IsUnit (N : k) →
  ∀ (U W Z U₀ : Scheme.{u}) (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W)
    [SmoothOfRelativeDimension 1 g] (i : Z ⟶ U) [IsClosedImmersion i] [Etale (i ≫ g)]
    (j : U₀ ⟶ U) [IsOpenImmersion j] (hj : Set.range j.base = (Set.range i.base)ᶜ)
    [HasDerivedCategory.{u + 2} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
    [HasDerivedCategory.{u + 2} (Sheaf (smallEtaleTopology U) Ab.{u + 1})]
    (hN₀ : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤)))
    (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t)
    (H : EtaleModules.{u, 0} (ZMod N) U), lccModules U N H →
    IsIsoStalksOver (Set.range i.base)
      (kummerClassMapAb j N hN₀ hNU i hj.subset hcov H)

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [hℓp : Fact ℓ.Prime]
  [hRA : ∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [hWSo : ∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [hWS : ∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The ℓ-adic tower form of relative cohomological purity**, from the stalkwise purity of the
class map `α ↦ α_* s` over the divisor and the compatibility of the twist with inverse images:
for `G` lisse on `U`, the tower `n ↦ R¹ j_*(j⁻¹ Gₙ)` is `i_*` of the tower of levels of the twist
of `i⁻¹ G`. -/
theorem relativeCurvePurityLAdicInput_of_isIsoStalksOver
    (hC : TwistNegOneTowerInverseImageInput B ℓ)
    (hD : PurityClassMapStalkIsoInput.{u}) :
    RelativeCurvePurityLAdicInput B ℓ (LAdicSheaf.twistNegOneOp B ℓ) := by
  intro k _ hℓk U W Z hUn hZn U₀ pW _ g _ i _ _ _ f hZ j _ hj G hG
  let := HasDerivedCategory.standard (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})
  let := HasDerivedCategory.standard (Sheaf (smallEtaleTopology U.1) Ab.{u + 1})
  have : NeZero (ℓ : k) := ⟨hℓk.ne_zero⟩
  let fU : U.1 ⟶ Spec (.of k) := B.inclusion.map g ≫ pW
  have hℓ : IsUnit ((ℓ : ℕ) : Γ(U.1, ⊤)) := isUnit_natCast_globalSections_of_over fU hℓk
  have hℓ₀ : IsUnit ((ℓ : ℕ) : Γ(U₀, ⊤)) := isUnit_natCast_globalSections_of_over (j ≫ fU) hℓk
  have : Etale (B.inclusion.map i ≫ B.inclusion.map g) := by
    rw [← CategoryTheory.Functor.map_comp]; infer_instance
  have hcov : ∀ x : U.1, ∃ (V : U.1.Opens) (t : Γ(U.1, V)), x ∈ V ∧
      IsLocalEquation (B.inclusion.map i) V t :=
    exists_isLocalEquation k pW (B.inclusion.map g) (B.inclusion.map i)
  have : IsLocallyNoetherian U.1 := hUn.toIsLocallyNoetherian
  have : QuasiCompact j := inferInstance
  let c := purityTowerMap j G hℓ₀ hℓ (B.inclusion.map i) hj.subset hcov fU
  -- `(D)`: the purity maps are invertible after `i⁻¹`
  have hc : ∀ n : ℕᵒᵖ, IsIso ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map i)).map
      (c.app n)) := by
    rintro ⟨n⟩
    have hH : lccModules U.1 (ℓ ^ (n + 1)) (LAdicSheaf.etaleLevel B U ℓ G n) :=
      (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B U
        (ZMod (ℓ ^ (n + 1))) (G.level n)).2
        (@LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse B U ℓ hℓp hRA hWSo hWS hUn G hG n)
    have hk : IsUnit (((ℓ ^ (n + 1) : ℕ)) : k) := by rw [Nat.cast_pow]; exact hℓk.pow _
    have d1 := hD k (ℓ ^ (n + 1)) hk U.1 W.1 Z.1 U₀ pW (B.inclusion.map g) (B.inclusion.map i) j hj
    have d2 := d1 (by rw [Nat.cast_pow]; exact hℓ₀.pow _) (by rw [Nat.cast_pow]; exact hℓ.pow _)
      hcov
    have h0 : IsIsoStalksOver (Set.range (B.inclusion.map i).base) _ :=
      d2 (LAdicSheaf.etaleLevel B U ℓ G n) hH
    refine isIso_etaleModuleInverseImage_map_of_isIsoStalksOver ℤ_[ℓ] (B.inclusion.map i) _ ?_
    have e1 : (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map (c.app (op n)) =
        purityTowerLevelMapAb j G hℓ₀ hℓ (B.inclusion.map i) hj.subset hcov fU n :=
      (congrArg _ (purityTowerMap_app j G hℓ₀ hℓ (B.inclusion.map i) hj.subset hcov fU n)).trans
        (etaleModuleForgetAb_map_purityTowerLevelMap j G hℓ₀ hℓ (B.inclusion.map i) hj.subset hcov
          fU n)
    change IsIsoStalksOver _ ((etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map (c.app (op n)))
    rw [e1]
    exact @IsIsoStalksOver.comp_of_isIso _ _ _ _ _ _ h0 _ (Iso.isIso_hom
      (((smallEtalePushforwardAb j).rightDerived 1).mapIso ((smallEtalePullbackAb j).mapIso
        ((etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).mapIso ((sheafEquivRestrictScalarsIso B U.1
          U.property (PadicInt.toZModPow (p := ℓ) (n + 1))).app (G.level n)))) ≪≫
        (etaleModuleForgetHigherDirectImageRestrictionIso ℤ_[ℓ] j
          ((LAdicSheaf.padicTower B U ℓ G).obj (op n)) 1).symm))
  have : IsIso (Functor.whiskerRight c (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
      (B.inclusion.map i))) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hc
  -- `(A)`: `R¹ j_*(j⁻¹ Gₙ)` is supported on `Z`
  have hu : ∀ n : ℕᵒᵖ, IsIso ((etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map i)).unit.app
      ((purityTowerTarget j G).obj n)) := by
    rintro ⟨n⟩
    have hF : ℓ ^ (n + 1) • 𝟙 ((etaleModuleRestriction.{u, 0} ℤ_[ℓ] j).obj
        (towerObj (LAdicSheaf.padicTower B U ℓ G) n)) = 0 := by
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
        LAdicSheaf.padicTower_annihilated, Functor.map_zero]
    exact isIso_unit_rightDerived_directImage_of_nsmul_id_eq_zero ℤ_[ℓ]
      (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
      (by rw [Int.cast_natCast, Nat.cast_pow]; exact hℓ.pow _) j (B.inclusion.map i) hj _ hF 1
      Nat.one_pos
  have : IsIso (Functor.whiskerLeft (purityTowerTarget j G)
      (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map i)).unit) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hu
  have hGZ := @LAdicSheaf.IsLisse.inverseImage B Z U i ℓ hℓp hRA hWSo hWS hZn hUn G hG
  exact ⟨(Functor.rightUnitor _).symm ≪≫
    asIso (Functor.whiskerLeft (purityTowerTarget j G)
      (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map i)).unit) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (Functor.whiskerRight c (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
      (B.inclusion.map i)))).symm _ ≪≫
    Functor.isoWhiskerRight (hC U Z i k fU G hG).some _ ≪≫
    Functor.isoWhiskerRight (LAdicSheaf.padicTowerTwistNegOneOpIso
      (B.inclusion.map i ≫ fU) hGZ).symm _⟩

/-- **Relative cohomological purity along an étale divisor of a smooth relative curve**, with the
Tate twist: the sheaf-level part (`Stacks.EtaleCohomology.Purity.relativeCurvePuritySheafInput`)
and the ℓ-adic tower form
(`Stacks.EtaleCohomology.Purity.relativeCurvePurityLAdicInput_of_isIsoStalksOver`), from the
stalkwise purity of the class map and the compatibility of the twist with inverse images. -/
theorem relativeCurvePurityInput_of_isIsoStalksOver (hC : TwistNegOneTowerInverseImageInput B ℓ)
    (hD : PurityClassMapStalkIsoInput.{u}) :
    RelativeCurvePurityInput B ℓ (LAdicSheaf.twistNegOneOp B ℓ) :=
  ⟨relativeCurvePuritySheafInput, relativeCurvePurityLAdicInput_of_isIsoStalksOver B ℓ hC hD⟩

end Stacks.EtaleCohomology.Purity

end
