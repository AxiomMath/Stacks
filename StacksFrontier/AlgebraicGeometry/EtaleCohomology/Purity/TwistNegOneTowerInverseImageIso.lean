module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.TwistNegOnePrecompPowComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleLevelInverseImageTransition

/-!
# The inverse image of the tower of the Tate twist

Let `g : Y ⟶ X` be a morphism of Noetherian schemes of a big étale site, `fX : X ⟶ Spec k` with
`ℓ` invertible in the field `k`, and `F` an ℓ-adic sheaf on `X`. Level by level,
`g⁻¹ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ) ≅ 𝓗om(μ_{ℓⁿ⁺¹}, (g⁻¹F)ₙ)`
(`Stacks.EtaleCohomology.LAdicSheaf.twistNegOneLevelInverseImageIso`): the comparison
`g⁻¹ 𝓗om(μ, Fₙ) ≅ 𝓗om(g⁻¹μ, g⁻¹Fₙ)` (an isomorphism, `μ` being dualizable), then `g⁻¹ μ ≅ μ` and
`g⁻¹ Fₙ ≅ (g⁻¹F)ₙ`. These isomorphisms commute with the transitions of the two twisted towers
(`Stacks.EtaleCohomology.LAdicSheaf.twistNegOneLevelInverseImageIso_transition`): after
precomposition with the `ℓ`-th power map, which is invertible, this is the compatibility of the
comparison with precomposition across the change of level `ℤ/ℓⁿ⁺² → ℤ/ℓⁿ⁺¹`
(`Stacks.EtaleCohomology.inverseImageRestrictScalars_comp_map_comparison_comp_homPrecomp`), of
`g⁻¹ μ ≅ μ` with the power maps (`Stacks.Kummer.rootsOfUnityModuleInverseImageIso_powMap`) and of
`g⁻¹ Fₙ ≅ (g⁻¹F)ₙ` with the transitions of `F`
(`Stacks.EtaleCohomology.LAdicSheaf.etaleLevelInverseImageIso_transition`). Restricting scalars to
`ℤ_ℓ`, they form an isomorphism of towers of sheaves of `ℤ_ℓ`-modules
(`Stacks.EtaleCohomology.LAdicSheaf.twistNegOneTowerInverseImageIso`), which proves
`Stacks.EtaleCohomology.Purity.TwistNegOneTowerInverseImageInput`
(`Stacks.EtaleCohomology.Purity.twistNegOneTowerInverseImageInput`): the step
`i⁻¹ (G(-1)) ≅ (i⁻¹ G)(-1)` of the tower form of cohomological purity along a divisor
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneLevelInverseImageIso`.
* `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneTowerInverseImageIso`.

## Main results

* `Stacks.EtaleCohomology.inverseImage_twistNegOneTransition_comp`: the generic square.
* `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneLevelInverseImageIso_transition`.
* `Stacks.EtaleCohomology.Purity.twistNegOneTowerInverseImageInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.SmallEtale Stacks.ConstantSheaf Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageMonoidal

/-! ### The square at variable objects -/

section Square

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The chain of the square of the twisted transitions, on variables. -/
theorem twist_square_chain {C D : Type*} [Category* C] [Category* D] (R : C ⥤ D)
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ : D} {q₀ q₁ q₂ q₃ : C}
    (a : o₀ ⟶ o₁) (k : o₁ ⟶ R.obj q₀) (c : q₀ ⟶ q₁) (h : q₁ ⟶ q₃) (P : R.obj q₃ ⟶ o₂)
    (u : q₁ ⟶ q₂) (v : q₂ ⟶ q₃) (P₀ : R.obj q₂ ⟶ o₃) (w : o₃ ⟶ o₂)
    (z : o₁ ⟶ o₄) (cc : o₄ ⟶ o₅) (hs : o₅ ⟶ o₃) (Lt : o₀ ⟶ o₄) (c' : o₀ ⟶ o₆) (ht : o₆ ⟶ o₅)
    (hE : o₆ ⟶ o₇) (τ : o₇ ⟶ R.obj q₃)
    (hsplit : h = u ≫ v) (hPre : R.map v ≫ P = P₀ ≫ w)
    (hCR : k ≫ R.map (c ≫ u) ≫ P₀ = z ≫ cc ≫ hs) (hτ : a ≫ z = Lt) (hc : Lt ≫ cc = c' ≫ ht)
    (hm : ht ≫ hs ≫ w = hE ≫ τ ≫ P) :
    (a ≫ k ≫ R.map (c ≫ h)) ≫ P = ((c' ≫ hE) ≫ τ) ≫ P := by
  calc (a ≫ k ≫ R.map (c ≫ h)) ≫ P = a ≫ (k ≫ R.map (c ≫ u) ≫ P₀) ≫ w := by
        rw [hsplit, ← Category.assoc c u v, R.map_comp]
        simp only [Category.assoc, hPre]
    _ = (a ≫ z) ≫ cc ≫ hs ≫ w := by rw [hCR]; simp only [Category.assoc]
    _ = c' ≫ ht ≫ hs ≫ w := by rw [hτ, ← Category.assoc, hc, Category.assoc]
    _ = ((c' ≫ hE) ≫ τ) ≫ P := by rw [hm]; simp only [Category.assoc]

/-- **The inverse image of the transition of the Tate twist, at variable objects.** Let
`p : M' ⟶ res M`, `t : G' ⟶ res G` on `Y` and `p_X : N' ⟶ res N`, `tx : Gx' ⟶ res Gx` on `X`, with
identifications `r : f⁻¹M ≅ N`, `r' : f⁻¹M' ≅ N'`, `λ : f⁻¹G ≅ Gx`, `λ' : f⁻¹G' ≅ Gx'` compatible
with them. Let `τ`, `τx` be the transitions of the twist: `τ ≫ p^* = 𝓗om(1, t)`,
`τx ≫ p_X^* = 𝓗om(1, tx)`, `p_X^*` mono. Then `E = c ≫ 𝓗om(r⁻¹, λ)` and `E' = c ≫ 𝓗om(r'⁻¹, λ')`
commute with them: `f⁻¹τ ≫ κ ≫ res E = E' ≫ τx`. -/
theorem inverseImage_twistNegOneTransition_comp
    {M G : EtaleModules.{u, 0} Λ' Y} {M' G' : EtaleModules.{u, 0} Λ Y}
    (p : M' ⟶ (etaleModuleRestrictScalars ρ Y).obj M)
    (t : G' ⟶ (etaleModuleRestrictScalars ρ Y).obj G)
    {N Gx : EtaleModules.{u, 0} Λ' X} {N' Gx' : EtaleModules.{u, 0} Λ X}
    (pX : N' ⟶ (etaleModuleRestrictScalars ρ X).obj N)
    (tx : Gx' ⟶ (etaleModuleRestrictScalars ρ X).obj Gx)
    (r : (etaleModuleInverseImage.{u, 0} Λ' f).obj M ≅ N)
    (r' : (etaleModuleInverseImage.{u, 0} Λ f).obj M' ≅ N')
    (lam : (etaleModuleInverseImage.{u, 0} Λ' f).obj G ≅ Gx)
    (lam' : (etaleModuleInverseImage.{u, 0} Λ f).obj G' ≅ Gx')
    (τ : moduleSheafHom Y.smallEtaleTopology Λ M' G' ⟶
      (etaleModuleRestrictScalars ρ Y).obj (moduleSheafHom Y.smallEtaleTopology Λ' M G))
    (hτ : τ ≫ etaleModuleRestrictScalarsHomPrecomp ρ p G =
      moduleSheafHomMap Y.smallEtaleTopology Λ (𝟙 M') t)
    (τx : moduleSheafHom X.smallEtaleTopology Λ N' Gx' ⟶
      (etaleModuleRestrictScalars ρ X).obj (moduleSheafHom X.smallEtaleTopology Λ' N Gx))
    (hτx : τx ≫ etaleModuleRestrictScalarsHomPrecomp ρ pX Gx =
      moduleSheafHomMap X.smallEtaleTopology Λ (𝟙 N') tx)
    (hmono : Mono (etaleModuleRestrictScalarsHomPrecomp ρ pX Gx))
    (hS₁ : (etaleModuleInverseImage.{u, 0} Λ f).map p ≫
        (etaleModuleInverseImageRestrictScalars ρ f).hom.app M ≫
        (etaleModuleRestrictScalars ρ X).map r.hom = r'.hom ≫ pX)
    (hS₂ : (etaleModuleInverseImage.{u, 0} Λ f).map t ≫
        (etaleModuleInverseImageRestrictScalars ρ f).hom.app G ≫
        (etaleModuleRestrictScalars ρ X).map lam.hom = lam'.hom ≫ tx) :
    (etaleModuleInverseImage.{u, 0} Λ f).map τ ≫
        (etaleModuleInverseImageRestrictScalars ρ f).hom.app
          (moduleSheafHom Y.smallEtaleTopology Λ' M G) ≫
        (etaleModuleRestrictScalars ρ X).map
          (etaleModuleInverseImageModuleSheafHomComparison f M G ≫
            moduleSheafHomMap X.smallEtaleTopology Λ' r.inv lam.hom) =
      (etaleModuleInverseImageModuleSheafHomComparison f M' G' ≫
          moduleSheafHomMap X.smallEtaleTopology Λ r'.inv lam'.hom) ≫ τx := by
  have hs : r'.inv ≫ (etaleModuleInverseImage.{u, 0} Λ f).map p ≫
      (etaleModuleInverseImageRestrictScalars ρ f).hom.app M =
      pX ≫ (etaleModuleRestrictScalars ρ X).map r.inv := by
    rw [← cancel_mono ((etaleModuleRestrictScalars ρ X).map r.hom), Category.assoc, Category.assoc,
      hS₁, Iso.inv_hom_id_assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hsplit : moduleSheafHomMap X.smallEtaleTopology Λ' r.inv lam.hom =
      moduleSheafHomMap X.smallEtaleTopology Λ' r.inv (𝟙 _) ≫
        moduleSheafHomMap X.smallEtaleTopology Λ' (𝟙 _) lam.hom := by
    rw [moduleSheafHomMap_comp_moduleSheafHomMap, Category.id_comp, Category.id_comp]
  have hPre := etaleModuleRestrictScalarsHomPrecomp_naturality ρ pX lam.hom
  have hCR := inverseImageRestrictScalars_comp_map_comparison_comp_homPrecomp ρ f (H := G) p pX
    r.inv r'.inv hs
  have hτ' : (etaleModuleInverseImage.{u, 0} Λ f).map τ ≫
      (etaleModuleInverseImage.{u, 0} Λ f).map (etaleModuleRestrictScalarsHomPrecomp ρ p G) =
      (etaleModuleInverseImage.{u, 0} Λ f).map
        (moduleSheafHomMap Y.smallEtaleTopology Λ (𝟙 M') t) := by
    rw [← CategoryTheory.Functor.map_comp, hτ]
  have hc := etaleModuleInverseImageModuleSheafHomComparison_naturality f M' t
  have hm : moduleSheafHomMap X.smallEtaleTopology Λ (𝟙 _)
        ((etaleModuleInverseImage.{u, 0} Λ f).map t) ≫
      moduleSheafHomMap X.smallEtaleTopology Λ r'.inv
        ((etaleModuleInverseImageRestrictScalars ρ f).hom.app G) ≫
      moduleSheafHomMap X.smallEtaleTopology Λ (𝟙 _)
        ((etaleModuleRestrictScalars ρ X).map lam.hom) =
      moduleSheafHomMap X.smallEtaleTopology Λ r'.inv lam'.hom ≫ τx ≫
        etaleModuleRestrictScalarsHomPrecomp ρ pX Gx := by
    rw [hτx, moduleSheafHomMap_comp_moduleSheafHomMap, moduleSheafHomMap_comp_moduleSheafHomMap,
      moduleSheafHomMap_comp_moduleSheafHomMap, ← hS₂]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
  have := hmono
  rw [← cancel_mono (etaleModuleRestrictScalarsHomPrecomp ρ pX Gx)]
  exact twist_square_chain (etaleModuleRestrictScalars ρ X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hsplit hPre hCR hτ' hc hm

end Square

/-! ### The levels -/

/-- The chain of the square of the towers over `ℤ_ℓ`, on variables. -/
theorem tower_square_chain {C D E : Type*} [Category* C] [Category* D] [Category* E] (L : C ⥤ D)
    (R : E ⥤ D) {a₀ a₁ a₂ : C} {d₀ d₁ : D} {e₀ e₁ e₂ e₃ e₄ : E}
    (A : a₀ ⟶ a₁) (Bm : a₁ ⟶ a₂) (κT : L.obj a₂ ⟶ d₀) (RE : d₀ ⟶ d₁)
    (κr : L.obj a₁ ⟶ R.obj e₁) (cY : R.obj e₂ ⟶ d₀) (κ' : L.obj a₀ ⟶ R.obj e₀)
    (cT : R.obj e₃ ⟶ d₁) (x : e₀ ⟶ e₁) (y : e₁ ⟶ e₂) (z : e₂ ⟶ e₃) (w : e₀ ⟶ e₄) (v : e₄ ⟶ e₃)
    (h₁ : L.map Bm ≫ κT = κr ≫ R.map y ≫ cY) (h₂ : L.map A ≫ κr = κ' ≫ R.map x)
    (h₃ : cY ≫ RE = R.map z ≫ cT) (hSQ : x ≫ y ≫ z = w ≫ v) :
    L.map (A ≫ Bm) ≫ κT ≫ RE = (κ' ≫ R.map w) ≫ R.map v ≫ cT := by
  have h₄ : R.map x ≫ R.map y ≫ R.map z = R.map w ≫ R.map v := by
    rw [← R.map_comp, ← R.map_comp, ← R.map_comp, hSQ]
  rw [L.map_comp, Category.assoc, reassoc_of% h₁, reassoc_of% h₂, h₃, reassoc_of% h₄,
    Category.assoc]

attribute [local instance] neZero_pow_of_fact_prime neZero_natCast_pow moduleCat_hasLimitsOfSize

section Tower

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {X Y : B.Scheme} [IsNoetherian X.1] [IsNoetherian Y.1] (g : Y ⟶ X)
  {k : Type u} [Field k] (fX : X.1 ⟶ Spec (.of k)) [NeZero (ℓ : k)]
  (F : LAdicSheaf.{u, u + 1} B X ℓ)

include fX in
/-- `ℓⁿ⁺¹` is invertible on `X`. -/
theorem LAdicSheaf.isUnit_pow_globalSections (n : ℕ) :
    IsUnit (((ℓ ^ (n + 1) : ℕ) : ℕ) : Γ(X.1, ⊤)) :=
  Kummer.isUnit_natCast_globalSections_of_isUnit_field fX (ℓ ^ (n + 1))
    (isUnit_iff_ne_zero.2 (NeZero.ne _))

/-- **Level `n` of the Tate twist commutes with inverse image**:
`g⁻¹ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ) ≅ 𝓗om(g⁻¹ μ_{ℓⁿ⁺¹}, g⁻¹ Fₙ) ≅ 𝓗om(μ_{ℓⁿ⁺¹}, (g⁻¹F)ₙ)`, the comparison (an
isomorphism, `μ_{ℓⁿ⁺¹}` being dualizable) followed by `g⁻¹ μ ≅ μ` and `g⁻¹ Fₙ ≅ (g⁻¹F)ₙ`. -/
def LAdicSheaf.twistNegOneLevelInverseImageIso (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) (B.inclusion.map g)).obj
        (LAdicSheaf.twistNegOneLevel F n) ≅
      LAdicSheaf.twistNegOneLevel (LAdicSheaf.inverseImage g F) n :=
  @asIso _ _ _ _ (etaleModuleInverseImageModuleSheafHomComparison (B.inclusion.map g)
      (Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))) (LAdicSheaf.etaleLevel B X ℓ F n))
    (@isIso_etaleModuleInverseImageModuleSheafHomComparison _ _ _ _ (B.inclusion.map g)
    (Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1)))
    (etaleModuleDual (Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))))
    (etaleModuleDualExactPairing (Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))) (by
      intro V
      obtain ⟨I, W, φ, hcov, htriv⟩ :=
        Kummer.isFreeFiniteLocallyConstant_rootsOfUnityModule.{u, 0} fX (ℓ ^ (n + 1)) V
      exact ⟨I, W, φ, hcov, fun j => by
        obtain ⟨E, hfree, hfin, he⟩ := htriv j
        exact ⟨E, ⟨hfree, hfin⟩, he⟩⟩))
    (LAdicSheaf.etaleLevel B X ℓ F n)) ≪≫
    moduleSheafHomMapIso Y.1.smallEtaleTopology (ZMod (ℓ ^ (n + 1)))
      (Kummer.rootsOfUnityModuleInverseImageIso (B.inclusion.map g) (ℓ ^ (n + 1))
        (LAdicSheaf.isUnit_pow_globalSections fX n))
      (LAdicSheaf.etaleLevelInverseImageIso B g ℓ F n)

/-- The identification at level `n` is the comparison followed by `𝓗om(r⁻¹, λ)`. -/
theorem LAdicSheaf.twistNegOneLevelInverseImageIso_hom (n : ℕ) :
    (LAdicSheaf.twistNegOneLevelInverseImageIso g fX F n).hom =
      etaleModuleInverseImageModuleSheafHomComparison (B.inclusion.map g)
          (Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1))) (LAdicSheaf.etaleLevel B X ℓ F n) ≫
        moduleSheafHomMap Y.1.smallEtaleTopology (ZMod (ℓ ^ (n + 1)))
          (Kummer.rootsOfUnityModuleInverseImageIso (B.inclusion.map g) (ℓ ^ (n + 1))
            (LAdicSheaf.isUnit_pow_globalSections fX n)).inv
          (LAdicSheaf.etaleLevelInverseImageIso B g ℓ F n).hom :=
  rfl

/-- The transition of the Tate twist, followed by the precomposition with the power map, is the
map induced by the transition of the tower. -/
private theorem twistNegOneTransition_comp_homPrecomp {Z : B.Scheme} [IsNoetherian Z.1]
    (fZ : Z.1 ⟶ Spec (.of k)) (G : LAdicSheaf.{u, u + 1} B Z ℓ) (n : ℕ) :
    LAdicSheaf.twistNegOneTransition fZ G n ≫
      etaleModuleRestrictScalarsHomPrecomp (levelCast ℓ n)
        (Kummer.rootsOfUnityModulePowMap.{u, 0} Z.1 ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1))
          (mul_pow_succ_eq ℓ n)) (LAdicSheaf.etaleLevel B Z ℓ G n) =
      moduleSheafHomMap Z.1.smallEtaleTopology (ZMod (ℓ ^ (n + 1 + 1))) (𝟙 _)
        (LAdicSheaf.etaleTransition B Z ℓ G n) :=
  (congrArg (LAdicSheaf.twistNegOneTransition fZ G n ≫ ·)
    (Kummer.twistNegOnePrecompPow_eq_etaleModuleRestrictScalarsHomPrecomp Z.1 ℓ (ℓ ^ (n + 1))
      (ℓ ^ (n + 1 + 1)) (mul_pow_succ_eq ℓ n) (LAdicSheaf.etaleLevel B Z ℓ G n))).symm.trans
    (Kummer.twistNegOneModuleTransition_comp_precompPow.{u, 0} Z.1 ℓ (ℓ ^ (n + 1))
      (ℓ ^ (n + 1 + 1)) (mul_pow_succ_eq ℓ n) (LAdicSheaf.etaleLevel B Z ℓ G n) fZ
      (LAdicSheaf.etaleLevel B Z ℓ G (n + 1)) (LAdicSheaf.etaleTransition B Z ℓ G n))

/-- **The levelwise identifications commute with the transitions of the Tate twist**:
`g⁻¹ τₙ`, read through `g⁻¹ ∘ res ≅ res ∘ g⁻¹` and the identification at level `n`, is the
identification at level `n + 1` followed by the transition of the twist of `g⁻¹F`. -/
theorem LAdicSheaf.twistNegOneLevelInverseImageIso_transition (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) (B.inclusion.map g)).map
        (LAdicSheaf.twistNegOneTransition fX F n) ≫
      (etaleModuleInverseImageRestrictScalars (levelCast ℓ n) (B.inclusion.map g)).hom.app
        (LAdicSheaf.twistNegOneLevel F n) ≫
      (etaleModuleRestrictScalars (levelCast ℓ n) Y.1).map
        (LAdicSheaf.twistNegOneLevelInverseImageIso g fX F n).hom =
    (LAdicSheaf.twistNegOneLevelInverseImageIso g fX F (n + 1)).hom ≫
      LAdicSheaf.twistNegOneTransition (B.inclusion.map g ≫ fX)
        (LAdicSheaf.inverseImage g F) n := by
  have hN := mul_pow_succ_eq ℓ n
  have : IsIso (etaleModuleRestrictScalarsHomPrecomp (levelCast ℓ n)
      (Kummer.rootsOfUnityModulePowMap.{u, 0} Y.1 ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1)) hN)
      (LAdicSheaf.etaleLevel B Y ℓ (LAdicSheaf.inverseImage g F) n)) :=
    (Kummer.twistNegOnePrecompPow_eq_etaleModuleRestrictScalarsHomPrecomp Y.1 ℓ (ℓ ^ (n + 1))
      (ℓ ^ (n + 1 + 1)) hN (LAdicSheaf.etaleLevel B Y ℓ (LAdicSheaf.inverseImage g F) n)) ▸
    Kummer.isIso_twistNegOnePrecompPow.{u, 0} Y.1 ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1)) hN
      (LAdicSheaf.etaleLevel B Y ℓ (LAdicSheaf.inverseImage g F) n) (B.inclusion.map g ≫ fX)
  have hS₁ := Kummer.rootsOfUnityModuleInverseImageIso_powMap (B.inclusion.map g) ℓ (ℓ ^ (n + 1))
    (ℓ ^ (n + 1 + 1)) hN (LAdicSheaf.isUnit_pow_globalSections fX n)
    (LAdicSheaf.isUnit_pow_globalSections fX (n + 1))
  have hS₂ := LAdicSheaf.etaleLevelInverseImageIso_transition.{u} B g ℓ F n
  rw [LAdicSheaf.twistNegOneLevelInverseImageIso_hom,
    LAdicSheaf.twistNegOneLevelInverseImageIso_hom]
  exact inverseImage_twistNegOneTransition_comp.{u} (levelCast ℓ n) (B.inclusion.map g)
    (p := Kummer.rootsOfUnityModulePowMap.{u, 0} X.1 ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1)) hN)
    (t := LAdicSheaf.etaleTransition B X ℓ F n)
    (pX := Kummer.rootsOfUnityModulePowMap.{u, 0} Y.1 ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1)) hN)
    (tx := LAdicSheaf.etaleTransition B Y ℓ (LAdicSheaf.inverseImage g F) n)
    (r := Kummer.rootsOfUnityModuleInverseImageIso (B.inclusion.map g) (ℓ ^ (n + 1))
      (LAdicSheaf.isUnit_pow_globalSections fX n))
    (r' := Kummer.rootsOfUnityModuleInverseImageIso (B.inclusion.map g) (ℓ ^ (n + 1 + 1))
      (LAdicSheaf.isUnit_pow_globalSections fX (n + 1)))
    (lam := LAdicSheaf.etaleLevelInverseImageIso B g ℓ F n)
    (lam' := LAdicSheaf.etaleLevelInverseImageIso B g ℓ F (n + 1))
    (τ := LAdicSheaf.twistNegOneTransition fX F n)
    (twistNegOneTransition_comp_homPrecomp fX F n)
    (τx := LAdicSheaf.twistNegOneTransition (B.inclusion.map g ≫ fX)
      (LAdicSheaf.inverseImage g F) n)
    (twistNegOneTransition_comp_homPrecomp (B.inclusion.map g ≫ fX) (LAdicSheaf.inverseImage g F) n)
    (IsIso.mono_of_iso _) hS₁ hS₂

/-- The identification at level `n`, over `ℤ_ℓ`: `g⁻¹ ∘ res ≅ res ∘ g⁻¹` followed by the
restriction of scalars of `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneLevelInverseImageIso`. -/
abbrev LAdicSheaf.twistNegOneLevelPadicInverseImageIso (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g)).obj
        ((etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1).obj
          (LAdicSheaf.twistNegOneLevel F n)) ≅
      (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) Y.1).obj
        (LAdicSheaf.twistNegOneLevel (LAdicSheaf.inverseImage g F) n) :=
  (etaleModuleInverseImageRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1))
      (B.inclusion.map g)).app (LAdicSheaf.twistNegOneLevel F n) ≪≫
    (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) Y.1).mapIso
      (LAdicSheaf.twistNegOneLevelInverseImageIso g fX F n)

/-- **The Tate twist commutes with inverse image, on towers**: the inverse image of the tower
`n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` of sheaves of `ℤ_ℓ`-modules is the tower `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, (g⁻¹F)ₙ)`. -/
def LAdicSheaf.twistNegOneTowerInverseImageIso :
    LAdicSheaf.twistNegOneTower fX F ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g) ≅
      LAdicSheaf.twistNegOneTower (B.inclusion.map g ≫ fX) (LAdicSheaf.inverseImage g F) :=
  let α : LAdicSheaf.twistNegOneTower fX F ⋙
      etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g) ⟶
      LAdicSheaf.twistNegOneTower (B.inclusion.map g ≫ fX) (LAdicSheaf.inverseImage g F) :=
    NatTrans.ofOpSequence (fun n => (LAdicSheaf.twistNegOneLevelPadicInverseImageIso g fX F n).hom)
      (fun n => by
        rw [Functor.comp_map, LAdicSheaf.twistNegOneTower_map_succ,
          LAdicSheaf.twistNegOneTower_map_succ]
        exact tower_square_chain (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g))
          (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) Y.1)
          _ _ _ _ _ _ _ _ _ _ _ _ _
          (etaleModuleInverseImageRestrictScalars_comp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))
            (levelCast ℓ n) (PadicInt.toZModPow (p := ℓ) (n + 1)) (toZModPow_succ_comp ℓ n)
            (B.inclusion.map g) (LAdicSheaf.twistNegOneLevel F n))
          ((etaleModuleInverseImageRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))
            (B.inclusion.map g)).hom.naturality (LAdicSheaf.twistNegOneTransition fX F n))
          ((etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))
            (levelCast ℓ n) (PadicInt.toZModPow (p := ℓ) (n + 1)) (toZModPow_succ_comp ℓ n)
            Y.1).hom.naturality (LAdicSheaf.twistNegOneLevelInverseImageIso g fX F n).hom).symm
          (LAdicSheaf.twistNegOneLevelInverseImageIso_transition g fX F n))
  haveI : IsIso α :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun n => by
      induction n using Opposite.rec with
      | op n =>
        exact (inferInstance :
          IsIso (LAdicSheaf.twistNegOneLevelPadicInverseImageIso g fX F n).hom))
  asIso α

end Tower

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology.Purity

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The Tate twist commutes with inverse image, on towers** (the proposition
`Stacks.EtaleCohomology.Purity.TwistNegOneTowerInverseImageInput`): it holds for every ℓ-adic
sheaf, lisse or not, by `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneTowerInverseImageIso`. -/
theorem twistNegOneTowerInverseImageInput : TwistNegOneTowerInverseImageInput B ℓ :=
  fun _ _ _ _ g _ _ fX _ F _ => ⟨LAdicSheaf.twistNegOneTowerInverseImageIso g fX F⟩

end Stacks.EtaleCohomology.Purity

end
