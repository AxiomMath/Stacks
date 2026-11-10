module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairFunctor07JG
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTaylorLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StratifiedCrystal

/-!
# Taylor data of the system of [Stacks, Tag 07JN], and Taylor's formula for `d : D → Ω_D`

The descent system `...SmallSite.wholeSpaceDescentSystem` of the levels `T(n)_e` of
[Stacks, Tag 07JN] on the affine subsite carries the Taylor data
`Crystalline.StratifiedDescent.TaylorData` the Taylor stratification of a pair is built from:

* the monomials `ξ^{[K]}` of `Γ(T(1)_e, 𝒪)` and `v^{[K]} u^{[L]}` of `Γ(T(2)_e, 𝒪)`, the
  reductions of those of the envelopes `E(1)` and `E(2)` (`...SmallSite.levelTaylorMonomial`,
  `...SmallSite.levelTaylorMonomial₂`);
* the Taylor coefficients `δ_K : D → D` of the completed envelope `D = lim_e Γ(T_e, 𝒪)`
  (`...SmallSite.envDTaylorCoeff`): at the level `e` the section ring `Γ(T(1)_e, 𝒪)` is free over
  `Γ(T_e, 𝒪)` through the first projection on the `ξ^{[K]}`
  (`...SmallSite.levelRingTaylorExpansion`), so `p₁(d) = ∑_K ξ^{[K]} p₀(θ_K d)` for unique
  `θ_K d`, and these are compatible with the levels;
* the prime `p` and the exponents `N + e` with `p^{N + e} = 0` on the level `e`.

The structure maps of the descent system, defined there from the product property, are
identified with the cosimplicial maps (`...SmallSite.wholeSpaceDescentSystem_diag_hom` and the
face and level versions), after which every field is a statement about the envelopes.

Then **Taylor's formula for the derivation**: for the coordinate functionals
`...SmallSite.pairCoord` of `Ω_D` (the completed coordinates of the basis of `Ω_{E(0)}` on the
`d x_c`, [Stacks, Tag 07HW]), `c_i(d f) = -δ_{e_i}(f)` for every `f ∈ D`
(`...SmallSite.pairCoord_pairDerivation`).  On the image of `E(0)` this is
`...SmallSite.pairDerivation_pairOf`; in general both sides are additive and agree modulo every
`p^{N + e}`, hence agree at every level.  The coordinate functionals are dual to the `d x_c` by
`...SmallSite.isCoordinateDual_pairDx`.

## Main results

* `...SmallSite.wholeSpaceTaylorData` — the Taylor data of the system.
* `...SmallSite.isThetaMonomialFamily_wholeSpaceTaylorData_delta` — `δ_K = ∏_i δ_{e_i}^{k_i}`.
* `...SmallSite.pairCoord_pairDerivation` — Taylor's formula `c_i(d f) = -δ_{e_i}(f)`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.6.9, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline StratifiedDescent

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-! ### Restrictions of the structure sheaf along the system -/

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- Restricting sections of `𝒪_{X/S}` along two composable morphisms is restricting along the
composite. -/
theorem sheafRingMap_sheafRingMap {A B C : CrystallineThickening S} (k : A ⟶ B) (l : B ⟶ C)
    (x : crysSheafRing S C.obj) : sheafRingMap k (sheafRingMap l x) = sheafRingMap (k ≫ l) x :=
  crysSheafRingMap_comp k.hom l.hom x

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- Restricting sections of `𝒪_{X/S}` along an identity is the identity. -/
theorem sheafRingMap_id (A : CrystallineThickening S) (x : crysSheafRing S A.obj) :
    sheafRingMap (𝟙 A) x = x := by
  change ((crystallineStructureSheaf S).obj.map (𝟙 A.obj).op).hom x = x
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Two composites of cosimplicial transitions with the same composite restrict sections of
`𝒪_{X/S}` alike. -/
theorem sheafRingMap_wholeSpaceTrans_comp_eq {l m n : ℕ}
    {φ φ' : (⦋l⦌ : SimplexCategory) ⟶ ⦋m⦌} {ψ ψ' : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌}
    (h : φ ≫ ψ = φ' ≫ ψ') (e : ℕ) (x : crysSheafRing S (levelObj hp l e).obj) :
    sheafRingMap (wholeSpaceTrans hp ψ e) (sheafRingMap (wholeSpaceTrans hp φ e) x) =
      sheafRingMap (wholeSpaceTrans hp ψ' e) (sheafRingMap (wholeSpaceTrans hp φ' e) x) := by
  rw [sheafRingMap_sheafRingMap, sheafRingMap_sheafRingMap, wholeSpaceTrans_comp,
    wholeSpaceTrans_comp, h]

/-- Restricting along a cosimplicial transition followed by restricting along another one. -/
theorem sheafRingMap_wholeSpaceTrans_comp {l m n : ℕ} (φ : (⦋l⦌ : SimplexCategory) ⟶ ⦋m⦌)
    (ψ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (e : ℕ) (x : crysSheafRing S (levelObj hp l e).obj) :
    sheafRingMap (wholeSpaceTrans hp ψ e) (sheafRingMap (wholeSpaceTrans hp φ e) x) =
      sheafRingMap (wholeSpaceTrans hp (φ ≫ ψ) e) x := by
  rw [sheafRingMap_sheafRingMap, wholeSpaceTrans_comp]

/-- Restricting along the cosimplicial transition of an identity. -/
theorem sheafRingMap_wholeSpaceTrans_id {n : ℕ} (e : ℕ)
    (x : crysSheafRing S (levelObj hp n e).obj) :
    sheafRingMap (wholeSpaceTrans hp (𝟙 (⦋n⦌ : SimplexCategory)) e) x = x := by
  rw [wholeSpaceTrans_id, sheafRingMap_id]

/-- **The reduction `D → Γ(T_e, 𝒪)`**, `...SmallSite.levelSectionsScalars` with its target read
as the sections of `𝒪_{X/S}` over the object `T_e` of `Cris(X/S)`. -/
def levelRed (e : ℕ) : envD S hp →+* crysSheafRing S (levelObj hp 0 e).obj :=
  levelSectionsScalars hp ⦋0⦌ e

/-- The reduction of the image of an element of `E(0)` is `...SmallSite.envLevelMap`. -/
theorem levelRed_wsCompletionMap (e : ℕ) (y : wsEnvelope hp 0) :
    levelRed hp e (wsCompletionMap hp 0 y) = envLevelMap hp 0 e y := rfl

/-- The reductions `D → Γ(T_e, 𝒪)` are compatible with the level maps. -/
theorem sheafRingMap_levelRed {e e' : ℕ} (h : e ⟶ e') (d : envD S hp) :
    sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h) (levelRed hp e' d) =
      levelRed hp e d := by
  have hl := (envelopeLevelRingLimitEquiv hp 0
    ((wholeSpaceSystemEnvelopeRingEquiv hp 0).symm d)).property h
  have h1 := levelSectionsScalars_eq_envelopeLevelRingLimitEquiv hp ⦋0⦌ e' d
  have h0 := levelSectionsScalars_eq_envelopeLevelRingLimitEquiv hp ⦋0⦌ e d
  change ((structureSheaf S).obj.map _).hom (levelSectionsScalars hp ⦋0⦌ e' d) =
    levelSectionsScalars hp ⦋0⦌ e d
  rw [h1, h0]
  exact hl

/-- **An element of `D` is determined by its reductions to the levels.** -/
theorem eq_of_levelRed_eq {x y : envD S hp} (h : ∀ e, levelRed hp e x = levelRed hp e y) :
    x = y := by
  apply (wholeSpaceSystemEnvelopeRingEquiv hp 0).symm.injective
  apply (envelopeLevelRingLimitEquiv hp 0).injective
  refine Subtype.ext (funext fun e ↦ ?_)
  have hx := levelSectionsScalars_eq_envelopeLevelRingLimitEquiv hp ⦋0⦌ e x
  have hy := levelSectionsScalars_eq_envelopeLevelRingLimitEquiv hp ⦋0⦌ e y
  exact hx.symm.trans ((h e).trans hy)

/-- The element of `D` with prescribed compatible reductions to the levels. -/
def envDOfLevels (a : levelRingLimit S ((wholeSpaceSystem S hp).obj (op ⦋0⦌))) : envD S hp :=
  wholeSpaceSystemEnvelopeRingEquiv hp 0 ((envelopeLevelRingLimitEquiv hp 0).symm a)

/-- The reductions of `...SmallSite.envDOfLevels a` are the components of `a`. -/
theorem levelRed_envDOfLevels (a : levelRingLimit S ((wholeSpaceSystem S hp).obj (op ⦋0⦌)))
    (e : ℕ) : levelRed hp e (envDOfLevels hp a) = a.val e := by
  have h := levelSectionsScalars_eq_envelopeLevelRingLimitEquiv hp ⦋0⦌ e (envDOfLevels hp a)
  change _ = (envelopeLevelRingLimitEquiv hp 0
    ((wholeSpaceSystemEnvelopeRingEquiv hp 0).symm (envDOfLevels hp a))).val e at h
  rw [envDOfLevels, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at h
  exact h

/-- `p^{N + e}` vanishes in `Γ(T_e, 𝒪)`, as the reduction of `D`. -/
theorem levelRed_pow (e : ℕ) :
    levelRed hp e
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) : envD S hp) =
        0 := by
  have h := envLevelMap_pow hp 0 e
  rwa [← levelRed_wsCompletionMap, map_natCast] at h

/-! ### Taylor's formula for `𝒪` at a level -/

/-- **The Taylor expansion datum of `𝒪_{X/S}` at the level `e`**: the two restrictions
`p₀, p₁ : Γ(T_e, 𝒪) → Γ(T(1)_e, 𝒪)` and the monomials `ξ^{[K]}`, on which `Γ(T(1)_e, 𝒪)` is free
over `Γ(T_e, 𝒪)` through `p₀` (`...SmallSite.bijective_levelTaylorMonomial`). -/
def levelRingTaylorExpansion (e : ℕ) :
    TaylorExpansion (crysSheafRing S (levelObj hp 1 e).obj)
      (crysSheafRing S (levelObj hp 0 e).obj) (crysSheafRing S (levelObj hp 1 e).obj)
      (wholeSpaceIndex S hp) where
  a₀ := (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 1) e)).toAddMonoidHom
  a₁ := (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 0) e)).toAddMonoidHom
  xi := levelTaylorMonomial hp e
  bijective := bijective_levelTaylorMonomial hp e

/-- **The Taylor coefficients of a reduction of an element of `E(0)`** are the reductions of its
Taylor coefficients `Crystalline.envelopeTaylorCoeff`. -/
theorem levelRingTaylorExpansion_coeffs_envLevelMap (e : ℕ) (y : wsEnvelope hp 0) :
    (levelRingTaylorExpansion hp e).coeffs (envLevelMap hp 0 e y) =
      (envelopeTaylorCoeff _ _ y).mapRange (envLevelMap hp 0 e) (map_zero _) := by
  refine (levelRingTaylorExpansion hp e).coeffs_eq_of_taylorSum ?_
  have hT := (envelopeTaylorExpansion (affineSituation S hp)
    (wholeSpacePresentation S hp)).taylorSum_coeffs y
  rw [envelopeTaylorExpansion_coeffs, taylorSum_apply] at hT
  rw [taylorSum_apply, Finsupp.sum_mapRange_index (fun _ ↦ by rw [map_zero, smul_zero])]
  change _ = sheafRingMap _ (envLevelMap hp 0 e y)
  rw [envLevelMap_restriction]
  change _ = envLevelMap hp 1 e ((envelopeTaylorExpansion (affineSituation S hp)
    (wholeSpacePresentation S hp)).a₁ y)
  rw [← hT, map_finsuppSum]
  refine Finsupp.sum_congr fun K _ ↦ ?_
  change envLevelMap hp 1 e (envelopeTaylorMonomial _ _ K) *
      sheafRingMap _ (envLevelMap hp 0 e _) =
    envLevelMap hp 1 e (envelopeTaylorMonomial _ _ K * envReindex _ _ _ _)
  rw [envLevelMap_restriction, map_mul]

/-- The operators `θ_K` of `𝒪_{X/S}` at a level on the reduction of an element `y` of `E(0)` are
the reductions of the Taylor coefficients `δ_K(y)`. -/
theorem levelRingTaylorExpansion_theta_envLevelMap (e : ℕ) (K : wholeSpaceIndex S hp →₀ ℕ)
    (y : wsEnvelope hp 0) :
    (levelRingTaylorExpansion hp e).theta K (envLevelMap hp 0 e y) =
      envLevelMap hp 0 e (envelopeTaylorCoeff _ _ y K) := by
  rw [TaylorExpansion.theta_apply, levelRingTaylorExpansion_coeffs_envLevelMap,
    Finsupp.mapRange_apply]

/-- `θ_0 = id` for `𝒪_{X/S}` at every level. -/
theorem levelRingTaylorExpansion_theta_zero (e : ℕ) (x : crysSheafRing S (levelObj hp 0 e).obj) :
    (levelRingTaylorExpansion hp e).theta 0 x = x :=
  (levelRingTaylorExpansion hp e).theta_zero (R₀ := crysSheafRing S (levelObj hp 0 e).obj)
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.σ (n := 0) 0) e))
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.σ (n := 0) 0) e)).toAddMonoidHom
    (fun r y ↦ map_mul (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.σ (n := 0) 0) e)) r y)
    (fun m ↦ by
      change sheafRingMap _ (sheafRingMap _ m) = m
      rw [sheafRingMap_wholeSpaceTrans_comp, δ_one_comp_σ_zero, sheafRingMap_wholeSpaceTrans_id])
    (fun m ↦ by
      change sheafRingMap _ (sheafRingMap _ m) = m
      rw [sheafRingMap_wholeSpaceTrans_comp, δ_zero_comp_σ_zero, sheafRingMap_wholeSpaceTrans_id])
    (by
      change sheafRingMap _ (envLevelMap hp 1 e (envelopeTaylorMonomial _ _ 0)) = 1
      rw [envelopeTaylorMonomial_zero, map_one, map_one])
    (fun K hK ↦ by
      change sheafRingMap _ (envLevelMap hp 1 e (envelopeTaylorMonomial _ _ K)) = 0
      rw [envLevelMap_restriction, envReindex_degeneracy_envelopeTaylorMonomial _ _ hK, map_zero])
    x

/-- `θ_L ∘ θ_K = θ_{K + L}` for `𝒪_{X/S}` at every level, from `Γ(T(2)_e, 𝒪)`. -/
theorem levelRingTaylorExpansion_theta_theta (e : ℕ)
    (K L : wholeSpaceIndex S hp →₀ ℕ) (x : crysSheafRing S (levelObj hp 0 e).obj) :
    (levelRingTaylorExpansion hp e).theta L ((levelRingTaylorExpansion hp e).theta K x) =
      (levelRingTaylorExpansion hp e).theta (K + L) x := by
  classical
  refine (levelRingTaylorExpansion hp e).theta_theta
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) e)).toAddMonoidHom
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 2) e)).toAddMonoidHom
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 0) e)).toAddMonoidHom
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 1) e)).toAddMonoidHom
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 2) e))
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 0) e))
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 1) e))
    (fun r y ↦ map_mul (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 2) e)) r y)
    (fun r y ↦ map_mul (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 0) e)) r y)
    (fun r y ↦ map_mul (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 1) e)) r y)
    (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (levelTaylorMonomial₂ hp e)
    (fun L ↦ ?_) (fun K ↦ ?_) (fun N ↦ ?_) (fun K L ↦ ?_)
    (bijective_levelTaylorMonomial₂ hp e).1 K L x
  · exact (sheafRingMap_wholeSpaceTrans_comp hp _ _ e m).trans (by rw [δ_one_comp_δ_two]; rfl)
  · exact (sheafRingMap_wholeSpaceTrans_comp hp _ _ e m).trans (by rw [δ_one_comp_δ_one]; rfl)
  · exact sheafRingMap_wholeSpaceTrans_comp_eq hp δ_one_comp_δ_zero e m
  · exact sheafRingMap_wholeSpaceTrans_comp_eq hp δ_zero_comp_δ_zero e m
  · change sheafRingMap _ (envLevelMap hp 1 e _) = envLevelMap hp 2 e _
    rw [envLevelMap_restriction, envReindex_delta_two_envelopeTaylorMonomial]
  · change sheafRingMap _ (envLevelMap hp 1 e _) = envLevelMap hp 2 e _
    rw [envLevelMap_restriction, envReindex_delta_zero_envelopeTaylorMonomial]
  · change sheafRingMap _ (envLevelMap hp 1 e _) = ∑ x ∈ _, envLevelMap hp 2 e _
    rw [envLevelMap_restriction, envReindex_delta_one_envelopeTaylorMonomial, map_sum]
  · change envLevelMap hp 2 e _ * envLevelMap hp 2 e _ = envLevelMap hp 2 e _
    rw [← map_mul, envelopeTaylorMonomial₂_mul]

/-- Restricting along a cosimplicial transition and a level map commute. -/
private theorem sheafRingMap_levelMap_sheafRingMap_wholeSpaceTrans {e e' : ℕ} (h : e ⟶ e')
    {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (x : crysSheafRing S (levelObj hp m e').obj) :
    sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map h)
        (sheafRingMap (wholeSpaceTrans hp φ e') x) =
      sheafRingMap (wholeSpaceTrans hp φ e)
        (sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋m⦌)).map h) x) := by
  rw [sheafRingMap_sheafRingMap, sheafRingMap_sheafRingMap, wholeSpaceTrans_naturality]

/-- The operators `θ_K` of `𝒪_{X/S}` are compatible with the restrictions between the levels. -/
theorem levelRingTaylorExpansion_theta_levelMap {e e' : ℕ} (h : e ⟶ e')
    (K : wholeSpaceIndex S hp →₀ ℕ) (x : crysSheafRing S (levelObj hp 0 e').obj) :
    (levelRingTaylorExpansion hp e).theta K
        (sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h) x) =
      sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h)
        ((levelRingTaylorExpansion hp e').theta K x) :=
  (levelRingTaylorExpansion hp e').theta_naturality (levelRingTaylorExpansion hp e)
    (sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h)).toAddMonoidHom
    (sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋1⦌)).map h)).toAddMonoidHom
    (sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋1⦌)).map h))
    (fun r y ↦ map_mul (sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋1⦌)).map h)) r y)
    (fun _ ↦ envLevelMap_levelMap hp 1 h _)
    (sheafRingMap_levelMap_sheafRingMap_wholeSpaceTrans hp h _)
    (sheafRingMap_levelMap_sheafRingMap_wholeSpaceTrans hp h _)
    K x

/-! ### The Taylor coefficients of `D` -/

/-- The `θ_K` of the reductions of an element of `D` form a compatible family. -/
theorem levelRingTaylorExpansion_theta_mem (K : wholeSpaceIndex S hp →₀ ℕ) (d : envD S hp) :
    (fun e ↦ (levelRingTaylorExpansion hp e).theta K (levelRed hp e d)) ∈
      levelRingLimit S ((wholeSpaceSystem S hp).obj (op ⦋0⦌)) := by
  intro e e' h
  change sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h)
      ((levelRingTaylorExpansion hp e').theta K (levelRed hp e' d)) =
    (levelRingTaylorExpansion hp e).theta K (levelRed hp e d)
  rw [← levelRingTaylorExpansion_theta_levelMap, sheafRingMap_levelRed]

/-- **The Taylor coefficient `δ_K : D → D`**: the element of `D = lim_e Γ(T_e, 𝒪)` whose
reduction to every level is `θ_K` of the reduction, `θ_K` the Taylor coefficient of `𝒪_{X/S}`
over `T(1)_e`. -/
def envDTaylorCoeff (K : wholeSpaceIndex S hp →₀ ℕ) : envD S hp →+ envD S hp :=
  AddMonoidHom.mk' (fun d ↦ envDOfLevels hp ⟨_, levelRingTaylorExpansion_theta_mem hp K d⟩)
    fun d d' ↦ eq_of_levelRed_eq hp fun e ↦ by
      rw [map_add, levelRed_envDOfLevels, levelRed_envDOfLevels, levelRed_envDOfLevels]
      simp only [map_add]

/-- **The reductions of `δ_K(d)` are the `θ_K` of the reductions of `d`.** -/
theorem levelRed_envDTaylorCoeff (K : wholeSpaceIndex S hp →₀ ℕ) (d : envD S hp) (e : ℕ) :
    levelRed hp e (envDTaylorCoeff hp K d) =
      (levelRingTaylorExpansion hp e).theta K (levelRed hp e d) :=
  levelRed_envDOfLevels hp _ e

/-- **`δ_K` extends the Taylor coefficients of `E(0)`.** -/
theorem envDTaylorCoeff_wsCompletionMap (K : wholeSpaceIndex S hp →₀ ℕ)
    (y : wsEnvelope hp 0) :
    envDTaylorCoeff hp K (wsCompletionMap hp 0 y) =
      wsCompletionMap hp 0 (envelopeTaylorCoeff _ _ y K) :=
  eq_of_levelRed_eq hp fun e ↦ by
    rw [levelRed_envDTaylorCoeff, levelRed_wsCompletionMap, levelRed_wsCompletionMap,
      levelRingTaylorExpansion_theta_envLevelMap]

/-- `δ_0 = id`. -/
theorem envDTaylorCoeff_zero (d : envD S hp) : envDTaylorCoeff hp 0 d = d :=
  eq_of_levelRed_eq hp fun e ↦ by
    rw [levelRed_envDTaylorCoeff, levelRingTaylorExpansion_theta_zero]

/-- `δ_L ∘ δ_K = δ_{K + L}`. -/
theorem envDTaylorCoeff_envDTaylorCoeff
    (K L : wholeSpaceIndex S hp →₀ ℕ) (d : envD S hp) :
    envDTaylorCoeff hp L (envDTaylorCoeff hp K d) = envDTaylorCoeff hp (K + L) d :=
  eq_of_levelRed_eq hp fun e ↦ by
    rw [levelRed_envDTaylorCoeff, levelRed_envDTaylorCoeff, levelRed_envDTaylorCoeff,
      levelRingTaylorExpansion_theta_theta]

/-! ### The structure maps of the descent system are the cosimplicial maps -/

/-- A cosimplicial transition followed by a vertex is a vertex. -/
theorem wholeSpaceTrans_comp_wholeSpaceVertex {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌)
    (e : ℕ) (j : Fin (m + 1)) :
    wholeSpaceTrans hp φ e ≫ wholeSpaceVertex S hp m e j =
      wholeSpaceVertex S hp n e (φ.toOrderHom j) := by
  change wholeSpaceTrans hp φ e ≫ wholeSpaceTrans hp (SimplexCategory.const ⦋0⦌ ⦋m⦌ j) e =
    wholeSpaceTrans hp (SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom j)) e
  rw [wholeSpaceTrans_comp, SimplexCategory.const_comp]

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The structure maps of the descent system are read on the section rings as restrictions. -/
theorem affineSectionsRing_map_apply {A B : AffineCrystallineThickening S} (k : A ⟶ B)
    (x : crysSheafRing S B.obj.obj) :
    ((affineSectionsRing S).map k.op).hom x = sheafRingMap k.hom x := rfl

/-- The vertex `0` of `T(1)_e` is the first projection `δ 1`. -/
theorem wholeSpaceVertex_one_zero (e : ℕ) :
    wholeSpaceVertex S hp 1 e 0 = wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 1) e := by
  change wholeSpaceTrans hp (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) e = _
  congr 1
  ext i; fin_cases i; rfl

/-- The vertex `1` of `T(1)_e` is the second projection `δ 0`. -/
theorem wholeSpaceVertex_one_one (e : ℕ) :
    wholeSpaceVertex S hp 1 e 1 = wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 0) e := by
  change wholeSpaceTrans hp (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) e = _
  congr 1
  ext i; fin_cases i; rfl

/-- A map into `T(1)_e` of the descent system is the given map of thickenings once their
compositions with the two vertices agree. -/
private theorem wholeSpaceDescentSystem_hom_eq {A : AffineCrystallineThickening S} {e : ℕ}
    (f : A ⟶ (wholeSpaceDescentSystem S hp).T1 e)
    (g : A.obj ⟶ ((wholeSpaceDescentSystem S hp).T1 e).obj)
    (h₀ : g ≫ wholeSpaceVertex S hp 1 e 0 = (f ≫ (wholeSpaceDescentSystem S hp).v e 0).hom)
    (h₁ : g ≫ wholeSpaceVertex S hp 1 e 1 = (f ≫ (wholeSpaceDescentSystem S hp).v e 1).hom) :
    f.hom = g := by
  have : f = ObjectProperty.homMk g :=
    (wholeSpaceDescentSystem S hp).hom_ext_T1
      (InducedCategory.hom_ext h₀.symm) (InducedCategory.hom_ext h₁.symm)
  rw [this]
  rfl

/-- The diagonal of the descent system is the degeneracy `σ 0`. -/
theorem wholeSpaceDescentSystem_diag_hom (e : ℕ) :
    ((wholeSpaceDescentSystem S hp).diag e).hom =
      wholeSpaceTrans hp (SimplexCategory.σ (n := 0) 0) e :=
  wholeSpaceDescentSystem_hom_eq hp _ _
    (by rw [System.diag_v]; exact σ_app_comp_wholeSpaceVertex hp e 0)
    (by rw [System.diag_v]; exact σ_app_comp_wholeSpaceVertex hp e 1)

/-- A cosimplicial transition followed by a vertex is a vertex, with the value of the map named. -/
theorem wholeSpaceTrans_comp_wholeSpaceVertex_of_eq {m n : ℕ}
    (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (e : ℕ) (j : Fin (m + 1)) (k : Fin (n + 1))
    (hk : φ.toOrderHom j = k) :
    wholeSpaceTrans hp φ e ≫ wholeSpaceVertex S hp m e j = wholeSpaceVertex S hp n e k := by
  rw [wholeSpaceTrans_comp_wholeSpaceVertex, hk]

/-- The face `p₀₁` of the descent system is the coface `δ 2`. -/
theorem wholeSpaceDescentSystem_face01_hom (e : ℕ) :
    ((wholeSpaceDescentSystem S hp).face01 e).hom =
      wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 2) e :=
  wholeSpaceDescentSystem_hom_eq hp _ _
    (by rw [System.face01_v_zero]; exact wholeSpaceTrans_comp_wholeSpaceVertex_of_eq hp _ e 0 0 rfl)
    (by rw [System.face01_v_one]; exact wholeSpaceTrans_comp_wholeSpaceVertex_of_eq hp _ e 1 1 rfl)

/-- The face `p₁₂` of the descent system is the coface `δ 0`. -/
theorem wholeSpaceDescentSystem_face12_hom (e : ℕ) :
    ((wholeSpaceDescentSystem S hp).face12 e).hom =
      wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 0) e :=
  wholeSpaceDescentSystem_hom_eq hp _ _
    (by rw [System.face12_v_zero]; exact wholeSpaceTrans_comp_wholeSpaceVertex_of_eq hp _ e 0 1 rfl)
    (by rw [System.face12_v_one]; exact wholeSpaceTrans_comp_wholeSpaceVertex_of_eq hp _ e 1 2 rfl)

/-- The face `p₀₂` of the descent system is the coface `δ 1`. -/
theorem wholeSpaceDescentSystem_face02_hom (e : ℕ) :
    ((wholeSpaceDescentSystem S hp).face02 e).hom =
      wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 1) e :=
  wholeSpaceDescentSystem_hom_eq hp _ _
    (by rw [System.face02_v_zero]; exact wholeSpaceTrans_comp_wholeSpaceVertex_of_eq hp _ e 0 0 rfl)
    (by rw [System.face02_v_one]; exact wholeSpaceTrans_comp_wholeSpaceVertex_of_eq hp _ e 1 2 rfl)

/-- The level map of `T(1)` in the descent system is the level map of the system. -/
theorem wholeSpaceDescentSystem_lev1_hom (e : ℕ) :
    ((wholeSpaceDescentSystem S hp).lev1 e).hom =
      ((wholeSpaceSystem S hp).obj (op ⦋1⦌)).map (homOfLE (Nat.le_succ e)) :=
  wholeSpaceDescentSystem_hom_eq hp _ _
    (by rw [System.lev1_v]; exact map_comp_wholeSpaceVertex hp 1 (Nat.le_succ e) 0)
    (by rw [System.lev1_v]; exact map_comp_wholeSpaceVertex hp 1 (Nat.le_succ e) 1)

/-- The restriction along `diag` is the restriction along the degeneracy `σ 0`. -/
theorem wholeSpaceDescentSystem_diag_apply (e : ℕ) (x : crysSheafRing S (levelObj hp 1 e).obj) :
    ((affineSectionsRing S).map ((wholeSpaceDescentSystem S hp).diag e).op).hom x =
      sheafRingMap (wholeSpaceTrans hp (SimplexCategory.σ (n := 0) 0) e) x :=
  congrArg (fun k ↦ sheafRingMap k x) (wholeSpaceDescentSystem_diag_hom hp e)

/-- The restriction along `face01` is the restriction along the coface `δ 2`. -/
theorem wholeSpaceDescentSystem_face01_apply (e : ℕ) (x : crysSheafRing S (levelObj hp 1 e).obj) :
    ((affineSectionsRing S).map ((wholeSpaceDescentSystem S hp).face01 e).op).hom x =
      sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 2) e) x :=
  congrArg (fun k ↦ sheafRingMap k x) (wholeSpaceDescentSystem_face01_hom hp e)

/-- The restriction along `face12` is the restriction along the coface `δ 0`. -/
theorem wholeSpaceDescentSystem_face12_apply (e : ℕ) (x : crysSheafRing S (levelObj hp 1 e).obj) :
    ((affineSectionsRing S).map ((wholeSpaceDescentSystem S hp).face12 e).op).hom x =
      sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 0) e) x :=
  congrArg (fun k ↦ sheafRingMap k x) (wholeSpaceDescentSystem_face12_hom hp e)

/-- The restriction along `face02` is the restriction along the coface `δ 1`. -/
theorem wholeSpaceDescentSystem_face02_apply (e : ℕ) (x : crysSheafRing S (levelObj hp 1 e).obj) :
    ((affineSectionsRing S).map ((wholeSpaceDescentSystem S hp).face02 e).op).hom x =
      sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 1) e) x :=
  congrArg (fun k ↦ sheafRingMap k x) (wholeSpaceDescentSystem_face02_hom hp e)

/-- The restriction along `lev1` is the restriction along the level map of `T(1)`. -/
theorem wholeSpaceDescentSystem_lev1_apply (e : ℕ)
    (x : crysSheafRing S (levelObj hp 1 (e + 1)).obj) :
    ((affineSectionsRing S).map ((wholeSpaceDescentSystem S hp).lev1 e).op).hom x =
      sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋1⦌)).map (homOfLE (Nat.le_succ e))) x :=
  congrArg (fun k ↦ sheafRingMap k x) (wholeSpaceDescentSystem_lev1_hom hp e)

/-! ### The Taylor data -/

/-- The ring map of the vertex `0` of `T(1)_e` is the reduction followed by `p₀`. -/
theorem ptRing_wholeSpaceDescentSystem_v_zero (e : ℕ) (d : envD S hp) :
    (wholeSpaceDescentSystem S hp).ptRing ((wholeSpaceDescentSystem S hp).v e 0) d =
      (levelRingTaylorExpansion hp e).a₀ (levelRed hp e d) := by
  change sheafRingMap (wholeSpaceVertex S hp 1 e 0) (levelRed hp e d) = _
  rw [wholeSpaceVertex_one_zero]
  rfl

/-- The ring map of the vertex `1` of `T(1)_e` is the reduction followed by `p₁`. -/
theorem ptRing_wholeSpaceDescentSystem_v_one (e : ℕ) (d : envD S hp) :
    (wholeSpaceDescentSystem S hp).ptRing ((wholeSpaceDescentSystem S hp).v e 1) d =
      (levelRingTaylorExpansion hp e).a₁ (levelRed hp e d) := by
  change sheafRingMap (wholeSpaceVertex S hp 1 e 1) (levelRed hp e d) = _
  rw [wholeSpaceVertex_one_one]
  rfl

variable (S) [DecidableEq (wholeSpaceIndex S hp)] in
/-- **The Taylor data of the system of [Stacks, Tag 07JN]**: the monomials `ξ^{[K]}` of
`Γ(T(1)_e, 𝒪)` and `v^{[K]} u^{[L]}` of `Γ(T(2)_e, 𝒪)` (the reductions of those of the envelopes
`E(1)` and `E(2)`), the Taylor coefficients `δ_K` of `D` (`...SmallSite.envDTaylorCoeff`), the
prime `p` and the exponents `N + e`, `p^{N + e}` vanishing on the level `e`. -/
abbrev wholeSpaceTaylorData :
    TaylorData (wholeSpaceDescentSystem S hp) (wholeSpaceIndex S hp) where
  xi e K := levelTaylorMonomial hp e K
  eta e KL := levelTaylorMonomial₂ hp e KL
  xi_mul e A B := by
    change envLevelMap hp 1 e _ * envLevelMap hp 1 e _ = _ * envLevelMap hp 1 e _
    rw [← map_mul, envelopeTaylorMonomial_mul, map_mul, map_natCast]
    rfl
  xi_diag e K := by
    refine (wholeSpaceDescentSystem_diag_apply hp e _).trans ?_
    change sheafRingMap _ (envLevelMap hp 1 e (envelopeTaylorMonomial _ _ K)) = _
    rw [envLevelMap_restriction]
    split_ifs with hK
    · rw [hK, envelopeTaylorMonomial_zero, map_one, map_one]
      rfl
    · rw [envReindex_degeneracy_envelopeTaylorMonomial _ _ hK, map_zero]
      rfl
  xi_face01 e L := by
    refine (wholeSpaceDescentSystem_face01_apply hp e _).trans ?_
    change sheafRingMap _ (envLevelMap hp 1 e _) = envLevelMap hp 2 e _
    rw [envLevelMap_restriction, envReindex_delta_two_envelopeTaylorMonomial]
  xi_face12 e K := by
    refine (wholeSpaceDescentSystem_face12_apply hp e _).trans ?_
    change sheafRingMap _ (envLevelMap hp 1 e _) = envLevelMap hp 2 e _
    rw [envLevelMap_restriction, envReindex_delta_zero_envelopeTaylorMonomial]
  xi_face02 e N := by
    refine (wholeSpaceDescentSystem_face02_apply hp e _).trans ?_
    change sheafRingMap _ (envLevelMap hp 1 e _) = ∑ x ∈ _, envLevelMap hp 2 e _
    rw [envLevelMap_restriction, envReindex_delta_one_envelopeTaylorMonomial, map_sum]
  eta_mul e K L := by
    change envLevelMap hp 2 e _ * envLevelMap hp 2 e _ = envLevelMap hp 2 e _
    rw [← map_mul, envelopeTaylorMonomial₂_mul]
  xi_lev e K := by
    refine (wholeSpaceDescentSystem_lev1_apply hp e _).trans ?_
    exact envLevelMap_levelMap hp 1 (homOfLE (Nat.le_succ e)) _
  delta := envDTaylorCoeff hp
  taylor e d := by
    refine ⟨((levelRingTaylorExpansion hp e).coeffs (levelRed hp e d)).support, fun A hA ↦ ?_, ?_⟩
    · rw [ptRing_wholeSpaceDescentSystem_v_zero, levelRed_envDTaylorCoeff,
        TaylorExpansion.theta_apply, Finsupp.notMem_support_iff.mp hA, map_zero]
      exact zero_mul _
    · rw [ptRing_wholeSpaceDescentSystem_v_one, TaylorExpansion.a₁_eq_sum, Finsupp.sum]
      refine Finset.sum_congr rfl fun A _ ↦ ?_
      rw [ptRing_wholeSpaceDescentSystem_v_zero, levelRed_envDTaylorCoeff,
        TaylorExpansion.theta_apply, smul_eq_mul, mul_comm]
      rfl
  p := S.p
  nil e := _root_.Crystalline.uniformLevel (affineSituation S hp) + e
  nil_one e := by
    have h := envLevelMap_pow hp 1 e
    rw [map_natCast, Nat.cast_pow] at h
    exact h
  nil_two e := by
    have h := envLevelMap_pow hp 2 e
    rw [map_natCast, Nat.cast_pow] at h
    exact h

variable (S) [DecidableEq (wholeSpaceIndex S hp)] in
/-- The Taylor coefficients of the Taylor data are `...SmallSite.envDTaylorCoeff`. -/
theorem wholeSpaceTaylorData_delta :
    (wholeSpaceTaylorData S hp).delta = envDTaylorCoeff hp := rfl

variable (S) [DecidableEq (wholeSpaceIndex S hp)] in
/-- **The Taylor coefficients `δ_K` of `D` are the monomials `∏_i δ_{e_i}^{k_i}`.** -/
theorem isThetaMonomialFamily_wholeSpaceTaylorData_delta :
    IsThetaMonomialFamily (envD S hp)
      (fun i ↦ (wholeSpaceTaylorData S hp).delta (Finsupp.single i 1))
      (fun K ↦ (wholeSpaceTaylorData S hp).delta K) :=
  ⟨funext fun d ↦ envDTaylorCoeff_zero hp d, fun i K ↦ funext fun d ↦
    (envDTaylorCoeff_envDTaylorCoeff hp K (Finsupp.single i 1) d).symm⟩

/-! ### Taylor's formula for the derivation of `D` -/

section Derivation

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- Every element of `D` is the image of an element of `E(0)` up to a multiple of `p^k`. -/
theorem exists_eq_wsCompletionMap_add (x : envD S hp) (k : ℕ) :
    ∃ (y : wsEnvelope hp 0) (z : envD S hp),
      x = wsCompletionMap hp 0 y + ((S.p ^ k : ℕ) : envD S hp) * z := by
  obtain ⟨y, hy⟩ := _root_.Crystalline.surjective_mk_algebraMap (R := wsEnvelope hp 0) S.p k
    (Ideal.Quotient.mk _ x)
  have h := Ideal.Quotient.eq.mp hy
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨z, hz⟩ := h
  refine ⟨y, -z, ?_⟩
  change x = algebraMap _ (AdicCompletion (Ideal.span {(S.p : wsEnvelope hp 0)}) (wsEnvelope hp 0))
      y +
    ((S.p ^ k : ℕ) : AdicCompletion (Ideal.span {(S.p : wsEnvelope hp 0)}) (wsEnvelope hp 0)) * -z
  rw [mul_neg, Nat.cast_pow, mul_comm, hz]
  exact (add_sub_cancel (algebraMap _ (AdicCompletion (Ideal.span {(S.p : wsEnvelope hp 0)})
    (wsEnvelope hp 0)) y) x).symm.trans (congrArg _ (neg_sub _ _).symm)

/-- **The coordinate `f ↦ c_c(d f)` of the derivation of `D`** along `d x_c`, as an additive map
of `D`. -/
def pairCoordDerivation (c : wholeSpaceIndex S hp) : envD S hp →+ envD S hp where
  toFun x := pairCoord hp c (pairDerivation hp x)
  map_zero' :=
    (congrArg (pairCoord hp c) (DividedPowerDerivation.map_zero (pairDerivation hp))).trans
      (map_zero _)
  map_add' x x' :=
    (congrArg (pairCoord hp c) (DividedPowerDerivation.map_add (pairDerivation hp) x x')).trans
      (map_add _ _ _)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- `...SmallSite.pairCoordDerivation` is the coordinate of the derivation. -/
theorem pairCoordDerivation_apply (c : wholeSpaceIndex S hp) (x : envD S hp) :
    pairCoordDerivation hp c x = pairCoord hp c (pairDerivation hp x) := rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **Taylor's formula for the differential of `E(0)` in coordinates**: the coordinate of
`d y` along `d x_c` is `-δ_{e_c}(y)`. -/
theorem pairCoord_pairDerivation_pairOf (c : wholeSpaceIndex S hp) (y : wsEnvelope hp 0) :
    pairCoord hp c (pairDerivation hp (pairOf hp y)) =
      -pairOf hp (envelopeTaylorCoeff _ _ y (Finsupp.single c 1)) := by
  classical
  set T : Finset (wholeSpaceIndex S hp) := (envelopeTaylorCoeff _ _ y).support.preimage
    (fun i ↦ Finsupp.single i 1)
    ((Finsupp.single_left_injective one_ne_zero).injOn) with hTdef
  have hT : ∀ i ∉ T, envelopeTaylorCoeff _ _ y (Finsupp.single i 1) = 0 := fun i hi ↦ by
    rwa [hTdef, Finset.mem_preimage, Finsupp.mem_support_iff, not_not] at hi
  rw [pairDerivation_pairOf hp y T hT, map_neg, map_sum]
  congr 1
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single c]
  · rw [(isCoordinateDual_pairDx hp).self c, mul_one]
  · intro i _ hi
    rw [(isCoordinateDual_pairDx hp).of_ne hi, mul_zero]
  · intro hc
    rw [hT c hc, map_zero, zero_mul]

variable (S) [DecidableEq (wholeSpaceIndex S hp)] in
/-- **Taylor's formula for the derivation of `D`**: for every `f ∈ D`, the coordinate of `d f`
along `d x_c` is `-δ_{e_c}(f)`, `δ_K` the Taylor coefficients of the Taylor data of the system.
On the image of `E(0)` this is `...SmallSite.pairCoord_pairDerivation_pairOf`; both sides are
additive, and an element of `D` agrees with an element of the image of `E(0)` modulo every
`p^{N + e}`, which vanishes on the level `e`, so the two sides agree at every level and hence in
`D`. -/
theorem pairCoord_pairDerivation (c : wholeSpaceIndex S hp) (f : pairRing hp) :
    pairCoord hp c (pairDerivation hp f) =
      -(wholeSpaceTaylorData S hp).delta (Finsupp.single c 1) f := by
  let Φ : envD S hp →+ envD S hp :=
    pairCoordDerivation hp c + envDTaylorCoeff hp (Finsupp.single c 1)
  have hΦ : ∀ x, Φ x = pairCoordDerivation hp c x + envDTaylorCoeff hp (Finsupp.single c 1) x :=
    fun _ ↦ rfl
  have h0 : ∀ y, Φ (wsCompletionMap hp 0 y) = 0 := fun y ↦ by
    rw [hΦ, pairCoordDerivation_apply, show wsCompletionMap hp 0 y = pairOf hp y from rfl,
      pairCoord_pairDerivation_pairOf, show pairOf hp y = wsCompletionMap hp 0 y from rfl,
      envDTaylorCoeff_wsCompletionMap]
    exact neg_add_cancel _
  have hx : Φ f = 0 := eq_of_levelRed_eq hp fun e ↦ by
    obtain ⟨y, z, rfl⟩ := exists_eq_wsCompletionMap_add hp f
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
    rw [map_add, h0, zero_add, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, map_mul, levelRed_pow,
      zero_mul, map_zero]
  exact eq_neg_of_add_eq_zero_left ((hΦ f).symm.trans hx)

end Derivation

end Crystalline.GlobalCrystallineSituation.SmallSite

end
