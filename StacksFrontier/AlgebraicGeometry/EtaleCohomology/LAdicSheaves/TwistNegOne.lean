module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModuleStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModuleLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.OfStrictTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLowerShriekTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageRealizable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Tate twist `F(-1)` of an ℓ-adic sheaf

Let `X` be a scheme over a field `k` in which `ℓ` is invertible and `F` an ℓ-adic sheaf on `X`,
with levels `Fₙ` (sheaves of `ℤ/ℓⁿ⁺¹`-modules, read on Mathlib's small étale site). The Tate twist
`F(-1)` has levels `𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` (`Stacks.Kummer.twistNegOneModule`), with the transitions
`𝓗om(μ_{ℓⁿ⁺²}, Fₙ₊₁) ⟶ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` induced by those of `F` and the `ℓ`-th power map
`μ_{ℓⁿ⁺²} ⟶ μ_{ℓⁿ⁺¹}` (`Stacks.Kummer.twistNegOneModuleTransition`).

This file builds the tower `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` of sheaves of `ℤ_ℓ`-modules
(`Stacks.EtaleCohomology.LAdicSheaf.twistNegOneTower`) and proves that it is a strict ℓ-adic tower
(`Stacks.EtaleCohomology.LAdicSheaf.twistNegOneTower_isStrict`). Strictness is checked on stalks:
pairing with a primitive root of unity identifies the stalks of the twist with those of `F`
(`Stacks.Kummer.bijective_fiberPairing_of_bijective`), compatibly with the transitions, and the
tower of `F` is strict (`Stacks.EtaleCohomology.LAdicSheaf.padicTower_isStrict`).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneLevel`, `…twistNegOneTransition`.
* `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneTower`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneTower_isStrict`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.SmallEtale GrothendieckTopology Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- A power of a nonzero natural number is nonzero. -/
theorem neZero_pow_of_fact_prime (ℓ n : ℕ) [Fact ℓ.Prime] : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

/-- A power of an element which is nonzero in a field is nonzero there. -/
theorem neZero_natCast_pow (k : Type*) [Field k] (ℓ n : ℕ) [NeZero (ℓ : k)] :
    NeZero (((ℓ ^ n : ℕ) : k)) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ (NeZero.ne _)⟩

attribute [local instance] neZero_pow_of_fact_prime neZero_natCast_pow

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] (fX : X.1 ⟶ Spec (.of k)) [NeZero (ℓ : k)]

variable (F : LAdicSheaf.{u, u + 1} B X ℓ)

/-- **Level `n` of the Tate twist**: `𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` on Mathlib's small étale site. -/
abbrev LAdicSheaf.twistNegOneLevel (n : ℕ) : EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) X.1 :=
  Stacks.Kummer.twistNegOneModule.{u, 0} X.1 (ℓ ^ (n + 1)) (LAdicSheaf.etaleLevel B X ℓ F n)

/-- `ℓ · ℓⁿ⁺¹ = ℓⁿ⁺²`. -/
theorem mul_pow_succ_eq (ℓ n : ℕ) : ℓ * ℓ ^ (n + 1) = ℓ ^ (n + 1 + 1) := (pow_succ' ℓ (n + 1)).symm

/-- **The transition of the Tate twist** `𝓗om(μ_{ℓⁿ⁺²}, Fₙ₊₁) ⟶ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)`. -/
def LAdicSheaf.twistNegOneTransition (n : ℕ) :
    LAdicSheaf.twistNegOneLevel F (n + 1) ⟶
      (etaleModuleRestrictScalars (levelCast ℓ n) X.1).obj (LAdicSheaf.twistNegOneLevel F n) :=
  Stacks.Kummer.twistNegOneModuleTransition.{u, 0} X.1 ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1))
    (mul_pow_succ_eq ℓ n) (LAdicSheaf.etaleLevel B X ℓ F n) fX
    (LAdicSheaf.etaleLevel B X ℓ F (n + 1)) (LAdicSheaf.etaleTransition B X ℓ F n)

/-- **The tower `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)`** of sheaves of `ℤ_ℓ`-modules on Mathlib's small étale
site, with the transitions of the Tate twist. -/
def LAdicSheaf.twistNegOneTower : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1 :=
  Functor.ofOpSequence
    (X := fun n => (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1).obj
      (LAdicSheaf.twistNegOneLevel F n))
    (fun n => (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) X.1).map
        (LAdicSheaf.twistNegOneTransition fX F n) ≫
      (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) (levelCast ℓ n)
        (PadicInt.toZModPow (p := ℓ) (n + 1)) (toZModPow_succ_comp ℓ n) X.1).hom.app
        (LAdicSheaf.twistNegOneLevel F n))

/-- The map `n + 1 ⟶ n` of the twisted tower is the transition of the Tate twist, read over
`ℤ_ℓ`. -/
theorem LAdicSheaf.twistNegOneTower_map_succ (n : ℕ) :
    (LAdicSheaf.twistNegOneTower fX F).map (homOfLE (n.le_add_right 1)).op =
      (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) X.1).map
          (LAdicSheaf.twistNegOneTransition fX F n) ≫
        (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) (levelCast ℓ n)
          (PadicInt.toZModPow (p := ℓ) (n + 1)) (toZModPow_succ_comp ℓ n) X.1).hom.app
          (LAdicSheaf.twistNegOneLevel F n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The levels of the twisted tower are killed by the powers of `ℓ`. -/
theorem LAdicSheaf.twistNegOneTower_annihilated (n : ℕ) :
    ℓ ^ (n + 1) • 𝟙 (towerObj (LAdicSheaf.twistNegOneTower fX F) n) = 0 := by
  let R := etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1
  change ℓ ^ (n + 1) • 𝟙 (R.obj (LAdicSheaf.twistNegOneLevel F n)) = 0
  rw [← R.map_id, ← R.map_nsmul,
    zmodSheaf_nsmul_id X.1.smallEtaleTopology (ℓ ^ (n + 1)) (LAdicSheaf.twistNegOneLevel F n),
    R.map_zero]

/-! ### Strictness, on stalks -/

/-- The transition `Fₙ₊₁ ⟶ Fₙ` of `F` on Mathlib's site, read over `ℤ_ℓ`. -/
abbrev LAdicSheaf.etaleLevelPadicTransition (n : ℕ) :
    (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) X.1).obj
        (LAdicSheaf.etaleLevel B X ℓ F (n + 1)) ⟶
      (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1).obj
        (LAdicSheaf.etaleLevel B X ℓ F n) :=
  (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) X.1).map
      (LAdicSheaf.etaleTransition B X ℓ F n) ≫
    (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) (levelCast ℓ n)
      (PadicInt.toZModPow (p := ℓ) (n + 1)) (toZModPow_succ_comp ℓ n) X.1).hom.app
      (LAdicSheaf.etaleLevel B X ℓ F n)

/-- Multiplication by `ℓⁿ⁺¹` on `Fₙ₊₁` followed by the transition `Fₙ₊₁ ⟶ Fₙ` over `ℤ_ℓ` is
zero. -/
theorem LAdicSheaf.etaleLevelPadicTransition_condition (n : ℕ) :
    ((ℓ ^ (n + 1)) • 𝟙 ((etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))
      X.1).obj (LAdicSheaf.etaleLevel B X ℓ F (n + 1)))) ≫
        LAdicSheaf.etaleLevelPadicTransition F n = 0 := by
  let R := etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) X.1
  rw [← R.map_id, ← R.map_nsmul, ← Category.assoc, ← R.map_comp,
    LAdicSheaf.etaleTransition_condition, R.map_zero, zero_comp]

/-- **The transition of `F` over `ℤ_ℓ` is the quotient by `ℓⁿ⁺¹`.** -/
def LAdicSheaf.etaleLevelPadicTransitionIsCokernel (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (LAdicSheaf.etaleLevelPadicTransition F n)
      (LAdicSheaf.etaleLevelPadicTransition_condition F n)) := by
  let R := etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) X.1
  have h₁ := isColimitCoforkMapOfIsColimit' R (LAdicSheaf.etaleTransition_condition B X ℓ F n)
    (LAdicSheaf.etaleTransitionIsCokernel B X ℓ F n)
  have hf : R.map ((ℓ ^ (n + 1)) • 𝟙 (LAdicSheaf.etaleLevel B X ℓ F (n + 1))) =
      (ℓ ^ (n + 1)) • 𝟙 (R.obj (LAdicSheaf.etaleLevel B X ℓ F (n + 1))) := by
    rw [R.map_nsmul, R.map_id]
  exact isColimitCokernelCoforkCompIso _ (isColimitCokernelCoforkOfEq hf _ h₁)
    (e := (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))
      (levelCast ℓ n) (PadicInt.toZModPow (p := ℓ) (n + 1)) (toZModPow_succ_comp ℓ n) X.1).hom.app
        (LAdicSheaf.etaleLevel B X ℓ F n)) inferInstance

/-- Exactness and surjectivity transfer along bijections of the terms commuting with the maps. -/
theorem surjective_and_exact_of_conj {M₁ M₂ N₁ N₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [AddCommGroup N₁] [AddCommGroup N₂] (a : M₁ →+ M₂) (b : N₁ →+ N₂) (φ₁ : M₁ →+ N₁)
    (φ₂ : M₂ →+ N₂) (h₁ : Function.Bijective φ₁) (h₂ : Function.Bijective φ₂)
    (hsq : ∀ x, φ₂ (a x) = b (φ₁ x)) (c : ℕ) (hb : Function.Surjective b)
    (hex : ∀ y, b y = 0 → ∃ z, c • z = y) :
    Function.Surjective a ∧ ∀ x, a x = 0 → ∃ z, c • z = x := by
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  · obtain ⟨z, hz⟩ := hb (φ₂ y)
    obtain ⟨x, rfl⟩ := h₁.2 z
    exact ⟨x, h₂.1 ((hsq x).trans hz)⟩
  · obtain ⟨z, hz⟩ := hex _ (by rw [← hsq, hx, map_zero])
    obtain ⟨w, rfl⟩ := h₁.2 z
    exact ⟨w, h₁.1 (by rw [map_nsmul, hz])⟩

/-- The base change `U ×_k k(ζ_N) ⟶ U` alone is an étale covering of `U`. -/
private theorem ofArrows_cyclotomicBaseChangeπ_mem {S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ Spec (.of K)) (N : ℕ) [NeZero N] [NeZero (N : K)] (U : S.Etale) :
    Sieve.ofArrows (fun _ : PUnit.{u + 2} => Stacks.Kummer.cyclotomicBaseChange f N U)
      (fun _ => Stacks.Kummer.cyclotomicBaseChangeπ f N U) ∈ S.smallEtaleTopology U := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact Set.eq_univ_of_forall fun _ => Set.mem_iUnion.2 ⟨PUnit.unit, by
    rw [Stacks.Kummer.range_cyclotomicBaseChangeπ]
    trivial⟩

/-- Pairing with the restriction of a primitive `N`-th root of unity is bijective on sections. -/
private theorem bijective_twistNegOneModulePairing_map_sliceRootSection {S : Scheme.{u}} {N : ℕ}
    [NeZero N] (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))) {V W : S.Etale}
    (g : W ⟶ V) {K : Type u} [Field K] (κ : K →+* Γ(V.left, ⊤)) {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) :
    Function.Bijective (fun α => Stacks.Kummer.twistNegOneModulePairing.{u, 0} S N G W α
      ((Stacks.Kummer.rootsOfUnitySheaf.{u, 0} S N).obj.map g.op
        (Stacks.Kummer.sliceRootSection.{u, 0} V κ hζ (Over.mk (𝟙 V)) 1))) := by
  rw [Stacks.Kummer.rootsOfUnitySheaf_map_sliceRootSection N g κ hζ 1]
  exact Stacks.Kummer.bijective_twistNegOneModuleEvalRoot.{u, 0} W _ hζ G

/-- **Surjectivity and exactness transfer along pairings of stalks**: if pairing with fixed germs
`m, φ₂ m` identifies the stalks of `τ` with those of `σ`, compatibly with the maps, and `σ` is
surjective on stalks with kernel `c` times the stalk, then so is `τ`. -/
private theorem surjective_and_exact_of_fiberPairing {S : Scheme.{u}}
    (Φ : Point.{u + 1} S.smallEtaleTopology)
    {R₁ R₂ R₃ : Type} [Ring R₁] [Ring R₂] [Ring R₃]
    {P₁ Q₁ : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R₁} {P₂ Q₂ : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R₂}
    {P₃ Q₃ : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u + 1} R₃}
    (pair : ∀ U : S.Etale, ToType (P₁.obj (op U)) → ToType (P₂.obj (op U)) →
      ToType (P₃.obj (op U)))
    (hpair : ∀ {U V : S.Etale} (g : V ⟶ U) z s,
      pair V (P₁.map g.op z) (P₂.map g.op s) = P₃.map g.op (pair U z s))
    (pair' : ∀ U : S.Etale, ToType (Q₁.obj (op U)) → ToType (Q₂.obj (op U)) →
      ToType (Q₃.obj (op U)))
    (hpair' : ∀ {U V : S.Etale} (g : V ⟶ U) z s,
      pair' V (Q₁.map g.op z) (Q₂.map g.op s) = Q₃.map g.op (pair' U z s))
    (hadd : ∀ U z z' s, pair U (z + z') s = pair U z s + pair U z' s)
    (hadd' : ∀ U z z' s, pair' U (z + z') s = pair' U z s + pair' U z' s)
    (τ : P₁ ⟶ Q₁) (φ₂ : P₂ ⟶ Q₂) (σ : P₃ ⟶ Q₃)
    (h : ∀ U z s, pair' U (τ.app (op U) z) (φ₂.app (op U) s) = σ.app (op U) (pair U z s))
    (m : ToType (Φ.presheafFiber.obj P₂)) (m' : ToType (Φ.presheafFiber.obj Q₂))
    (hm : m' = Φ.presheafFiber.map φ₂ m)
    (hb : Function.Bijective fun a => Stacks.Kummer.fiberPairing Φ pair a m)
    (hb' : Function.Bijective fun a => Stacks.Kummer.fiberPairing Φ pair' a m') (c : ℕ)
    (hσ : Function.Surjective (Φ.presheafFiber.map σ))
    (hex : ∀ y, Φ.presheafFiber.map σ y = 0 → ∃ z, c • z = y) :
    Function.Surjective (Φ.presheafFiber.map τ) ∧
      ∀ x, Φ.presheafFiber.map τ x = 0 → ∃ z, c • z = x :=
  surjective_and_exact_of_conj (Φ.presheafFiber.map τ).hom.toAddMonoidHom
    (Φ.presheafFiber.map σ).hom.toAddMonoidHom
    (AddMonoidHom.mk' (fun a => Stacks.Kummer.fiberPairing Φ pair a m)
      fun a a' => Stacks.Kummer.fiberPairing_add_left Φ pair hpair hadd a a' m)
    (AddMonoidHom.mk' (fun a => Stacks.Kummer.fiberPairing Φ pair' a m')
      fun a a' => Stacks.Kummer.fiberPairing_add_left Φ pair' hpair' hadd' a a' m')
    hb hb' (fun a => by
      rw [hm]
      exact Stacks.Kummer.fiberPairing_presheafFiber_map Φ pair hpair pair' hpair' τ φ₂ σ h a m)
    c hσ hex

/-- On stalks, `c • 𝟙 P ≫ g = 0` is exact at `P` iff the kernel of `g` is `c` times the stalk. -/
private theorem exact_map_sheafFiber_iff_nsmul {S : Scheme.{u}}
    (Φ : Point.{u + 1} S.smallEtaleTopology)
    {P Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} ℤ_[ℓ])} (c : ℕ) (g : P ⟶ Q)
    (w : (c • 𝟙 P) ≫ g = 0) :
    ((ShortComplex.mk _ _ w).map (Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ]))).Exact ↔
      ∀ y, Φ.presheafFiber.map g.hom y = 0 → ∃ z, c • z = y := by
  have : (Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).Additive :=
    Functor.additive_of_preserves_binary_products _
  rw [ShortComplex.moduleCat_exact_iff]
  refine forall₂_congr fun y hy => exists_congr fun z => ?_
  change ((Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).map (c • 𝟙 P)) z = y ↔ _
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

section Point

variable (Φ : Point.{u + 1} X.1.smallEtaleTopology) {U₀ : X.1.Etale} (u₀ : Φ.fiber.obj U₀)

/-- **The transitions of `F` on stalks** are surjective with kernel `ℓⁿ⁺¹` times the stalk. -/
private theorem LAdicSheaf.etaleLevelPadicTransition_fiber (n : ℕ) :
    Function.Surjective (Φ.presheafFiber.map (LAdicSheaf.etaleLevelPadicTransition F n).hom) ∧
      ∀ x, Φ.presheafFiber.map (LAdicSheaf.etaleLevelPadicTransition F n).hom x = 0 →
        ∃ z, ℓ ^ (n + 1) • z = x := by
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u + 1, u} ℤ_[ℓ]
  have hcok := LAdicSheaf.etaleLevelPadicTransitionIsCokernel F n
  have : Epi (LAdicSheaf.etaleLevelPadicTransition F n) := Cofork.IsColimit.epi hcok
  have hS := (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk _ _ (LAdicSheaf.etaleLevelPadicTransition_condition F n)) hcok).map
      (Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ]))
  have : (Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ⟨(ModuleCat.epi_iff_surjective _).1 (inferInstanceAs (Epi
    ((Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).map
      (LAdicSheaf.etaleLevelPadicTransition F n)))),
    (exact_map_sheafFiber_iff_nsmul Φ _ _ _).1 hS⟩

include u₀ in
/-- **The transitions of the twisted tower on stalks** are surjective with kernel `ℓⁿ⁺¹` times the
stalk: pairing with compatible primitive roots of unity `ζ, ζ^ℓ` identifies them with the
transitions of `F` on stalks, which have these properties. -/
theorem LAdicSheaf.twistNegOneTower_fiber (n : ℕ) :
    Function.Surjective (Φ.presheafFiber.map
        ((LAdicSheaf.twistNegOneTower fX F).map (homOfLE (n.le_add_right 1)).op).hom) ∧
      ∀ x, Φ.presheafFiber.map
          ((LAdicSheaf.twistNegOneTower fX F).map (homOfLE (n.le_add_right 1)).op).hom x = 0 →
        ∃ z, ℓ ^ (n + 1) • z = x := by
  have hN := mul_pow_succ_eq ℓ n
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u + 1, u} ℤ_[ℓ]
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u + 1, u}
    (ZMod (ℓ ^ (n + 1)))
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u + 1, u}
    (ZMod (ℓ ^ (n + 1 + 1)))
  -- a neighbourhood carrying a primitive `ℓⁿ⁺²`-th root of unity
  let V := Stacks.Kummer.cyclotomicBaseChange fX (ℓ ^ (n + 1 + 1)) U₀
  obtain ⟨Y, g, ⟨Z, h, -, ⟨⟩, -⟩, y, -⟩ :=
    Φ.jointly_surjective _ (ofArrows_cyclotomicBaseChangeπ_mem fX (ℓ ^ (n + 1 + 1)) U₀) u₀
  let v : Φ.fiber.obj V := Φ.fiber.map h y
  let κ := Stacks.Kummer.cyclotomicBaseChangeStructMap fX (ℓ ^ (n + 1 + 1)) U₀
  let ζ := IsCyclotomicExtension.zeta (ℓ ^ (n + 1 + 1)) k (CyclotomicField (ℓ ^ (n + 1 + 1)) k)
  have hζ : IsPrimitiveRoot ζ (ℓ ^ (n + 1 + 1)) := IsCyclotomicExtension.zeta_spec _ k _
  have hζ' : IsPrimitiveRoot (ζ ^ ℓ) (ℓ ^ (n + 1)) := hζ.pow (NeZero.pos (ℓ ^ (n + 1 + 1))) hN.symm
  let G' := LAdicSheaf.etaleLevel B X ℓ F (n + 1)
  let G := LAdicSheaf.etaleLevel B X ℓ F n
  let R' := etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) X.1
  let R := etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1
  let M' := Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1 + 1))
  let Mr := (sheafCompose X.1.smallEtaleTopology
    (Stacks.Kummer.zmodRestrict.{u, 0} ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1)) hN)).obj
      (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.1 (ℓ ^ (n + 1)))
  let p := Stacks.Kummer.rootsOfUnityModulePowMap.{u, 0} X.1 ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1)) hN
  let pair₁ : ∀ U : X.1.Etale, ToType ((R'.obj (LAdicSheaf.twistNegOneLevel F (n + 1))).obj.obj
      (op U)) → ToType (M'.obj.obj (op U)) → ToType ((R'.obj G').obj.obj (op U)) :=
    fun U α s => Stacks.Kummer.twistNegOneModulePairing.{u, 0} X.1 _ G' U α s
  have hpair₁ : ∀ {U W : X.1.Etale} (g : W ⟶ U) α s, pair₁ W
      ((R'.obj (LAdicSheaf.twistNegOneLevel F (n + 1))).obj.map g.op α) (M'.obj.map g.op s) =
        (R'.obj G').obj.map g.op (pair₁ U α s) := fun g α s =>
    Stacks.Kummer.twistNegOneModulePairing_naturality.{u, 0} X.1 _ G' g α s
  let pair₀ : ∀ U : X.1.Etale, ToType ((R.obj (LAdicSheaf.twistNegOneLevel F n)).obj.obj
      (op U)) → ToType (Mr.obj.obj (op U)) → ToType ((R.obj G).obj.obj (op U)) :=
    fun U α s => Stacks.Kummer.twistNegOneModulePairing.{u, 0} X.1 _ G U α s
  have hpair₀ : ∀ {U W : X.1.Etale} (g : W ⟶ U) α s, pair₀ W
      ((R.obj (LAdicSheaf.twistNegOneLevel F n)).obj.map g.op α) (Mr.obj.map g.op s) =
        (R.obj G).obj.map g.op (pair₀ U α s) := fun g α s =>
    Stacks.Kummer.twistNegOneModulePairing_naturality.{u, 0} X.1 _ G g α s
  let r' : ToType (M'.obj.obj (op V)) :=
    Stacks.Kummer.sliceRootSection.{u, 0} V κ hζ (Over.mk (𝟙 V)) 1
  let r : ToType (Mr.obj.obj (op V)) :=
    Stacks.Kummer.sliceRootSection.{u, 0} V κ hζ' (Over.mk (𝟙 V)) 1
  have hr : p.hom.app (op V) r' = r := by
    have := Stacks.Kummer.rootsOfUnityPowMap_sliceRootSection.{u, 0} ℓ (ℓ ^ (n + 1))
      (ℓ ^ (n + 1 + 1)) hN V κ hζ hζ' (Over.mk (𝟙 V)) 1
    rwa [Nat.cast_one, Nat.cast_one] at this
  have hb₁ := Stacks.Kummer.bijective_fiberPairing_of_bijective.{u + 1, u} Φ pair₁ hpair₁ v r'
    fun _ g => bijective_twistNegOneModulePairing_map_sliceRootSection G' g κ hζ
  have hb₀ := Stacks.Kummer.bijective_fiberPairing_of_bijective.{u + 1, u} Φ pair₀ hpair₀ v r
    fun _ g => bijective_twistNegOneModulePairing_map_sliceRootSection G g κ hζ'
  rw [LAdicSheaf.twistNegOneTower_map_succ]
  let τH := R'.map (LAdicSheaf.twistNegOneTransition fX F n) ≫
    (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) (levelCast ℓ n)
      (PadicInt.toZModPow (p := ℓ) (n + 1)) (toZModPow_succ_comp ℓ n) X.1).hom.app
      (LAdicSheaf.twistNegOneLevel F n)
  change Function.Surjective (Φ.presheafFiber.map τH.hom) ∧
    ∀ x, Φ.presheafFiber.map τH.hom x = 0 → ∃ z, ℓ ^ (n + 1) • z = x
  obtain ⟨hsurj, hex⟩ := LAdicSheaf.etaleLevelPadicTransition_fiber F Φ n
  exact surjective_and_exact_of_fiberPairing Φ pair₁ hpair₁ pair₀ hpair₀
    (fun U => (Stacks.Kummer.twistNegOneModulePairing.{u, 0} X.1 _ G' U).map_add₂)
    (fun U => (Stacks.Kummer.twistNegOneModulePairing.{u, 0} X.1 _ G U).map_add₂)
    τH.hom p.hom (LAdicSheaf.etaleLevelPadicTransition F n).hom
    (fun U α s => Stacks.Kummer.twistNegOneModulePairing_transition.{u} ℓ _ _
      hN fX G G' (LAdicSheaf.etaleTransition B X ℓ F n) U α s)
    _ _ (by rw [Point.toPresheafFiber_naturality_apply, hr]) hb₁ hb₀ _ hsurj hex

end Point

/-- **The tower `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` is a strict ℓ-adic tower**: its transitions are the
quotients by `ℓⁿ⁺¹`, as checked on the stalks at the residue geometric points. -/
theorem LAdicSheaf.twistNegOneTower_isStrict :
    IsStrict (LAdicSheaf.twistNegOneTower fX F) ℓ := by
  refine IsStrict.of_isCokernel (LAdicSheaf.twistNegOneTower_annihilated fX F) (fun n => ?_)
  have hP := isConservativeFamilyOfPoints_residueGeometricPoints.{u, 0} X.1
  have := Stacks.Kummer.preservesFilteredColimitsOfSize_forget_moduleCat.{u + 1, u} ℤ_[ℓ]
  have hfib : ∀ Φ : (residueGeometricPoints.{u, 0} X.1).FullSubcategory,
      Function.Surjective (Φ.obj.presheafFiber.map
        ((LAdicSheaf.twistNegOneTower fX F).map (homOfLE (n.le_add_right 1)).op).hom) ∧
      ∀ x, Φ.obj.presheafFiber.map
          ((LAdicSheaf.twistNegOneTower fX F).map (homOfLE (n.le_add_right 1)).op).hom x = 0 →
        ∃ z, ℓ ^ (n + 1) • z = x := by
    rintro ⟨_, ⟨x⟩⟩
    exact LAdicSheaf.twistNegOneTower_fiber fX F _
      (U₀ := Scheme.Etale.mk (𝟙 X.1)) (ULift.up (Over.homMk (residueGeometricPoint X.1 x))) n
  let S := ShortComplex.mk _ _
    (nsmul_id_comp_eq_zero (LAdicSheaf.twistNegOneTower_annihilated fX F) n)
  have hS : S.Exact := by
    refine ((hP.jointlyReflectIsomorphisms (ModuleCat.{u + 1} ℤ_[ℓ])).exact_iff S).2
      (fun Φ => ?_)
    exact (exact_map_sheafFiber_iff_nsmul Φ.obj _ _ _).2 (hfib Φ).2
  have : Epi S.g := ((hP.jointlyReflectEpimorphisms (ModuleCat.{u + 1} ℤ_[ℓ])).epi_iff _).2
    (fun Φ => (ModuleCat.epi_iff_surjective _).2 (hfib Φ).1)
  exact hS.gIsCokernel

/-! ### The ℓ-adic sheaf `F(-1)` -/

/-- The identity of sections, from level `n` of the ℓ-adic sheaf of the twisted tower. -/
def LAdicSheaf.strictTowerLevelTwistHomApp (n : ℕ) (U : (SmallEtale B X.1 X.property)ᵒᵖ) :
    (strictTowerLevel (LAdicSheaf.twistNegOneTower fX F)
        (LAdicSheaf.twistNegOneTower_isStrict fX F) n).obj.obj U ⟶
      ((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.obj
          (LAdicSheaf.twistNegOneLevel F n)).obj.obj U :=
  ModuleCat.ofHom (X := (strictTowerLevel (LAdicSheaf.twistNegOneTower fX F)
        (LAdicSheaf.twistNegOneTower_isStrict fX F) n).obj.obj U)
    (Y := ((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.obj
          (LAdicSheaf.twistNegOneLevel F n)).obj.obj U)
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun c x =>
        (zmod_smul_eq_val_nsmul (M := ToType ((strictTowerLevel (LAdicSheaf.twistNegOneTower fX F)
        (LAdicSheaf.twistNegOneTower_isStrict fX F) n).obj.obj U)) c x).trans
          (zmod_smul_eq_val_nsmul (M := ToType (((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.obj
          (LAdicSheaf.twistNegOneLevel F n)).obj.obj U)) c x).symm }

/-- The identity of sections, to level `n` of the ℓ-adic sheaf of the twisted tower. -/
def LAdicSheaf.strictTowerLevelTwistInvApp (n : ℕ) (U : (SmallEtale B X.1 X.property)ᵒᵖ) :
    ((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.obj
          (LAdicSheaf.twistNegOneLevel F n)).obj.obj U ⟶
      (strictTowerLevel (LAdicSheaf.twistNegOneTower fX F)
        (LAdicSheaf.twistNegOneTower_isStrict fX F) n).obj.obj U :=
  ModuleCat.ofHom (X := ((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.obj
          (LAdicSheaf.twistNegOneLevel F n)).obj.obj U)
    (Y := (strictTowerLevel (LAdicSheaf.twistNegOneTower fX F)
        (LAdicSheaf.twistNegOneTower_isStrict fX F) n).obj.obj U)
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun c x =>
        (zmod_smul_eq_val_nsmul (M := ToType (((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.obj
          (LAdicSheaf.twistNegOneLevel F n)).obj.obj U)) c x).trans
          (zmod_smul_eq_val_nsmul (M := ToType ((strictTowerLevel (LAdicSheaf.twistNegOneTower fX F)
        (LAdicSheaf.twistNegOneTower_isStrict fX F) n).obj.obj U)) c x).symm }

/-- **Level `n` of the ℓ-adic sheaf of the twisted tower, on the site of Stacks 021B, is
`𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` read there**: the two `ℤ/ℓⁿ⁺¹`-module structures on a sheaf killed by
`ℓⁿ⁺¹` agree. -/
def LAdicSheaf.strictTowerLevelTwistIso (n : ℕ) :
    strictTowerLevel (LAdicSheaf.twistNegOneTower fX F)
        (LAdicSheaf.twistNegOneTower_isStrict fX F) n ≅
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.obj
        (LAdicSheaf.twistNegOneLevel F n) where
  hom := ⟨{ app := LAdicSheaf.strictTowerLevelTwistHomApp fX F n
            naturality := fun _ _ _ => rfl }⟩
  inv := ⟨{ app := LAdicSheaf.strictTowerLevelTwistInvApp fX F n
            naturality := fun _ _ _ => rfl }⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

variable {F} in
/-- **The levels of the twist of a lisse ℓ-adic sheaf are locally constant of finite type**, on
the site of Stacks 021B. -/
theorem LAdicSheaf.isFiniteTypeLocallyConstant_strictTowerLevel_twist (hF : F.IsLisse) (n : ℕ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (SmallEtale.topology B X.1 X.property)
      (strictTowerLevel (LAdicSheaf.twistNegOneTower fX F)
        (LAdicSheaf.twistNegOneTower_isStrict fX F) n) := by
  have : ∀ U : X.1.Etale, HasWeakSheafify (X.1.smallEtaleTopology.over U)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) := fun U =>
    have := Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE.{u + 1, u, 0, u + 1}
      X.1.smallEtaleTopology (ZMod (ℓ ^ (n + 1))) U
    inferInstance
  have h1 := LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse F hF n
  have h2 := (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B X
    (ZMod (ℓ ^ (n + 1))) (F.level n)).2 h1
  have h3 := Stacks.Kummer.isFiniteTypeLocallyConstant_twistNegOneModule.{u, 0} fX (ℓ ^ (n + 1))
    _ h2
  have h4 := (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B X
    (ZMod (ℓ ^ (n + 1))) (LAdicSheaf.twistNegOneLevel F n)).2 h3
  exact Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.of_iso _ _
    (LAdicSheaf.strictTowerLevelTwistIso fX F n).symm h4

variable {F} in
/-- **The Tate twist `F(-1)` of a lisse ℓ-adic sheaf `F`**, on a scheme over a field in which `ℓ`
is invertible: the ℓ-adic sheaf of the strict tower `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)`. -/
@[sga "7 I 0.0.6" "special case", sga "7 IX 9.2"]
def LAdicSheaf.twistNegOne (hF : F.IsLisse) : LAdicSheaf.{u, u + 1} B X ℓ :=
  LAdicSheaf.ofStrictTower (LAdicSheaf.twistNegOneTower fX F)
    (LAdicSheaf.twistNegOneTower_isStrict fX F) (fun n =>
      isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B X _ _
        (LAdicSheaf.isFiniteTypeLocallyConstant_strictTowerLevel_twist fX hF n))

variable {F} in
/-- **The tower of levels of `F(-1)` is `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)`**, as sheaves of `ℤ_ℓ`-modules on
Mathlib's small étale site. -/
def LAdicSheaf.padicTowerTwistNegOneIso (hF : F.IsLisse) :
    LAdicSheaf.padicTower B X ℓ (LAdicSheaf.twistNegOne fX hF) ≅
      LAdicSheaf.twistNegOneTower fX F :=
  LAdicSheaf.padicTowerOfStrictTowerIso _ _ _

variable {F} in
/-- **The Tate twist of a lisse ℓ-adic sheaf is lisse.** -/
theorem LAdicSheaf.isLisse_twistNegOne (hF : F.IsLisse) : (LAdicSheaf.twistNegOne fX hF).IsLisse :=
  fun n => ⟨fun U => by
    obtain ⟨I, V, f, hcov, hV⟩ :=
      LAdicSheaf.isFiniteTypeLocallyConstant_strictTowerLevel_twist fX hF n U
    exact ⟨I, V, f, hcov, fun i => by
      obtain ⟨E, -, ⟨e⟩⟩ := hV i
      exact ⟨E, ⟨e⟩⟩⟩⟩

end Stacks.EtaleCohomology

end
