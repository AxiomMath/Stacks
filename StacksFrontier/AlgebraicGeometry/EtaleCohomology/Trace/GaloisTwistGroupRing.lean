module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisTwistDescentSheaf
public import StacksFrontier.Algebra.Module.Injective.ZModPrimePower
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import StacksFrontier.LinearAlgebra.Matrix.AdditiveFunctorCharSeries

/-!
# The twist functor on the group ring

Let `ℓ` be a prime, `k₀ = ℤ/ℓᴹ`, `G` a finite group, `R = k₀[G]`, `Λ` a commutative `k₀`-algebra
and `E` a finite `Λ`-module with a `Λ`-linear action `ρ` of `G`.  This file identifies the value of
the twist functor `Ψ = Hom_R(E^∨, -)` on `R` itself:

`Ψ(R) = Hom_R(E^∨, R) ≅ Hom_{k₀}(E^∨, k₀) = E^∨∨ ≅ E`,

as `Λ`-modules, the right action of `g` on `R` going to `ρ(g)`.

## Main results

* `Stacks.EtaleCohomology.ZModPrimePower.bijective_dual_eval`: `M ≅ M^∨∨` for finite `M`.
* `Stacks.EtaleCohomology.twistFunctorGroupRingEquiv`: `Ψ(R) ≅ E`.
* `Stacks.EtaleCohomology.twistFunctorGroupRingEquiv_map_rightMulHom`: it carries the right
  action of `g` on `R` to `ρ(g)`.
* `Stacks.EtaleCohomology.sourceHomDescentSheafIso`: `Hom_A(D, -)` of a descent sheaf is the
  descent sheaf of `Hom_A(D, N)`, for finite `D`.
* `Stacks.EtaleCohomology.descentSheafTwistIso`: `D(E) ≅ Ψ(D(R))`, `R` with its right action.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Duality for finite `ℤ/ℓᴹ`-modules -/

namespace ZModPrimePower

open Stacks.ZModPrimePower

variable {ℓ M : ℕ} [hℓ : Fact ℓ.Prime]

/-- `ℤ/ℓᴹ` is a cogenerator: a nonzero element of a module is detected by a linear form. -/
theorem exists_dual_apply_ne_zero {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ M)) V]
    {m : V} (hm : m ≠ 0) : ∃ ξ : Module.Dual (ZMod (ℓ ^ M)) V, ξ m ≠ 0 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    exfalso
    apply hm
    have h10 : (1 : ZMod (ℓ ^ 0)) = 0 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_zero_iff, pow_zero]
    rw [← one_smul (ZMod (ℓ ^ 0)) m, h10, zero_smul]
  have hne : ((ℓ : ZMod (ℓ ^ M)) ^ (M - 1)) ≠ 0 := by
    rw [← Nat.cast_pow, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.pow_dvd_pow_iff_le_right hℓ.out.one_lt |>.1 h) (by omega)
  have hpow : (ℓ : ZMod (ℓ ^ M)) ^ M = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  let f := LinearMap.toSpanSingleton (ZMod (ℓ ^ M)) V m
  let g₀ : ZMod (ℓ ^ M) →ₗ[ZMod (ℓ ^ M)] ZMod (ℓ ^ M) :=
    LinearMap.mulRight (ZMod (ℓ ^ M)) ((ℓ : ZMod (ℓ ^ M)) ^ (M - 1))
  have hker : LinearMap.ker f ≤ LinearMap.ker g₀ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    obtain ⟨a, -, w, rfl⟩ := exists_eq_pow_mul_unit (p := ℓ) (m := M) c
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      exfalso
      apply hm
      have hc' : (w : ZMod (ℓ ^ M)) • m = 0 := by simpa [f] using hc
      simpa using congrArg (fun x => ((w⁻¹ : (ZMod (ℓ ^ M))ˣ) : ZMod (ℓ ^ M)) • x) hc'
    · show (ℓ : ZMod (ℓ ^ M)) ^ a * w * (ℓ : ZMod (ℓ ^ M)) ^ (M - 1) = 0
      rw [mul_right_comm, ← pow_add, show a + (M - 1) = M + (a - 1) by omega, pow_add, hpow,
        zero_mul, zero_mul]
  let ι := (LinearMap.range f).subtype ∘ₗ (f.quotKerEquivRange).toLinearMap
  have hι : Function.Injective ι :=
    (Submodule.injective_subtype _).comp (LinearEquiv.injective _)
  obtain ⟨h, hh⟩ := Module.Baer.extension_property (baer_self (p := ℓ) (m := M)) ι hι
    ((LinearMap.ker f).liftQ g₀ hker)
  refine ⟨h, ?_⟩
  have := congrArg (fun φ => φ (Submodule.Quotient.mk 1)) hh
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.liftQ_apply] at this
  have hm1 : ι (Submodule.Quotient.mk 1) = m := by
    show (f.quotKerEquivRange (Submodule.Quotient.mk 1) : V) = m
    rw [LinearMap.quotKerEquivRange_apply_mk]
    exact one_smul _ m
  rw [← hm1, this]
  simpa [g₀] using hne

/-- The character `y ↦ e^{2πi y/n}` of `ℤ/n` is injective. -/
theorem injective_zmod_one {n : ℕ} [NeZero n] : Function.Injective (AddChar.zmod n 1) := by
  have hsymm : ∀ x y : ZMod n, AddChar.zmod n x y = AddChar.zmod n y x := by
    intro x y
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
    rw [AddChar.zmod_intCast, AddChar.zmod_intCast, mul_comm (a : ℝ)]
  intro y y' h
  apply AddChar.zmod_injective (n := n)
  refine DFunLike.ext _ _ fun z => ?_
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  rw [← zsmul_one, AddChar.map_zsmul_eq_zpow, AddChar.map_zsmul_eq_zpow, hsymm y 1, hsymm y' 1, h]

/-- **A finite `ℤ/ℓᴹ`-module has at most as many linear forms as elements.** -/
theorem card_dual_le (V : Type*) [AddCommGroup V] [Module (ZMod (ℓ ^ M)) V] [Finite V] :
    Nat.card (Module.Dual (ZMod (ℓ ^ M)) V) ≤ Nat.card V := by
  classical
  have : NeZero (ℓ ^ M) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  have := Fintype.ofFinite V
  let F : Module.Dual (ZMod (ℓ ^ M)) V → AddChar V ℂ := fun ξ =>
    AddChar.circleEquivComplex ((AddChar.zmod (ℓ ^ M) 1).compAddMonoidHom ξ.toAddMonoidHom)
  have hF : Function.Injective F := fun ξ ξ' h => LinearMap.ext fun v =>
    injective_zmod_one (DFunLike.congr_fun (AddChar.circleEquivComplex.injective h) v)
  calc Nat.card (Module.Dual (ZMod (ℓ ^ M)) V) ≤ Nat.card (AddChar V ℂ) :=
        Nat.card_le_card_of_injective F hF
    _ = Nat.card V := by rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

/-- The dual of a finite `ℤ/ℓᴹ`-module is finite. -/
instance finite_dual (V : Type*) [AddCommGroup V] [Module (ZMod (ℓ ^ M)) V] [Finite V] :
    Finite (Module.Dual (ZMod (ℓ ^ M)) V) :=
  haveI : NeZero (ℓ ^ M) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  Finite.of_injective (fun ξ : Module.Dual (ZMod (ℓ ^ M)) V => (ξ : V → ZMod (ℓ ^ M)))
    DFunLike.coe_injective

/-- **Duality for finite `ℤ/ℓᴹ`-modules**: the evaluation `M ⟶ M^∨∨` is bijective. -/
theorem bijective_dual_eval (V : Type*) [AddCommGroup V] [Module (ZMod (ℓ ^ M)) V] [Finite V] :
    Function.Bijective (Module.Dual.eval (ZMod (ℓ ^ M)) V) := by
  refine Function.Injective.bijective_of_nat_card_le (fun v w hvw => ?_)
    ((card_dual_le (ℓ := ℓ) (M := M) (Module.Dual (ZMod (ℓ ^ M)) V)).trans
      (card_dual_le (ℓ := ℓ) (M := M) V))
  by_contra hne
  obtain ⟨ξ, hξ⟩ := exists_dual_apply_ne_zero (ℓ := ℓ) (M := M) (sub_ne_zero.2 hne)
  apply hξ
  have := DFunLike.congr_fun hvw ξ
  simp only [Module.Dual.eval_apply] at this
  rw [map_sub, this, sub_self]

end ZModPrimePower

/-! ### `Ψ(R) ≅ E` -/

section GroupRing

open _root_.Stacks.EtaleCohomology.ZModPrimePower Stacks.CharSeriesTraceDetection

variable (ℓ M : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] [Fintype G] (Λ : Type) [CommRing Λ]
  [Algebra (ZMod (ℓ ^ M)) Λ] (E : Type (u + 1)) [AddCommGroup E] [Module Λ E]
  [Module (ZMod (ℓ ^ M)) E] [IsScalarTower (ZMod (ℓ ^ M)) Λ E] (ρ : Representation Λ G E)
  [Finite E]

/-- `Ψ(R) ≅ Hom_{k₀}(E^∨, k₀)`: `R` is coinduced from `k₀`. -/
def twistFunctorGroupRingCoinductionEquiv :
    (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ).obj
        (ModuleCat.of (MonoidAlgebra (ZMod (ℓ ^ M)) G)
          (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G))) ≃ₗ[Λ]
      SourceHom (ZMod (ℓ ^ M)) Λ (TwistDual (ZMod (ℓ ^ M)) G Λ E ρ)
        (ULift.{u + 1} (ZMod (ℓ ^ M))) :=
  ((twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ).mapIso
      (groupRingCoinductionEquiv (ZMod (ℓ ^ M)) G).toModuleIso ≪≫
    (sourceHomCoinductionIso (ZMod (ℓ ^ M)) G Λ (TwistDual (ZMod (ℓ ^ M)) G Λ E ρ)).app
      (ModuleCat.of (ZMod (ℓ ^ M)) (ULift.{u + 1} (ZMod (ℓ ^ M))))).toLinearEquiv

omit [Fact (Nat.Prime ℓ)] [Finite E] in
/-- The image of `φ : Ψ(R)` in `Hom_{k₀}(E^∨, k₀)` sends `d` to the coefficient at `1` of `φ d`. -/
lemma twistFunctorGroupRingCoinductionEquiv_apply
    (φ : (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ).obj
        (ModuleCat.of (MonoidAlgebra (ZMod (ℓ ^ M)) G)
          (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G))))
    (d : TwistDual (ZMod (ℓ ^ M)) G Λ E ρ) :
    ((twistFunctorGroupRingCoinductionEquiv ℓ M G Λ E ρ φ).toLinearMap d).down =
      (φ.toLinearMap d).down.coeff 1 := by
  show (1 * (φ.toLinearMap d).down).coeff 1 * 1 = _
  rw [one_mul, mul_one]

/-- `Hom_{k₀}(E^∨, k₀) ≅ E`, by duality for finite `k₀`-modules. -/
def sourceHomDualEquiv :
    SourceHom (ZMod (ℓ ^ M)) Λ (TwistDual (ZMod (ℓ ^ M)) G Λ E ρ) (ULift.{u + 1} (ZMod (ℓ ^ M)))
      ≃ₗ[Λ] E :=
  let ev := LinearEquiv.ofBijective _ (bijective_dual_eval (ℓ := ℓ) (M := M) E)
  { toFun := fun φ => ev.symm
      { toFun := fun ξ => (φ.toLinearMap ⟨ξ⟩).down
        map_add' := fun ξ ξ' => congrArg ULift.down (map_add φ.toLinearMap ⟨ξ⟩ ⟨ξ'⟩)
        map_smul' := fun c ξ => congrArg ULift.down (map_smul φ.toLinearMap c ⟨ξ⟩) }
    invFun := fun e => SourceHom.ofLinearMap
      { toFun := fun d => ULift.up (d.toDual e)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    map_add' := fun φ φ' => ev.injective (by
      rw [map_add, ev.apply_symm_apply, ev.apply_symm_apply, ev.apply_symm_apply]; rfl)
    map_smul' := fun c φ => ev.injective (by
      rw [ev.apply_symm_apply]
      refine LinearMap.ext fun ξ => ?_
      change (φ.toLinearMap (c • ⟨ξ⟩)).down = ξ (c • ev.symm _)
      rw [show ξ (c • ev.symm _) = (ev (ev.symm _)) ((⟨ξ⟩ : TwistDual _ G Λ E ρ).toDual ∘ₗ
          (LinearMap.lsmul Λ E c).restrictScalars _) from rfl, ev.apply_symm_apply]
      rfl)
    left_inv := fun φ => SourceHom.ext fun d => by
      change ULift.up (d.toDual (ev.symm _)) = φ.toLinearMap d
      rw [show d.toDual (ev.symm _) = ev (ev.symm _) d.toDual from rfl, ev.apply_symm_apply]
      rfl
    right_inv := fun e => ev.injective (by rw [ev.apply_symm_apply]; rfl) }

omit [Fintype G] in
/-- A linear form `ξ` evaluated on the image of `φ` in `E` is `φ ξ`. -/
lemma dual_eval_sourceHomDualEquiv
    (φ : SourceHom (ZMod (ℓ ^ M)) Λ (TwistDual (ZMod (ℓ ^ M)) G Λ E ρ)
      (ULift.{u + 1} (ZMod (ℓ ^ M)))) (ξ : Module.Dual (ZMod (ℓ ^ M)) E) :
    ξ (sourceHomDualEquiv ℓ M G Λ E ρ φ) = (φ.toLinearMap ⟨ξ⟩).down :=
  DFunLike.congr_fun ((LinearEquiv.ofBijective _
    (bijective_dual_eval (ℓ := ℓ) (M := M) E)).apply_symm_apply _) ξ

/-- **`Ψ(R) ≅ E`**: `Hom_{k₀[G]}(E^∨, k₀[G]) ≅ Hom_{k₀}(E^∨, k₀) ≅ E`. -/
def twistFunctorGroupRingEquiv :
    (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ).obj
        (ModuleCat.of (MonoidAlgebra (ZMod (ℓ ^ M)) G)
          (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G))) ≃ₗ[Λ] E :=
  (twistFunctorGroupRingCoinductionEquiv ℓ M G Λ E ρ).trans (sourceHomDualEquiv ℓ M G Λ E ρ)

/-- A linear form `ξ` evaluated on the image of `φ : Ψ(R)` in `E` is the coefficient at `1` of
`φ ξ`. -/
lemma dual_eval_twistFunctorGroupRingEquiv
    (φ : (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ).obj
        (ModuleCat.of (MonoidAlgebra (ZMod (ℓ ^ M)) G)
          (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G))))
    (ξ : Module.Dual (ZMod (ℓ ^ M)) E) :
    ξ (twistFunctorGroupRingEquiv ℓ M G Λ E ρ φ) = (φ.toLinearMap ⟨ξ⟩).down.coeff 1 :=
  (dual_eval_sourceHomDualEquiv ℓ M G Λ E ρ _ ξ).trans
    (twistFunctorGroupRingCoinductionEquiv_apply ℓ M G Λ E ρ φ ⟨ξ⟩)

/-- **`Ψ(R) ≅ E` carries the right action of `g` on `R` to `ρ(g)`.** -/
theorem twistFunctorGroupRingEquiv_map_rightMulHom (g : G)
    (φ : (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ).obj
        (ModuleCat.of (MonoidAlgebra (ZMod (ℓ ^ M)) G)
          (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G)))) :
    twistFunctorGroupRingEquiv ℓ M G Λ E ρ (((twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ).map
        (rightMulHom (ULift.moduleEquiv.symm : MonoidAlgebra (ZMod (ℓ ^ M)) G ≃ₗ[_]
          ModuleCat.of (MonoidAlgebra (ZMod (ℓ ^ M)) G)
            (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G)))
          (MonoidAlgebra.single g⁻¹ 1))).hom φ) =
      ρ g (twistFunctorGroupRingEquiv ℓ M G Λ E ρ φ) := by
  refine (LinearEquiv.ofBijective _ (bijective_dual_eval (ℓ := ℓ) (M := M) E)).injective
    (LinearMap.ext fun ξ => ?_)
  show ξ _ = ξ (ρ g _)
  rw [dual_eval_twistFunctorGroupRingEquiv,
    show ξ (ρ g (twistFunctorGroupRingEquiv ℓ M G Λ E ρ φ)) =
      (ξ ∘ₗ (ρ g).restrictScalars (ZMod (ℓ ^ M)))
        (twistFunctorGroupRingEquiv ℓ M G Λ E ρ φ) from rfl,
    dual_eval_twistFunctorGroupRingEquiv]
  have hξ : (⟨ξ ∘ₗ (ρ g).restrictScalars (ZMod (ℓ ^ M))⟩ : TwistDual (ZMod (ℓ ^ M)) G Λ E ρ) =
      (MonoidAlgebra.single g⁻¹ (1 : ZMod (ℓ ^ M))) • (⟨ξ⟩ : TwistDual (ZMod (ℓ ^ M)) G Λ E ρ) := by
    rw [TwistDual.single_smul, one_smul]
    exact TwistDual.ext fun e => by simp
  rw [hξ, map_smul]
  show ((φ.toLinearMap ⟨ξ⟩).down * MonoidAlgebra.single g⁻¹ 1).coeff 1 =
    (MonoidAlgebra.single g⁻¹ 1 * (φ.toLinearMap ⟨ξ⟩).down).coeff 1
  rw [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply]
  simp

end GroupRing

/-! ### The twist of the descent sheaf of the group ring -/

section DescentSheaf

variable {X : Scheme.{u}} {H : Type} [Group H] (C : EtaleGaloisCovering X H)

/-- **Descent sheaves of isomorphic modules with compatible actions are isomorphic.** -/
def descentSheafCongr {A : Type} [Ring A] {N₁ N₂ : Type (u + 1)} [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] (ρ₁ : H →* Module.End A N₁) (ρ₂ : H →* Module.End A N₂)
    (e : N₁ ≃ₗ[A] N₂) (he : ∀ h n, e (ρ₁ h n) = ρ₂ h (e n)) :
    EtaleGaloisCovering.descentSheaf.{u, 0, _, 0} C A N₁ ρ₁ ≅
      EtaleGaloisCovering.descentSheaf.{u, 0, _, 0} C A N₂ ρ₂ :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun W => LinearEquiv.toModuleIso
      ({ toFun := fun f => ⟨f.1.map e, fun h z => by
            change e (f.1 _) = ρ₂ h (e (f.1 z))
            rw [f.2 h z, he]⟩
         invFun := fun f => ⟨f.1.map e.symm, fun h z => by
            change e.symm (f.1 _) = ρ₁ h (e.symm (f.1 z))
            rw [f.2 h z, ← e.symm_apply_apply (ρ₁ h (e.symm (f.1 z))), he, e.apply_symm_apply]⟩
         map_add' := fun _ _ => Subtype.ext (LocallyConstant.ext fun _ => map_add e _ _)
         map_smul' := fun _ _ => Subtype.ext (LocallyConstant.ext fun _ => map_smul e _ _)
         left_inv := fun f => Subtype.ext (LocallyConstant.ext fun _ => e.symm_apply_apply _)
         right_inv := fun f => Subtype.ext (LocallyConstant.ext fun _ => e.apply_symm_apply _) } :
        C.equivariantMaps A N₁ ρ₁ W.unop ≃ₗ[A] C.equivariantMaps A N₂ ρ₂ W.unop))
      (fun _ => rfl))

variable {A : Type} [Ring A] (Λ : Type) [CommRing Λ] (D : Type (u + 1)) [AddCommGroup D]
  [Module A D] [Module Λ D] [SMulCommClass Λ A D] [Module.Finite A D]
  {N : Type (u + 1)} [AddCommGroup N] [Module A N] (ρ' : H →* Module.End A N)

/-- The action of `H` on `Hom_A(D, N)` induced by an action on `N`. -/
def sourceHomAction : H →* Module.End Λ (SourceHom A Λ D N) where
  toFun h := ((sourceHomFunctor A Λ D).map (ModuleCat.ofHom (ρ' h))).hom
  map_one' := by
    refine LinearMap.ext fun φ => SourceHom.ext fun d => ?_
    change (ρ' 1) (φ.toLinearMap d) = φ.toLinearMap d
    rw [map_one]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun φ => SourceHom.ext fun d => ?_
    change (ρ' (g * h)) (φ.toLinearMap d) = ρ' g (ρ' h (φ.toLinearMap d))
    rw [map_mul]; rfl

/-- `Hom_A(D, -)` of the equivariant locally constant maps is the equivariant locally constant
maps into `Hom_A(D, N)`, `D` being finite. -/
def sourceHomEquivariantMapsEquiv (W : X.Etale) :
    SourceHom A Λ D (C.equivariantMaps A N ρ' W) ≃ₗ[Λ]
      C.equivariantMaps Λ (SourceHom A Λ D N) (sourceHomAction Λ D ρ') W where
  toFun φ := ⟨⟨fun z => SourceHom.ofLinearMap
      ((LocallyConstant.evalₗ A z) ∘ₗ (Submodule.subtype _) ∘ₗ φ.toLinearMap),
      ((isLocallyConstant_evalₗ_comp ((Submodule.subtype _) ∘ₗ φ.toLinearMap)).comp
        (SourceHom.ofLinearMap (Λ := Λ)))⟩, fun h z => SourceHom.ext fun d =>
      (φ.toLinearMap d).2 h z⟩
  invFun f := SourceHom.ofLinearMap
    { toFun := fun d => ⟨f.1.map fun ψ => ψ.toLinearMap d, fun h z => by
        change (f.1 _).toLinearMap d = ρ' h ((f.1 z).toLinearMap d)
        rw [f.2 h z]; rfl⟩
      map_add' := fun d d' => Subtype.ext (LocallyConstant.ext fun z =>
        map_add (f.1 z).toLinearMap d d')
      map_smul' := fun a d => Subtype.ext (LocallyConstant.ext fun z =>
        map_smul (f.1 z).toLinearMap a d) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`Ψ_D` of a descent sheaf is the descent sheaf of `Ψ_D` of the module.** -/
def sourceHomDescentSheafIso :
    (sheafCompose X.smallEtaleTopology (sourceHomFunctor A Λ D)).obj
        (EtaleGaloisCovering.descentSheaf.{u, 0, _, 0} C A N ρ') ≅
      EtaleGaloisCovering.descentSheaf.{u, 0, _, 0} C Λ (SourceHom A Λ D N)
        (sourceHomAction Λ D ρ') :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun W => (sourceHomEquivariantMapsEquiv C Λ D ρ' W.unop).toModuleIso)
      (fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext
        (LocallyConstant.ext fun _ => SourceHom.ext fun _ => by
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
          rfl))))

end DescentSheaf

/-! ### `F = D(E) ≅ Ψ(𝒫)` -/

section TwistDescent

open Stacks.CharSeriesTraceDetection

variable (ℓ M : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] [Fintype G] (Λ : Type) [CommRing Λ]
  [Algebra (ZMod (ℓ ^ M)) Λ] (E : Type (u + 1)) [AddCommGroup E] [Module Λ E]
  [Module (ZMod (ℓ ^ M)) E] [IsScalarTower (ZMod (ℓ ^ M)) Λ E] (ρ : Representation Λ G E)
  [Finite E] {X : Scheme.{u}} (C : EtaleGaloisCovering X G)

/-- The right action `x ↦ x g⁻¹` of `G` on `k₀[G]`, the action of the descent sheaf `𝒫`. -/
def groupRingRightAction :
    G →* Module.End (MonoidAlgebra (ZMod (ℓ ^ M)) G)
      (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G)) where
  toFun g := rightMul (ULift.moduleEquiv.symm : MonoidAlgebra (ZMod (ℓ ^ M)) G ≃ₗ[_]
    ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G)) (MonoidAlgebra.single g⁻¹ 1)
  map_one' := by
    rw [inv_one, ← MonoidAlgebra.one_def, rightMul_one]
    rfl
  map_mul' g h := by
    rw [mul_inv_rev, show (MonoidAlgebra.single (h⁻¹ * g⁻¹) (1 : ZMod (ℓ ^ M))) =
      MonoidAlgebra.single h⁻¹ 1 * MonoidAlgebra.single g⁻¹ 1 by
        rw [MonoidAlgebra.single_mul_single, mul_one], rightMul_mul]
    rfl

/-- **`F = D(E) ≅ Ψ(D(k₀[G]))`**: the descent sheaf of `E` is the twist of the descent sheaf
`𝒫` of the group ring with its right action. -/
def descentSheafTwistIso :
    EtaleGaloisCovering.descentSheaf.{u, 0, _, 0} C Λ E ρ ≅
      (sheafCompose X.smallEtaleTopology (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ)).obj
        (EtaleGaloisCovering.descentSheaf.{u, 0, _, 0} C (MonoidAlgebra (ZMod (ℓ ^ M)) G)
          (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G)) (groupRingRightAction ℓ M G)) :=
  descentSheafCongr C ρ (sourceHomAction Λ (TwistDual (ZMod (ℓ ^ M)) G Λ E ρ)
      (groupRingRightAction ℓ M G)) (twistFunctorGroupRingEquiv ℓ M G Λ E ρ).symm
      (fun g n => (twistFunctorGroupRingEquiv ℓ M G Λ E ρ).injective
        (((twistFunctorGroupRingEquiv ℓ M G Λ E ρ).apply_symm_apply _).trans
          ((congrArg (ρ g) ((twistFunctorGroupRingEquiv ℓ M G Λ E ρ).apply_symm_apply n)).symm.trans
            (twistFunctorGroupRingEquiv_map_rightMulHom ℓ M G Λ E ρ g
              ((twistFunctorGroupRingEquiv ℓ M G Λ E ρ).symm n)).symm))) ≪≫
    (sourceHomDescentSheafIso C Λ (TwistDual (ZMod (ℓ ^ M)) G Λ E ρ)
      (groupRingRightAction ℓ M G)).symm

end TwistDescent

end Stacks.EtaleCohomology

end
