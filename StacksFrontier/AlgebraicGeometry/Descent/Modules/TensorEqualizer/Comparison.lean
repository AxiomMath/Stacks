module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.TensorEqualizer.CharacterDuality

/-!
# The comparison arrow of the base-changed descent equalizer

For a universally injective algebra map `R → A`, the character-module duals of the unit
insertions `p ↦ 1 ⊗ p` admit a family of sections natural in the module. This file also
defines the first arrow `ModuleCat.tensorPushforwardComparison` of the base-changed equalizer
diagram of a module descent datum, computes it on pure tensors, and proves the fork condition.
-/

@[expose] public section

universe u v w

noncomputable section

namespace ModuleCat

open CategoryTheory TensorProduct
open scoped ModuleCat.Algebra

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- The algebra map `R → A`, read as a linear map between universe-lifted copies of `R` and `A`. -/
private noncomputable def liftedAlgebraLinearMap :
    ULift.{max (max u v) w} R →ₗ[R] ULift.{max (max u v) w} A :=
  (ULift.moduleEquiv.{u, v, max (max u v) w} (R := R) (M := A)).symm.toLinearMap.comp
    ((Algebra.linearMap R A).comp
      (ULift.moduleEquiv.{u, u, max (max u v) w} (R := R) (M := R)).toLinearMap)

/-- The universe-lifted algebra map is universally injective whenever the algebra map is. -/
private theorem liftedAlgebraLinearMap_universallyInjective
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A)) :
    _root_.UniversallyInjective.{u, max (max u v) w} (liftedAlgebraLinearMap R A) := by
  intro Q _ _
  have hQ := Algebra.rTensor_injective_of_universallyInjective R A h Q
  let eR : ULift.{max (max u v) w} R ≃ₗ[R] R :=
    ULift.moduleEquiv.{u, u, max (max u v) w} (R := R) (M := R)
  let eA : ULift.{max (max u v) w} A ≃ₗ[R] A :=
    ULift.moduleEquiv.{u, v, max (max u v) w} (R := R) (M := A)
  let d₀ : (ULift.{max (max u v) w} R ⊗[R] Q) ≃ₗ[R] (R ⊗[R] Q) :=
    TensorProduct.congr eR (LinearEquiv.refl R Q)
  let d₁ : (ULift.{max (max u v) w} A ⊗[R] Q) ≃ₗ[R] (A ⊗[R] Q) :=
    TensorProduct.congr eA (LinearEquiv.refl R Q)
  have key : ∀ z, d₁ ((liftedAlgebraLinearMap R A).rTensor Q z) =
      (Algebra.linearMap R A).rTensor Q (d₀ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [d₀, d₁, liftedAlgebraLinearMap]
    | tmul x y => simp [d₀, d₁, liftedAlgebraLinearMap, eA, eR]
    | add x y hx hy => simp [hx, hy]
  exact fun x y hxy => d₀.injective (hQ (by simpa only [key] using congrArg d₁ hxy))

/-- For a universally injective algebra map, the character-module dual of its universe-lifted
form admits a section, together with the functorial splittings and naturality squares of
Tag 08WV. -/
private theorem exists_liftedAlgebra_characterModuleSplitting
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A)) :
    ∃ s : CharacterModule (ULift.{max (max u v) w} R) →ₗ[R]
        CharacterModule (ULift.{max (max u v) w} A),
      CharacterModule.dual (liftedAlgebraLinearMap R A) ∘ₗ s = LinearMap.id ∧
      (∀ (P : Type (max (max u v) w)) [AddCommGroup P] [Module R P],
        CharacterModule.dual (LinearMap.lTensor P (liftedAlgebraLinearMap R A)) ∘ₗ
          _root_.functorialCharacterModuleSection s P = LinearMap.id) ∧
      ∀ (P Q : Type (max (max u v) w)) [AddCommGroup P] [Module R P]
        [AddCommGroup Q] [Module R Q] (k : P →ₗ[R] Q),
        _root_.functorialCharacterModuleSection s P ∘ₗ
            CharacterModule.dual (LinearMap.rTensor (ULift.{max (max u v) w} R) k) =
          CharacterModule.dual (LinearMap.rTensor (ULift.{max (max u v) w} A) k) ∘ₗ
            _root_.functorialCharacterModuleSection s Q :=
  _root_.exists_functorialCharacterModuleSplitting
    (liftedAlgebraLinearMap R A)
    (liftedAlgebraLinearMap_universallyInjective R A h)

/-- The insertion `p ↦ 1 ⊗ p` of a module into its base change along `R → A`. -/
public noncomputable def unitBaseChangeMap
    (P : Type w) [AddCommGroup P] [Module R P] : P →ₗ[R] A ⊗[R] P :=
  TensorProduct.mk R A P (1 : A)

/-- For a universally injective algebra map there is a family of sections of the character-module
duals of the unit insertions `p ↦ 1 ⊗ p`, natural in the module. -/
public theorem exists_unitBaseChange_characterSectionFamily
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A)) :
    ∃ s : ∀ (P : Type w) [AddCommGroup P] [Module R P],
        CharacterModule P →ₗ[R] CharacterModule (A ⊗[R] P),
      (∀ (P : Type w) [AddCommGroup P] [Module R P],
        CharacterModule.dual (unitBaseChangeMap (R := R) (A := A) P) ∘ₗ s P =
          LinearMap.id) ∧
      (∀ (P Q : Type w) [AddCommGroup P] [Module R P]
        [AddCommGroup Q] [Module R Q] (k : P →ₗ[R] Q),
        s P ∘ₗ CharacterModule.dual k =
          CharacterModule.dual (LinearMap.lTensor A k) ∘ₗ s Q) := by
  obtain ⟨s₀, hs₀, hsP, hnat⟩ := exists_liftedAlgebra_characterModuleSplitting R A h
  let s : ∀ (P : Type w) [AddCommGroup P] [Module R P],
      CharacterModule P →ₗ[R] CharacterModule (A ⊗[R] P) :=
    fun P _ _ => by
      let eR : ULift.{max (max u v) w} R ≃ₗ[R] R :=
        ULift.moduleEquiv.{u, u, max (max u v) w} (R := R) (M := R)
      let eA : ULift.{max (max u v) w} A ≃ₗ[R] A :=
        ULift.moduleEquiv.{u, v, max (max u v) w} (R := R) (M := A)
      let eP : ULift.{max (max u v) w} P ≃ₗ[R] P :=
        ULift.moduleEquiv.{u, w, max (max u v) w} (R := R) (M := P)
      let d₀ : (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} R) ≃ₗ[R] P :=
        (TensorProduct.congr eP eR).trans
          ((TensorProduct.comm R P R).trans (TensorProduct.lid R P))
      let d₁ : (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} A) ≃ₗ[R] (A ⊗[R] P) :=
        (TensorProduct.congr eP eA).trans (TensorProduct.comm R P A)
      let sf : CharacterModule (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} R) →ₗ[R]
          CharacterModule (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} A) :=
        _root_.functorialCharacterModuleSection s₀ (ULift.{max (max u v) w} P)
      exact (CharacterModule.dual d₁.symm.toLinearMap).comp <|
        sf.comp (CharacterModule.dual d₀.toLinearMap)
  refine ⟨s, ?_, ?_⟩
  · intro P _ _
    classical
    let eR : ULift.{max (max u v) w} R ≃ₗ[R] R :=
      ULift.moduleEquiv.{u, u, max (max u v) w} (R := R) (M := R)
    let eA : ULift.{max (max u v) w} A ≃ₗ[R] A :=
      ULift.moduleEquiv.{u, v, max (max u v) w} (R := R) (M := A)
    let eP : ULift.{max (max u v) w} P ≃ₗ[R] P :=
      ULift.moduleEquiv.{u, w, max (max u v) w} (R := R) (M := P)
    let d₀ : (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} R) ≃ₗ[R] P :=
      (TensorProduct.congr eP eR).trans
        ((TensorProduct.comm R P R).trans (TensorProduct.lid R P))
    let d₁ : (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} A) ≃ₗ[R] (A ⊗[R] P) :=
      (TensorProduct.congr eP eA).trans (TensorProduct.comm R P A)
    let j : (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} R) →ₗ[R]
        (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} A) :=
          LinearMap.lTensor (ULift.{max (max u v) w} P)
          (liftedAlgebraLinearMap R A)
    let sf : CharacterModule (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} R) →ₗ[R]
        CharacterModule (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} A) :=
      _root_.functorialCharacterModuleSection s₀ (ULift.{max (max u v) w} P)
    let uP := unitBaseChangeMap (R := R) (A := A) P
    let sP : CharacterModule P →ₗ[R] CharacterModule (A ⊗[R] P) :=
      (CharacterModule.dual d₁.symm.toLinearMap).comp <|
        sf.comp (CharacterModule.dual d₀.toLinearMap)
    have hcomm : d₁.toLinearMap.comp j = uP.comp d₀.toLinearMap := by
      refine LinearMap.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp [d₀, d₁, j, uP]
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul p r =>
          cases r with
          | up r =>
              show (algebraMap R A r) ⊗ₜ[R] eP p =
                (1 : A) ⊗ₜ[R] (r • eP p)
              simp [TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
    have hkey : CharacterModule.dual uP ∘ₗ CharacterModule.dual d₁.symm.toLinearMap =
        CharacterModule.dual d₀.symm.toLinearMap ∘ₗ CharacterModule.dual j := by
      refine LinearMap.ext fun χ => ?_
      ext p
      show χ (d₁.symm (uP p)) = χ (j (d₀.symm p))
      have hp : d₁ (j (d₀.symm p)) = uP p := by
        simpa using DFunLike.congr_fun hcomm (d₀.symm p)
      exact congrArg χ (d₁.symm_apply_eq.mpr hp.symm)
    have hsplit : CharacterModule.dual (LinearMap.lTensor (ULift.{max (max u v) w} P)
        (liftedAlgebraLinearMap R A)) ∘ₗ sf = LinearMap.id := hsP (ULift.{max (max u v) w} P)
    calc
      CharacterModule.dual uP ∘ₗ sP =
          CharacterModule.dual d₀.symm.toLinearMap ∘ₗ
            CharacterModule.dual j ∘ₗ sf ∘ₗ CharacterModule.dual d₀.toLinearMap := by
              dsimp [sP]
              calc
                _ = (CharacterModule.dual uP ∘ₗ CharacterModule.dual d₁.symm.toLinearMap) ∘ₗ
                    sf ∘ₗ CharacterModule.dual d₀.toLinearMap := by simp [LinearMap.comp_assoc]
                _ = (CharacterModule.dual d₀.symm.toLinearMap ∘ₗ CharacterModule.dual j) ∘ₗ
                    sf ∘ₗ CharacterModule.dual d₀.toLinearMap := by rw [hkey]
                _ = _ := by simp [LinearMap.comp_assoc]
      _ = LinearMap.id := by
        calc
          _ = CharacterModule.dual d₀.symm.toLinearMap ∘ₗ
              (CharacterModule.dual j ∘ₗ sf) ∘ₗ CharacterModule.dual d₀.toLinearMap := by
                simp [LinearMap.comp_assoc]
          _ = _ := by
            rw [hsplit]
            simp only [LinearMap.id_comp]
            rw [← CharacterModule.dual_comp d₀.symm.toLinearMap d₀.toLinearMap]
            rw [LinearEquiv.comp_symm]
            ext χ p
            rfl
  · intro P Q _ _ _ _ k
    classical
    let eR : ULift.{max (max u v) w} R ≃ₗ[R] R :=
      ULift.moduleEquiv.{u, u, max (max u v) w} (R := R) (M := R)
    let eA : ULift.{max (max u v) w} A ≃ₗ[R] A :=
      ULift.moduleEquiv.{u, v, max (max u v) w} (R := R) (M := A)
    let eP : ULift.{max (max u v) w} P ≃ₗ[R] P :=
      ULift.moduleEquiv.{u, w, max (max u v) w} (R := R) (M := P)
    let eQ : ULift.{max (max u v) w} Q ≃ₗ[R] Q :=
      ULift.moduleEquiv.{u, w, max (max u v) w} (R := R) (M := Q)
    let p₀ : (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} R) ≃ₗ[R] P :=
      (TensorProduct.congr eP eR).trans
        ((TensorProduct.comm R P R).trans (TensorProduct.lid R P))
    let q₀ : (ULift.{max (max u v) w} Q ⊗[R] ULift.{max (max u v) w} R) ≃ₗ[R] Q :=
      (TensorProduct.congr eQ eR).trans
        ((TensorProduct.comm R Q R).trans (TensorProduct.lid R Q))
    let p₁ : (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} A) ≃ₗ[R] (A ⊗[R] P) :=
      (TensorProduct.congr eP eA).trans (TensorProduct.comm R P A)
    let q₁ : (ULift.{max (max u v) w} Q ⊗[R] ULift.{max (max u v) w} A) ≃ₗ[R] (A ⊗[R] Q) :=
      (TensorProduct.congr eQ eA).trans (TensorProduct.comm R Q A)
    let k' : ULift.{max (max u v) w} P →ₗ[R] ULift.{max (max u v) w} Q := {
      toFun := fun x => ULift.up (k (ULift.down x))
      map_add' _ _ := congrArg ULift.up (map_add k _ _)
      map_smul' _ _ := congrArg ULift.up (map_smul k _ _) }
    let kp : (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} R) →ₗ[R]
        (ULift.{max (max u v) w} Q ⊗[R] ULift.{max (max u v) w} R) :=
          LinearMap.rTensor (ULift.{max (max u v) w} R) k'
    let kA : (A ⊗[R] P) →ₗ[R] (A ⊗[R] Q) := LinearMap.lTensor A k
    let kA' : (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} A) →ₗ[R]
        (ULift.{max (max u v) w} Q ⊗[R] ULift.{max (max u v) w} A) :=
          LinearMap.rTensor (ULift.{max (max u v) w} A) k'
    let sp : CharacterModule P →ₗ[R] CharacterModule (A ⊗[R] P) := s P
    let sq : CharacterModule Q →ₗ[R] CharacterModule (A ⊗[R] Q) := s Q
    let sfP : CharacterModule (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} R) →ₗ[R]
        CharacterModule (ULift.{max (max u v) w} P ⊗[R] ULift.{max (max u v) w} A) :=
      _root_.functorialCharacterModuleSection s₀ (ULift.{max (max u v) w} P)
    let sfQ : CharacterModule (ULift.{max (max u v) w} Q ⊗[R] ULift.{max (max u v) w} R) →ₗ[R]
        CharacterModule (ULift.{max (max u v) w} Q ⊗[R] ULift.{max (max u v) w} A) :=
      _root_.functorialCharacterModuleSection s₀ (ULift.{max (max u v) w} Q)
    have hdom : q₀.toLinearMap.comp kp = k.comp p₀.toLinearMap := by
      refine LinearMap.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp [q₀, kp, k', p₀]
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul x r => cases r with | up r => simp [q₀, kp, k', p₀, eR, eP, eQ]
    have hcod : q₁.toLinearMap.comp kA' = kA.comp p₁.toLinearMap := by
      refine LinearMap.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp [q₁, kA', k', kA, p₁]
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul x a => simp [q₁, kA', k', kA, p₁, eP, eQ]
    have hdualDom : CharacterModule.dual kp ∘ₗ CharacterModule.dual q₀.toLinearMap =
        CharacterModule.dual p₀.toLinearMap ∘ₗ CharacterModule.dual k := by
      rw [← CharacterModule.dual_comp p₀.toLinearMap k,
        ← CharacterModule.dual_comp kp q₀.toLinearMap, hdom]
    have hdualCod : CharacterModule.dual kA' ∘ₗ CharacterModule.dual q₁.toLinearMap =
        CharacterModule.dual p₁.toLinearMap ∘ₗ CharacterModule.dual kA := by
      rw [← CharacterModule.dual_comp p₁.toLinearMap kA,
        ← CharacterModule.dual_comp kA' q₁.toLinearMap, hcod]
    have hnat' : sfP ∘ₗ CharacterModule.dual kp = CharacterModule.dual kA' ∘ₗ sfQ :=
      hnat (ULift.{max (max u v) w} P) (ULift.{max (max u v) w} Q) k'
    have hdualCodKey : CharacterModule.dual p₁.symm.toLinearMap ∘ₗ
        CharacterModule.dual kA' = CharacterModule.dual kA ∘ₗ
          CharacterModule.dual q₁.symm.toLinearMap := by
      refine LinearMap.ext fun χ => ?_
      ext z
      show χ (kA' (p₁.symm z)) = χ (q₁.symm (kA z))
      have hz : q₁ (kA' (p₁.symm z)) = kA z := by
        simpa using DFunLike.congr_fun hcod (p₁.symm z)
      exact congrArg χ (q₁.eq_symm_apply.mpr hz)
    show sp ∘ₗ CharacterModule.dual k =
      CharacterModule.dual kA ∘ₗ sq
    dsimp [sp, sq, s]
    calc
      CharacterModule.dual p₁.symm.toLinearMap ∘ₗ sfP ∘ₗ
          CharacterModule.dual p₀.toLinearMap ∘ₗ CharacterModule.dual k =
        CharacterModule.dual p₁.symm.toLinearMap ∘ₗ sfP ∘ₗ
          CharacterModule.dual kp ∘ₗ CharacterModule.dual q₀.toLinearMap := by
            rw [← LinearMap.comp_assoc, ← hdualDom]
            simp [LinearMap.comp_assoc]
      _ = CharacterModule.dual p₁.symm.toLinearMap ∘ₗ
          (sfP ∘ₗ CharacterModule.dual kp) ∘ₗ CharacterModule.dual q₀.toLinearMap := by
            simp [LinearMap.comp_assoc]
      _ = CharacterModule.dual p₁.symm.toLinearMap ∘ₗ
          (CharacterModule.dual kA' ∘ₗ sfQ) ∘ₗ CharacterModule.dual q₀.toLinearMap := by
            rw [hnat']
      _ = CharacterModule.dual p₁.symm.toLinearMap ∘ₗ
          CharacterModule.dual kA' ∘ₗ sfQ ∘ₗ CharacterModule.dual q₀.toLinearMap := by
            simp [LinearMap.comp_assoc]
      _ = CharacterModule.dual kA ∘ₗ CharacterModule.dual q₁.symm.toLinearMap ∘ₗ
          sfQ ∘ₗ CharacterModule.dual q₀.toLinearMap := by
            calc
              _ = (CharacterModule.dual p₁.symm.toLinearMap ∘ₗ
                  CharacterModule.dual kA') ∘ₗ sfQ ∘ₗ
                  CharacterModule.dual q₀.toLinearMap := by simp [LinearMap.comp_assoc]
              _ = (CharacterModule.dual kA ∘ₗ
                  CharacterModule.dual q₁.symm.toLinearMap) ∘ₗ sfQ ∘ₗ
                  CharacterModule.dual q₀.toLinearMap := by rw [hdualCodKey]
              _ = _ := by simp [LinearMap.comp_assoc]
      _ = CharacterModule.dual kA ∘ₗ sq := rfl

/-- The first `A`-linear arrow of the base-changed equalizer diagram. -/
public def tensorPushforwardComparison
    (D : DescentData.{u, v, w} R A) :
    (A ⊗[R] invariantSubmodule R A D) →ₗ[A]
      (A ⊗[R] restrictModule R A D.module) where
  toFun := (invariantSubmodule R A D).subtype.lTensor A
  map_add' := (invariantSubmodule R A D).subtype.lTensor A |>.map_add
  map_smul' a x := (LinearMap.smul_lTensor
    ((invariantSubmodule R A D).subtype) a x).symm

/-- Under tensor symmetry, the first arrow applies the descent transition to
the unit pullback of the scalar multiple of an invariant section. -/
@[stacks 08X7 "comparison formula"]
public theorem tensorPushforwardComparison_tmul
    (D : DescentData.{u, v, w} R A)
    (a : A) (m : invariantSubmodule R A D) :
    tensorPushforwardComparison R A D (a ⊗ₜ[R] m) =
      D.transitionRestrictScalars R A
        ((a • (m.1 : restrictModule R A D.module)) ⊗ₜ[R] (1 : A)) := by
  show a ⊗ₜ[R] m.1 = D.transition ((a • m.1) ⊗ₜ[R] (1 : A))
  have hinv : D.transition (m.1 ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] m.1 := m.2
  have h := D.transition.map_smul (a ⊗ₜ[R] (1 : A)) (m.1 ⊗ₜ[R] (1 : A))
  rw [sourceTensor_smul_tmul, hinv, targetTensor_smul_tmul] at h
  have hscalar : restrictedScalarAction R A D.module a m.1 =
      a • (m.1 : restrictModule R A D.module) :=
    restrictedScalarAction_apply R A D.module a m.1
  rw [hscalar] at h
  simpa only [one_mul, mul_one, map_one, Module.End.one_apply] using h.symm

/-- The base-changed inclusion equalizes the two pullbacks of a descent datum. -/
@[stacks 08X7 "fork condition"]
public theorem tensorPushforwardComparison_condition
    (D : DescentData.{u, v, w} R A) :
    ModuleCat.ofHom (tensorPushforwardComparison R A D) ≫
        ModuleCat.ofHom (DescentData.transition12AfterUnitHom R A D) =
      ModuleCat.ofHom (tensorPushforwardComparison R A D) ≫
        ModuleCat.ofHom (DescentData.rightUnitBaseChangeHom R A D) := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x => ?_
  show DescentData.transition12AfterUnitHom R A D
      (tensorPushforwardComparison R A D x) =
    DescentData.rightUnitBaseChangeHom R A D
      (tensorPushforwardComparison R A D x)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a m =>
      have h : DescentData.transition12AfterUnit R A D
            (a ⊗ₜ[R] (m.1 : restrictModule R A D.module)) =
          DescentData.rightUnitBaseChange R A D
            (a ⊗ₜ[R] (m.1 : restrictModule R A D.module)) := by
        simp only [DescentData.transition12AfterUnit, transition12, LinearMap.coe_comp,
          LinearEquiv.coe_coe, Function.comp_apply, LinearMap.flip_apply, mk_apply,
          assoc_tmul, LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars,
          DescentData.rightUnitBaseChange, map_tmul, LinearMap.id_coe, id_eq]
        rw [← DescentData.transitionRestrictScalars_apply R A D,
          m.2]
        simp
      have hl := congrArg
        (fun f : (A ⊗[R] restrictModule R A D.module) →ₗ[R]
            ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) =>
          f (a ⊗ₜ[R] (m.1 : restrictModule R A D.module)))
        (DescentData.transition12AfterUnitHom_restrictScalars R A D)
      have hr := congrArg
        (fun f : (A ⊗[R] restrictModule R A D.module) →ₗ[R]
            ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) =>
          f (a ⊗ₜ[R] (m.1 : restrictModule R A D.module)))
        (DescentData.rightUnitBaseChangeHom_restrictScalars R A D)
      exact hl.trans (h.trans hr.symm)

end ModuleCat

end
