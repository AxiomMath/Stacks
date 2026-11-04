module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Flat.LocalCriteria
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Flat.LocalCriterionVariant.TorVanishing
public import StacksFrontier.RingTheory.Flat.LocalCriterionVariant.Criterion
import all StacksFrontier.RingTheory.Flat.LocalCriterionVariant.TorVanishing
import all StacksFrontier.RingTheory.Flat.LocalCriterionVariant.Criterion

@[expose] public section

/-!
# Stacks 00MO: the criterion after a base change and a localization

The variant 00MO of the local criterion for flatness, for a commutative square with `S'` a
localization of `S ⊗_R R'` (`Module.Flat.of_flat_quotient_of_tor_one_map_eq_zero`), and its form
with a larger ideal at the target needed by Stacks 0471
(`Module.Flat.of_flat_quotient_of_tor_one_map_eq_zero_of_mem`).
-/

open TensorProduct

namespace Stacks.Flat.LocalCriterion

section Square

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- For `B = S ⊗[R] R'` and an `S`-module `M`, the `B`-module `B ⊗[S] M` is the base change of `M`
along `R → R'`, the structural map being `m ↦ 1 ⊗ₜ m`. -/
private theorem isBaseChange_one_tmul {R S R' M : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    IsBaseChange R' ((TensorProduct.mk S (S ⊗[R] R') M 1).restrictScalars R) := by
  have halg : ∀ r' : R', (algebraMap R' (S ⊗[R] R')) r' = 1 ⊗ₜ[R] r' := fun _ => rfl
  have hone : (1 : S ⊗[R] R') = (1 : S) ⊗ₜ[R] (1 : R') := rfl
  have hsmulS : ∀ (s s₀ : S) (r' : R'), s • (s₀ ⊗ₜ[R] r') = (s * s₀) ⊗ₜ[R] r' := by
    intro s s₀ r'
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp
  have hsmulR' : ∀ (r' r'' : R') (s₀ : S), r' • (s₀ ⊗ₜ[R] r'') = s₀ ⊗ₜ[R] (r' * r'') := by
    intro r' r'' s₀
    rw [Algebra.smul_def, halg, Algebra.TensorProduct.tmul_mul_tmul]
    simp [mul_comm]
  have hgen :
    ∀ (s : S) (r' : R') (m : M),
      (s ⊗ₜ[R] r') ⊗ₜ[S] m = r' • (((1 : S ⊗[R] R')) ⊗ₜ[S] (s • m)) := by
    intro s r' m
    rw [TensorProduct.smul_tmul' r' (1 : S ⊗[R] R') (s • m), ← TensorProduct.smul_tmul s _ m, hone,
      hsmulR', hsmulS]
    simp
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ g
  let inner : S → R' → (M →ₗ[R] Q) := fun s r' =>
    { toFun := fun m => r' • g (s • m)
      map_add' := by
        intro a b; simp [smul_add]
      map_smul' := by
        intro c m; simp [smul_comm s c m, smul_comm r' c] }
  let ψ : S →ₗ[R] R' →ₗ[R] (M →ₗ[R] Q) :=
    LinearMap.mk₂ R inner
      (by
        intro s1 s2 r'; ext m; simp [inner, add_smul, smul_add])
      (by
        intro c s r'; ext m; simp [inner, smul_assoc, smul_comm r' c])
      (by
        intro s r1 r2; ext m; simp [inner, add_smul])
      (by
        intro c s r'; ext m; simp [inner, smul_assoc, smul_comm c])
  let Θ : (S ⊗[R] R') →ₗ[R] (M →ₗ[R] Q) := TensorProduct.lift ψ
  have hΘ : ∀ (s : S) (r' : R') (m : M), Θ (s ⊗ₜ[R] r') m = r' • g (s • m) := fun _ _ _ => rfl
  have hbal : ∀ (s : S) (b : S ⊗[R] R') (m : M), Θ (s • b) m = Θ b (s • m) := by
    intro s b m
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul s₀ r' => rw [hsmulS, hΘ, hΘ, mul_comm, mul_smul]
    | add x y hx hy =>
      rw [smul_add, map_add, map_add]; simp [hx, hy]
  have hsm : ∀ (r' : R') (b : S ⊗[R] R') (m : M), Θ (r' • b) m = r' • Θ b m := by
    intro r' b m
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul s₀ r'' => rw [hsmulR', hΘ, hΘ, mul_smul]
    | add x y hx hy =>
      rw [smul_add, map_add, map_add]; simp [hx, hy]
  let F : (S ⊗[R] R') →+ (M →+ Q) :=
    { toFun := fun b => (Θ b).toAddMonoidHom
      map_zero' := by
        ext m; simp
      map_add' := by
        intro a b; ext m; simp }
  let g₀ : ((S ⊗[R] R') ⊗[S] M) →+ Q := TensorProduct.liftAddHom F hbal
  have hg₀ : ∀ (b : S ⊗[R] R') (m : M), g₀ (b ⊗ₜ[S] m) = Θ b m := fun _ _ => rfl
  have hsmul' : ∀ (r' : R') (z : (S ⊗[R] R') ⊗[S] M), g₀ (r' • z) = r' • g₀ z := by
    intro r' z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      rw [TensorProduct.smul_tmul', hg₀, hg₀]; exact hsm r' b m
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  set g' : ((S ⊗[R] R') ⊗[S] M) →ₗ[R'] Q :=
    { toFun := g₀, map_add' := g₀.map_add, map_smul' := hsmul' } with hg'def
  have hg' : ∀ (b : S ⊗[R] R') (m : M), g' (b ⊗ₜ[S] m) = Θ b m := fun _ _ => rfl
  refine ⟨g', ?_, ?_⟩
  · ext m
    simpa [hg', hone] using hΘ 1 1 m
  · intro h hh
    have hh' : ∀ m : M, h ((1 : S ⊗[R] R') ⊗ₜ[S] m) = g m := fun m => LinearMap.congr_fun hh m
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul s r' =>
        rw [hgen]
        simp only [map_smul]
        rw [hh', hg', hone, hΘ]
        simp
      | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `lTensor` in the right factor commutes with the action of a bigger ring on the left factor. -/
private theorem lTensor_smul {A B X P Q : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X] [SMulCommClass A B X]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] (g : P →ₗ[A] Q) (b : B)
    (u : X ⊗[A] P) : LinearMap.lTensor X g (b • u) = b • LinearMap.lTensor X g u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x p =>
    rw [TensorProduct.smul_tmul', LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **Stacks 00MM and 00MN for the square.** The `Tor`-vanishing hypothesis of the variant 00ML
of the local criterion, for the module `M'` over `R'` and the ideal `I' = IR'`: the map
`I' ⊗_{R'} M' → R' ⊗_{R'} M'` is injective. -/
private theorem rTensor_subtype_map_injective_square {R R' S S' M M' : Type*} [CommRing R]
    [CommRing R'] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S']
    [Algebra R' S']
    [Algebra (S ⊗[R] R') S'] [IsScalarTower S (S ⊗[R] R') S']
    (hR' :
      (algebraMap (S ⊗[R] R') S').comp
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom =
        algebraMap R' S')
    (T : Submonoid (S ⊗[R] R')) [IsLocalization T S'] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [AddCommGroup M'] [Module R M'] [Module S M'] [Module R' M']
    [Module S' M'] [IsScalarTower R S M'] [IsScalarTower R R' M'] [IsScalarTower S S' M']
    [IsScalarTower R' S' M'] (I : Ideal R) (f : M →ₗ[S] M') (hf : IsBaseChange S' f)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (htor :
      LinearMap.ker (I.subtype.rTensor M) ≤
        LinearMap.ker
          (TensorProduct.lift
            (((TensorProduct.mk R' ↥(I.map (algebraMap R R')) M').restrictScalars₁₂ R R).compl₁₂
              ((Algebra.linearMap R R').restrict (p := I) (q :=
                (I.map (algebraMap R R')).restrictScalars R) fun _ hx => Ideal.mem_map_of_mem _ hx)
              (f.restrictScalars R)))) :
    Function.Injective ((I.map (algebraMap R R')).subtype.rTensor M') := by
  -- the `B = S ⊗_R R'`-module structure on `M'`, restricted from `S'`
  let _ : Module (S ⊗[R] R') M' := Module.compHom M' (algebraMap (S ⊗[R] R') S')
  have _ : IsScalarTower (S ⊗[R] R') S' M' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : IsScalarTower S (S ⊗[R] R') M' :=
    IsScalarTower.of_algebraMap_smul fun s x => by
      have h :
        (algebraMap S (S ⊗[R] R') s) • x =
          (algebraMap (S ⊗[R] R') S') (algebraMap S (S ⊗[R] R') s) • x :=
        rfl
      rw [h, ← IsScalarTower.algebraMap_apply, algebraMap_smul]
  have _ : IsScalarTower R' (S ⊗[R] R') M' :=
    IsScalarTower.of_algebraMap_smul fun r' x => by
      have h :
        (algebraMap R' (S ⊗[R] R')) r' • x =
          (algebraMap (S ⊗[R] R') S') (algebraMap R' (S ⊗[R] R') r') • x :=
        rfl
      have h2 :
        (algebraMap (S ⊗[R] R') S') ((algebraMap R' (S ⊗[R] R')) r') = algebraMap R' S' r' :=
        RingHom.congr_fun hR' r'
      rw [h, h2, algebraMap_smul]
  -- `N = B ⊗_S M` is the base change of `M` both to `B` and to `R'`, and `M'` is its
  -- localization at `T`
  have hjB : IsBaseChange (S ⊗[R] R') (TensorProduct.mk S (S ⊗[R] R') M 1) :=
    TensorProduct.isBaseChange S M (S ⊗[R] R')
  have hgloc : IsLocalizedModule T (hjB.lift f) := by
    rw [isLocalizedModule_iff_isBaseChange T S']
    refine hjB.of_comp ?_
    rw [hjB.lift_comp]
    exact hf
  have hj : IsBaseChange R' ((TensorProduct.mk S (S ⊗[R] R') M 1).restrictScalars R) :=
    isBaseChange_one_tmul
  have hJ : ∀ a ∈ I, algebraMap R R' a ∈ I.map (algebraMap R R') := fun _ hx =>
    Ideal.mem_map_of_mem _ hx
  -- the two localization maps on the tensor products
  set Γ := AlgebraTensorModule.rTensor R' ↥(I.map (algebraMap R R')) (hjB.lift f) with hΓ
  set ΓR := AlgebraTensorModule.rTensor R' R' (hjB.lift f) with hΓR
  -- the `R'`-linear map `I' ⊗_R M → M' ⊗_{R'} I'` through which `htor` is read
  set Ψ : ↥(I.map (algebraMap R R')) ⊗[R] M →ₗ[R'] M' ⊗[R'] ↥(I.map (algebraMap R R')) :=
    (Γ.restrictScalars R') ∘ₗ (bc hj ↥(I.map (algebraMap R R'))).toLinearMap with hΨ
  have hΨtor :
    ∀ x : ↥I ⊗[R] M,
      LinearMap.rTensor M I.subtype x = 0 →
        Ψ (LinearMap.rTensor M (incl I (I.map (algebraMap R R')) hJ) x) = 0 := by
    have hval :
      ∀ x : ↥I ⊗[R] M,
        Ψ (LinearMap.rTensor M (incl I _ hJ) x) =
          TensorProduct.comm R' ↥(I.map (algebraMap R R')) M'
            (TensorProduct.lift
              (((TensorProduct.mk R' ↥(I.map (algebraMap R R')) M').restrictScalars₁₂ R R).compl₁₂
                ((Algebra.linearMap R R').restrict (p := I) (q :=
                  (I.map (algebraMap R R')).restrictScalars R) fun _ hx =>
                  Ideal.mem_map_of_mem _ hx)
                (f.restrictScalars R))
              x) := by
      have hlift : ∀ m : M, (hjB.lift f) ((TensorProduct.mk S (S ⊗[R] R') M 1) m) = f m :=
        hjB.lift_eq f
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a
        m =>
        rw [LinearMap.rTensor_tmul, hΨ, LinearMap.comp_apply, LinearEquiv.coe_coe, bc_tmul]
        simp only [LinearMap.coe_restrictScalars, hΓ, AlgebraTensorModule.rTensor_tmul, hlift]
        rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    intro x hx
    rw [hval x, (LinearMap.mem_ker).mp (htor (LinearMap.mem_ker.mpr hx)), map_zero]
  -- pass to the flipped tensor product, where the localization instances live
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  have hzero :
    ∀ w : M' ⊗[R'] ↥(I.map (algebraMap R R')),
      LinearMap.lTensor M' (I.map (algebraMap R R')).subtype w = 0 → w = 0 := by
    intro w hw
    obtain ⟨⟨y, t⟩, hyt⟩ := IsLocalizedModule.surj T Γ w
    -- the commuting square for the two localization maps
    have hsq :
      ∀ v,
        LinearMap.lTensor M' (I.map (algebraMap R R')).subtype (Γ v) =
          ΓR (LinearMap.lTensor ((S ⊗[R] R') ⊗[S] M) (I.map (algebraMap R R')).subtype v) := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul n a => simp [hΓ, hΓR]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    have h1 :
      ΓR (LinearMap.lTensor ((S ⊗[R] R') ⊗[S] M) (I.map (algebraMap R R')).subtype y) = 0 := by
      rw [← hsq y, ← hyt, Submonoid.smul_def,
        lTensor_smul (A := R') (B := S ⊗[R] R') _ (t : S ⊗[R] R') w, hw, smul_zero]
    obtain ⟨t₀, ht₀⟩ := (IsLocalizedModule.eq_zero_iff T ΓR).mp h1
    have h2 :
      LinearMap.lTensor ((S ⊗[R] R') ⊗[S] M) (I.map (algebraMap R R')).subtype
          ((t₀ : S ⊗[R] R') • y) =
        0 := by
      rwa [lTensor_smul (A := R') (B := S ⊗[R] R') _ (t₀ : S ⊗[R] R') y, ← Submonoid.smul_def]
    -- `key` applies to the transported element
    have hz :
      sg (I.map (algebraMap R R')) M
          ((bc hj ↥(I.map (algebraMap R R'))).symm ((t₀ : S ⊗[R] R') • y)) =
        0 := by
      apply (bc hj R').injective
      rwa [map_zero, ← bc_sg hj, LinearEquiv.apply_symm_apply]
    have h3 := key I (I.map (algebraMap R R')) hJ hflat Ψ hΨtor _ hz
    rw [hΨ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h3
    have e1 : (t : S ⊗[R] R') • w = Γ y := by rw [← hyt, Submonoid.smul_def]
    have h4 : (t₀ : S ⊗[R] R') • ((t : S ⊗[R] R') • w) = 0 := by
      rwa [e1, ← LinearMap.map_smul]
    have h5 : (t : S ⊗[R] R') • w = 0 := by
      refine IsLocalizedModule.smul_injective Γ t₀ ?_
      change t₀ • ((t : S ⊗[R] R') • w) = t₀ • (0 : M' ⊗[R'] ↥(I.map (algebraMap R R')))
      rw [Submonoid.smul_def, h4, smul_zero]
    refine IsLocalizedModule.smul_injective Γ t ?_
    change t • w = t • (0 : M' ⊗[R'] ↥(I.map (algebraMap R R')))
    rw [Submonoid.smul_def, h5, smul_zero]
  intro a b hab
  exact sub_eq_zero.mp (hzero (a - b) (by rw [map_sub, hab, sub_self]))


/-- **Stacks 00MM and 00MN for the square, for any ideal `J` of `R'` containing `IR'`.** The
`Tor`-vanishing hypothesis of 00ML for the module `M'` over `R'` and the ideal `J`: the map
`J ⊗_{R'} M' → R' ⊗_{R'} M'` is injective. For `J = IR'` this is the hypothesis needed by 00MO;
`Stacks.Flat.LocalCriterion.key` is stated for an arbitrary such `J`. -/
private theorem rTensor_subtype_injective_of_mem {R R' S S' M M' : Type*} [CommRing R]
    [CommRing R'] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S']
    [Algebra R' S'] [Algebra (S ⊗[R] R') S'] [IsScalarTower S (S ⊗[R] R') S']
    (hR' :
      (algebraMap (S ⊗[R] R') S').comp
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom =
        algebraMap R' S')
    (T : Submonoid (S ⊗[R] R')) [IsLocalization T S'] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [AddCommGroup M'] [Module R M'] [Module S M'] [Module R' M']
    [Module S' M'] [IsScalarTower R S M'] [IsScalarTower R R' M'] [IsScalarTower S S' M']
    [IsScalarTower R' S' M'] (I : Ideal R) (J : Ideal R') (hJ : ∀ a ∈ I, algebraMap R R' a ∈ J)
    (f : M →ₗ[S] M') (hf : IsBaseChange S' f)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (htor :
      LinearMap.ker (I.subtype.rTensor M) ≤
        LinearMap.ker
          (TensorProduct.lift
            (((TensorProduct.mk R' ↥J M').restrictScalars₁₂ R R).compl₁₂
              ((Algebra.linearMap R R').restrict (p := I) (q := J.restrictScalars R) hJ)
              (f.restrictScalars R)))) :
    Function.Injective (J.subtype.rTensor M') := by
  -- the `B = S ⊗_R R'`-module structure on `M'`, restricted from `S'`
  let _ : Module (S ⊗[R] R') M' := Module.compHom M' (algebraMap (S ⊗[R] R') S')
  have _ : IsScalarTower (S ⊗[R] R') S' M' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : IsScalarTower S (S ⊗[R] R') M' :=
    IsScalarTower.of_algebraMap_smul fun s x => by
      have h :
        (algebraMap S (S ⊗[R] R') s) • x =
          (algebraMap (S ⊗[R] R') S') (algebraMap S (S ⊗[R] R') s) • x :=
        rfl
      rw [h, ← IsScalarTower.algebraMap_apply, algebraMap_smul]
  have _ : IsScalarTower R' (S ⊗[R] R') M' :=
    IsScalarTower.of_algebraMap_smul fun r' x => by
      have h :
        (algebraMap R' (S ⊗[R] R')) r' • x =
          (algebraMap (S ⊗[R] R') S') (algebraMap R' (S ⊗[R] R') r') • x :=
        rfl
      have h2 :
        (algebraMap (S ⊗[R] R') S') ((algebraMap R' (S ⊗[R] R')) r') = algebraMap R' S' r' :=
        RingHom.congr_fun hR' r'
      rw [h, h2, algebraMap_smul]
  -- `N = B ⊗_S M` is the base change of `M` both to `B` and to `R'`, and `M'` is its
  -- localization at `T`
  have hjB : IsBaseChange (S ⊗[R] R') (TensorProduct.mk S (S ⊗[R] R') M 1) :=
    TensorProduct.isBaseChange S M (S ⊗[R] R')
  have hgloc : IsLocalizedModule T (hjB.lift f) := by
    rw [isLocalizedModule_iff_isBaseChange T S']
    refine hjB.of_comp ?_
    rw [hjB.lift_comp]
    exact hf
  have hj : IsBaseChange R' ((TensorProduct.mk S (S ⊗[R] R') M 1).restrictScalars R) :=
    isBaseChange_one_tmul
  -- the two localization maps on the tensor products
  set Γ := AlgebraTensorModule.rTensor R' ↥J (hjB.lift f) with hΓ
  set ΓR := AlgebraTensorModule.rTensor R' R' (hjB.lift f) with hΓR
  -- the `R'`-linear map `J ⊗_R M → M' ⊗_{R'} J` through which `htor` is read
  set Ψ : ↥J ⊗[R] M →ₗ[R'] M' ⊗[R'] ↥J := (Γ.restrictScalars R') ∘ₗ (bc hj ↥J).toLinearMap with hΨ
  have hΨtor :
    ∀ x : ↥I ⊗[R] M,
      LinearMap.rTensor M I.subtype x = 0 → Ψ (LinearMap.rTensor M (incl I J hJ) x) = 0 := by
    have hval :
      ∀ x : ↥I ⊗[R] M,
        Ψ (LinearMap.rTensor M (incl I J hJ) x) =
          TensorProduct.comm R' ↥J M'
            (TensorProduct.lift
              (((TensorProduct.mk R' ↥J M').restrictScalars₁₂ R R).compl₁₂
                ((Algebra.linearMap R R').restrict (p := I) (q := J.restrictScalars R) hJ)
                (f.restrictScalars R))
              x) := by
      have hlift : ∀ m : M, (hjB.lift f) ((TensorProduct.mk S (S ⊗[R] R') M 1) m) = f m :=
        hjB.lift_eq f
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a
        m =>
        rw [LinearMap.rTensor_tmul, hΨ, LinearMap.comp_apply, LinearEquiv.coe_coe, bc_tmul]
        simp only [LinearMap.coe_restrictScalars, hΓ, AlgebraTensorModule.rTensor_tmul, hlift]
        rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    intro x hx
    rw [hval x, (LinearMap.mem_ker).mp (htor (LinearMap.mem_ker.mpr hx)), map_zero]
  -- pass to the flipped tensor product, where the localization instances live
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  have hzero : ∀ w : M' ⊗[R'] ↥J, LinearMap.lTensor M' J.subtype w = 0 → w = 0 := by
    intro w hw
    obtain ⟨⟨y, t⟩, hyt⟩ := IsLocalizedModule.surj T Γ w
    -- the commuting square for the two localization maps
    have hsq :
      ∀ v,
        LinearMap.lTensor M' J.subtype (Γ v) =
          ΓR (LinearMap.lTensor ((S ⊗[R] R') ⊗[S] M) J.subtype v) := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul n a => simp [hΓ, hΓR]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    have h1 : ΓR (LinearMap.lTensor ((S ⊗[R] R') ⊗[S] M) J.subtype y) = 0 := by
      rw [← hsq y, ← hyt, Submonoid.smul_def,
        lTensor_smul (A := R') (B := S ⊗[R] R') _ (t : S ⊗[R] R') w, hw, smul_zero]
    obtain ⟨t₀, ht₀⟩ := (IsLocalizedModule.eq_zero_iff T ΓR).mp h1
    have h2 : LinearMap.lTensor ((S ⊗[R] R') ⊗[S] M) J.subtype ((t₀ : S ⊗[R] R') • y) = 0 := by
      rwa [lTensor_smul (A := R') (B := S ⊗[R] R') _ (t₀ : S ⊗[R] R') y, ← Submonoid.smul_def]
    -- `key` applies to the transported element
    have hz : sg J M ((bc hj ↥J).symm ((t₀ : S ⊗[R] R') • y)) = 0 := by
      apply (bc hj R').injective
      rwa [map_zero, ← bc_sg hj, LinearEquiv.apply_symm_apply]
    have h3 := key I J hJ hflat Ψ hΨtor _ hz
    rw [hΨ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h3
    have e1 : (t : S ⊗[R] R') • w = Γ y := by rw [← hyt, Submonoid.smul_def]
    have h4 : (t₀ : S ⊗[R] R') • ((t : S ⊗[R] R') • w) = 0 := by
      rwa [e1, ← LinearMap.map_smul]
    have h5 : (t : S ⊗[R] R') • w = 0 := by
      refine IsLocalizedModule.smul_injective Γ t₀ ?_
      change t₀ • ((t : S ⊗[R] R') • w) = t₀ • (0 : M' ⊗[R'] ↥J)
      rw [Submonoid.smul_def, h4, smul_zero]
    refine IsLocalizedModule.smul_injective Γ t ?_
    change t • w = t • (0 : M' ⊗[R'] ↥J)
    rw [Submonoid.smul_def, h5, smul_zero]
  intro a b hab
  exact sub_eq_zero.mp (hzero (a - b) (by rw [map_sub, hab, sub_self]))

/-- The image `IR'` of a proper ideal of a local ring `R` under a local homomorphism into a local
ring `R'` is again proper. -/
private theorem map_ne_top_of_isLocalHom {R R' : Type*} [CommRing R] [CommRing R'] [IsLocalRing R]
    [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] {I : Ideal R} (hI : I ≠ ⊤) :
    I.map (algebraMap R R') ≠ ⊤ := by
  have h1 : I.map (algebraMap R R') ≤ IsLocalRing.maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact fun hu => (IsLocalRing.le_maximalIdeal hI hx) (isUnit_of_map_unit _ x hu)
  exact fun h => (IsLocalRing.maximalIdeal.isMaximal R').ne_top (top_le_iff.1 (h ▸ h1))

/-- Injectivity of `P ⊗_A u` passes from a `C`-module `P` to a localization `P'` of `P` at a
submonoid `T` of `C`, from the weaker hypothesis that `P ⊗_A u` kills nothing that survives
multiplication by `T`.

Here `A → C` is a ring map, `P` and `P'` are `C`-modules and `u : X → Y` is a map of `A`-modules.
The point is that `P' ⊗_A X` is the localization of `P ⊗_A X` at `T` (`IsLocalizedModule.rTensor`),
so an element of `P' ⊗_A X` killed by `P' ⊗_A u` comes, after multiplication by an element of `T`,
from an element of `P ⊗_A X` killed by `P ⊗_A u`. -/
public theorem lTensor_injective_of_isLocalizedModule {A C P P' X Y : Type*} [CommRing A]
    [CommRing C] [Algebra A C] [AddCommGroup P] [Module A P] [Module C P] [IsScalarTower A C P]
    [AddCommGroup P'] [Module A P'] [Module C P'] [IsScalarTower A C P'] [AddCommGroup X]
    [Module A X] [AddCommGroup Y] [Module A Y] (T : Submonoid C) (g : P →ₗ[C] P')
    [IsLocalizedModule T g] (u : X →ₗ[A] Y)
    (hu : ∀ z : P ⊗[A] X, LinearMap.lTensor P u z = 0 → ∃ t : T, (t : C) • z = 0) :
    Function.Injective (LinearMap.lTensor P' u) := by
  let α : P ⊗[A] X →ₗ[C] P ⊗[A] Y := AlgebraTensorModule.map LinearMap.id u
  let α' : P' ⊗[A] X →ₗ[C] P' ⊗[A] Y := AlgebraTensorModule.map LinearMap.id u
  have hcα : ⇑α = ⇑(LinearMap.lTensor P u) := rfl
  have hcα' : ⇑α' = ⇑(LinearMap.lTensor P' u) := rfl
  have hsq : ∀ z : P ⊗[A] X,
      α' (AlgebraTensorModule.rTensor A X g z) = AlgebraTensorModule.rTensor A Y g (α z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul p x => simp [α, α']
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  rw [← hcα']
  refine IsLocalizedModule.injective_of_map_zero T (AlgebraTensorModule.rTensor A X g) ?_
  intro z hz
  rw [hsq] at hz
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T _).mp hz
  obtain ⟨t', ht'⟩ := hu ((t : C) • z) (by
    rw [← hcα, map_smul]
    simpa [Submonoid.smul_def] using ht)
  rw [IsLocalizedModule.eq_zero_iff T]
  exact ⟨t' * t, by simpa [mul_smul, Submonoid.smul_def] using ht'⟩

/-- Tensoring over `A'` with the base change `A' ⊗_{R'} P` and tensoring over `R'` with `P` detect
the same injective maps, for `A'` a quotient of `R'` and `P` an `R'`-module.

This is the natural isomorphism `(A' ⊗_{R'} P) ⊗_{A'} X = P ⊗_{R'} X` for an `A'`-module `X`,
read off on injectivity: it is what lets a flatness statement over `A'` about `A' ⊗_{R'} P` be
tested on `R'`-tensor products with `P`. -/
public theorem lTensor_baseChange_injective_iff {R' A' P X Y : Type*} [CommRing R'] [CommRing A']
    [Algebra R' A'] [AddCommGroup P] [Module R' P] [AddCommGroup X] [Module R' X] [Module A' X]
    [IsScalarTower R' A' X] [AddCommGroup Y] [Module R' Y] [Module A' Y] [IsScalarTower R' A' Y]
    (u : X →ₗ[A'] Y) :
    Function.Injective (LinearMap.lTensor (A' ⊗[R'] P) u) ↔
      Function.Injective (LinearMap.lTensor P (u.restrictScalars R')) := by
  set eX :=
    (((TensorProduct.comm A' (A' ⊗[R'] P) X).trans
              (AlgebraTensorModule.cancelBaseChange R' A' A' X P)).restrictScalars
          R').trans
      (TensorProduct.comm R' X P) with
    heX
  set eY :=
    (((TensorProduct.comm A' (A' ⊗[R'] P) Y).trans
              (AlgebraTensorModule.cancelBaseChange R' A' A' Y P)).restrictScalars
          R').trans
      (TensorProduct.comm R' Y P) with
    heY
  have key :
    ∀ z,
      LinearMap.lTensor P (u.restrictScalars R') (eX z) =
        eY (LinearMap.lTensor (A' ⊗[R'] P) u z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul w x =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a p => simp [heX, heY]
      | add w1 w2 h1 h2 => rw [TensorProduct.add_tmul, map_add, map_add, map_add, map_add, h1, h2]
    | add z1 z2 h1 h2 => rw [map_add, map_add, map_add, map_add, h1, h2]
  refine ⟨fun h1 a b hab => ?_, fun h1 a b hab => eX.injective (h1 (by rw [key, key, hab]))⟩
  obtain ⟨a', rfl⟩ := eX.surjective a
  obtain ⟨b', rfl⟩ := eX.surjective b
  rw [key, key] at hab
  exact congrArg eX (h1 (eY.injective hab))

/-- **Stacks 00HI for a square.** Let `R → R'` be a ring map, let `I ⊆ R` be an ideal and put
`I' = IR'`. Let `N` be the base change to `R'` of an `R`-module `M`. If `M/IM` is flat over `R/I`
then `N/I'N` is flat over `R'/I'`.

Indeed `N/I'N = M/IM ⊗_{R/I} R'/I'`, so this is flat base change along `R/I → R'/I'`. -/
private theorem flat_quotient_of_isBaseChange {R R' M N : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module R' N]
    [IsScalarTower R R' N] (I : Ideal R) {j : M →ₗ[R] N} (hj : IsBaseChange R' j)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat (R' ⧸ I.map (algebraMap R R'))
      (N ⧸ (I.map (algebraMap R R') • (⊤ : Submodule R' N))) := by
  have hsR : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have hsR' : Function.Surjective (algebraMap R' (R' ⧸ I.map (algebraMap R R'))) :=
    Ideal.Quotient.mk_surjective
  have h1 : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    flat_of_linearEquiv_of_surjective hsR (TensorProduct.quotTensorEquivQuotSMul M I).symm
  have h2 :
    Module.Flat (R' ⧸ I.map (algebraMap R R'))
      ((R' ⧸ I.map (algebraMap R R')) ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] M)) :=
    Module.Flat.baseChange (R ⧸ I) (R' ⧸ I.map (algebraMap R R')) _
  have e1 :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R' ⧸ I.map (algebraMap R R'))
      (R' ⧸ I.map (algebraMap R R')) M
  have e2 :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R R' (R' ⧸ I.map (algebraMap R R'))
      (R' ⧸ I.map (algebraMap R R')) M
  have e3 :
    (R' ⧸ I.map (algebraMap R R')) ⊗[R'] (R' ⊗[R] M) ≃ₗ[R' ⧸ I.map (algebraMap R R')]
      (R' ⧸ I.map (algebraMap R R')) ⊗[R'] N :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) hj.equiv
  have h3 : Module.Flat (R' ⧸ I.map (algebraMap R R')) ((R' ⧸ I.map (algebraMap R R')) ⊗[R'] N) :=
    Module.Flat.of_linearEquiv (e3.symm.trans (e2.trans e1.symm))
  exact
    flat_of_linearEquiv_of_surjective hsR'
      (TensorProduct.quotTensorEquivQuotSMul N (I.map (algebraMap R R')))

/-- Flatness of `N/I'N` over `R' ⧸ I'` passes to a localization `M'` of `N` at a submonoid `T` of
a ring `B` acting on `N`.

Both `N/I'N` and `M'/I'M'` are base changes to `R' ⧸ I'` of `R'`-modules, so by
`lTensor_baseChange_injective_iff` flatness over `R' ⧸ I'` of either is a statement about
`R'`-tensor products, and there `lTensor_injective_of_isLocalizedModule` applies. -/
theorem flat_quotient_of_isLocalizedModule {R' B N M' : Type*} [CommRing R'] [CommRing B]
    [Algebra R' B] [AddCommGroup N] [Module R' N] [Module B N] [IsScalarTower R' B N]
    [AddCommGroup M'] [Module R' M'] [Module B M'] [IsScalarTower R' B M'] (I' : Ideal R')
    (T : Submonoid B) (g : N →ₗ[B] M') [IsLocalizedModule T g]
    (h : Module.Flat (R' ⧸ I') (N ⧸ (I' • (⊤ : Submodule R' N)))) :
    Module.Flat (R' ⧸ I') (M' ⧸ (I' • (⊤ : Submodule R' M'))) := by
  have hs : Function.Surjective (algebraMap R' (R' ⧸ I')) := Ideal.Quotient.mk_surjective
  have hN : Module.Flat (R' ⧸ I') ((R' ⧸ I') ⊗[R'] N) :=
    flat_of_linearEquiv_of_surjective hs (TensorProduct.quotTensorEquivQuotSMul N I').symm
  have hM' : Module.Flat (R' ⧸ I') ((R' ⧸ I') ⊗[R'] M') := by
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro X Y _ _ _ _ u hu
    let _ : Module R' X := Module.compHom X (algebraMap R' (R' ⧸ I'))
    have _ : IsScalarTower R' (R' ⧸ I') X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let _ : Module R' Y := Module.compHom Y (algebraMap R' (R' ⧸ I'))
    have _ : IsScalarTower R' (R' ⧸ I') Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    rw [lTensor_baseChange_injective_iff]
    have hinj : Function.Injective (LinearMap.lTensor N (u.restrictScalars R')) := by
      rw [← lTensor_baseChange_injective_iff]
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := (R' ⧸ I') ⊗[R'] N) u hu
    exact lTensor_injective_of_isLocalizedModule T g (u.restrictScalars R')
      fun z hz => ⟨1, by rw [hinj (hz.trans (map_zero _).symm), smul_zero]⟩
  exact flat_of_linearEquiv_of_surjective hs (TensorProduct.quotTensorEquivQuotSMul M' I')

/-- **Stacks 00HI for the square, plus flatness of a localization.** The first hypothesis of the
variant 00ML of the local criterion, for the module `M'` over `R'` and the ideal `I' = IR'`:
`M'/I'M'` is flat over `R'/I'`.

The proof is the source's, in two steps, both carried out above for an arbitrary base: with
`B = S ⊗_R R'` and `N = B ⊗_S M` the base change of `M` to `B`,

* `N/I'N = M/IM ⊗_{R/I} R'/I'` is flat over `R'/I'` by flat base change (00HI), because `N` is
  also the base change of `M` to `R'`: this is `flat_quotient_of_isBaseChange`;
* `M'/I'M'` is the localization of `N/I'N` at `T`, and a localization of a module flat over
  `R'/I'` is again flat over `R'/I'`: this is `flat_quotient_of_isLocalizedModule`.

What remains is the geometry of the square: that `B` is an `R'`-algebra
(`Algebra.TensorProduct.rightAlgebra`) compatibly with `R' → S'`, which is `hR'`; that `N` is the
base change of `M` along `R → R'`, which is the identity `(S ⊗_R R') ⊗_S M = R' ⊗_R M`; and that
`M'` is the localization of `N` at `T`, which follows from `hf` by `IsBaseChange.of_comp` and
`isLocalizedModule_iff_isBaseChange`. -/
private theorem flat_quotient_baseChange {R R' S S' M M' : Type*} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra (S ⊗[R] R') S'] [IsScalarTower S (S ⊗[R] R') S']
    (hR' :
      (algebraMap (S ⊗[R] R') S').comp
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom =
        algebraMap R' S')
    (T : Submonoid (S ⊗[R] R')) [IsLocalization T S'] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [AddCommGroup M'] [Module R M'] [Module S M'] [Module R' M']
    [Module S' M'] [IsScalarTower R S M'] [IsScalarTower R R' M'] [IsScalarTower S S' M']
    [IsScalarTower R' S' M'] (I : Ideal R) (f : M →ₗ[S] M') (hf : IsBaseChange S' f)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat (R' ⧸ I.map (algebraMap R R'))
      (M' ⧸ (I.map (algebraMap R R') • (⊤ : Submodule R' M'))) := by
  let _ : Module (S ⊗[R] R') M' := Module.compHom M' (algebraMap (S ⊗[R] R') S')
  have : IsScalarTower (S ⊗[R] R') S' M' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower S (S ⊗[R] R') M' :=
    IsScalarTower.of_algebraMap_smul fun s x => by
      have h :
        (algebraMap S (S ⊗[R] R') s) • x =
          (algebraMap (S ⊗[R] R') S') (algebraMap S (S ⊗[R] R') s) • x :=
        rfl
      rw [h, ← IsScalarTower.algebraMap_apply, algebraMap_smul]
  have : IsScalarTower R' (S ⊗[R] R') M' :=
    IsScalarTower.of_algebraMap_smul fun r' x => by
      have h :
        (algebraMap R' (S ⊗[R] R')) r' • x =
          (algebraMap (S ⊗[R] R') S') (algebraMap R' (S ⊗[R] R') r') • x :=
        rfl
      have h2 :
        (algebraMap (S ⊗[R] R') S') ((algebraMap R' (S ⊗[R] R')) r') = algebraMap R' S' r' :=
        RingHom.congr_fun hR' r'
      rw [h, h2, algebraMap_smul]
  have hjB : IsBaseChange (S ⊗[R] R') (TensorProduct.mk S (S ⊗[R] R') M 1) :=
    TensorProduct.isBaseChange S M (S ⊗[R] R')
  have : IsLocalizedModule T (hjB.lift f) := by
    rw [isLocalizedModule_iff_isBaseChange T S']
    refine hjB.of_comp ?_
    rw [hjB.lift_comp]
    exact hf
  exact
    flat_quotient_of_isLocalizedModule (I.map (algebraMap R R')) T (hjB.lift f)
      (flat_quotient_of_isBaseChange I isBaseChange_one_tmul hflat)

end Square

end Stacks.Flat.LocalCriterion

namespace Module.Flat

/-- **Stacks 00MO.** Let `S ← R → R' → S'`, `S → S'` be a commutative square of ring maps with
`R`, `R'`, `S'` local, `R'` and `S'` Noetherian and `R → R'`, `R' → S'` local, let `I ⊆ R` be a
proper ideal, let `M` be a finite `S`-module and let `f : M → M'` be the base change of `M` to an
`S'`-module. Assume `S'` is a localization of `S ⊗_R R'`. If `M/IM` is flat over `R/I` and the
canonical map `Tor_1^R(M, R/I) → Tor_1^{R'}(M', R'/I')` is zero, then `M'` is flat over `R'`.

By Remark 00M6 the source `Tor_1^R(M, R/I)` is `Ker(I ⊗_R M → R ⊗_R M)` and the target is a
submodule of `I' ⊗_{R'} M'` for `I' = IR'`, so the last hypothesis is that the canonical map
`I ⊗_R M → I' ⊗_{R'} M'`, the unique `R`-linear map with `a ⊗ x ↦ a ⊗ f x`, vanishes on that
kernel; see the module docstring. -/
@[stacks 00MO "`Tor₁` is spelled through Remark 00M6 as `Ker(I ⊗_R M → R ⊗_R M)`, and the
hypothesis that `Tor_1^R(M, R/I) → Tor_1^{R'}(M', R'/I')` is zero as the vanishing on that kernel
of the canonical map `I ⊗_R M → I' ⊗_{R'} M'`. `M'` and `S'` are abstract (`IsBaseChange`,
`IsLocalization`). The unused hypotheses `R` Noetherian, `S` local Noetherian, `R → S` local and
`S → S'` local are dropped; see the module docstring.",
  ega "IV 11.2.5" "case b), local rings",
  ega "IV 11.3.12" "partial"]
public theorem of_flat_quotient_of_tor_one_map_eq_zero {R R' S S' M M' : Type*} [CommRing R]
    [CommRing R'] [CommRing S] [CommRing S'] [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R']
    [IsLocalRing S'] [IsNoetherianRing S'] [Algebra R S] [Algebra R R'] [Algebra S S']
    [Algebra R' S'] [IsLocalHom (algebraMap R R')] [IsLocalHom (algebraMap R' S')]
    [Algebra (S ⊗[R] R') S'] [IsScalarTower S (S ⊗[R] R') S']
    (hR' :
      (algebraMap (S ⊗[R] R') S').comp
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom =
        algebraMap R' S')
    (T : Submonoid (S ⊗[R] R')) [IsLocalization T S'] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M] [AddCommGroup M'] [Module R M'] [Module S M']
    [Module R' M'] [Module S' M'] [IsScalarTower R S M'] [IsScalarTower R R' M']
    [IsScalarTower S S' M'] [IsScalarTower R' S' M'] (I : Ideal R) (hI : I ≠ ⊤) (f : M →ₗ[S] M')
    (hf : IsBaseChange S' f) (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (htor :
      LinearMap.ker (I.subtype.rTensor M) ≤
        LinearMap.ker
          (TensorProduct.lift
            (((TensorProduct.mk R' ↥(I.map (algebraMap R R')) M').restrictScalars₁₂ R R).compl₁₂
              ((Algebra.linearMap R R').restrict (p := I) (q :=
                (I.map (algebraMap R R')).restrictScalars R) fun _ hx => Ideal.mem_map_of_mem _ hx)
              (f.restrictScalars R)))) :
    Module.Flat R' M' := by
  have hfin : Module.Finite S' M' := Module.Finite.equiv hf.equiv
  exact
    Module.Flat.of_rTensor_subtype_injective_of_flat_quotient S' M' (I.map (algebraMap R R'))
      (Stacks.Flat.LocalCriterion.map_ne_top_of_isLocalHom hI)
      (Stacks.Flat.LocalCriterion.rTensor_subtype_injective_of_mem hR' T I _
        (fun _ hx => Ideal.mem_map_of_mem _ hx) f hf hflat htor)
      (Stacks.Flat.LocalCriterion.flat_quotient_baseChange hR' T I f hf hflat)

end Module.Flat

/-!
## 00MO with a larger ideal at the target

Stacks 0471 needs 00MO in a slightly wider form. In the square

```
S  →  S'
↑     ↑
R  →  R'
```

with `S'` a localization of `S ⊗_R R'`, the conclusion of 00MO is read off `Ker(I' ⊗_{R'} M' → M')`
for the *smallest* candidate ideal `I' = IR'`. What `Stacks.Flat.LocalCriterion.key` actually
proves is more: for
**every** ideal `J ⊆ R'` containing the image of `I`, the kernel of `J ⊗_R M → R' ⊗_R M` is
generated as an `R'`-module by the image of `Ker(I ⊗_R M → R ⊗_R M)`, so any map out of
`J ⊗_R M` that kills the latter kills the former. In the source's proof of 0471 this wider form is
the last of the four arrows of the displayed diagram: 00MM applied to
`R_{λ'} → R_{λ'}/I_λ R_{λ'} → R_{λ'}/I_{λ'}`, which passes from the ideal `I_λ R_{λ'}` to the
larger ideal `I_{λ'}`, the inverse image of `I`. It is needed because the colimit that makes the
generators of `Tor_1^{R_λ}(M_λ, R_λ/I_λ)` die at a finite stage is the colimit of the
`Tor_1^{R_{λ'}}(M_{λ'}, R_{λ'}/I_{λ'})`, whose ideals are the inverse images of `I` and not the
images of `I_λ`.

The price of the larger `J` is that the flatness of `M'/JM'` over `R'/J` is no longer a base change
of the flatness of `M/IM` over `R/I`, so it becomes a hypothesis; and locality of `R → R'` is
replaced by the hypothesis `J ≠ ⊤` it was used to produce. For `J = IR'` the two extra hypotheses
are `Stacks.Flat.LocalCriterion.flat_quotient_baseChange` and
`Stacks.Flat.LocalCriterion.map_ne_top_of_isLocalHom`, which is how
00MO itself is recovered.
-/

namespace Stacks.Flat.LocalCriterion

section GeneralTargetIdeal

attribute [local instance] Algebra.TensorProduct.rightAlgebra

end GeneralTargetIdeal

end Stacks.Flat.LocalCriterion

namespace Module.Flat

/-- **Stacks 00MO for an ideal `J` of `R'` containing `IR'`.** Let `S ← R → R' → S'`, `S → S'` be a
commutative square of ring maps with `R'`, `S'` local Noetherian and `R' → S'` local, let `M` be a
finite `S`-module and let `f : M → M'` be the base change of `M` to an `S'`-module. Assume `S'` is
a localization of `S ⊗_R M`. Let `I ⊆ R` be an ideal and let `J ≠ R'` be an ideal of `R'`
containing the image of `I`. If `M/IM` is flat over `R/I`, `M'/JM'` is flat over `R'/J`, and the
canonical map `Tor_1^R(M, R/I) → Tor_1^{R'}(M', R'/J)` is zero, then `M'` is flat over `R'`.

For `J = IR'` this is `Module.Flat.of_flat_quotient_of_tor_one_map_eq_zero`, whose two extra
hypotheses are then automatic. As there, `Tor_1` is spelled through Remark 00M6: the source of the
last hypothesis is `Ker(I ⊗_R M → R ⊗_R M)` and the hypothesis is that the canonical map
`I ⊗_R M → J ⊗_{R'} M'`, the unique `R`-linear map with `a ⊗ x ↦ a ⊗ f x`, vanishes on it. -/
@[ega "IV 11.3.12" "partial"]
public theorem of_flat_quotient_of_tor_one_map_eq_zero_of_mem {R R' S S' M M' : Type*} [CommRing R]
    [CommRing R'] [CommRing S] [CommRing S'] [IsLocalRing R'] [IsNoetherianRing R']
    [IsLocalRing S'] [IsNoetherianRing S'] [Algebra R S] [Algebra R R'] [Algebra S S']
    [Algebra R' S'] [IsLocalHom (algebraMap R' S')] [Algebra (S ⊗[R] R') S']
    [IsScalarTower S (S ⊗[R] R') S']
    (hR' :
      (algebraMap (S ⊗[R] R') S').comp
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom =
        algebraMap R' S')
    (T : Submonoid (S ⊗[R] R')) [IsLocalization T S'] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M] [AddCommGroup M'] [Module R M'] [Module S M']
    [Module R' M'] [Module S' M'] [IsScalarTower R S M'] [IsScalarTower R R' M']
    [IsScalarTower S S' M'] [IsScalarTower R' S' M'] (I : Ideal R) (J : Ideal R')
    (hJ : ∀ a ∈ I, algebraMap R R' a ∈ J) (hJtop : J ≠ ⊤) (f : M →ₗ[S] M') (hf : IsBaseChange S' f)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hflatJ : Module.Flat (R' ⧸ J) (M' ⧸ (J • (⊤ : Submodule R' M'))))
    (htor :
      LinearMap.ker (I.subtype.rTensor M) ≤
        LinearMap.ker
          (TensorProduct.lift
            (((TensorProduct.mk R' ↥J M').restrictScalars₁₂ R R).compl₁₂
              ((Algebra.linearMap R R').restrict (p := I) (q := J.restrictScalars R) hJ)
              (f.restrictScalars R)))) :
    Module.Flat R' M' := by
  have hfin : Module.Finite S' M' := Module.Finite.equiv hf.equiv
  exact
    Module.Flat.of_rTensor_subtype_injective_of_flat_quotient S' M' J hJtop
      (Stacks.Flat.LocalCriterion.rTensor_subtype_injective_of_mem hR' T I J hJ f hf hflat htor)
        hflatJ

end Module.Flat
