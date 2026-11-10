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
import all StacksFrontier.RingTheory.Flat.LocalCriterionVariant.TorVanishing

@[expose] public section

/-!
# Stacks 00ML, and the kernel of `J ⊗_R M → R' ⊗_R M` for Stacks 00MO

Stacks 00ML, `Module.Flat.of_rTensor_subtype_injective_of_flat_quotient`: if `R → S` is a local
homomorphism of Noetherian local rings, `I ⊊ R`, `M` is a finite `S`-module,
`I ⊗_R M → R ⊗_R M` is injective and `M/IM` is flat over `R/I`, then `M` is flat over `R`.

Then the core of the proof of Stacks 00MO, `Stacks.Flat.LocalCriterion.key`: for `J ⊆ R'` an
ideal containing the image of `I`, the kernel of `J ⊗_R M → R' ⊗_R M` is generated as an
`R'`-module by the image of `Ker(I ⊗_R M → R ⊗_R M) = Tor_1^R(M, R/I)`.
-/

universe u v w x
open TensorProduct

namespace Module.Flat

/-- If `p.lTensor W` is injective, `(p ∘ₗ g).lTensor W` killing `x` implies `g.lTensor W` does. -/
private theorem lTensor_eq_zero_of_comp_injective {A W X Y Z : Type*} [CommRing A]
    [AddCommGroup W] [Module A W] [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z] (p : Y →ₗ[A] Z) (g : X →ₗ[A] Y)
    (hp : Function.Injective (p.lTensor W)) {x : W ⊗[A] X} (hx : (p ∘ₗ g).lTensor W x = 0) :
    g.lTensor W x = 0 :=
  hp (by rwa [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp])

/-- **Stacks 00ML** (variant of the local criterion for flatness). Let `R → S` be a local
homomorphism of Noetherian local rings, let `I ≠ R` be an ideal of `R` and let `M` be a finite
`S`-module. If `Tor₁^R(M, R/I) = 0` and `M/IM` is flat over `R/I`, then `M` is flat over `R`.
Here the Tor hypothesis appears in the form of Remark 00M6, as the injectivity of
`I ⊗_R M → R ⊗_R M`, and `M/IM` is `M ⧸ I • ⊤` with its canonical `R ⧸ I`-module structure. -/
@[stacks 00ML "The hypothesis `Tor_1^R(M, R/I) = 0` is stated in the form Remark 00M6 identifies
it with, the injectivity of `I ⊗_R M → R ⊗_R M`; this is the form the source's own second proof
of the lemma assumes, and unlike `Tor_1` it puts `R` and `M` in no common universe. See the
module docstring.", ega "IV 11.3.12" "partial", sga "1 IV 5.6" "(ii)⇒(i), special case"]
public theorem of_rTensor_subtype_injective_of_flat_quotient {R : Type u} (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.Finite S M] (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : Function.Injective (I.subtype.rTensor M))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) : Module.Flat R M := by
  have htor := Stacks.Flatness.LocalCriterionVariant.lift_lsmul_injective_of_rTensor_injective I
    hTor
  -- `IS` is a proper ideal of `S`, since `I ⊆ 𝔪_R` and `R → S` is local.
  have hIS : I.map (algebraMap R S) ≠ ⊤ := by
    have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
    have h1 : I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap]
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal r).mp (hIm hr) (isUnit_of_map_unit (algebraMap R S) r hu)
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ h1))
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  -- `M ⊗_R J` is a finite `S`-module.
  have hfin : Module.Finite S (M ⊗[R] ↥J) := by
    have h1 : Module.Finite S (M ⊗[S] (S ⊗[R] ↥J)) := Module.Finite.tensorProduct S M (S ⊗[R] ↥J)
    exact Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M ↥J)
  -- The Artin–Rees constant of `I` and `J`.
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (M := R) J
  have hsmulTop : ∀ A : Ideal R, A • (⊤ : Submodule R R) = A := fun A => by simp
  -- Every element of the kernel lies in `Iⁿ(M ⊗_R J)` for every `n`.
  have hmem :
    ∀ (n : ℕ) (x : M ⊗[R] ↥J),
      LinearMap.lTensor M J.subtype x = 0 → x ∈ I ^ n • (⊤ : Submodule R (M ⊗[R] ↥J)) := by
    intro n x hx
    set L : Ideal R := I ^ (n + c) with hL
    set rho : ↥J →ₗ[R] (R ⧸ L) := L.mkQ ∘ₗ J.subtype with hrho
    set P : Submodule R (R ⧸ L) := LinearMap.range rho with hP
    have hfact : P.subtype ∘ₗ rho.rangeRestrict = rho := by
      ext y; rfl
    have hinj : Function.Injective (LinearMap.lTensor M P.subtype) :=
      Stacks.Flatness.LocalCriterionVariant.lTensor_subtype_injective_of_quotient_annihilated I
        hflat htor P (n + c)
        (Stacks.Flatness.LocalCriterionVariant.smul_top_quotient_of_smul_top
          (Stacks.Flatness.LocalCriterionVariant.smul_top_quotient_self L) P)
    have hxrho : LinearMap.lTensor M rho.rangeRestrict x = 0 := by
      refine lTensor_eq_zero_of_comp_injective _ _ hinj ?_
      rw [hfact, hrho, LinearMap.lTensor_comp, LinearMap.comp_apply, hx, map_zero]
    have hmemrange :
      x ∈ LinearMap.range (LinearMap.lTensor M (LinearMap.ker rho.rangeRestrict).subtype) := by
      rw [←
        LinearMap.exact_iff.mp
          (_root_.lTensor_exact M (LinearMap.exact_subtype_ker_map rho.rangeRestrict)
            (LinearMap.surjective_rangeRestrict rho))]
      exact hxrho
    refine Stacks.Flatness.LocalCriterionVariant.lTensor_range_subtype_le_smul_top (I ^ n) _ (fun y
      hy => ?_) hmemrange
    have hyL : (y : R) ∈ L := by
      rw [LinearMap.ker_rangeRestrict, hrho, LinearMap.ker_comp, Submodule.ker_mkQ,
        Submodule.mem_comap] at hy
      exact hy
    rw [Submodule.mem_comap]
    have hAR := hc (n + c) (Nat.le_add_left c n)
    simp only [Nat.add_sub_cancel, hsmulTop] at hAR
    have hmem2 : (y : R) ∈ I ^ (n + c) ⊓ (J : Submodule R R) := ⟨hyL, y.2⟩
    rw [hAR] at hmem2
    exact Submodule.smul_mono le_rfl inf_le_right hmem2
  -- Pass from `Iⁿ` over `R` to `(IS)ⁿ` over `S`.
  have hRS :
    ∀ (n : ℕ) (y : M ⊗[R] ↥J),
      y ∈ I ^ n • (⊤ : Submodule R (M ⊗[R] ↥J)) →
        y ∈ (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S (M ⊗[R] ↥J)) := by
    intro n y hy
    refine Submodule.smul_induction_on hy ?_ (fun a b ha hb => Submodule.add_mem _ ha hb)
    intro r hr z _
    rw [← IsScalarTower.algebraMap_smul S r z]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  -- Krull's intersection theorem over the Noetherian local ring `S`.
  have hkrull : (⨅ i : ℕ, (I.map (algebraMap R S)) ^ i • (⊤ : Submodule S (M ⊗[R] ↥J))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I.map (algebraMap R S)) hIS
  have hzero : ∀ x : M ⊗[R] ↥J, LinearMap.lTensor M J.subtype x = 0 → x = 0 := by
    intro x hx
    have hx2 : x ∈ (⨅ i : ℕ, (I.map (algebraMap R S)) ^ i • (⊤ : Submodule S (M ⊗[R] ↥J))) :=
      (Submodule.mem_iInf _).mpr fun i => hRS i x (hmem i x hx)
    rw [hkrull, Submodule.mem_bot] at hx2
    exact hx2
  intro a b hab
  exact sub_eq_zero.mp (hzero (a - b) (by rw [map_sub, hab, sub_self]))

end Module.Flat

/-!
## Stacks 00MO: the criterion after a base change and a localization

The rest of this file proves Stacks 00MO, the variant of 00ML for a commutative square

```
S  →  S'
↑     ↑
R  →  R'
```

with `S'` a localization of `S ⊗_R R'`: if `M` is a finite `S`-module with `M/IM` flat over `R/I`
and the canonical map `Tor_1^R(M, R/I) → Tor_1^{R'}(M', R'/I')` is zero, then the base change `M'`
of `M` to `S'` is flat over `R'`. The two hypotheses of 00ML are supplied for `M'` over `R'` and
the ideal `I' = IR'` by `Stacks.Flat.LocalCriterion.flat_quotient_baseChange` (flat base change,
Lemma 00HI, plus the passage to the localization) and
`Stacks.Flat.LocalCriterion.rTensor_subtype_map_injective_square` (Lemmas 00MM and 00MN, in the
kernel spelling of Remark 00M6).

The content of the second of these is `Stacks.Flat.LocalCriterion.key`: for `J ⊆ R'` an ideal
containing the image of `I`, the kernel of `J ⊗_R M → R' ⊗_R M` — the source's
`Tor_1^R(M, R'/J)` — is generated as an `R'`-module by the image of
`Ker(I ⊗_R M → R ⊗_R M) = Tor_1^R(M, R/I)`. This is Lemma 00MM
for `R → R/I → R'/J`, and it is where the flatness of `M/IM` over `R/I` is used the second time;
Lemma 00MN needs no separate argument in this spelling, because `J ⊗_{R'} (R' ⊗_R M) = J ⊗_R M`
identifies the two `Tor`'s directly. Reading it off a free presentation `Zm → F → M → 0` of `M`
over `R` needs no change-of-rings map on `Tor` and hence no choice of resolution.
-/

namespace Stacks.Flat.LocalCriterion

section Core

variable {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']

/-- The inclusion `I → J` induced by `R → R'`, for `J` an ideal of `R'` containing the image
of the ideal `I` of `R`. -/
private noncomputable def incl (I : Ideal R) (J : Ideal R') (hJ : ∀ a ∈ I, algebraMap R R' a ∈ J) :
    ↥I →ₗ[R] ↥J :=
  (Algebra.linearMap R R').restrict (p := I) (q := J.restrictScalars R) hJ

private theorem incl_apply (I : Ideal R) (J : Ideal R') (hJ : ∀ a ∈ I, algebraMap R R' a ∈ J)
    (a : ↥I) : ((incl I J hJ a : ↥J) : R') = algebraMap R R' (a : R) :=
  rfl

/-- The multiplication `a ⊗ x ↦ a • x` on `I ⊗_R X`. -/
private noncomputable def sm {X : Type*} [AddCommGroup X] [Module R X] (I : Ideal R) :
    ↥I ⊗[R] X →ₗ[R] X :=
  TensorProduct.lift ((LinearMap.lsmul R X).comp I.subtype)

private theorem sm_tmul {X : Type*} [AddCommGroup X] [Module R X] (I : Ideal R) (a : ↥I) (x : X) :
    sm I (a ⊗ₜ[R] x) = (a : R) • x :=
  rfl

private theorem exists_sm_eq {X : Type*} [AddCommGroup X] [Module R X] (I : Ideal R) {y : X}
    (hy : y ∈ I • (⊤ : Submodule R X)) : ∃ θ : ↥I ⊗[R] X, sm I θ = y := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro a ha x _
    exact ⟨(⟨a, ha⟩ : ↥I) ⊗ₜ[R] x, rfl⟩
  · rintro x y ⟨θ, hθ⟩ ⟨ρ, hρ⟩
    exact ⟨θ + ρ, by rw [map_add, hθ, hρ]⟩

/-- The change of the left factor from `J` to `R'`, an `R'`-linear map `J ⊗_R X → R' ⊗_R X`. -/
private noncomputable abbrev sg (J : Ideal R') (X : Type*) [AddCommGroup X] [Module R X] :
    ↥J ⊗[R] X →ₗ[R'] R' ⊗[R] X :=
  AlgebraTensorModule.map J.subtype LinearMap.id

private theorem sg_eq_rTensor (J : Ideal R') (X : Type*) [AddCommGroup X] [Module R X]
    (y : ↥J ⊗[R] X) : sg J X y = LinearMap.rTensor X (J.subtype.restrictScalars R) y := by
  induction y using TensorProduct.inductionOn with
  | tmul a x => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- `lTensor` and `rTensor` commute. -/
private theorem lTensor_rTensor_apply_comm {A B X Y : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : A →ₗ[R] B) (g : X →ₗ[R] Y) (x : A ⊗[R] X) :
    LinearMap.lTensor B g (LinearMap.rTensor X f x) =
      LinearMap.rTensor Y f (LinearMap.lTensor A g x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

private theorem sg_injective (J : Ideal R') (X : Type*) [AddCommGroup X] [Module R X]
    [Module.Flat R X] : Function.Injective (sg (R := R) J X) := by
  have h : ⇑(sg (R := R) J X) = ⇑(LinearMap.rTensor X (J.subtype.restrictScalars R)) :=
    funext (sg_eq_rTensor J X)
  rw [h]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

private theorem sg_tau (I : Ideal R) (J : Ideal R') (hJ : ∀ a ∈ I, algebraMap R R' a ∈ J)
    (X : Type*) [AddCommGroup X] [Module R X] (θ : ↥I ⊗[R] X) :
    sg J X (LinearMap.rTensor X (incl I J hJ) θ) = 1 ⊗ₜ[R] (sm I θ) := by
  induction θ using TensorProduct.inductionOn with
  | tmul a
    x =>
    simp only [LinearMap.rTensor_tmul, AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq,
      Submodule.coe_subtype, incl_apply, sm_tmul]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, TensorProduct.tmul_add]

private theorem atm_map_id_eq_lTensor {W X Y : Type*} [AddCommGroup W] [Module R W] [Module R' W]
    [IsScalarTower R R' W] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (g : X →ₗ[R] Y) (y : W ⊗[R] X) :
    AlgebraTensorModule.map (LinearMap.id : W →ₗ[R'] W) g y = LinearMap.lTensor W g y := by
  induction y using TensorProduct.inductionOn with
  | tmul w x => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- `sg` is natural in the right factor. -/
private theorem sg_natural (J : Ideal R') {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (g : X →ₗ[R] Y) (w : ↥J ⊗[R] X) :
    sg J Y (AlgebraTensorModule.map (LinearMap.id : ↥J →ₗ[R'] ↥J) g w) =
      AlgebraTensorModule.map (LinearMap.id : R' →ₗ[R'] R') g (sg J X w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a x => simp
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Composing `sg` with the reduction `R' → R'/J` kills everything. -/
private theorem mk_sg (J : Ideal R') (X : Type*) [AddCommGroup X] [Module R X] (w : ↥J ⊗[R] X) :
    LinearMap.rTensor X (J.mkQ.restrictScalars R) (sg J X w) = 0 := by
  induction w using TensorProduct.inductionOn with
  | tmul a
    x =>
    simp only [AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq, Submodule.coe_subtype,
      LinearMap.rTensor_tmul, LinearMap.coe_restrictScalars, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 a.2, TensorProduct.zero_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

/-- The element of `I ⊗_R M` attached to `θ : I ⊗_R F` lies in `Ker(I ⊗_R M → R ⊗_R M)`
as soon as `sm I θ` lies in `Ker π`. -/
private theorem rTensor_subtype_lTensor (I : Ideal R) {F M : Type*} [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] (π : F →ₗ[R] M) (θ : ↥I ⊗[R] F) :
    TensorProduct.lid R M (LinearMap.rTensor M I.subtype (LinearMap.lTensor ↥I π θ)) =
      π (sm I θ) := by
  induction θ using TensorProduct.inductionOn with
  | tmul a x => simp [sm_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem lTensor_incl_natural (I : Ideal R) (J : Ideal R')
    (hJ : ∀ a ∈ I, algebraMap R R' a ∈ J) {F M : Type*} [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] (π : F →ₗ[R] M) (θ : ↥I ⊗[R] F) :
    AlgebraTensorModule.map (LinearMap.id : ↥J →ₗ[R'] ↥J) π (LinearMap.rTensor F (incl I J hJ) θ) =
      LinearMap.rTensor M (incl I J hJ) (LinearMap.lTensor ↥I π θ) := by
  induction θ using TensorProduct.inductionOn with
  | tmul a x => simp
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Flatness transfers along an `R`-linear equivalence of `A`-modules, for `A` a quotient of `R`.
-/
private theorem flat_of_linearEquiv_of_surjective {A P Q : Type*} [CommRing A] [Algebra R A]
    (h : Function.Surjective (algebraMap R A)) [AddCommGroup P] [Module R P] [Module A P]
    [IsScalarTower R A P] [AddCommGroup Q] [Module R Q] [Module A Q] [IsScalarTower R A Q]
    (e : P ≃ₗ[R] Q) [Module.Flat A P] : Module.Flat A Q := by
  have hs : ∀ (a : A) (p : P), e (a • p) = a • e p := by
    intro a p
    obtain ⟨r, rfl⟩ := h a
    rw [algebraMap_smul, algebraMap_smul, e.map_smul]
  exact
    Module.Flat.of_linearEquiv
      (({ toFun := e.symm, map_add' := (e.symm).map_add,
          map_smul' := fun a q => by
            have h2 := hs a (e.symm q)
            rw [e.apply_symm_apply] at h2
            exact
              e.injective
                (by
                  rw [e.apply_symm_apply]; exact h2.symm)
          invFun := e, left_inv := e.right_inv, right_inv := e.left_inv } : Q ≃ₗ[A] P))

/-- Right exactness of `W ⊗ -` at the kernel of a map with flat cokernel. -/
private theorem ker_lTensor_eq_range_lTensor_ker_subtype {A X Y P W : Type*} [CommRing A]
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y] [AddCommGroup P] [Module A P]
    [Module.Flat A P] [AddCommGroup W] [Module A W] (u : X →ₗ[A] Y) (p : Y →ₗ[A] P)
    (hp : Function.Surjective p) (hup : Function.Exact u p) :
    LinearMap.ker (u.lTensor W) = LinearMap.range ((LinearMap.ker u).subtype.lTensor W) := by
  set C := LinearMap.ker p with hC
  set u₀ : X →ₗ[A] C := u.codRestrict C (fun x => hup.apply_apply_eq_zero x) with hu₀
  have hcomp : C.subtype ∘ₗ u₀ = u := by
    ext x; rfl
  have hsurj : Function.Surjective u₀ := by
    intro c
    obtain ⟨x, hx⟩ := (hup c.1).mp c.2
    exact ⟨x, Subtype.ext hx⟩
  have hker : LinearMap.ker u₀ ≤ LinearMap.ker u := by
    intro x hx
    have h2 : C.subtype (u₀ x) = 0 := by
      rw [hx]
      simp
    rwa [← LinearMap.comp_apply, hcomp] at h2
  have hinj : Function.Injective (C.subtype.lTensor W) :=
    LinearMap.lTensor_injective_of_exact_of_flat p hp C.subtype C.subtype_injective
      (LinearMap.exact_subtype_ker_map p) W
  have hex := lTensor_exact W (LinearMap.exact_subtype_ker_map u₀) hsurj
  apply le_antisymm
  · intro z hz
    have h0 : (u₀.lTensor W) z = 0 :=
      Module.Flat.lTensor_eq_zero_of_comp_injective _ _ hinj (by rwa [hcomp])
    have hmem : z ∈ LinearMap.range ((LinearMap.ker u₀).subtype.lTensor W) := by
      rwa [← LinearMap.exact_iff.mp hex]
    obtain ⟨y, hy⟩ := hmem
    refine ⟨(Submodule.inclusion hker).lTensor W y, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show (LinearMap.ker u).subtype ∘ₗ Submodule.inclusion hker = (LinearMap.ker u₀).subtype by
        ext; rfl]
    exact hy
  · rw [LinearMap.range_le_iff_comap, eq_top_iff]
    intro z _
    simp only [Submodule.mem_comap, LinearMap.mem_ker, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp]
    have h3 : u ∘ₗ (LinearMap.ker u).subtype = 0 := by
      ext x
      exact x.2
    rw [h3]
    simp

/-- **The flatness step of Stacks 00MM.** -/
private theorem ker_lTensor_le_range_of_flat_quotient {A W Zm F M : Type*} [CommRing A]
    (I : Ideal A) [AddCommGroup W] [Module A W] [Module (A ⧸ I) W] [IsScalarTower A (A ⧸ I) W]
    [AddCommGroup Zm] [Module A Zm] [AddCommGroup F] [Module A F] [AddCommGroup M] [Module A M]
    (ι : Zm →ₗ[A] F) (π : F →ₗ[A] M) (hπ : Function.Surjective π) (hex : Function.Exact ι π)
    [Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M)] :
    LinearMap.ker (ι.lTensor W) ≤
      LinearMap.range (((I • (⊤ : Submodule A F)).comap ι).subtype.lTensor W) := by
  set B := A ⧸ I with hB
  set u : B ⊗[A] Zm →ₗ[B] B ⊗[A] F := AlgebraTensorModule.map LinearMap.id ι with hu
  set p : B ⊗[A] F →ₗ[B] B ⊗[A] M := AlgebraTensorModule.map LinearMap.id π with hp
  have hps : Function.Surjective p := LinearMap.lTensor_surjective B hπ
  have hup : Function.Exact u p := lTensor_exact B hex hπ
  set eZ := AlgebraTensorModule.cancelBaseChange A B B W Zm with heZ
  set eF := AlgebraTensorModule.cancelBaseChange A B B W F with heF
  have hsq : ∀ x : W ⊗[B] (B ⊗[A] Zm), eF (LinearMap.lTensor W u x) = ι.lTensor W (eZ x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul w ν =>
      induction ν using TensorProduct.inductionOn with
      | tmul a z => simp [heZ, heF, hu]
      | add ν₁ ν₂ h1 h2 => rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, h1, h2]
    | add x y h1 h2 => rw [map_add, map_add, map_add, map_add, h1, h2]
  intro ζ hζ
  have h1 : eZ.symm ζ ∈ LinearMap.ker (LinearMap.lTensor W u) :=
    LinearMap.mem_ker.mpr <| eF.injective <| by
      rw [hsq, eZ.apply_symm_apply, map_zero]
      exact hζ
  rw [ker_lTensor_eq_range_lTensor_ker_subtype u p hps hup] at h1
  obtain ⟨y, hy⟩ := h1
  have hgoal :
    ∀ y : W ⊗[B] (LinearMap.ker u),
      eZ ((LinearMap.ker u).subtype.lTensor W y) ∈
        LinearMap.range (((I • (⊤ : Submodule A F)).comap ι).subtype.lTensor W) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul w
      ν =>
      obtain ⟨z, hz⟩ := TensorProduct.mk_surjective A Zm B Ideal.Quotient.mk_surjective ν.1
      have hz0 : ι z ∈ I • (⊤ : Submodule A F) := by
        have hzν : (1 : B) ⊗ₜ[A] z = (ν : B ⊗[A] Zm) := hz
        have h2 : u ((1 : B) ⊗ₜ[A] z) = 0 := by
          rw [hzν]; exact ν.2
        have h3 : (1 : B) ⊗ₜ[A] ι z = 0 := h2
        have h4 := congrArg (TensorProduct.quotTensorEquivQuotSMul F I) h3
        rw [map_zero] at h4
        exact
          (Submodule.Quotient.mk_eq_zero _).mp
            ((TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I (ι z)).symm.trans h4)
      refine ⟨w ⊗ₜ[A] ⟨z, hz0⟩, ?_⟩
      simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype, heZ]
      rw [← hz]
      simp
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
  have h5 := hgoal y
  rwa [hy, eZ.apply_symm_apply] at h5

/-- **Stacks 00MM in the kernel spelling of Remark 00M6.** Let `R → R'` be a ring map, let
`I ⊆ R` be an ideal and let `J ⊆ R'` be an ideal containing the image of `I`. Let `M` be an
`R`-module with `M/IM` flat over `R/I`, and let `Z → F → M → 0` be an exact sequence of
`R`-modules with `F` flat and `F → M` surjective. Then every `R'`-linear map out of `J ⊗_R M`
which kills the image of `Ker(I ⊗_R M → R ⊗_R M)` also kills `Ker(J ⊗_R M → R' ⊗_R M)`.

In other words `Ker(J ⊗_R M → R' ⊗_R M)`, which is the `Tor_1^R(M, R'/J)` of the source, is
generated as an `R'`-module by the image of `Tor_1^R(M, R/I) = Ker(I ⊗_R M → R ⊗_R M)`. -/
private theorem key_aux {M Q F Zm : Type*} [AddCommGroup M] [Module R M] [AddCommGroup Q]
    [Module R' Q] [AddCommGroup F] [Module R F] [Module.Flat R F] [AddCommGroup Zm] [Module R Zm]
    (I : Ideal R) (J : Ideal R') (hJ : ∀ a ∈ I, algebraMap R R' a ∈ J) (ι : Zm →ₗ[R] F)
    (π : F →ₗ[R] M) (hπ : Function.Surjective π) (hex : Function.Exact ι π)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)] (ψ : ↥J ⊗[R] M →ₗ[R'] Q)
    (hψ :
      ∀ x : ↥I ⊗[R] M,
        LinearMap.rTensor M I.subtype x = 0 → ψ (LinearMap.rTensor M (incl I J hJ) x) = 0)
    (z : ↥J ⊗[R] M) (hz : sg J M z = 0) : ψ z = 0 := by
  classical
  let _ : Algebra (R ⧸ I) (R' ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hJ
  have _ : IsScalarTower R (R ⧸ I) (R' ⧸ J) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- `PF : J ⊗_R F → J ⊗_R M`, an `R'`-linear surjection.
  set PF := AlgebraTensorModule.map (LinearMap.id : ↥J →ₗ[R'] ↥J) π with hPF
  have hPFsurj : Function.Surjective PF := by
    intro y
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective (R := R) ↥J hπ y
    exact
      ⟨x, by
        rw [hPF, atm_map_id_eq_lTensor]; exact hx⟩
  obtain ⟨η, hη⟩ := hPFsurj z
  -- it suffices to show that `η` is killed by `ψ ∘ PF`
  suffices hgoal : ψ (PF η) = 0 by rwa [hη] at hgoal
  -- `σ_F η` dies in `R' ⊗_R M`, hence comes from `R' ⊗_R Zm`
  have hsq : sg J M (PF η) = AlgebraTensorModule.map (LinearMap.id : R' →ₗ[R'] R') π (sg J F η) :=
    sg_natural J π η
  have hstep1 : LinearMap.lTensor R' π (sg J F η) = 0 := by
    rw [← atm_map_id_eq_lTensor (R' := R') π (sg J F η), ← hsq, hη]
    exact hz
  obtain ⟨ζ, hζ⟩ := (lTensor_exact R' hex hπ (sg J F η)).mp hstep1
  -- reduce `ζ` modulo `J`; it lands in the kernel of `(R'/J) ⊗_R Zm → (R'/J) ⊗_R F`
  have hzbar :
    LinearMap.rTensor Zm (J.mkQ.restrictScalars R) ζ ∈ LinearMap.ker (ι.lTensor (R' ⧸ J)) := by
    change LinearMap.lTensor (R' ⧸ J) ι _ = 0
    rw [lTensor_rTensor_apply_comm, hζ, mk_sg]
  -- Stacks 00MM: the class of `ζ` comes from `Zm ∩ IF`
  obtain ⟨ν, hν⟩ := ker_lTensor_le_range_of_flat_quotient (W := R' ⧸ J) I ι π hπ hex hzbar
  obtain ⟨ν', hν'⟩ :=
    LinearMap.rTensor_surjective (R := R) ↥((I • (⊤ : Submodule R F)).comap ι) (g :=
      J.mkQ.restrictScalars R) J.mkQ_surjective ν
  -- the difference between `ζ` and its lift comes from `J ⊗_R Zm`
  obtain ⟨δ₀, hδ₀⟩ :=
    (rTensor_exact (f := J.subtype.restrictScalars R) (g := J.mkQ.restrictScalars R) Zm
          (LinearMap.exact_subtype_mkQ J) J.mkQ_surjective
          (ζ - LinearMap.lTensor R' ((I • (⊤ : Submodule R F)).comap ι).subtype ν')).mp
      (by rw [map_sub, ← lTensor_rTensor_apply_comm, hν', hν, sub_self])
  -- the two halves of `σ_F η`, each visibly killed by `ψ ∘ PF`
  have claimA :
    ∀ x : R' ⊗[R] ↥((I • (⊤ : Submodule R F)).comap ι),
      ∃ w : ↥J ⊗[R] F,
        ψ (PF w) = 0 ∧
          sg J F w =
            LinearMap.lTensor R' (ι ∘ₗ ((I • (⊤ : Submodule R F)).comap ι).subtype) x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r'
      z₀ =>
      have hy1 : ι (((I • (⊤ : Submodule R F)).comap ι).subtype z₀) ∈ I • (⊤ : Submodule R F) :=
        z₀.2
      have hy2 : π (ι (((I • (⊤ : Submodule R F)).comap ι).subtype z₀)) = 0 :=
        hex.apply_apply_eq_zero _
      obtain ⟨θ, hθ⟩ := exists_sm_eq I hy1
      refine ⟨r' • LinearMap.rTensor F (incl I J hJ) θ, ?_, ?_⟩
      · rw [map_smul, map_smul, hPF, lTensor_incl_natural, hψ, smul_zero]
        apply (TensorProduct.lid R M).injective
        rw [map_zero, rTensor_subtype_lTensor, hθ, hy2]
      · rw [map_smul, sg_tau, hθ, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
          LinearMap.lTensor_tmul, LinearMap.comp_apply]
    | add a b ha hb =>
      obtain ⟨w₁, h₁, h₁'⟩ := ha
      obtain ⟨w₂, h₂, h₂'⟩ := hb
      exact
        ⟨w₁ + w₂, by rw [map_add, map_add, h₁, h₂, add_zero], by rw [map_add, h₁', h₂', map_add]⟩
  have claimB :
    ∀ d : ↥J ⊗[R] Zm,
      ∃ w : ↥J ⊗[R] F,
        ψ (PF w) = 0 ∧
          sg J F w =
            LinearMap.lTensor R' ι (LinearMap.rTensor Zm (J.subtype.restrictScalars R) d) := by
    intro d
    refine ⟨AlgebraTensorModule.map (LinearMap.id : ↥J →ₗ[R'] ↥J) ι d, ?_, ?_⟩
    · have h0 : PF (AlgebraTensorModule.map (LinearMap.id : ↥J →ₗ[R'] ↥J) ι d) = 0 := by
        induction d using TensorProduct.inductionOn with
        | tmul a zz =>
          rw [AlgebraTensorModule.map_tmul, hPF, AlgebraTensorModule.map_tmul]
          rw [show π (ι zz) = 0 from hex.apply_apply_eq_zero zz]
          simp
        | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
      rw [h0, map_zero]
    · rw [sg_natural J ι d, atm_map_id_eq_lTensor]
      exact congrArg _ (sg_eq_rTensor J Zm d)
  obtain ⟨w₁, hw₁, hw₁'⟩ := claimA ν'
  obtain ⟨w₂, hw₂, hw₂'⟩ := claimB δ₀
  have hfin : sg J F (w₁ + w₂) = sg J F η := by
    rw [map_add, hw₁', hw₂', ← hζ,
      show
        ζ =
          LinearMap.lTensor R' ((I • (⊤ : Submodule R F)).comap ι).subtype ν' +
            LinearMap.rTensor Zm (J.subtype.restrictScalars R) δ₀
        from by
        rw [hδ₀]; abel,
      map_add]
    congr 1
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  rw [← sg_injective J F hfin, map_add, map_add, hw₁, hw₂, add_zero]

/-- The wrapper of `key_aux` for the canonical free presentation of `M` over `R`. -/
private theorem key {M Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R' Q]
    (I : Ideal R) (J : Ideal R') (hJ : ∀ a ∈ I, algebraMap R R' a ∈ J)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) (ψ : ↥J ⊗[R] M →ₗ[R'] Q)
    (hψ :
      ∀ x : ↥I ⊗[R] M,
        LinearMap.rTensor M I.subtype x = 0 → ψ (LinearMap.rTensor M (incl I J hJ) x) = 0)
    (z : ↥J ⊗[R] M) (hz : sg J M z = 0) : ψ z = 0 := by
  have _ : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    flat_of_linearEquiv_of_surjective Ideal.Quotient.mk_surjective
      (TensorProduct.quotTensorEquivQuotSMul M I).symm
  exact
    key_aux I J hJ (LinearMap.ker (Finsupp.linearCombination R (id : M → M))).subtype
      (Finsupp.linearCombination R (id : M → M)) (Finsupp.linearCombination_id_surjective R M)
      (LinearMap.exact_subtype_ker_map _) ψ hψ z hz

section BaseChange

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module R' N]
  [IsScalarTower R R' N]

/-- For `N` the base change of `M` to `R'` and `P` an `R'`-module, the canonical `R'`-linear
identification `P ⊗_R M = N ⊗_{R'} P`. -/
private noncomputable def bc {j : M →ₗ[R] N} (hj : IsBaseChange R' j) (P : Type*) [AddCommGroup P]
    [Module R P] [Module R' P] [IsScalarTower R R' P] : P ⊗[R] M ≃ₗ[R'] N ⊗[R'] P :=
  ((AlgebraTensorModule.cancelBaseChange R R' R' P M).symm.trans
        (TensorProduct.congr (LinearEquiv.refl R' P) hj.equiv)).trans
    (TensorProduct.comm R' P N)

private theorem bc_tmul {j : M →ₗ[R] N} (hj : IsBaseChange R' j) (P : Type*) [AddCommGroup P]
    [Module R P] [Module R' P] [IsScalarTower R R' P] (a : P) (m : M) :
    bc hj P (a ⊗ₜ[R] m) = j m ⊗ₜ[R'] a := by simp [bc, IsBaseChange.equiv_tmul]

private theorem bc_sg {j : M →ₗ[R] N} (hj : IsBaseChange R' j) (J : Ideal R') (v : ↥J ⊗[R] M) :
    LinearMap.lTensor N J.subtype (bc hj ↥J v) = bc hj R' (sg J M v) := by
  induction v using TensorProduct.inductionOn with
  | tmul a m => simp [bc_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end BaseChange

end Core

end Stacks.Flat.LocalCriterion
