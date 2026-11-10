module

public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.TraceElement
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingBaseChange.Independence
public import StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatAlgebraBaseChange
public import StacksFrontier.RingTheory.TateMap.ChartBaseChange

/-!
# The relative dualizing module along a chart base change

Let `A → B` be a flat quasi-finite map of Noetherian rings and let `D` be a chart base change
from `A → B` to `A' → B'`: `B'` is the localization of `A' ⊗_A B` away from one element, with
`A'` Noetherian. Then the relative dualizing module commutes with this base change: there is a
canonical isomorphism `B' ⊗_B ω_{B/A} ≅ ω_{B'/A'}`, and it carries `1 ⊗ τ_{B/A}` to `τ_{B'/A'}`.
This is the base change map of Stacks, Section 0FKB, on affine charts.

## Main definitions

* `Stacks.TateMap.omegaBaseChange D F G`: the isomorphism `B' ⊗_B ω_{B/A} ≅ ω_{B'/A'}`, for
  finite-open factorizations `F` of `A → B` and `G` of `A' → B'`.

## Main results

* `Stacks.TateMap.omegaBaseChange_traceElement`: it carries `1 ⊗ τ_{B/A}` to `τ_{B'/A'}`.
* `Stacks.TateMap.omegaBaseChange_natural_right`, `Stacks.TateMap.omegaBaseChange_natural_left`:
  it does not depend on the finite-open factorizations, up to the canonical comparisons.

## Implementation notes

The isomorphism is the composite of the base change isomorphism of Tag 0BVF along `A → A'`,
which identifies `(A' ⊗_A B) ⊗_B ω_{B/A}` with the dualizing module of the base-changed
factorization, and the localization isomorphism of Tag 0BT2, part (2), along
`A' ⊗_A B → B'`. The trace element is preserved by both (Tag 0BT9), and so is the
independence of the factorization (Tags 0BVC and 0BT2).

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
* [Stacks Project, Tag 0BVF](https://stacks.math.columbia.edu/tag/0BVF)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BT9](https://stacks.math.columbia.edu/tag/0BT9)
-/

@[expose] public noncomputable section

open scoped TensorProduct

open Stacks.Discriminant

universe u

namespace Stacks.TateMap

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B']

attribute [local instance] algebraDualModule

/-- The finite-open factorization of `A' → B'` induced by one of `A → B` along a chart base
change: the intermediate algebra is `A' ⊗_A C`, mapping to `B'` through `A' ⊗_A B`. -/
def omegaFactorization (D : ChartBaseChange A B A' B')
    (F : FiniteOpenFactorization.{u, u, u} A B) : FiniteOpenFactorization.{u, u, u} A' B' :=
  letI := D.algebra
  haveI : IsScalarTower A' (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_left x).symm)
  haveI := D.isLocalization
  locFact D.elt (FiniteOpenFactorization.baseChange F A')

/-- The pure tensor `a ⊗ c` of `A' ⊗_A C`, as an element of the intermediate algebra of the
induced factorization. -/
def omegaTmul (D : ChartBaseChange A B A' B') (F : FiniteOpenFactorization.{u, u, u} A B)
    (a : A') (c : F.middle) : (omegaFactorization D F).middle :=
  a ⊗ₜ[A] c

/-- The structure map of the induced factorization on a pure tensor. -/
theorem algebraMap_omegaFactorization (D : ChartBaseChange A B A' B')
    (F : FiniteOpenFactorization.{u, u, u} A B) (a : A') (c : F.middle) :
    algebraMap (omegaFactorization D F).middle B' (omegaTmul D F a c) =
      algebraMap A' B' a * algebraMap B B' (algebraMap F.middle B c) := by
  let := D.algebra
  change algebraMap (A' ⊗[A] B) B' (a ⊗ₜ[A] algebraMap F.middle B c) = _
  rw [← D.base_left, ← D.base_right, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul]

/-- The scalar extension `A' ⊗_A C → A'` of a functional `φ : C → A`, as a functional on the
intermediate algebra of the induced factorization. -/
def omegaDual (D : ChartBaseChange A B A' B') (F : FiniteOpenFactorization.{u, u, u} A B)
    (φ : Module.Dual A F.middle) : Module.Dual A' (omegaFactorization D F).middle :=
  φ.baseChange A'

/-- The extended functional on a pure tensor. -/
theorem omegaDual_tmul (D : ChartBaseChange A B A' B') (F : FiniteOpenFactorization.{u, u, u} A B)
    (φ : Module.Dual A F.middle) (a : A') (c : F.middle) :
    omegaDual D F φ (omegaTmul D F a c) = φ c • a :=
  rfl

/-- Two `B'`-linear maps out of `B' ⊗_B ω_{B/A}` agree once they agree on the tensors
`1 ⊗ (φ ⊗ b)`. -/
theorem linearMap_ext_one_tmul_tmul {M : Type*} [AddCommGroup M] [Module B' M]
    (F : FiniteOpenFactorization.{u, u, u} A B)
    {f g : B' ⊗[B] dualizingModule F →ₗ[B'] M}
    (h : ∀ (φ : Module.Dual A F.middle) (b : B),
      f (1 ⊗ₜ dualizingModule.tmul F φ b) = g (1 ⊗ₜ dualizingModule.tmul F φ b)) :
    f = g := by
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a m => ?_
  rw [show a ⊗ₜ[B] m = a • ((1 : B') ⊗ₜ[B] m) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul]
  congr 1
  induction m using dualizingModule.induction_on F with
  | tmul φ b => exact h φ b
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

section OmegaBaseChange

variable [IsNoetherianRing A] [IsNoetherianRing A'] [Module.Flat A B]

/-- **The base change isomorphism `B' ⊗_B ω_{B/A} ≅ ω_{B'/A'}`** along a chart base change,
computed with finite-open factorizations `F` of `A → B` and `G` of `A' → B'`: the base change
isomorphism of Tag 0BVF along `A → A'`, followed by localization in the target (Tag 0BT2). -/
def omegaBaseChange (D : ChartBaseChange A B A' B')
    (F : FiniteOpenFactorization.{u, u, u} A B) (G : FiniteOpenFactorization.{u, u, u} A' B') :
    B' ⊗[B] dualizingModule F ≃ₗ[B'] dualizingModule G := by
  letI := D.algebra
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower B (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_right x).symm)
  haveI : IsScalarTower A' (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_left x).symm)
  haveI := D.isLocalization
  haveI : Algebra.FiniteType A B :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F).1
  haveI : Algebra.QuasiFinite A B :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F).2
  haveI : IsNoetherianRing (A' ⊗[A] B) := Algebra.FiniteType.isNoetherianRing A' _
  let F₁ := FiniteOpenFactorization.baseChange F A'
  letI : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B (A' ⊗[A] B))
  haveI : IsScalarTower B (A' ⊗[A] B) (dualizingModule F₁) :=
    IsScalarTower.of_compHom B (A' ⊗[A] B) _
  let e₂ : (A' ⊗[A] B) ⊗[B] dualizingModule F ≃ₗ[A' ⊗[A] B] dualizingModule F₁ :=
    LinearEquiv.ofBijective (dualizingModule.baseChangeLinearMap F A')
      (dualizingModule.baseChangeLinearMap_bijective F A')
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange B (A' ⊗[A] B) B' B'
      (dualizingModule F)).symm ≪≫ₗ e₂.baseChange (A' ⊗[A] B) B' _ _ ≪≫ₗ
    localizedModule_dualizingModule_equiv D.elt F₁ G (targetLocalizationMap D.elt F₁)
      (targetLocalizationMap_isLocalized D.elt F₁)

/-- The base change isomorphism carries `1 ⊗ τ_{B/A}` to `τ_{B'/A'}` (Tag 0BT9). -/
theorem omegaBaseChange_traceElement (D : ChartBaseChange A B A' B')
    [IsNoetherianRing B] [Algebra.QuasiFinite A B] [IsNoetherianRing B'] [Module.Flat A' B']
    [Algebra.QuasiFinite A' B']
    (F : FiniteOpenFactorization.{u, u, u} A B) (G : FiniteOpenFactorization.{u, u, u} A' B') :
    omegaBaseChange D F G (1 ⊗ₜ dualizingModule.traceElement F) =
      dualizingModule.traceElement G := by
  let := D.algebra
  let : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_right x).symm)
  have : IsScalarTower A' (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_left x).symm)
  have := D.isLocalization
  have : Algebra.FiniteType A B :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F).1
  have : IsNoetherianRing (A' ⊗[A] B) := Algebra.FiniteType.isNoetherianRing A' _
  let F₁ := FiniteOpenFactorization.baseChange F A'
  let : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B (A' ⊗[A] B))
  have : IsScalarTower B (A' ⊗[A] B) (dualizingModule F₁) :=
    IsScalarTower.of_compHom B (A' ⊗[A] B) _
  have h₁ : dualizingModule.baseChange F A' (dualizingModule.traceElement F) =
      dualizingModule.traceElement F₁ :=
    eq_traceElement_of_isTraceElement F₁
      (isTraceElement_baseChange F A' _ (isTraceElement_traceElement F))
  have h₂ := eq_traceElement_of_isTraceElement G
      (isTraceElement_localization (M := B' ⊗[A' ⊗[A] B] dualizingModule F₁) D.elt F₁ G
        (targetLocalizationMap D.elt F₁)
        (targetLocalizationMap_isLocalized D.elt F₁) (isTraceElement_traceElement F₁))
  have h₀ : dualizingModule.baseChangeLinearMap F A' (1 ⊗ₜ dualizingModule.traceElement F) =
      dualizingModule.baseChange F A' (dualizingModule.traceElement F) :=
    dualizingModule.baseChangeLinearMap_one_tmul F A' _
  rw [← h₂, ← h₁, ← h₀]
  rfl

/-- The base change isomorphism is natural in the factorization of `A' → B'`. -/
theorem omegaBaseChange_natural_right (D : ChartBaseChange A B A' B')
    (F : FiniteOpenFactorization.{u, u, u} A B) (G G' : FiniteOpenFactorization.{u, u, u} A' B')
    (x : B' ⊗[B] dualizingModule F) :
    dualizingModuleEquiv G G' (omegaBaseChange D F G x) = omegaBaseChange D F G' x := by
  let := D.algebra
  let : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_right x).symm)
  have : IsScalarTower A' (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_left x).symm)
  have := D.isLocalization
  have : Algebra.FiniteType A B :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F).1
  have : Algebra.QuasiFinite A B :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F).2
  have : IsNoetherianRing (A' ⊗[A] B) := Algebra.FiniteType.isNoetherianRing A' _
  let F₁ := FiniteOpenFactorization.baseChange F A'
  let : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B (A' ⊗[A] B))
  have : IsScalarTower B (A' ⊗[A] B) (dualizingModule F₁) :=
    IsScalarTower.of_compHom B (A' ⊗[A] B) _
  exact localizedModule_dualizingModule_equiv_natural (M := B' ⊗[A' ⊗[A] B] dualizingModule F₁)
    D.elt F₁ G G' (targetLocalizationMap D.elt F₁) (targetLocalizationMap_isLocalized D.elt F₁) _

/-- The base change isomorphism is natural in the factorization of `A → B`, on `1 ⊗ m`. -/
theorem omegaBaseChange_one_tmul_natural_left (D : ChartBaseChange A B A' B')
    (F F' : FiniteOpenFactorization.{u, u, u} A B) (G : FiniteOpenFactorization.{u, u, u} A' B')
    (m : dualizingModule F) :
    omegaBaseChange D F' G (1 ⊗ₜ dualizingModuleEquiv F F' m) =
      omegaBaseChange D F G (1 ⊗ₜ m) := by
  let := D.algebra
  let : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_right x).symm)
  have : IsScalarTower A' (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_left x).symm)
  have := D.isLocalization
  have : Algebra.FiniteType A B :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F).1
  have : Algebra.QuasiFinite A B :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F).2
  have : IsNoetherianRing (A' ⊗[A] B) := Algebra.FiniteType.isNoetherianRing A' _
  let F₁ := FiniteOpenFactorization.baseChange F A'
  let F₁' := FiniteOpenFactorization.baseChange F' A'
  let : Module B (dualizingModule F₁') := Module.compHom _ (algebraMap B (A' ⊗[A] B))
  have : IsScalarTower B (A' ⊗[A] B) (dualizingModule F₁') :=
    IsScalarTower.of_compHom B (A' ⊗[A] B) _
  let : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B (A' ⊗[A] B))
  have : IsScalarTower B (A' ⊗[A] B) (dualizingModule F₁) :=
    IsScalarTower.of_compHom B (A' ⊗[A] B) _
  have h₀ : ∀ (H : FiniteOpenFactorization.{u, u, u} A B) (n : dualizingModule H),
      omegaBaseChange D H G (1 ⊗ₜ n) =
        localizedModule_dualizingModule_equiv (M := B' ⊗[A' ⊗[A] B] dualizingModule
            (FiniteOpenFactorization.baseChange H A')) D.elt
          (FiniteOpenFactorization.baseChange H A') G
          (targetLocalizationMap D.elt (FiniteOpenFactorization.baseChange H A'))
          (targetLocalizationMap_isLocalized D.elt (FiniteOpenFactorization.baseChange H A'))
          (targetLocalizationMap D.elt (FiniteOpenFactorization.baseChange H A')
            (dualizingModule.baseChange H A' n)) := by
    intro H n
    rw [← dualizingModule.baseChangeLinearMap_one_tmul H A' n]
    rfl
  rw [h₀, h₀, ← dualizingModule.baseChange_congr F F' A' m]
  have key := localizedModule_dualizingModule_equiv_natural_in_source
    (M := B' ⊗[A' ⊗[A] B] dualizingModule F₁) (M' := B' ⊗[A' ⊗[A] B] dualizingModule F₁')
    D.elt F₁ F₁' G G (targetLocalizationMap D.elt F₁) (targetLocalizationMap_isLocalized D.elt F₁)
    (targetLocalizationMap D.elt F₁') (targetLocalizationMap_isLocalized D.elt F₁')
    ((dualizingModuleEquiv F₁ F₁').toLinearMap.baseChange B')
    (fun n ↦ rfl) (targetLocalizationMap D.elt F₁ (dualizingModule.baseChange F A' m))
  rw [dualizingModuleEquiv_refl] at key
  exact key.symm

/-- **The pure-tensor formula.** On `1 ⊗ (φ ⊗ b)` the base change isomorphism is the tensor
`φ_{A'} ⊗ b` of the induced factorization, read in any factorization of `A' → B'`. -/
theorem omegaBaseChange_one_tmul_tmul (D : ChartBaseChange A B A' B')
    (F : FiniteOpenFactorization.{u, u, u} A B) (G : FiniteOpenFactorization.{u, u, u} A' B')
    (φ : Module.Dual A F.middle) (b : B) :
    omegaBaseChange D F G (1 ⊗ₜ dualizingModule.tmul F φ b) =
      dualizingModuleEquiv (omegaFactorization D F) G
        (dualizingModule.tmul (omegaFactorization D F) (omegaDual D F φ) (algebraMap B B' b)) := by
  let := D.algebra
  let : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_right x).symm)
  have : IsScalarTower A' (A' ⊗[A] B) B' := IsScalarTower.of_algebraMap_eq' (by
    ext x; exact (D.base_left x).symm)
  have := D.isLocalization
  have : Algebra.FiniteType A B :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F).1
  have : Algebra.QuasiFinite A B :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F).2
  have : IsNoetherianRing (A' ⊗[A] B) := Algebra.FiniteType.isNoetherianRing A' _
  let F₁ := FiniteOpenFactorization.baseChange F A'
  let : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B (A' ⊗[A] B))
  have : IsScalarTower B (A' ⊗[A] B) (dualizingModule F₁) :=
    IsScalarTower.of_compHom B (A' ⊗[A] B) _
  have h₀ : omegaBaseChange D F G (1 ⊗ₜ dualizingModule.tmul F φ b) =
      localizedModule_dualizingModule_equiv (M := B' ⊗[A' ⊗[A] B] dualizingModule F₁) D.elt F₁ G
        (targetLocalizationMap D.elt F₁) (targetLocalizationMap_isLocalized D.elt F₁)
        (targetLocalizationMap D.elt F₁
          (dualizingModule.baseChange F A' (dualizingModule.tmul F φ b))) := by
    rw [← dualizingModule.baseChangeLinearMap_one_tmul F A']
    rfl
  rw [h₀, localizedModule_dualizingModule_equiv_apply]
  rw [show dualizingModule.baseChange F A' (dualizingModule.tmul F φ b) =
    dualizingModule.tmul F₁ (φ.baseChange A') (1 ⊗ₜ[A] b) from rfl]
  have h₁ := dualizingTensorLocalizationEquiv_tmul (Bg := B') D.elt F₁ (φ.baseChange A')
    ((1 : A') ⊗ₜ[A] b)
  rw [D.base_right] at h₁
  exact congrArg (dualizingModuleEquiv (locFact D.elt F₁) G) h₁

/-- The base change isomorphism is natural in the factorization of `A → B`. -/
theorem omegaBaseChange_natural_left (D : ChartBaseChange A B A' B')
    (F F' : FiniteOpenFactorization.{u, u, u} A B) (G : FiniteOpenFactorization.{u, u, u} A' B') :
    (dualizingModuleEquiv F F').baseChange B B' _ _ ≪≫ₗ omegaBaseChange D F' G =
      omegaBaseChange D F G := by
  refine LinearEquiv.toLinearMap_injective (linearMap_ext_one_tmul_tmul F fun φ b ↦ ?_)
  exact omegaBaseChange_one_tmul_natural_left D F F' G _

/-- For two finite-open factorizations of `A' → B'` with isomorphic intermediate algebras and
compatible structure maps, a pure tensor of one and the pure tensor of the restricted functional
in the other have the same image in any third factorization. -/
private theorem dualizingModuleEquiv_tmul_of_algebraMap_eq
    (H H' : FiniteOpenFactorization.{u, u, u} A' B') (e : H'.middle ≃ₐ[A'] H.middle)
    (he : ∀ c, algebraMap H.middle B' (e c) = algebraMap H'.middle B' c)
    (G : FiniteOpenFactorization.{u, u, u} A' B') (ψ : Module.Dual A' H.middle) (x : B') :
    dualizingModuleEquiv H G (dualizingModule.tmul H ψ x) =
      dualizingModuleEquiv H' G (dualizingModule.tmul H' (ψ.comp e.toLinearMap) x) := by
  rw [← dualizingModuleEquiv_trans H H' G, LinearEquiv.trans_apply,
    comparison_restrict_of_equiv H' H e he]

/-- **Independence of the chart base change datum.** The base change isomorphism depends only
on the square, not on the algebra structure or the localizing element of the datum. -/
theorem omegaBaseChange_congr (D D' : ChartBaseChange A B A' B')
    (F : FiniteOpenFactorization.{u, u, u} A B) (G : FiniteOpenFactorization.{u, u, u} A' B') :
    omegaBaseChange D F G = omegaBaseChange D' F G := by
  refine LinearEquiv.toLinearMap_injective (linearMap_ext_one_tmul_tmul F fun φ b ↦ ?_)
  change omegaBaseChange D F G _ = omegaBaseChange D' F G _
  rw [omegaBaseChange_one_tmul_tmul, omegaBaseChange_one_tmul_tmul]
  refine dualizingModuleEquiv_tmul_of_algebraMap_eq (omegaFactorization D F)
    (omegaFactorization D' F) AlgEquiv.refl (fun c ↦ ?_) G _ _
  change algebraMap (omegaFactorization D F).middle B' c =
    algebraMap (omegaFactorization D' F).middle B' c
  induction c using TensorProduct.inductionOn with
  | tmul a c =>
      change algebraMap (omegaFactorization D F).middle B' (omegaTmul D F a c) =
        algebraMap (omegaFactorization D' F).middle B' (omegaTmul D' F a c)
      rw [algebraMap_omegaFactorization, algebraMap_omegaFactorization]
  | add x y hx hy =>
      exact (RingHom.map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
        (RingHom.map_add _ x y).symm)

end OmegaBaseChange

section Functoriality

/-- **The identity square.** For a chart base change from `A → B` to itself, the base change
isomorphism is `B ⊗_B ω_{B/A} ≅ ω_{B/A}` followed by the canonical comparison. -/
theorem omegaBaseChange_refl {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] (D : ChartBaseChange A B A B)
    (F G : FiniteOpenFactorization.{u, u, u} A B) :
    omegaBaseChange D F G =
      TensorProduct.lid B (dualizingModule F) ≪≫ₗ dualizingModuleEquiv F G := by
  refine LinearEquiv.toLinearMap_injective (linearMap_ext_one_tmul_tmul F fun φ b ↦ ?_)
  change omegaBaseChange D F G _ = dualizingModuleEquiv F G (TensorProduct.lid B _ _)
  rw [omegaBaseChange_one_tmul_tmul, TensorProduct.lid_tmul, one_smul, Algebra.algebraMap_self,
    RingHom.id_apply]
  refine (dualizingModuleEquiv_tmul_of_algebraMap_eq (omegaFactorization D F) F
    (Algebra.TensorProduct.lid A F.middle).symm (fun c ↦ ?_) G _ _).trans ?_
  · change algebraMap (omegaFactorization D F).middle B (omegaTmul D F 1 c) = _
    rw [algebraMap_omegaFactorization, map_one, one_mul, Algebra.algebraMap_self,
      RingHom.id_apply]
  · congr 2
    ext c
    change (φ.baseChange A) ((1 : A) ⊗ₜ[A] c) = φ c
    rw [Module.Dual.baseChange_apply_tmul, smul_eq_mul, mul_one]

/-- **Composition.** Base change along a composite of chart base changes is the composite of
the base changes. -/
theorem omegaBaseChange_comp {A B A' B' A'' B'' : Type u} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B''] [Algebra A B] [Algebra A A']
    [Algebra A' B'] [Algebra B B'] [Algebra A' A''] [Algebra B' B''] [Algebra A A'']
    [Algebra B B''] [Algebra A'' B''] [IsScalarTower A A' A''] [IsScalarTower B B' B'']
    [IsNoetherianRing A] [IsNoetherianRing A'] [IsNoetherianRing A''] [Module.Flat A B]
    [Module.Flat A' B']
    (D₁ : ChartBaseChange A B A' B') (D₂ : ChartBaseChange A' B' A'' B'')
    (D₃ : ChartBaseChange A B A'' B'') (F : FiniteOpenFactorization.{u, u, u} A B)
    (G : FiniteOpenFactorization.{u, u, u} A' B') (H : FiniteOpenFactorization.{u, u, u} A'' B'') :
    omegaBaseChange D₃ F H =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B''
          (dualizingModule F)).symm ≪≫ₗ
        (omegaBaseChange D₁ F G).baseChange B' B'' _ _ ≪≫ₗ omegaBaseChange D₂ G H := by
  refine LinearEquiv.toLinearMap_injective (linearMap_ext_one_tmul_tmul F fun φ b ↦ ?_)
  have h₁ : ((TensorProduct.AlgebraTensorModule.cancelBaseChange B B' B'' B''
      (dualizingModule F)).symm ≪≫ₗ (omegaBaseChange D₁ F G).baseChange B' B'' _ _ ≪≫ₗ
        omegaBaseChange D₂ G H) (1 ⊗ₜ dualizingModule.tmul F φ b) =
      omegaBaseChange D₂ G H (1 ⊗ₜ omegaBaseChange D₁ F G (1 ⊗ₜ dualizingModule.tmul F φ b)) := by
    simp only [LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul]
  refine Eq.trans ?_ h₁.symm
  change omegaBaseChange D₃ F H (1 ⊗ₜ dualizingModule.tmul F φ b) = _
  rw [omegaBaseChange_one_tmul_tmul D₁, omegaBaseChange_one_tmul_natural_left,
    omegaBaseChange_one_tmul_tmul D₂ (omegaFactorization D₁ F), omegaBaseChange_one_tmul_tmul,
    ← IsScalarTower.algebraMap_apply B B' B'']
  refine Eq.trans ?_ (dualizingModuleEquiv_tmul_of_algebraMap_eq
    (omegaFactorization D₂ (omegaFactorization D₁ F)) (omegaFactorization D₃ F)
    (Algebra.TensorProduct.cancelBaseChange A A' A'' A'' F.middle).symm (fun c ↦ ?_) H _ _).symm
  · congr 2
    refine LinearMap.ext fun z ↦ ?_
    change omegaDual D₃ F φ z = omegaDual D₂ (omegaFactorization D₁ F) (omegaDual D₁ F φ)
      ((Algebra.TensorProduct.cancelBaseChange A A' A'' A'' F.middle).symm z)
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
        exact (LinearMap.map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
          ((LinearMap.map_add _ _ _).symm.trans (congrArg _ (map_add _ x y).symm)))
    | tmul a c => ?_
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    change omegaDual D₃ F φ (omegaTmul D₃ F a c) =
      omegaDual D₂ (omegaFactorization D₁ F) (omegaDual D₁ F φ)
        (omegaTmul D₂ (omegaFactorization D₁ F) a (omegaTmul D₁ F 1 c))
    rw [omegaDual_tmul, omegaDual_tmul, omegaDual_tmul, smul_one_smul]
  · change algebraMap (omegaFactorization D₂ (omegaFactorization D₁ F)).middle B''
      ((Algebra.TensorProduct.cancelBaseChange A A' A'' A'' F.middle).symm c) =
      algebraMap (omegaFactorization D₃ F).middle B'' c
    induction c using TensorProduct.inductionOn with
    | add x y hx hy =>
        exact (congrArg _ (map_add _ x y)).trans ((RingHom.map_add _ _ _).trans
          ((congrArg₂ (· + ·) hx hy).trans (RingHom.map_add _ x y).symm))
    | tmul a c =>
        rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
        change algebraMap (omegaFactorization D₂ (omegaFactorization D₁ F)).middle B''
          (omegaTmul D₂ (omegaFactorization D₁ F) a (omegaTmul D₁ F 1 c)) =
          algebraMap (omegaFactorization D₃ F).middle B'' (omegaTmul D₃ F a c)
        rw [algebraMap_omegaFactorization, algebraMap_omegaFactorization,
          algebraMap_omegaFactorization, map_one, one_mul,
          ← IsScalarTower.algebraMap_apply B B' B'']

end Functoriality

end Stacks.TateMap
