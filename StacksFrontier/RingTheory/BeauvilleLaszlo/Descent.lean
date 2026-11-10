module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.BeauvilleLaszlo.ModuleEquivalence

/-!
# Descent of module properties along a Beauville--Laszlo glueing pair

Let `(R → S, f)` be a Beauville--Laszlo glueing pair. This file proves that flatness and finite
projectivity of an `R`-module can be checked after base change to `S` and after localization
away from `f`. Neither statement asks the module to be glueable.

## Main results

* `flat_iff_flat_baseChange_and_localization` (Stacks 0BP7): `M` is flat over `R` if and only
  if `S ⊗[R] M` is flat over `S` and `M_f` is flat over `R_f`.
* `finite_projective_iff_baseChange_and_localization` (Stacks 0BP6): `M` is finite projective
  over `R` if and only if both base changes are finite projective.

## Implementation notes

Scalar extension is represented as `S ⊗[R] M`, with the scalar ring on the left, and `M_f` is
represented by `LocalizedModule.Away f M`. A finite projective module is expressed by the
conjunction of `Module.Finite` and `Module.Projective`.

The flatness criterion is proved first for the module `M̄` of compatible sections of the
canonical glueing datum of `M`, where the Beauville--Laszlo module sequence is short exact: a
five-term diagram chase then turns exactness of `0 → A → B → C → 0` into exactness of its
`M̄`-tensor, which is Mathlib's criterion for flatness. The canonical map `M → M̄` is surjective
(Stacks 0BP9) and bijective after both base changes, and its kernel is killed by tensoring with
`S × R_f`, hence zero (Stacks 0BNL); so `M ≅ M̄`.

For finite projectivity, flatness comes from Stacks 0BP7, finite generation from Stacks 0BNN,
and then the kernel of a finite free presentation is itself finitely generated after each base
change — because a finite projective module is finitely presented — so Stacks 0BNN applies
again and `M` is finitely presented and flat, hence projective.

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0BP7](https://stacks.math.columbia.edu/tag/0BP7)
* [Stacks Project, Tag 0BP6](https://stacks.math.columbia.edu/tag/0BP6)
-/

@[expose] public section

namespace BeauvilleLaszlo

section

open CategoryTheory
open scoped TensorProduct

section TensorGluing

universe uR

variable {R : Type uR} {S T U : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup T] [Module R T] [AddCommGroup U] [Module R U]

/-- The diagonal map `N → (S ⊗ N) × (T ⊗ N)` attached to an element `t : T`. -/
private abbrev tensorDiagonal (t : T) (N : Type*) [AddCommGroup N] [Module R N] :
    N →ₗ[R] (S ⊗[R] N) × (T ⊗[R] N) :=
  (TensorProduct.mk R S N 1).prod (TensorProduct.mk R T N t)

/-- The difference map `(S ⊗ N) × (T ⊗ N) → U ⊗ N` attached to `σ : S → U` and `τ : T → U`. -/
private abbrev tensorDifference (σ : S →ₗ[R] U) (τ : T →ₗ[R] U)
    (N : Type*) [AddCommGroup N] [Module R N] :
    ((S ⊗[R] N) × (T ⊗[R] N)) →ₗ[R] U ⊗[R] N :=
  (σ.rTensor N).coprod (-τ.rTensor N)

private lemma rTensor_lTensor_comm
    {A B N P : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (g : A →ₗ[R] B) (i : N →ₗ[R] P) (x : A ⊗[R] N) :
    g.rTensor P (i.lTensor A x) = i.lTensor B (g.rTensor N x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The diagonal map `R → S × T` attached to an element `t : T`. -/
private abbrev ringDiagonal (t : T) : R →ₗ[R] S × T :=
  (Algebra.linearMap R S).prod ((LinearMap.id : R →ₗ[R] R).smulRight t)

/-- The difference map `S × T → U` attached to `σ : S → U` and `τ : T → U`. -/
private abbrev ringDifference (σ : S →ₗ[R] U) (τ : T →ₗ[R] U) : S × T →ₗ[R] U :=
  σ.coprod (-τ)

private lemma tensorDifference_exact (t : T) (σ : S →ₗ[R] U) (τ : T →ₗ[R] U)
    (hex : Function.Exact (ringDiagonal (R := R) (S := S) t) (ringDifference σ τ))
    (hes : Function.Surjective (ringDifference σ τ))
    (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Exact (tensorDiagonal (R := R) (S := S) t N) (tensorDifference σ τ N) := by
  let d := ringDiagonal (R := R) (S := S) t
  let e := ringDifference σ τ
  have hten := _root_.rTensor_exact N hex hes
  let p := TensorProduct.prodLeft R R S T N
  have hp (x : (S × T) ⊗[R] N) : e.rTensor N x = tensorDifference σ τ N (p x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a n =>
      rcases a with ⟨a, b⟩
      simp [e, ringDifference, p, tensorDifference, TensorProduct.add_tmul,
        TensorProduct.prodLeft_tmul, TensorProduct.neg_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hpd (x : R ⊗[R] N) :
      p (d.rTensor N x) = tensorDiagonal (R := R) (S := S) t N (TensorProduct.lid R N x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r n =>
      simp [p, d, ringDiagonal, tensorDiagonal, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hten (p.symm x)).mp (by rw [hp]; simpa using hx)
    exact ⟨TensorProduct.lid R N y, by rw [← hpd, hy]; simp⟩
  · rintro ⟨y, rfl⟩
    rw [← (TensorProduct.lid R N).apply_symm_apply y, ← hpd, ← hp]
    exact (hten _).mpr ⟨_, rfl⟩

private lemma tensorDifference_surjective (σ : S →ₗ[R] U) (τ : T →ₗ[R] U)
    (hs : Function.Surjective (ringDifference σ τ))
    (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Surjective (tensorDifference σ τ N) := by
  have he : (tensorDifference σ τ N).comp
      (TensorProduct.prodLeft R R S T N).toLinearMap = (ringDifference σ τ).rTensor N := by
    apply TensorProduct.ext'
    rintro ⟨x, y⟩ n
    simp [tensorDifference, ringDifference, TensorProduct.add_tmul,
      TensorProduct.prodLeft_tmul, TensorProduct.neg_tmul]
  intro u
  obtain ⟨x, hx⟩ := LinearMap.rTensor_surjective N hs u
  exact ⟨TensorProduct.prodLeft R R S T N x, by
    change ((tensorDifference σ τ N).comp (TensorProduct.prodLeft R R S T N).toLinearMap) x = u
    rw [he, hx]⟩

private lemma tensorDiagonal_injective_of_flat (t : T)
    (hd : Function.Injective (ringDiagonal (R := R) (S := S) t))
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Flat R N] :
    Function.Injective (tensorDiagonal (R := R) (S := S) t N) := by
  have he : tensorDiagonal (R := R) (S := S) t N =
      (TensorProduct.prodLeft R R S T N).toLinearMap.comp
        (((ringDiagonal (R := R) (S := S) t).rTensor N).comp
          (TensorProduct.lid R N).symm.toLinearMap) := by
    ext n <;> simp [tensorDiagonal, ringDiagonal]
  rw [he]
  exact (TensorProduct.prodLeft R R S T N).injective.comp
    ((Module.Flat.rTensor_preserves_injective_linearMap _ hd).comp
      (TensorProduct.lid R N).symm.injective)

private lemma rTensor_prod_exact
    {A B C D N : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    [AddCommGroup N] [Module R N]
    (a : A →ₗ[R] B) (b : A →ₗ[R] C) (c : B →ₗ[R] D) (d : C →ₗ[R] D)
    (h : Function.Exact (a.prod b) (c.coprod (-d)))
    (hs : Function.Surjective (c.coprod (-d))) :
    Function.Exact ((a.rTensor N).prod (b.rTensor N))
      ((c.rTensor N).coprod (-d.rTensor N)) := by
  let p := TensorProduct.prodLeft R R B C N
  have h₁ : p.toLinearMap.comp ((a.prod b).rTensor N) =
      (a.rTensor N).prod (b.rTensor N) := by
    apply TensorProduct.ext'
    intro a n
    rfl
  have h₂ : ((c.rTensor N).coprod (-d.rTensor N)).comp p.toLinearMap =
      (c.coprod (-d)).rTensor N := by
    apply TensorProduct.ext'
    rintro ⟨b, c⟩ n
    simp [p, TensorProduct.add_tmul, TensorProduct.neg_tmul]
  have he := _root_.rTensor_exact N h hs
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (he (p.symm x)).mp (by
      rw [← h₂]
      simpa using hx)
    refine ⟨y, ?_⟩
    rw [← h₁]
    change p ((a.prod b).rTensor N y) = x
    rw [hy, p.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    rw [← h₁]
    change (((c.rTensor N).coprod (-d.rTensor N)).comp p.toLinearMap)
      ((a.prod b).rTensor N y) = 0
    rw [h₂]
    exact he.apply_apply_eq_zero y

private lemma rTensor_prod_injective
    {A B C N : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup N] [Module R N] [Module.Flat R N]
    (a : A →ₗ[R] B) (b : A →ₗ[R] C) (h : Function.Injective (a.prod b)) :
    Function.Injective ((a.rTensor N).prod (b.rTensor N)) := by
  have he : (TensorProduct.prodLeft R R B C N).toLinearMap.comp
      ((a.prod b).rTensor N) = (a.rTensor N).prod (b.rTensor N) := by
    apply TensorProduct.ext'
    intro a n
    rfl
  rw [← he]
  exact (TensorProduct.prodLeft R R B C N).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ h)

variable [Module S U] [IsScalarTower R S U]

/-- The left map of the `P`-fibre of the glueing diagram, for an `S`-module `P`. -/
private abbrev fiberIn {P A B : Type*} [AddCommGroup P] [Module R P]
    [Module S P] [IsScalarTower R S P] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (σ : P →ₗ[S] U) (i : A →ₗ[R] B) :
    (P ⊗[R] A) →ₗ[S] (P ⊗[R] B) × (U ⊗[R] A) :=
  (TensorProduct.AlgebraTensorModule.lTensor S P i).prod
    (TensorProduct.AlgebraTensorModule.map σ LinearMap.id)

/-- The right map of the `P`-fibre of the glueing diagram, for an `S`-module `P`. -/
private abbrev fiberOut {P A B C : Type*} [AddCommGroup P] [Module R P]
    [Module S P] [IsScalarTower R S P] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (σ : P →ₗ[S] U) (i : A →ₗ[R] B) (d : B →ₗ[R] C) :
    ((P ⊗[R] B) × (U ⊗[R] A)) →ₗ[S] (P ⊗[R] C) × (U ⊗[R] B) :=
  ((TensorProduct.AlgebraTensorModule.lTensor S P d).comp (LinearMap.fst S _ _)).prod
    ((TensorProduct.AlgebraTensorModule.map σ LinearMap.id).comp (LinearMap.fst S _ _) -
      (TensorProduct.AlgebraTensorModule.lTensor S U i).comp (LinearMap.snd S _ _))

private lemma fiber_exact (t : T) (σ : S →ₗ[S] U) (τ : T →ₗ[R] U)
    (hex : Function.Exact (ringDiagonal (R := R) (S := S) t)
      (ringDifference (σ.restrictScalars R) τ))
    (hes : Function.Surjective (ringDifference (σ.restrictScalars R) τ))
    (hed : Function.Injective (ringDiagonal (R := R) (S := S) t))
    {A B C : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Flat R B] [Module.Flat R C] [Module.Flat R T]
    (i : A →ₗ[R] B) (d : B →ₗ[R] C) (hi : Function.Injective i) (hid : Function.Exact i d) :
    Function.Exact (fiberIn σ i) (fiberOut σ i d) := by
  have hdi : d.comp i = 0 := LinearMap.ext hid.apply_apply_eq_zero
  have ht := Module.Flat.lTensor_preserves_injective_linearMap (M := T) i hi
  have hcinj := tensorDiagonal_injective_of_flat t hed C
  intro x
  constructor
  · intro hx
    have hx₁ : d.lTensor S x.1 = 0 := congrArg Prod.fst hx
    have hx₂ : (σ.restrictScalars R).rTensor B x.1 = i.lTensor U x.2 :=
      sub_eq_zero.mp (congrArg Prod.snd hx)
    obtain ⟨⟨a, b⟩, hab⟩ := tensorDifference_surjective (σ.restrictScalars R) τ hes A x.2
    change (σ.restrictScalars R).rTensor A a - τ.rTensor A b = x.2 at hab
    have hxb : tensorDifference (σ.restrictScalars R) τ B
        (x.1 - i.lTensor S a, -i.lTensor T b) = 0 := by
      change (σ.restrictScalars R).rTensor B (x.1 - i.lTensor S a) +
        -(τ.rTensor B (-i.lTensor T b)) = 0
      rw [map_sub, map_neg, neg_neg, rTensor_lTensor_comm, rTensor_lTensor_comm, hx₂,
        ← hab, map_sub]
      abel
    obtain ⟨c, hc⟩ := (tensorDifference_exact t (σ.restrictScalars R) τ hex hes B _).mp hxb
    have hcS := congrArg Prod.fst hc
    have hcT := congrArg Prod.snd hc
    change (1 : S) ⊗ₜ[R] c = x.1 - i.lTensor S a at hcS
    change t ⊗ₜ[R] c = -i.lTensor T b at hcT
    clear hc
    have hdc : d c = 0 := by
      apply (injective_iff_map_eq_zero _).mp hcinj
      apply Prod.ext
      · change (1 : S) ⊗ₜ[R] d c = 0
        change d.lTensor S ((1 : S) ⊗ₜ[R] c) = 0
        rw [hcS, map_sub, hx₁, ← LinearMap.lTensor_comp_apply, hdi]
        simp
      · change t ⊗ₜ[R] d c = 0
        change d.lTensor T (t ⊗ₜ[R] c) = 0
        rw [hcT, map_neg, ← LinearMap.lTensor_comp_apply, hdi]
        simp
    obtain ⟨a₀, ha₀⟩ := (hid c).mp hdc
    refine ⟨a + (1 : S) ⊗ₜ[R] a₀, ?_⟩
    apply Prod.ext
    · change i.lTensor S (a + (1 : S) ⊗ₜ[R] a₀) = x.1
      rw [map_add]
      change i.lTensor S a + (1 : S) ⊗ₜ[R] i a₀ = x.1
      rw [ha₀, hcS]
      abel
    · change (σ.restrictScalars R).rTensor A (a + (1 : S) ⊗ₜ[R] a₀) = x.2
      have ht₀ : t ⊗ₜ[R] a₀ = -b := by
        apply ht
        change t ⊗ₜ[R] i a₀ = i.lTensor T (-b)
        rw [ha₀, hcT, map_neg]
      have hστ : σ 1 = τ t := by
        have hz := hex.apply_apply_eq_zero 1
        apply sub_eq_zero.mp
        simpa [ringDiagonal, ringDifference, sub_eq_add_neg] using hz
      rw [map_add]
      change (σ.restrictScalars R).rTensor A a + σ 1 ⊗ₜ[R] a₀ = x.2
      rw [hστ]
      change (σ.restrictScalars R).rTensor A a + τ.rTensor A (t ⊗ₜ[R] a₀) = x.2
      rw [ht₀, map_neg, ← sub_eq_add_neg, hab]
  · rintro ⟨a, rfl⟩
    apply Prod.ext
    · change d.lTensor S (i.lTensor S a) = 0
      rw [← LinearMap.lTensor_comp_apply, hdi]
      simp
    · change (σ.restrictScalars R).rTensor B (i.lTensor S a) -
        i.lTensor U ((σ.restrictScalars R).rTensor A a) = 0
      rw [rTensor_lTensor_comm, sub_self]

/-- The exchange isomorphism `(S ⊗ M) ⊗_S (X ⊗ N) ≅ (X ⊗ M) ⊗ N`. -/
private noncomputable def tensorExchange
    (M X N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
    [AddCommGroup N] [Module R N] :
    (S ⊗[R] M) ⊗[S] (X ⊗[R] N) ≃ₗ[S] (X ⊗[R] M) ⊗[R] N :=
  (TensorProduct.AlgebraTensorModule.assoc R S S (S ⊗[R] M) X N).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr
      (TensorProduct.comm S (S ⊗[R] M) X ≪≫ₗ
        TensorProduct.AlgebraTensorModule.cancelBaseChange R S S X M) (LinearEquiv.refl R N)

private lemma tensorExchange_tmul
    {M X N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
    [AddCommGroup N] [Module R N] (s : S) (m : M) (x : X) (n : N) :
    tensorExchange (R := R) (S := S) M X N ((s ⊗ₜ[R] m) ⊗ₜ[S] (x ⊗ₜ[R] n)) =
      ((s • x) ⊗ₜ[R] m) ⊗ₜ[R] n := by
  simp [tensorExchange]

private lemma fiber_exact_baseChange
    {A B C M : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M]
    [Module.Flat S (S ⊗[R] M)]
    (σ : S →ₗ[S] U) (i : A →ₗ[R] B) (d : B →ₗ[R] C)
    (h : Function.Exact (fiberIn σ i) (fiberOut σ i d)) :
    Function.Exact
      (fiberIn (TensorProduct.AlgebraTensorModule.map σ (LinearMap.id (R := R) (M := M))) i)
      (fiberOut (TensorProduct.AlgebraTensorModule.map σ
        (LinearMap.id (R := R) (M := M))) i d) := by
  let P := S ⊗[R] M
  let σM := TensorProduct.AlgebraTensorModule.map σ (LinearMap.id (R := R) (M := M))
  let e₀ := tensorExchange (R := R) (S := S) M S A
  let e₁ := TensorProduct.prodRight S S P (S ⊗[R] B) (U ⊗[R] A) ≪≫ₗ
    (tensorExchange (R := R) (S := S) M S B).prodCongr
      (tensorExchange (R := R) (S := S) M U A)
  let e₂ := TensorProduct.prodRight S S P (S ⊗[R] C) (U ⊗[R] B) ≪≫ₗ
    (tensorExchange (R := R) (S := S) M S C).prodCongr
      (tensorExchange (R := R) (S := S) M U B)
  have hin : e₁.toLinearMap.comp ((fiberIn σ i).lTensor P) =
      (fiberIn σM i).comp e₀.toLinearMap := by
    apply TensorProduct.ext'
    intro p a
    induction p using TensorProduct.inductionOn with
    | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq]
    | tmul s m =>
      induction a using TensorProduct.inductionOn with
      | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
      | tmul s' a =>
        simp [e₀, e₁, fiberIn, σM, tensorExchange, ← map_smul]
  have hout : e₂.toLinearMap.comp ((fiberOut σ i d).lTensor P) =
      (fiberOut σM i d).comp e₁.toLinearMap := by
    apply TensorProduct.ext'
    intro p x
    induction p using TensorProduct.inductionOn with
    | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq]
    | tmul s m =>
      rcases x with ⟨b, a⟩
      have split : (b, a) = (b, 0) + (0, a) := by simp
      rw [split, TensorProduct.tmul_add, map_add, map_add]
      clear split
      congr 1
      · induction b using TensorProduct.inductionOn with
        | add b c hb hc =>
          have hh : (b + c, (0 : U ⊗[R] A)) = (b, 0) + (c, 0) := by simp
          rw [hh]
          simp only [TensorProduct.tmul_add, map_add, hb, hc]
        | tmul s' b => simp [e₁, e₂, fiberOut, σM, tensorExchange, ← map_smul]
      · induction a using TensorProduct.inductionOn with
        | add a b ha hb =>
          have hh : ((0 : S ⊗[R] B), a + b) = (0, a) + (0, b) := by simp
          rw [hh]
          simp only [TensorProduct.tmul_add, map_add, ha, hb]
        | tmul u a =>
          simp only [e₁, e₂, fiberOut, σM, LinearMap.comp_apply, LinearEquiv.coe_trans,
            LinearMap.lTensor_tmul, LinearMap.prod_apply]
          simp [tensorExchange, ← TensorProduct.neg_tmul]
  have he := Module.Flat.lTensor_exact P h
  intro x
  constructor
  · intro hx
    have hz : (fiberOut σ i d).lTensor P (e₁.symm x) = 0 := by
      apply e₂.injective
      change (e₂.toLinearMap.comp ((fiberOut σ i d).lTensor P)) (e₁.symm x) = e₂ 0
      rw [hout]
      simpa using hx
    obtain ⟨a, ha⟩ := (he _).mp hz
    refine ⟨e₀ a, ?_⟩
    change ((fiberIn σM i).comp e₀.toLinearMap) a = x
    rw [← hin]
    change e₁ ((fiberIn σ i).lTensor P a) = x
    rw [ha, e₁.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    have ha := he.apply_apply_eq_zero (e₀.symm a)
    have h₁ := LinearMap.congr_fun hin (e₀.symm a)
    change e₁ ((fiberIn σ i).lTensor P (e₀.symm a)) = fiberIn σM i (e₀ (e₀.symm a)) at h₁
    rw [e₀.apply_symm_apply] at h₁
    have h₂ := LinearMap.congr_fun hout ((fiberIn σ i).lTensor P (e₀.symm a))
    change e₂ ((fiberOut σ i d).lTensor P ((fiberIn σ i).lTensor P (e₀.symm a))) =
      fiberOut σM i d (e₁ ((fiberIn σ i).lTensor P (e₀.symm a))) at h₂
    rw [ha, map_zero, h₁] at h₂
    exact h₂.symm

private lemma lTensor_exact_of_gluing (t : T) (σ : S →ₗ[S] U) (τ : T →ₗ[R] U)
    (hex : Function.Exact (ringDiagonal (R := R) (S := S) t)
      (ringDifference (σ.restrictScalars R) τ))
    (hes : Function.Surjective (ringDifference (σ.restrictScalars R) τ))
    (hed : Function.Injective (ringDiagonal (R := R) (S := S) t))
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Flat S (S ⊗[R] M)] [Module.Flat R (T ⊗[R] M)] [Module.Flat R T]
    (hM : Function.Injective (tensorDiagonal (R := R) (S := S) t M))
    {A B C : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Flat R B] [Module.Flat R C]
    (i : A →ₗ[R] B) (d : B →ₗ[R] C) (hi : Function.Injective i) (hid : Function.Exact i d) :
    Function.Exact (i.lTensor M) (d.lTensor M) := by
  let a := TensorProduct.mk R S M 1
  let b := TensorProduct.mk R T M t
  let c := (σ.restrictScalars R).rTensor M
  let e := τ.rTensor M
  let σM := TensorProduct.AlgebraTensorModule.map σ (LinearMap.id (R := R) (M := M))
  have hc : c.comp a = e.comp b := by
    have hστ : σ 1 = τ t := by
      apply sub_eq_zero.mp
      simpa [ringDiagonal, ringDifference, sub_eq_add_neg] using hex.apply_apply_eq_zero 1
    ext m
    change σ 1 ⊗ₜ[R] m = τ t ⊗ₜ[R] m
    rw [hστ]
  have hf := fiber_exact_baseChange (M := M) σ i d
    (fiber_exact t σ τ hex hes hed i d hi hid)
  have hA := rTensor_prod_exact (N := A) a b c e
    (tensorDifference_exact t (σ.restrictScalars R) τ hex hes M)
    (tensorDifference_surjective (σ.restrictScalars R) τ hes M)
  have hB := rTensor_prod_injective (N := B) a b hM
  have hT := Module.Flat.lTensor_exact (T ⊗[R] M) hid
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hT (b.rTensor B x)).mp (by
      rw [← rTensor_lTensor_comm, hx, map_zero])
    have hxy : fiberOut σM i d (a.rTensor B x, e.rTensor A y) = 0 := by
      apply Prod.ext
      · change d.lTensor (S ⊗[R] M) (a.rTensor B x) = 0
        rw [← rTensor_lTensor_comm, hx, map_zero]
      · change c.rTensor B (a.rTensor B x) - i.lTensor (U ⊗[R] M) (e.rTensor A y) = 0
        rw [← LinearMap.rTensor_comp_apply, hc, LinearMap.rTensor_comp_apply,
          ← rTensor_lTensor_comm, hy, sub_self]
    obtain ⟨z, hz⟩ := (hf _).mp hxy
    have hz₁ : i.lTensor (S ⊗[R] M) z = a.rTensor B x := congrArg Prod.fst hz
    have hz₂ : c.rTensor A z = e.rTensor A y := congrArg Prod.snd hz
    obtain ⟨w, hw⟩ := (hA (z, y)).mp (by
      change c.rTensor A z + -(e.rTensor A y) = 0
      rw [hz₂, add_neg_cancel])
    have hw₁ : a.rTensor A w = z := congrArg Prod.fst hw
    have hw₂ : b.rTensor A w = y := congrArg Prod.snd hw
    refine ⟨w, hB ?_⟩
    apply Prod.ext
    · change a.rTensor B (i.lTensor M w) = a.rTensor B x
      rw [rTensor_lTensor_comm, hw₁, hz₁]
    · change b.rTensor B (i.lTensor M w) = b.rTensor B x
      rw [rTensor_lTensor_comm, hw₂, hy]
  · rintro ⟨x, rfl⟩
    have hdi : d.comp i = 0 := LinearMap.ext hid.apply_apply_eq_zero
    rw [← LinearMap.lTensor_comp_apply, hdi]
    simp

private lemma flat_of_lTensor_exact_of_flat_terms
    {M : Type*} [AddCommGroup M] [Module R M]
    (h : ∀ {A B C : Type uR} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
      [AddCommGroup C] [Module R C] [Module.Flat R B] [Module.Flat R C]
      (i : A →ₗ[R] B) (d : B →ₗ[R] C), Function.Injective i → Function.Exact i d →
      Function.Exact (i.lTensor M) (d.lTensor M)) : Module.Flat R M := by
  apply Module.Flat.iff_lTensor_injective'.mpr
  intro I
  let q : (I →₀ R) →ₗ[R] I := Finsupp.linearCombination R id
  have hq : Function.Surjective q := fun x => ⟨Finsupp.single x 1, by simp [q]⟩
  let d := I.subtype.comp q
  have he : Function.Exact q.ker.subtype d :=
    (LinearMap.exact_subtype_ker_map q).comp_injective I.subtype I.subtype_injective (map_zero _)
  have hm := h (A := q.ker) (B := I →₀ R) (C := R) q.ker.subtype d q.ker.subtype_injective he
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective M hq x
  have hz : d.lTensor M y = 0 := by
    rw [LinearMap.lTensor_comp_apply, hy, hx]
  obtain ⟨z, hz⟩ := (hm y).mp hz
  rw [← hy, ← hz, ← LinearMap.lTensor_comp_apply]
  have hqz : q.comp q.ker.subtype = 0 := LinearMap.ext fun z => z.property
  rw [hqz]
  simp

private lemma flat_of_gluing (t : T) (σ : S →ₗ[S] U) (τ : T →ₗ[R] U)
    (hex : Function.Exact (ringDiagonal (R := R) (S := S) t)
      (ringDifference (σ.restrictScalars R) τ))
    (hes : Function.Surjective (ringDifference (σ.restrictScalars R) τ))
    (hed : Function.Injective (ringDiagonal (R := R) (S := S) t))
    (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Flat S (S ⊗[R] M)] [Module.Flat R (T ⊗[R] M)] [Module.Flat R T]
    (hM : Function.Injective (tensorDiagonal (R := R) (S := S) t M)) :
    Module.Flat R M := by
  exact flat_of_lTensor_exact_of_flat_terms fun i d hi hid =>
    lTensor_exact_of_gluing t σ τ hex hes hed M hM i d hi hid

end TensorGluing

section BeauvilleLaszloDescent

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The map `R_f → S_f` induced by `R → S`, as an `R`-linear map. -/
private noncomputable def awayMapLinear (f : R) :
    Localization.Away f →ₗ[R] Localization.Away (algebraMap R S f) where
  toFun := Localization.awayMap (algebraMap R S) f
  map_add' := map_add _
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply, Algebra.smul_def]
    rw [map_mul]
    congr 1
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    exact (IsScalarTower.algebraMap_apply R S
      (Localization.Away (algebraMap R S f)) r).symm

private lemma awayMapLinear_apply (f : R) (x : Localization.Away f) :
    awayMapLinear (S := S) f x = Localization.awayMap (algebraMap R S) f x := rfl

private lemma flat_tensor_away_of_flat_localization (f : R)
    (M : Type w) [AddCommGroup M] [Module R M]
    [Module.Flat (Localization.Away f) (LocalizedModule.Away f M)] :
    Module.Flat R (Localization.Away f ⊗[R] M) := by
  let e := (IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).equiv
  have : Module.Flat (Localization.Away f) (Localization.Away f ⊗[R] M) :=
    Module.Flat.of_linearEquiv e
  exact Module.Flat.trans R (Localization.Away f) _

/-- A glueable module whose two base changes are flat is flat. -/
private lemma flat_of_beauvilleLaszloModuleSequence_shortExact
    (f : R)
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (M : Type w) [AddCommGroup M] [Module R M]
    [Module.Flat S (S ⊗[R] M)]
    [Module.Flat (Localization.Away f) (LocalizedModule.Away f M)]
    (hM : (beauvilleLaszloModuleSequence (S := S) M f).ShortExact) :
    Module.Flat R M := by
  let T := Localization.Away f
  let U := Localization.Away (algebraMap R S f)
  let σ : S →ₗ[S] U := Algebra.linearMap S U
  let τ : T →ₗ[R] U := awayMapLinear (S := S) f
  let d := ringDiagonal (R := R) (S := S) (1 : T)
  let e := ringDifference (σ.restrictScalars R) τ
  have hd (r : R) : d r = (algebraMap R S r, algebraMap R T r) := by
    simp [d, ringDiagonal, Algebra.smul_def]
  have he (x : S × T) : e x =
      algebraMap S U x.1 - Localization.awayMap (algebraMap R S) f x.2 := rfl
  have hf (r : R) :
      (beauvilleLaszloSequence f (algebraMap R S)).f (ULift.up r) =
        ULift.up (d r) := by
    apply ULift.down_injective
    exact (hd r).symm
  have hg (x : S × T) :
      (beauvilleLaszloSequence f (algebraMap R S)).g (ULift.up x) =
        ULift.up (e x) := rfl
  have hinj : Function.Injective d := by
    intro r s hrs
    apply ULift.up_injective
    apply (AddCommGrpCat.mono_iff_injective _).mp hglue.mono_f
    rw [hf, hf, hrs]
  have hsurj : Function.Surjective e := by
    intro u
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hglue.epi_g (ULift.up u)
    exact ⟨x.down, congrArg ULift.down hx⟩
  have hex : Function.Exact d e := by
    intro x
    constructor
    · intro hx
      obtain ⟨r, hr⟩ := (CategoryTheory.ShortComplex.ab_exact_iff _).mp hglue.exact
        (ULift.up x) (by rw [hg, hx]; rfl)
      rcases r with ⟨r⟩
      rw [hf] at hr
      exact ⟨r, congrArg ULift.down hr⟩
    · rintro ⟨r, rfl⟩
      have hz := (beauvilleLaszloSequence f (algebraMap R S)).ab_zero_apply (ULift.up r)
      rw [hf, hg] at hz
      exact congrArg ULift.down hz
  have hdiag : Function.Injective (tensorDiagonal (R := R) (S := S) (1 : T) M) := by
    intro x y hxy
    apply ULift.up_injective
    apply (AddCommGrpCat.mono_iff_injective _).mp hM.mono_f
    apply ULift.down_injective
    apply Prod.ext
    · apply (TensorProduct.comm R M S).injective
      exact congrArg Prod.fst hxy
    · apply (TensorProduct.comm R M T).injective
      exact congrArg Prod.snd hxy
  have := flat_tensor_away_of_flat_localization f M
  exact flat_of_gluing (1 : T) σ τ hex hsurj hinj M hdiag

private lemma lTensor_injective_of_localizedModule_map_injective
    (P : Submonoid R) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (hg : Function.Injective (LocalizedModule.map P g)) :
    Function.Injective (g.lTensor (Localization P)) := by
  let eM := LocalizedModule.equivTensorProduct P M
  let eN := LocalizedModule.equivTensorProduct P N
  have hnat (x : LocalizedModule P M) :
      eN (LocalizedModule.map P g x) = g.lTensor (Localization P) (eM x) := by
    induction x using LocalizedModule.induction_on with
    | h m s => simp [eM, eN]
  intro x y hxy
  apply eM.symm.injective
  apply hg
  apply eN.injective
  rw [hnat, hnat, eM.apply_symm_apply, eM.apply_symm_apply, hxy]

private lemma subsingleton_tensor_ker_of_surjective
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R N]
    (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (A : Type*) [AddCommGroup A] [Module R A]
    (hA : Function.Injective (g.lTensor A)) :
    Subsingleton (A ⊗[R] g.ker) := by
  have hi := LinearMap.lTensor_injective_of_exact_of_flat g hg g.ker.subtype
    g.ker.subtype_injective (LinearMap.exact_subtype_ker_map g) A
  have hz : g.comp g.ker.subtype = 0 := by
    ext x
    exact x.property
  constructor
  intro x y
  apply hi
  apply hA
  rw [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, hz]
  simp

/-- Bijectivity of `quotientPowMap` gives bijectivity of the quotient map of the extended
ideals `(f) ^ n` in `R`. -/
private lemma bijective_quotientMap_of_quotientPowMap_bijective (f : R)
    (hquot : ∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n (algebraMap R S))) :
    ∀ n : ℕ, 0 < n → Function.Bijective
      (Ideal.quotientMap (Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n))
        (algebraMap R S) Ideal.le_comap_map) := by
  intro n hn
  have he : Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n) =
      (Ideal.span {algebraMap R S f}) ^ n := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
  let e := Ideal.quotEquivOfEq he
  let q := Ideal.quotientMap (Ideal.map (algebraMap R S) ((Ideal.span {f}) ^ n))
    (algebraMap R S) Ideal.le_comap_map
  have heq : e.toRingHom.comp q = quotientPowMap f n (algebraMap R S) := by
    ext r
    exact Ideal.quotEquivOfEq_mk he (algebraMap R S r)
  apply (e.bijective.of_comp_iff' q).mp
  change Function.Bijective (e.toRingHom.comp q)
  rw [heq]
  exact hquot n hn

/-- Let `(R → S, f)` be a Beauville--Laszlo glueing pair. An `R`-module `M` is flat
if and only if its scalar extension to `S` is flat over `S` and its localization away
from `f` is flat over `R_f`. -/
@[stacks 0BP7]
public theorem flat_iff_flat_baseChange_and_localization
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (f : R)
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (M : Type w) [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      Module.Flat S (S ⊗[R] M) ∧
        Module.Flat (Localization.Away f) (LocalizedModule.Away f M) := by
  constructor
  · intro hM
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hS, hL⟩
    let C := FormalGlueing.moduleGlueingConstruction.{u, v, w} S (fun _ : Fin 1 ↦ f)
    let := C.category
    let X := C.canonical.obj (ModuleCat.of R (ULift.{max u v w} M))
    let Mbar := C.sections.obj X
    obtain ⟨g, _, hbar, hgS, hgL, hg⟩ :=
      canonicalToSections_surjective R S f hquot hglue M
    let gS : S ⊗[R] M →ₗ[S] S ⊗[R] Mbar :=
      TensorProduct.AlgebraTensorModule.lTensor S S g
    have hgS' : Function.Bijective gS := hgS
    have : Module.Flat S (S ⊗[R] Mbar) :=
      Module.Flat.of_linearEquiv (LinearEquiv.ofBijective gS hgS').symm
    have : Module.Flat (Localization.Away f) (LocalizedModule.Away f Mbar) :=
      Module.Flat.of_linearEquiv
        (LinearEquiv.ofBijective (LocalizedModule.map (Submonoid.powers f) g) hgL).symm
    have : Module.Flat R Mbar :=
      flat_of_beauvilleLaszloModuleSequence_shortExact f hglue Mbar hbar
    have : Subsingleton (S ⊗[R] g.ker) :=
      subsingleton_tensor_ker_of_surjective g hg S hgS.1
    have : Subsingleton (Localization.Away f ⊗[R] g.ker) :=
      subsingleton_tensor_ker_of_surjective g hg (Localization.Away f)
        (lTensor_injective_of_localizedModule_map_injective (Submonoid.powers f) g hgL.1)
    have : Subsingleton ((S × Localization.Away f) ⊗[R] g.ker) :=
      (TensorProduct.prodLeft R R S (Localization.Away f) g.ker).injective.subsingleton
    have : Subsingleton (g.ker ⊗[R] (S × Localization.Away f)) :=
      (TensorProduct.comm R g.ker (S × Localization.Away f)).injective.subsingleton
    have hquot' := bijective_quotientMap_of_quotientPowMap_bijective f hquot
    have : Subsingleton g.ker := by
      by_contra hK
      have : Nontrivial g.ker := not_subsingleton_iff_nontrivial.mp hK
      have := (tensorProduct_prod_away_nontrivial_of_quotientMap_bijective
        R f).1 S hquot' g.ker
      exact not_nontrivial (g.ker ⊗[R] (S × Localization.Away f)) inferInstance
    have hginj : Function.Injective g := by
      apply (injective_iff_map_eq_zero _).mpr
      intro m hm
      exact congrArg Subtype.val (Subsingleton.elim (⟨m, hm⟩ : g.ker) 0)
    exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective g ⟨hginj, hg⟩)

end BeauvilleLaszloDescent

end

section

open scoped TensorProduct

universe u v w

/-- If the scalar extensions of an `R`-module `M` to two `R`-algebras `A` and `B` are finite,
then its scalar extension to `A × B` is a finite `A × B`-module. -/
lemma finite_tensorProduct_prod_of_finite
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    {B : Type w} [CommRing B] [Algebra R B]
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite A (A ⊗[R] M)] [Module.Finite B (B ⊗[R] M)] :
    Module.Finite (A × B) ((A × B) ⊗[R] M) := by
  let : Algebra (A × B) A := (RingHom.fst A B).toAlgebra
  let : Algebra (A × B) B := (RingHom.snd A B).toAlgebra
  let : IsScalarTower R (A × B) A := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R (A × B) B := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite (A × B) (A ⊗[R] M) := ⟨by
    change (Submodule.restrictScalars (A × B) (⊤ : Submodule A (A ⊗[R] M))).FG
    exact Submodule.FG.restrictScalars_of_surjective
        (Module.Finite.fg_top (R := A) (M := A ⊗[R] M))
        (fun a ↦ ⟨(a, 0), rfl⟩)⟩
  have : Module.Finite (A × B) (B ⊗[R] M) := ⟨by
    change (Submodule.restrictScalars (A × B) (⊤ : Submodule B (B ⊗[R] M))).FG
    exact Submodule.FG.restrictScalars_of_surjective
        (Module.Finite.fg_top (R := B) (M := B ⊗[R] M))
        (fun b ↦ ⟨(0, b), rfl⟩)⟩
  exact Module.Finite.equiv (TensorProduct.prodLeft R (A × B) A B M).symm

/-- The base change of the kernel of a finite free presentation of a flat module is finite,
as soon as the base change of the module is finite projective. -/
private lemma finite_baseChange_kernel_of_finite_projective
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (n : ℕ) (p : (Fin n → R) →ₗ[R] M) (hp : Function.Surjective p)
    [Module.Finite A (A ⊗[R] M)] [Module.Projective A (A ⊗[R] M)] :
    Module.Finite A (A ⊗[R] LinearMap.ker p) := by
  let q := LinearMap.baseChange A p
  have hq : Function.Surjective q := by
    simp only [q, LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective A hp
  let b := LinearMap.baseChange A (LinearMap.ker p).subtype
  have hbinj : Function.Injective b := by
    simp only [b, LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_injective_of_exact_of_flat p hp _
      (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map p) A
  have hrange : LinearMap.range b = LinearMap.ker q := by
    have hex := lTensor_exact A (LinearMap.exact_subtype_ker_map p) hp
    ext x
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      change (LinearMap.lTensor A p)
          ((LinearMap.lTensor A (LinearMap.ker p).subtype) y) = 0
      rw [← LinearMap.comp_apply, hex.linearMap_comp_eq_zero, LinearMap.zero_apply]
    · intro hx
      exact (hex x).mp hx
  let e : (A ⊗[R] LinearMap.ker p) ≃ₗ[A] LinearMap.ker q :=
    (LinearEquiv.ofInjective b hbinj).trans (LinearEquiv.ofEq _ _ hrange)
  have : Module.FinitePresentation A (A ⊗[R] M) :=
    Module.finitePresentation_of_projective A (A ⊗[R] M)
  have : Module.Finite A (LinearMap.ker q) :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker q hq)
  exact Module.Finite.equiv e.symm

/-- Let `(R → S, f)` be a Beauville--Laszlo glueing pair. An `R`-module `M` is finite
projective if and only if its scalar extension to `S` is finite projective over `S` and its
localization away from `f` is finite projective over `R_f`. -/
@[stacks 0BP6]
public theorem finite_projective_iff_baseChange_and_localization
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (f : R)
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    (M : Type w) [AddCommGroup M] [Module R M] :
    (Module.Finite R M ∧ Module.Projective R M) ↔
      ((Module.Finite S (S ⊗[R] M) ∧ Module.Projective S (S ⊗[R] M)) ∧
        (Module.Finite (Localization.Away f) (LocalizedModule.Away f M) ∧
          Module.Projective (Localization.Away f) (LocalizedModule.Away f M))) := by
  constructor
  · rintro ⟨hfin, hproj⟩
    have hfinAway : Module.Finite (Localization.Away f) (LocalizedModule.Away f M) :=
      Module.Finite.equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm
    have hprojAway : Module.Projective (Localization.Away f) (LocalizedModule.Away f M) :=
      Module.Projective.of_equiv
        (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm
    exact ⟨⟨inferInstance, inferInstance⟩, hfinAway, hprojAway⟩
  · rintro ⟨⟨hfinS, hprojS⟩, ⟨hfinAway, hprojAway⟩⟩
    have hflat : Module.Flat R M :=
      (flat_iff_flat_baseChange_and_localization R S f hquot hglue M).2
        ⟨inferInstance, inferInstance⟩
    have hquot' := bijective_quotientMap_of_quotientPowMap_bijective f hquot
    have hprod : Module.Finite (S × Localization.Away f)
        ((S × Localization.Away f) ⊗[R] M) := by
      have : Module.Finite (Localization.Away f)
          (Localization.Away f ⊗[R] M) :=
        Module.Finite.equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) M)
      exact finite_tensorProduct_prod_of_finite
    have hfin : Module.Finite R M :=
      (finite_iff_tensorProduct_prod_away_of_quotientMap_bijective R f).1
        S hquot' M |>.2 hprod
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
    have hkerS : Module.Finite S (S ⊗[R] LinearMap.ker p) :=
      finite_baseChange_kernel_of_finite_projective n p hp
    have hkerAway : Module.Finite (Localization.Away f)
        (Localization.Away f ⊗[R] LinearMap.ker p) := by
      have : Module.Finite (Localization.Away f)
          (Localization.Away f ⊗[R] M) :=
        Module.Finite.equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) M)
      have : Module.Projective (Localization.Away f)
          (Localization.Away f ⊗[R] M) :=
        Module.Projective.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) M)
      exact finite_baseChange_kernel_of_finite_projective n p hp
    have hkerProd : Module.Finite (S × Localization.Away f)
        ((S × Localization.Away f) ⊗[R] LinearMap.ker p) :=
      finite_tensorProduct_prod_of_finite
    have hker : Module.Finite R (LinearMap.ker p) :=
      (finite_iff_tensorProduct_prod_away_of_quotientMap_bijective R f).1
        S hquot' (LinearMap.ker p) |>.2 hkerProd
    have : Module.FinitePresentation R M :=
      Module.finitePresentation_of_surjective p hp (Module.Finite.iff_fg.mp hker)
    exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end

end BeauvilleLaszlo

end
