module

public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleProduct
public import StacksFrontier.RingTheory.TraceElement.Independence

/-!
# Trace elements of the factors of a product

Let `B` and `C` be flat quasi-finite algebras over a Noetherian ring `A`. The relative
dualizing module of `B × C` is the product of the two relative dualizing modules, by Tag 0BT5.
This file shows that a trace element of the product restricts to a trace element of each
factor.

Both statements reduce to the case of the product factorization `A → B' × C' → B × C`, by the
independence of the trace-element condition of the chosen factorization. For that factorization
the computation is explicit: a test datum for the first factor, consisting of a Noetherian
`A`-algebra `A₁` and a decomposition `A₁ ⊗_A B ≃ C₀ × D`, becomes a test datum for the product
by adjoining `A₁ ⊗_A C` to the complementary factor, and the restriction of a product element to
`C₀` only sees its first component.

## Main results

* `Stacks.Discriminant.isTraceElement_fst` and `Stacks.Discriminant.isTraceElement_snd`:
  Tag 0BT9, a trace element of a product restricts to a trace element of each factor.

## Implementation notes

Mathlib has `RingEquiv.prodComm` and `AlgEquiv.prodCongr` but no `AlgEquiv.prodComm`, so the
commutativity of a product of algebras is supplied here as `AlgEquiv.prodComm`.

The intermediate algebra of `Stacks.Discriminant.productFiniteOpenFactorization FB FC` is the
product of the two intermediate algebras, but its algebra structure is assembled from the two
factors' own fields rather than synthesized as `Prod.algebra`. The two agree definitionally and
not syntactically, so the computations below are arranged to go through `exact` and term-level
congruence, which see that identification, rather than through `rw`, which does not.

## References

* [Stacks Project, Tag 0BT9](https://stacks.math.columbia.edu/tag/0BT9)
* [Stacks Project, Tag 0BT5](https://stacks.math.columbia.edu/tag/0BT5)
-/

@[expose] public section

universe u v w x y z s t r

open scoped TensorProduct

/-- Commutativity of a product of two algebras over a common base. -/
def AlgEquiv.prodComm (R A B : Type*) [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] : (A × B) ≃ₐ[R] B × A :=
  AlgEquiv.ofRingEquiv (f := (RingEquiv.prodComm : A × B ≃+* B × A)) (fun _ => rfl)

/-- `AlgEquiv.prodComm R A B` sends `x` to `(x.2, x.1)`. -/
@[simp]
theorem AlgEquiv.prodComm_apply (R A B : Type*) [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (x : A × B) : AlgEquiv.prodComm R A B x = (x.2, x.1) := rfl

namespace Stacks.Discriminant

/-- Associativity of a triple product of algebras, in the form that turns a two-factor
decomposition of one factor into a two-factor decomposition of the whole product. -/
def prodAssocAlgEquiv (R A B C : Type*) [CommSemiring R] [Semiring A] [Semiring B]
    [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C] :
    ((A × B) × C) ≃ₐ[R] A × (B × C) :=
  AlgEquiv.ofRingEquiv (f :=
    { toFun := fun value => (value.1.1, (value.1.2, value.2))
      invFun := fun value => ((value.1, value.2.1), value.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }) (fun _ => rfl)

/-- Two additive maps out of a tensor product that agree on pure tensors are equal. -/
private theorem tensor_apply_eq_of_tmul_eq {R M N P F G : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [AddCommMonoid P]
    [FunLike F (M ⊗[R] N) P] [FunLike G (M ⊗[R] N) P] [AddMonoidHomClass F (M ⊗[R] N) P]
    [AddMonoidHomClass G (M ⊗[R] N) P] (f : F) (g : G)
    (h : ∀ (m : M) (n : N), f (m ⊗ₜ[R] n) = g (m ⊗ₜ[R] n)) (x : M ⊗[R] N) : f x = g x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul => exact h _ _

attribute [local instance] algebraDualModule

variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
  [Module.Flat A (B × C)]
  [Algebra.QuasiFinite A (B × C)] [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A C]

/-- **Stacks Project, Tag 0BT9.** A trace element of the relative dualizing module of a
product restricts to a trace element on the first factor. -/
@[stacks 0BT9 "trace_product_factors"]
theorem isTraceElement_fst [Module.Flat A B]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    {τ : dualizingModule F}
    (hτ : IsTraceElement.{u, max v w, x, s, t, max r (max s w)} F τ) :
    IsTraceElement.{u, v, y, s, t, r} FB ((dualizingModuleProdEquiv F FB FC τ).1) := by
  classical
  let G := productFiniteOpenFactorization FB FC
  have hG : IsTraceElement.{u, max v w, max y z, s, t, max r (max s w)} G
      (dualizingModuleEquiv F G τ) := (isTraceElement_congr F G τ).mp hτ
  have hcanonical : ∀ ω : dualizingModule G,
      IsTraceElement.{u, max v w, max y z, s, t, max r (max s w)} G ω →
      IsTraceElement.{u, v, y, s, t, r} FB ((dualizingModuleProdEquiv G FB FC ω).1) := by
    intro ω hω A₁ _ _ _ C₀ D _ _ _ _ e hfinite
    let G₁ := FiniteOpenFactorization.baseChange G A₁
    let F₁ := FiniteOpenFactorization.baseChange FB A₁
    let T := A₁ ⊗[A] C
    let e' : (A₁ ⊗[A] (B × C)) ≃ₐ[A₁] C₀ × (D × T) :=
      (Algebra.TensorProduct.prodRight A A₁ A₁ B C).trans
        ((AlgEquiv.prodCongr e (AlgEquiv.refl : T ≃ₐ[A₁] T)).trans
          (prodAssocAlgEquiv A₁ C₀ D T))
    let middleEquiv : G₁.middle ≃ₐ[A₁] F₁.middle × (A₁ ⊗[A] FC.middle) :=
      Algebra.TensorProduct.prodRight A A₁ A₁ FB.middle FC.middle
    let algProd : Algebra G₁.middle C₀ :=
      ((RingHom.fst C₀ (D × T)).comp
        (e'.toRingEquiv.toRingHom.comp (algebraMap G₁.middle (A₁ ⊗[A] (B × C))))).toAlgebra
    let algFirst : Algebra F₁.middle C₀ :=
      ((RingHom.fst C₀ D).comp
        (e.toRingEquiv.toRingHom.comp (algebraMap F₁.middle (A₁ ⊗[A] B)))).toAlgebra
    let : Algebra G₁.middle C₀ := algProd
    have : Module.Finite A₁ C₀ := hfinite
    obtain ⟨hprojective, hmfinite, hmprojective, htrace⟩ := hω A₁ C₀ (D × T) e' hfinite
    let lprod := finiteFactorRestriction G A₁ C₀ (D × T) e'
      (by intro; rfl) hfinite hprojective hmfinite hmprojective
    have hmap : ∀ scalar : G₁.middle,
        @algebraMap G₁.middle C₀ _ _ algProd scalar =
          @algebraMap F₁.middle C₀ _ _ algFirst (middleEquiv scalar).1 := by
      exact tensor_apply_eq_of_tmul_eq (@algebraMap G₁.middle C₀ _ _ algProd)
        ((@algebraMap F₁.middle C₀ _ _ algFirst).comp
          ((RingHom.fst _ _).comp middleEquiv.toRingEquiv.toRingHom)) (fun _ _ => rfl)
    have : Module.Finite G₁.middle C₀ := hmfinite
    have : Module.Projective G₁.middle C₀ := hmprojective
    let : Algebra F₁.middle C₀ := algFirst
    obtain ⟨hfiniteFirst, hprojectiveFirst, htr⟩ :=
      exists_finiteProjectiveTrace_of_prodEquiv middleEquiv.toRingEquiv hmap
    have : Module.Finite F₁.middle C₀ := hfiniteFirst
    have : Module.Projective F₁.middle C₀ := hprojectiveFirst
    let lfirst := finiteFactorRestriction FB A₁ C₀ D e
      (by intro; rfl) hfinite hprojective hfiniteFirst hprojectiveFirst
    refine ⟨hprojective, hfiniteFirst, hprojectiveFirst, ?_⟩
    have hbridge : ∀ element : dualizingModule G,
        lprod.1 (dualizingModule.baseChange G A₁ element) =
          lfirst.1 (dualizingModule.baseChange FB A₁
            ((dualizingModuleProdEquiv G FB FC element).1)) := by
      refine tensor_apply_eq_of_tmul_eq
        ((AddMonoidHom.ofClass lprod.1).comp
          (AddMonoidHom.ofClass (dualizingModule.baseChange G A₁)))
        ((AddMonoidHom.ofClass lfirst.1).comp
          ((AddMonoidHom.ofClass (dualizingModule.baseChange FB A₁)).comp
            ((AddMonoidHom.fst _ _).comp
              (AddMonoidHom.ofClass (dualizingModuleProdEquiv G FB FC))))) ?_
      rintro functional ⟨left, right⟩
      have hcomponent := dualizingModuleProdEquiv_tmul G FB FC
        (AlgEquiv.refl : (FB.middle × FC.middle) ≃ₐ[A] G.middle)
        (by intro; rfl) functional left right
      let functionalFirst : Module.Dual A FB.middle :=
        functional.comp ((AlgEquiv.refl : (FB.middle × FC.middle) ≃ₐ[A] G.middle).toLinearMap
          ∘ₗ LinearMap.inl A FB.middle FC.middle)
      have hdual : ∀ scalar : F₁.middle,
          functional.baseChange A₁ (middleEquiv.symm (scalar, 0)) =
            functionalFirst.baseChange A₁ scalar := by
        intro scalar
        induction scalar using TensorProduct.inductionOn with
        | add left right hleft hright =>
          refine (congrArg (⇑(functional.baseChange A₁))
            (congrArg middleEquiv.symm
              (show ((left + right : F₁.middle), (0 : A₁ ⊗[A] FC.middle)) =
                (left, 0) + (right, 0) by simp))).trans ?_
          refine ((congrArg (⇑(functional.baseChange A₁)) (map_add middleEquiv.symm _ _)).trans
            (map_add (functional.baseChange A₁) _ _)).trans ?_
          exact (congrArg₂ (· + ·) hleft hright).trans
            (map_add (functionalFirst.baseChange A₁) left right).symm
        | tmul scalar value =>
          have heq : middleEquiv.symm (scalar ⊗ₜ[A] value, 0) =
              scalar ⊗ₜ[A] ((value, 0) : G.middle) := by
            refine middleEquiv.injective ?_
            rw [middleEquiv.apply_symm_apply]
            change (scalar ⊗ₜ[A] value, 0) =
              (Algebra.TensorProduct.prodRight A A₁ A₁ FB.middle FC.middle)
                (scalar ⊗ₜ[A] ((value, 0) : FB.middle × FC.middle))
            rw [Algebra.TensorProduct.prodRight_tmul, TensorProduct.tmul_zero]
          rw [heq]
          simp only [Module.Dual.baseChange_apply_tmul]
          rfl
      have hcoeff : (e' ((1 : A₁) ⊗ₜ[A] ((left, right) : B × C))).1 =
          (e ((1 : A₁) ⊗ₜ[A] left)).1 := by
        simp only [e', AlgEquiv.trans_apply, Algebra.TensorProduct.prodRight_tmul,
          AlgEquiv.prodCongr_apply]
        rfl
      have hstep : ∀ value : C₀, (functional.baseChange A₁)
            (finiteProjectiveTrace G₁.middle C₀ (Algebra.lmul G₁.middle C₀
              ((e' ((1 : A₁) ⊗ₜ[A] ((left, right) : B × C))).1 * value))) =
          (functionalFirst.baseChange A₁)
            (finiteProjectiveTrace F₁.middle C₀ (Algebra.lmul F₁.middle C₀
              ((e ((1 : A₁) ⊗ₜ[A] left)).1 * value))) := by
        intro value
        rw [hcoeff, htr]
        exact hdual _
      change lprod.1 (dualizingModule.baseChange G A₁
        (dualizingModule.tmul G functional ((left, right) : B × C))) =
          lfirst.1 (dualizingModule.baseChange FB A₁
            ((dualizingModuleProdEquiv G FB FC
              (dualizingModule.tmul G functional ((left, right) : B × C))).1))
      rw [hcomponent]
      simp only [dualizingModule.baseChange_tmul]
      exact LinearMap.ext fun value =>
        (lprod.2 _ _ value).trans ((hstep value).trans (lfirst.2 _ _ value).symm)
    exact (hbridge ω).symm.trans htrace
  have hfirst := hcanonical _ hG
  have hn := dualizingModuleProdEquiv_naturality F G FB FB FC FC τ
  rw [dualizingModuleEquiv_refl, dualizingModuleEquiv_refl] at hn
  simpa only [congrArg Prod.fst hn, LinearEquiv.refl_apply] using hfirst

/-- **Stacks Project, Tag 0BT9.** A trace element of the relative dualizing module of a
product restricts to a trace element on the second factor. -/
@[stacks 0BT9 "trace_product_factors"]
theorem isTraceElement_snd [Module.Flat A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    {τ : dualizingModule F}
    (hτ : IsTraceElement.{u, max v w, x, s, t, max r (max s v)} F τ) :
    IsTraceElement.{u, w, z, s, t, r} FC ((dualizingModuleProdEquiv F FB FC τ).2) := by
  classical
  let G := productFiniteOpenFactorization FB FC
  have hG : IsTraceElement.{u, max v w, max y z, s, t, max r (max s v)} G
      (dualizingModuleEquiv F G τ) := (isTraceElement_congr F G τ).mp hτ
  have hcanonical : ∀ ω : dualizingModule G,
      IsTraceElement.{u, max v w, max y z, s, t, max r (max s v)} G ω →
      IsTraceElement.{u, w, z, s, t, r} FC ((dualizingModuleProdEquiv G FB FC ω).2) := by
    intro ω hω A₁ _ _ _ C₀ D _ _ _ _ e hfinite
    let G₁ := FiniteOpenFactorization.baseChange G A₁
    let F₁ := FiniteOpenFactorization.baseChange FC A₁
    let T := A₁ ⊗[A] B
    let e' : (A₁ ⊗[A] (B × C)) ≃ₐ[A₁] C₀ × (D × T) :=
      (Algebra.TensorProduct.prodRight A A₁ A₁ B C).trans
        ((AlgEquiv.prodComm A₁ T (A₁ ⊗[A] C)).trans
          ((AlgEquiv.prodCongr e (AlgEquiv.refl : T ≃ₐ[A₁] T)).trans
            (prodAssocAlgEquiv A₁ C₀ D T)))
    let middleEquiv : G₁.middle ≃ₐ[A₁] F₁.middle × (A₁ ⊗[A] FB.middle) :=
      (Algebra.TensorProduct.prodRight A A₁ A₁ FB.middle FC.middle).trans
        (AlgEquiv.prodComm A₁ (A₁ ⊗[A] FB.middle) (A₁ ⊗[A] FC.middle))
    let algProd : Algebra G₁.middle C₀ :=
      ((RingHom.fst C₀ (D × T)).comp
        (e'.toRingEquiv.toRingHom.comp (algebraMap G₁.middle (A₁ ⊗[A] (B × C))))).toAlgebra
    let algFirst : Algebra F₁.middle C₀ :=
      ((RingHom.fst C₀ D).comp
        (e.toRingEquiv.toRingHom.comp (algebraMap F₁.middle (A₁ ⊗[A] C)))).toAlgebra
    let : Algebra G₁.middle C₀ := algProd
    have : Module.Finite A₁ C₀ := hfinite
    obtain ⟨hprojective, hmfinite, hmprojective, htrace⟩ := hω A₁ C₀ (D × T) e' hfinite
    let lprod := finiteFactorRestriction G A₁ C₀ (D × T) e'
      (by intro; rfl) hfinite hprojective hmfinite hmprojective
    have hmap : ∀ scalar : G₁.middle,
        @algebraMap G₁.middle C₀ _ _ algProd scalar =
          @algebraMap F₁.middle C₀ _ _ algFirst (middleEquiv scalar).1 := by
      exact tensor_apply_eq_of_tmul_eq (@algebraMap G₁.middle C₀ _ _ algProd)
        ((@algebraMap F₁.middle C₀ _ _ algFirst).comp
          ((RingHom.fst _ _).comp middleEquiv.toRingEquiv.toRingHom)) (fun _ _ => rfl)
    have : Module.Finite G₁.middle C₀ := hmfinite
    have : Module.Projective G₁.middle C₀ := hmprojective
    let : Algebra F₁.middle C₀ := algFirst
    obtain ⟨hfiniteFirst, hprojectiveFirst, htr⟩ :=
      exists_finiteProjectiveTrace_of_prodEquiv middleEquiv.toRingEquiv hmap
    have : Module.Finite F₁.middle C₀ := hfiniteFirst
    have : Module.Projective F₁.middle C₀ := hprojectiveFirst
    let lfirst := finiteFactorRestriction FC A₁ C₀ D e
      (by intro; rfl) hfinite hprojective hfiniteFirst hprojectiveFirst
    refine ⟨hprojective, hfiniteFirst, hprojectiveFirst, ?_⟩
    have hbridge : ∀ element : dualizingModule G,
        lprod.1 (dualizingModule.baseChange G A₁ element) =
          lfirst.1 (dualizingModule.baseChange FC A₁
            ((dualizingModuleProdEquiv G FB FC element).2)) := by
      refine tensor_apply_eq_of_tmul_eq
        ((AddMonoidHom.ofClass lprod.1).comp
          (AddMonoidHom.ofClass (dualizingModule.baseChange G A₁)))
        ((AddMonoidHom.ofClass lfirst.1).comp
          ((AddMonoidHom.ofClass (dualizingModule.baseChange FC A₁)).comp
            ((AddMonoidHom.snd _ _).comp
              (AddMonoidHom.ofClass (dualizingModuleProdEquiv G FB FC))))) ?_
      rintro functional ⟨left, right⟩
      have hcomponent := dualizingModuleProdEquiv_tmul G FB FC
        (AlgEquiv.refl : (FB.middle × FC.middle) ≃ₐ[A] G.middle)
        (by intro; rfl) functional left right
      let functionalFirst : Module.Dual A FC.middle :=
        functional.comp ((AlgEquiv.refl : (FB.middle × FC.middle) ≃ₐ[A] G.middle).toLinearMap
          ∘ₗ LinearMap.inr A FB.middle FC.middle)
      have hdual : ∀ scalar : F₁.middle,
          functional.baseChange A₁ (middleEquiv.symm (scalar, 0)) =
            functionalFirst.baseChange A₁ scalar := by
        intro scalar
        induction scalar using TensorProduct.inductionOn with
        | add left right hleft hright =>
          refine (congrArg (⇑(functional.baseChange A₁))
            (congrArg middleEquiv.symm
              (show ((left + right : F₁.middle), (0 : A₁ ⊗[A] FB.middle)) =
                (left, 0) + (right, 0) by simp))).trans ?_
          refine ((congrArg (⇑(functional.baseChange A₁)) (map_add middleEquiv.symm _ _)).trans
            (map_add (functional.baseChange A₁) _ _)).trans ?_
          exact (congrArg₂ (· + ·) hleft hright).trans
            (map_add (functionalFirst.baseChange A₁) left right).symm
        | tmul scalar value =>
          have heq : middleEquiv.symm (scalar ⊗ₜ[A] value, 0) =
              scalar ⊗ₜ[A] ((0, value) : G.middle) := by
            refine middleEquiv.injective ?_
            rw [middleEquiv.apply_symm_apply]
            change (scalar ⊗ₜ[A] value, 0) =
              ((Algebra.TensorProduct.prodRight A A₁ A₁ FB.middle FC.middle).trans
                (AlgEquiv.prodComm A₁ (A₁ ⊗[A] FB.middle) (A₁ ⊗[A] FC.middle)))
                (scalar ⊗ₜ[A] ((0, value) : FB.middle × FC.middle))
            rw [AlgEquiv.trans_apply, Algebra.TensorProduct.prodRight_tmul,
              TensorProduct.tmul_zero]
            rfl
          rw [heq]
          simp only [Module.Dual.baseChange_apply_tmul]
          rfl
      have hcoeff : (e' ((1 : A₁) ⊗ₜ[A] ((left, right) : B × C))).1 =
          (e ((1 : A₁) ⊗ₜ[A] right)).1 := by
        simp only [e', AlgEquiv.trans_apply, Algebra.TensorProduct.prodRight_tmul,
          AlgEquiv.prodCongr_apply, AlgEquiv.prodComm_apply]
        rfl
      have hstep : ∀ value : C₀, (functional.baseChange A₁)
            (finiteProjectiveTrace G₁.middle C₀ (Algebra.lmul G₁.middle C₀
              ((e' ((1 : A₁) ⊗ₜ[A] ((left, right) : B × C))).1 * value))) =
          (functionalFirst.baseChange A₁)
            (finiteProjectiveTrace F₁.middle C₀ (Algebra.lmul F₁.middle C₀
              ((e ((1 : A₁) ⊗ₜ[A] right)).1 * value))) := by
        intro value
        rw [hcoeff, htr]
        exact hdual _
      change lprod.1 (dualizingModule.baseChange G A₁
        (dualizingModule.tmul G functional ((left, right) : B × C))) =
          lfirst.1 (dualizingModule.baseChange FC A₁
            ((dualizingModuleProdEquiv G FB FC
              (dualizingModule.tmul G functional ((left, right) : B × C))).2))
      rw [hcomponent]
      simp only [dualizingModule.baseChange_tmul]
      exact LinearMap.ext fun value =>
        (lprod.2 _ _ value).trans ((hstep value).trans (lfirst.2 _ _ value).symm)
    exact (hbridge ω).symm.trans htrace
  have hfirst := hcanonical _ hG
  have hn := dualizingModuleProdEquiv_naturality F G FB FB FC FC τ
  rw [dualizingModuleEquiv_refl, dualizingModuleEquiv_refl] at hn
  simpa only [congrArg Prod.snd hn, LinearEquiv.refl_apply] using hfirst

end Stacks.Discriminant

end
