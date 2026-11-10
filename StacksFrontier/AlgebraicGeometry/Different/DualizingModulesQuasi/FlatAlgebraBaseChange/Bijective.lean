module

public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatAlgebraBaseChange.FiniteProjectiveTarget
public import StacksCore.Tactic.StacksAttribute

/-!
# Arbitrary base change for the dualizing module of a flat quasi-finite algebra

This last part of `FlatAlgebraBaseChange` proves its main theorem.

## Main results

* `Stacks.Discriminant.dualizingModule.baseChangeLinearMap_bijective`: for a flat quasi-finite
  algebra over a Noetherian base, `baseChangeLinearMap` is bijective, so forming the relative
  dualizing module commutes with arbitrary base change.

## Implementation notes

The finite flat case is the heart of the matter: there `B` is finite locally free over `A`, the
dualizing module is the dual `A`-module `Hom_A(B, A)`, and the dual of a finitely generated
projective module commutes with arbitrary base change.

The quasi-finite case is reduced to that one locally on `Spec B₁`, since bijectivity of a module
map is detected on localizations at primes. Over a prime of `B₁` the local structure theory of
quasi-finite algebras supplies an étale `A → A'` and a prime of `A'` with the same residue field
for which `A' ⊗[A] B` splits off a factor that is finite and projective over `A'` and contains
the prime in question. The square of base change maps for `A → A' → A' ⊗[A] A₁` and
`A → A₁ → A' ⊗[A] A₁` commutes by Tag 0BVC and its vertical arrows are isomorphisms by
Tag 0BT3, while `B₁ → A' ⊗[A] B₁` is étale and hence flat, so the question descends.

Transport along the ring isomorphisms identifying the various iterated tensor products is
packaged by `tensorEquivAlong`, the semilinear analogue of `LinearEquiv.lTensor` for a ring
isomorphism of the scalars that is compatible with a common algebra over them.

## References

* [Stacks Project, Tag 0BVF](https://stacks.math.columbia.edu/tag/0BVF)
* [Stacks Project, Tag 0BVB](https://stacks.math.columbia.edu/tag/0BVB)
* [Stacks Project, Tag 0BT3](https://stacks.math.columbia.edu/tag/0BT3)
-/

@[expose] public section


open scoped TensorProduct

universe u v w x y

namespace Stacks.Discriminant

namespace dualizingModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

open Topology CategoryTheory Opposite AlgebraicGeometry

private lemma quasiFiniteAt_of_finiteOpenFactorization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {p : Ideal A} {q : Ideal B} [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    Algebra.QuasiFiniteAt A q := by
  let : Algebra.QuasiFinite A B :=
    (finiteType_quasiFinite_of_finiteOpenFactorization F).2
  infer_instance


private theorem lTensor_bijective_of_bijective
    {R T M N : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (h : Function.Bijective f) :
    Function.Bijective (LinearMap.lTensor T f) := by
  let e := LinearEquiv.ofBijective f h
  have he : LinearMap.lTensor T f =
      (e.toLinearMap.baseChange T).restrictScalars R := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp [hz, hz']
    | tmul t m => simp [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul, e]
  rw [he]
  exact (e.baseChange R T).bijective

private theorem lTensor_bijective_of_lTensor
    {R U T M N : Type*} [CommRing R] [CommRing U] [CommRing T]
    [Algebra R U] [Algebra U T] [Algebra R T] [IsScalarTower R U T]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (h : Function.Bijective (LinearMap.lTensor U f)) :
    Function.Bijective (LinearMap.lTensor T f) := by
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R U T T M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R U T T N
  let fU : U ⊗[R] M →ₗ[U] U ⊗[R] N :=
    TensorProduct.AlgebraTensorModule.lTensor U U f
  let fT : T ⊗[R] M →ₗ[T] T ⊗[R] N :=
    TensorProduct.AlgebraTensorModule.lTensor T T f
  let fUT : T ⊗[U] (U ⊗[R] M) →ₗ[T] T ⊗[U] (U ⊗[R] N) :=
    TensorProduct.AlgebraTensorModule.lTensor T T fU
  have hU : Function.Bijective fU := by
    change Function.Bijective (LinearMap.lTensor U f)
    exact h
  have hT : Function.Bijective fUT :=
    lTensor_bijective_of_bijective fU hU
  have hcomm : fT.comp eM.toLinearMap = eN.toLinearMap.comp fUT := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, LinearMap.comp_apply, hz, hz']
    | tmul t m =>
      induction m using TensorProduct.inductionOn with
      | add m m' hm hm' =>
        simp only [TensorProduct.tmul_add, map_add, hm, hm']
      | tmul u m =>
        simp [fT, fUT, fU, eM, eN,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  have hcomp : Function.Bijective (fT.comp eM.toLinearMap) := by
    rw [hcomm]
    exact eN.bijective.comp hT
  exact (Function.Bijective.of_comp_iff _ eM.bijective).mp hcomp

private noncomputable def towerTargetRingEquiv
    {A A₁ A' B : Type*} [CommRing A] [CommRing A₁] [CommRing A'] [CommRing B]
    [Algebra A A₁] [Algebra A A'] [Algebra A B] :
    let B₁ := A₁ ⊗[A] B
    let A₂ := A₁ ⊗[A] A'
    let B₂ := A₂ ⊗[A] B
    B₂ ≃+* A' ⊗[A] B₁ := by
  let B₁ := A₁ ⊗[A] B
  let A₂ := A₁ ⊗[A] A'
  let B₂ := A₂ ⊗[A] B
  let e₁ : B₂ ≃ₐ[A₁] A₁ ⊗[A] (A' ⊗[A] B) :=
    Algebra.TensorProduct.assoc A A A₁ A₁ A' B
  letI : Algebra A₁ ((A' ⊗[A] B) ⊗[A] A₁) := Algebra.TensorProduct.rightAlgebra
  let e₂ : A₁ ⊗[A] (A' ⊗[A] B) ≃ₐ[A₁]
      (A' ⊗[A] B) ⊗[A] A₁ :=
    Algebra.TensorProduct.commRight A A₁ (A' ⊗[A] B)
  let e₃ : ((A' ⊗[A] B) ⊗[A] A₁) ≃ₐ[A']
      A' ⊗[A] (B ⊗[A] A₁) :=
    Algebra.TensorProduct.assoc A A A' A' B A₁
  let e₄ : A' ⊗[A] (B ⊗[A] A₁) ≃ₐ[A]
      A' ⊗[A] (A₁ ⊗[A] B) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := A'))
      (Algebra.TensorProduct.comm A B A₁)
  exact e₁.toRingEquiv.trans (e₂.toRingEquiv.trans
      (e₃.toRingEquiv.trans e₄.toRingEquiv))

private theorem towerTargetRingEquiv_include
    {A A₁ A' B : Type*} [CommRing A] [CommRing A₁] [CommRing A'] [CommRing B]
    [Algebra A A₁] [Algebra A A'] [Algebra A B] :
    let B₁ := A₁ ⊗[A] B
    let A₂ := A₁ ⊗[A] A'
    let B₂ := A₂ ⊗[A] B
    (towerTargetRingEquiv : B₂ ≃+* A' ⊗[A] B₁).toRingHom.comp
      (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := A₁) (B := A'))
        (AlgHom.id A B)).toRingHom =
      (Algebra.TensorProduct.includeRight : B₁ →ₐ[A] A' ⊗[A] B₁).toRingHom := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a b => rfl

section
variable {R S T M N : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R T] [Algebra S T] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N]

private def tensorMapAlong (σ : R →+* S)
    (hσ : ∀ r, algebraMap S T (σ r) = algebraMap R T r)
    (f : M →ₛₗ[σ] N) : T ⊗[R] M →ₗ[T] T ⊗[S] N := by
  let i : T →ₛₗ[σ] T :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := by intro r t; simp only [id_eq, Algebra.smul_def, hσ] }
  let g := TensorProduct.map i f
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro t z
        induction z using TensorProduct.inductionOn with
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul a m => rfl }

private theorem tensorMapAlong_tmul (σ : R →+* S)
    (hσ : ∀ r, algebraMap S T (σ r) = algebraMap R T r)
    (f : M →ₛₗ[σ] N) (t : T) (m : M) :
    tensorMapAlong σ hσ f (t ⊗ₜ[R] m) = t ⊗ₜ[S] f m := rfl

private noncomputable def tensorEquivAlong (σ : R ≃+* S)
    (hσ : ∀ r, algebraMap S T (σ r) = algebraMap R T r)
    (f : M ≃+ N) (hf : ∀ r m, f (r • m) = σ r • f m) :
    T ⊗[R] M ≃ₗ[T] T ⊗[S] N := by
  letI := RingHomInvPair.of_ringEquiv σ
  letI := RingHomInvPair.symm (σ : R →+* S) (σ.symm : S →+* R)
  let f' : M ≃ₛₗ[(σ : R →+* S)] N := { f with map_smul' := hf }
  let i : T ≃ₛₗ[(σ : R →+* S)] T :=
    { Equiv.refl T with
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r t
        change r • t = σ r • t
        simp only [Algebra.smul_def]
        rw [hσ] }
  exact LinearEquiv.ofBijective (tensorMapAlong (σ : R →+* S) hσ f'.toLinearMap)
    (TensorProduct.congr i f').bijective

private theorem tensorEquivAlong_tmul (σ : R ≃+* S)
    (hσ : ∀ r, algebraMap S T (σ r) = algebraMap R T r)
    (f : M ≃+ N) (hf : ∀ r m, f (r • m) = σ r • f m) (t : T) (m : M) :
    tensorEquivAlong σ hσ f hf (t ⊗ₜ[R] m) = t ⊗ₜ[S] f m := rfl

end


section
variable {R S T M N : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

private theorem tensorMapAlong_bijective_iff
    (hσ : ∀ r, algebraMap S T (algebraMap R S r) = algebraMap R T r)
    (f : M →ₛₗ[algebraMap R S] N) (g : S ⊗[R] M →ₗ[S] N)
    (hfg : ∀ m, g (1 ⊗ₜ[R] m) = f m) :
    Function.Bijective (tensorMapAlong (algebraMap R S) hσ f) ↔
      Function.Bijective (g.baseChange T) := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M
  have he : (tensorMapAlong (algebraMap R S) hσ f).comp e.toLinearMap =
      g.baseChange T := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t z =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul s m =>
        change (s • t) ⊗ₜ[S] f m = t ⊗ₜ[S] g (s ⊗ₜ[R] m)
        rw [TensorProduct.tmul_eq_smul_one_tmul s m, map_smul, hfg]
        exact TensorProduct.smul_tmul _ _ _
  rw [← he, LinearMap.coe_comp]
  exact (Function.Bijective.of_comp_iff _ e.bijective).symm
end




private noncomputable def baseChangeSemilinear
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ : Type*) [CommRing A₁] [Algebra A A₁] :
    dualizingModule F →ₛₗ[(Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom]
      dualizingModule (FiniteOpenFactorization.baseChange F A₁) := by
  letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  letI : Module B (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
  exact { (dualizingModule.baseChange F A₁).toAddHom with
    map_smul' := fun b m => (dualizingModule.baseChange F A₁).map_smul b m }

private noncomputable def baseChangeTo
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ T : Type*) [CommRing A₁] [Algebra A A₁]
    [CommRing T] [Algebra B T] [Algebra (A₁ ⊗[A] B) T]
    (h : ∀ b, algebraMap (A₁ ⊗[A] B) T (1 ⊗ₜ[A] b) = algebraMap B T b) :
    T ⊗[B] dualizingModule F →ₗ[T]
      T ⊗[A₁ ⊗[A] B] dualizingModule (FiniteOpenFactorization.baseChange F A₁) :=
  tensorMapAlong _ h (baseChangeSemilinear F A₁)

private theorem baseChangeTo_tmul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ T : Type*) [CommRing A₁] [Algebra A A₁]
    [CommRing T] [Algebra B T] [Algebra (A₁ ⊗[A] B) T]
    (h : ∀ b, algebraMap (A₁ ⊗[A] B) T (1 ⊗ₜ[A] b) = algebraMap B T b)
    (t : T) (m : dualizingModule F) :
    baseChangeTo F A₁ T h (t ⊗ₜ[B] m) =
      t ⊗ₜ[A₁ ⊗[A] B] dualizingModule.baseChange F A₁ m := rfl

private theorem baseChangeTo_bijective_iff
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ T : Type*) [CommRing A₁] [Algebra A A₁]
    [CommRing T] [Algebra B T] [Algebra (A₁ ⊗[A] B) T]
    (h : ∀ b, algebraMap (A₁ ⊗[A] B) T (1 ⊗ₜ[A] b) = algebraMap B T b) :
    Function.Bijective (baseChangeTo F A₁ T h) ↔
      Function.Bijective (LinearMap.lTensor T (baseChangeLinearMap F A₁)) := by
  let : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B (A₁ ⊗[A] B) T :=
    IsScalarTower.of_algebraMap_eq (fun b => (h b).symm)
  exact tensorMapAlong_bijective_iff h (baseChangeSemilinear F A₁)
    (baseChangeLinearMap F A₁) (baseChangeLinearMap_one_tmul F A₁)

private theorem baseChangeTo_bijective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ T : Type*) [CommRing A₁] [Algebra A A₁]
    [CommRing T] [Algebra B T] [Algebra (A₁ ⊗[A] B) T]
    (h : ∀ b, algebraMap (A₁ ⊗[A] B) T (1 ⊗ₜ[A] b) = algebraMap B T b)
    (hf : Function.Bijective (baseChangeLinearMap F A₁)) :
    Function.Bijective (baseChangeTo F A₁ T h) :=
  (baseChangeTo_bijective_iff F A₁ T h).mpr (lTensor_bijective_of_bijective _ hf)

private noncomputable def baseChangeTowerTo
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ A₂ T : Type*)
    [CommRing A₁] [CommRing A₂] [Algebra A A₁] [Algebra A A₂]
    [Algebra A₁ A₂] [IsScalarTower A A₁ A₂]
    [CommRing T] [Algebra (A₂ ⊗[A₁] (A₁ ⊗[A] B)) T] [Algebra (A₂ ⊗[A] B) T]
    (h : ∀ b, algebraMap (A₂ ⊗[A] B) T
      (Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B b) =
        algebraMap (A₂ ⊗[A₁] (A₁ ⊗[A] B)) T b) :
    T ⊗[A₂ ⊗[A₁] (A₁ ⊗[A] B)] dualizingModule
        (FiniteOpenFactorization.baseChange
          (FiniteOpenFactorization.baseChange F A₁) A₂) ≃ₗ[T]
      T ⊗[A₂ ⊗[A] B] dualizingModule (FiniteOpenFactorization.baseChange F A₂) := by
  let F₁₂ := FiniteOpenFactorization.baseChange
    (FiniteOpenFactorization.baseChange F A₁) A₂
  let F₂ := FiniteOpenFactorization.baseChange F A₂
  let e := dualizingModule.baseChangeTowerEquiv F A₁ A₂
  refine tensorEquivAlong (Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B).toRingEquiv
    h e.1 ?_
  intro b m
  induction m using dualizingModule.induction_on with
  | tmul φ c =>
    change e.1 (b • dualizingModule.tmul F₁₂ φ c) =
      (Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B b) •
        e.1 (dualizingModule.tmul F₁₂ φ c)
    rw [dualizingModule.smul_tmul, e.2, e.2, dualizingModule.smul_tmul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem baseChangeTo_tower_bijective_iff
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ A₂ T : Type*)
    [CommRing A₁] [CommRing A₂] [Algebra A A₁] [Algebra A A₂]
    [Algebra A₁ A₂] [IsScalarTower A A₁ A₂]
    [CommRing T] [Algebra B T] [Algebra (A₁ ⊗[A] B) T]
    [Algebra (A₂ ⊗[A₁] (A₁ ⊗[A] B)) T] [Algebra (A₂ ⊗[A] B) T]
    (h₁ : ∀ b, algebraMap (A₁ ⊗[A] B) T (1 ⊗ₜ[A] b) = algebraMap B T b)
    (h₁₂ : ∀ b, algebraMap (A₂ ⊗[A₁] (A₁ ⊗[A] B)) T (1 ⊗ₜ[A₁] b) =
      algebraMap (A₁ ⊗[A] B) T b)
    (h₂ : ∀ b, algebraMap (A₂ ⊗[A] B) T (1 ⊗ₜ[A] b) = algebraMap B T b)
    (h : ∀ b, algebraMap (A₂ ⊗[A] B) T
      (Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B b) =
        algebraMap (A₂ ⊗[A₁] (A₁ ⊗[A] B)) T b)
    (hf : Function.Bijective (baseChangeTo
      (FiniteOpenFactorization.baseChange F A₁) A₂ T h₁₂)) :
    Function.Bijective (baseChangeTo F A₂ T h₂) ↔
      Function.Bijective (baseChangeTo F A₁ T h₁) := by
  let e := baseChangeTowerTo F A₁ A₂ T h
  let f := baseChangeTo (FiniteOpenFactorization.baseChange F A₁) A₂ T h₁₂
  have hc : e.toLinearMap.comp (f.comp (baseChangeTo F A₁ T h₁)) =
      baseChangeTo F A₂ T h₂ := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t m =>
      change t ⊗ₜ[A₂ ⊗[A] B]
        (dualizingModule.baseChangeTowerEquiv F A₁ A₂).1
          (dualizingModule.baseChange
            (FiniteOpenFactorization.baseChange F A₁) A₂
              (dualizingModule.baseChange F A₁ m)) = _
      rw [dualizingModule.baseChange_comp]
      rfl
  constructor
  · intro hbij
    have hc' : Function.Bijective (e.toLinearMap.comp (f.comp (baseChangeTo F A₁ T h₁))) :=
      hc ▸ hbij
    exact (Function.Bijective.of_comp_iff' (e.bijective.comp hf)
      (baseChangeTo F A₁ T h₁)).mp hc'
  · intro hbij
    rw [← hc]
    exact e.bijective.comp (hf.comp hbij)

private noncomputable def targetAwayTo
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (e : B) (T : Type*)
    [CommRing T] [Algebra B T] [Algebra (Localization.Away e) T]
    [IsScalarTower B (Localization.Away e) T] :
    T ⊗[B] dualizingModule F ≃ₗ[T]
      T ⊗[Localization.Away e] dualizingModule (targetAwayFactorization F e) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange B (Localization.Away e) T T
    (dualizingModule F)).symm.trans ((targetAwayDualizingEquiv F e).baseChange _ T)

private theorem targetAwayTo_tmul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (e : B) (T : Type*)
    [CommRing T] [Algebra B T] [Algebra (Localization.Away e) T]
    [IsScalarTower B (Localization.Away e) T]
    (t : T) (φ : Module.Dual A F.middle) (b : B) :
    targetAwayTo F e T (t ⊗ₜ[B] dualizingModule.tmul F φ b) =
      t ⊗ₜ[Localization.Away e] dualizingModule.tmul (targetAwayFactorization F e) φ
        (algebraMap B (Localization.Away e) b) := by
  simp only [targetAwayTo, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, targetAwayDualizingEquiv_tmul]




private noncomputable def targetAwayBaseChangeRingEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ : Type*) [CommRing A₁] [Algebra A A₁] (e : B) :
    (A₁ ⊗[A] Localization.Away e) ≃+* Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B) := by
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let G₁ := FiniteOpenFactorization.baseChange (targetAwayFactorization F e) A₁
  let H₁ := targetAwayFactorization F₁ (1 ⊗ₜ[A] e)
  let C := A₁ ⊗[A] F.middle
  let D := A₁ ⊗[A] Localization.Away e
  let U := Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)
  letI : Algebra C D := G₁.algebraTarget
  letI : Algebra C U := H₁.algebraTarget
  exact (targetAwayBaseChangeAlgEquiv F A₁ e).toRingEquiv

private theorem targetAwayBaseChangeAlgEquiv_one_tmul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ : Type*) [CommRing A₁] [Algebra A A₁]
    (e b : B) :
    targetAwayBaseChangeRingEquiv F A₁ e (1 ⊗ₜ[A] algebraMap B (Localization.Away e) b) =
      algebraMap (A₁ ⊗[A] B) (Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B))
        (1 ⊗ₜ[A] b) := by
  change IsLocalization.Away.tensorProductEquivTMulRight A A₁ e
    (Localization.Away e) (1 ⊗ₜ[A] algebraMap B (Localization.Away e) b) = _
  rw [IsLocalization.Away.tensorProductEquivTMulRight_tmul]

private noncomputable def targetAwayBaseChangeTo
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ T : Type*) [CommRing A₁] [Algebra A A₁]
    (e : B) [CommRing T]
    [Algebra (A₁ ⊗[A] Localization.Away e) T]
    [Algebra (Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)) T]
    (h : ∀ d, algebraMap (Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)) T
        (targetAwayBaseChangeRingEquiv F A₁ e d) =
      algebraMap (A₁ ⊗[A] Localization.Away e) T d) :
    T ⊗[A₁ ⊗[A] Localization.Away e] dualizingModule
        (FiniteOpenFactorization.baseChange (targetAwayFactorization F e) A₁) ≃ₗ[T]
      T ⊗[Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)] dualizingModule
        (targetAwayFactorization (FiniteOpenFactorization.baseChange F A₁)
          (1 ⊗ₜ[A] e)) := by
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let G₁ := FiniteOpenFactorization.baseChange (targetAwayFactorization F e) A₁
  let H₁ := targetAwayFactorization F₁ (1 ⊗ₜ[A] e)
  let C := A₁ ⊗[A] F.middle
  let D := A₁ ⊗[A] Localization.Away e
  let U := Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)
  letI : Algebra C D := G₁.algebraTarget
  letI : Algebra C U := H₁.algebraTarget
  let eD := targetAwayBaseChangeRingEquiv F A₁ e
  letI : Module U (dualizingModule G₁) := Module.compHom _ eD.symm.toRingHom
  let E : dualizingModule G₁ ≃ₗ[U] dualizingModule H₁ :=
    targetAwayBaseChangeDualizingEquiv F A₁ e
  refine tensorEquivAlong eD h E.toAddEquiv ?_
  intro d m
  have hm := E.map_smul (eD d) m
  change E (eD.symm (eD d) • m) = eD d • E m at hm
  rw [RingEquiv.symm_apply_apply] at hm
  change E (d • m) = eD d • E m
  exact hm

private theorem targetAwayBaseChangeTo_tmul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ T : Type*) [CommRing A₁] [Algebra A A₁]
    (e : B) [CommRing T]
    [Algebra (A₁ ⊗[A] Localization.Away e) T]
    [Algebra (Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)) T]
    (h : ∀ d, algebraMap (Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)) T
        (targetAwayBaseChangeRingEquiv F A₁ e d) =
      algebraMap (A₁ ⊗[A] Localization.Away e) T d)
    (t : T) (φ : Module.Dual A₁ (A₁ ⊗[A] F.middle))
    (d : A₁ ⊗[A] Localization.Away e) :
    targetAwayBaseChangeTo F A₁ T e h
      (t ⊗ₜ[A₁ ⊗[A] Localization.Away e] dualizingModule.tmul
        (FiniteOpenFactorization.baseChange (targetAwayFactorization F e) A₁) φ d) =
      t ⊗ₜ[Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)] dualizingModule.tmul
        (targetAwayFactorization (FiniteOpenFactorization.baseChange F A₁)
          (1 ⊗ₜ[A] e)) φ (targetAwayBaseChangeRingEquiv F A₁ e d) := rfl

private theorem baseChangeTo_bijective_of_targetAway
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) (A₁ T : Type*) [CommRing A₁] [Algebra A A₁]
    (e : B) [CommRing T]
    [Algebra B T] [Algebra (A₁ ⊗[A] B) T]
    [Algebra (Localization.Away e) T] [IsScalarTower B (Localization.Away e) T]
    [Algebra (A₁ ⊗[A] Localization.Away e) T]
    [Algebra (Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)) T]
    [IsScalarTower (A₁ ⊗[A] B) (Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)) T]
    (hB : ∀ b, algebraMap (A₁ ⊗[A] B) T (1 ⊗ₜ[A] b) = algebraMap B T b)
    (hD : ∀ d, algebraMap (A₁ ⊗[A] Localization.Away e) T (1 ⊗ₜ[A] d) =
      algebraMap (Localization.Away e) T d)
    (hE : ∀ d, algebraMap (Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)) T
        (targetAwayBaseChangeRingEquiv F A₁ e d) =
      algebraMap (A₁ ⊗[A] Localization.Away e) T d)
    (hf : Function.Bijective (baseChangeLinearMap (targetAwayFactorization F e) A₁)) :
    Function.Bijective (baseChangeTo F A₁ T hB) := by
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let G := targetAwayFactorization F e
  let a := targetAwayTo F e T
  let b := targetAwayTo F₁ (1 ⊗ₜ[A] e) T
  let c := targetAwayBaseChangeTo F A₁ T e hE
  let f := baseChangeTo F A₁ T hB
  let g := baseChangeTo G A₁ T hD
  have hc : b.toLinearMap.comp f = c.toLinearMap.comp (g.comp a.toLinearMap) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t m =>
      induction m using dualizingModule.induction_on with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul φ d =>
        have ha := targetAwayTo_tmul F e T t φ d
        have hb := targetAwayTo_tmul F₁ (1 ⊗ₜ[A] e) T t
          (Module.Dual.baseChange A₁ φ) (1 ⊗ₜ[A] d)
        have hr := targetAwayBaseChangeAlgEquiv_one_tmul F A₁ e d
        change targetAwayTo F₁ (1 ⊗ₜ[A] e) T
            (t ⊗ₜ[A₁ ⊗[A] B] dualizingModule.tmul F₁
              (Module.Dual.baseChange A₁ φ) (1 ⊗ₜ[A] d)) =
          targetAwayBaseChangeTo F A₁ T e hE
            (baseChangeTo G A₁ T hD (targetAwayTo F e T
              (t ⊗ₜ[B] dualizingModule.tmul F φ d)))
        rw [ha, hb]
        change _ = t ⊗ₜ[Localization.Away (1 ⊗ₜ[A] e : A₁ ⊗[A] B)]
          dualizingModule.tmul
            (targetAwayFactorization (FiniteOpenFactorization.baseChange F A₁)
              (1 ⊗ₜ[A] e)) (Module.Dual.baseChange A₁ φ)
            (targetAwayBaseChangeRingEquiv F A₁ e
              (1 ⊗ₜ[A] algebraMap B (Localization.Away e) d))
        rw [hr]
  have hg : Function.Bijective g := baseChangeTo_bijective G A₁ T hD hf
  refine (Function.Bijective.of_comp_iff' b.bijective f).mp ?_
  change Function.Bijective (b.toLinearMap.comp f)
  rw [hc]
  exact c.bijective.comp (hg.comp a.bijective)


/-- **Stacks Project, Tag 0BVF.** For a flat quasi-finite algebra over a Noetherian
base, arbitrary base change induces an isomorphism of relative dualizing modules. -/
@[stacks 0BVF]
theorem baseChangeLinearMap_bijective
    (F : FiniteOpenFactorization.{u, v, w} A B)
    [IsNoetherianRing A] [Module.Flat A B]
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    Function.Bijective (baseChangeLinearMap F A₁) := by
  let B₁ := A₁ ⊗[A] B
  let : Algebra A B₁ := Algebra.TensorProduct.leftAlgebra
  let : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower A B B₁ := Algebra.TensorProduct.right_isScalarTower
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let M := B₁ ⊗[B] dualizingModule F
  let N := dualizingModule F₁
  let : AddCommGroup M := inferInstance
  let : Module B₁ M := TensorProduct.leftModule
  let : AddCommGroup N := dualizingModule.instAddCommGroup F₁
  let : Module B₁ N := dualizingModule.instModule F₁
  let f : M →ₗ[B₁] N := baseChangeLinearMap F A₁
  have : Algebra.FiniteType A B :=
    (finiteType_quasiFinite_of_finiteOpenFactorization F).1
  change Function.Bijective f
  refine linearMap_bijective_of_localizations (R := B₁) (M := M) (N := N) f ?_
  intro q
  let qB : Ideal B := q.asIdeal.comap (algebraMap B B₁)
  let p : Ideal A := qB.comap (algebraMap A B)
  have : qB.IsPrime := Ideal.comap_isPrime (algebraMap B B₁) q.asIdeal
  have : p.IsPrime := Ideal.comap_isPrime (algebraMap A B) qB
  have : qB.LiesOver p := ⟨rfl⟩
  have hqLie : q.asIdeal.LiesOver p := by
    refine ⟨?_⟩
    ext a
    change algebraMap B B₁ (algebraMap A B a) ∈ q.asIdeal ↔
      algebraMap A B₁ a ∈ q.asIdeal
    rw [IsScalarTower.algebraMap_apply A B B₁ a]
  have hqf : Algebra.QuasiFiniteAt A qB :=
    quasiFiniteAt_of_finiteOpenFactorization F (p := p) (q := qB)
  obtain ⟨A', hA', alg, het, p', hp', hp'p, hres, Q, hQ, hQp', e, hdata⟩ :=
    exists_etale_projective_component_at (A := A) (B := B) p qB hqf
  rcases hdata with ⟨heidem, hfinite, hQq, heavoid, hproj⟩
  let : CommRing A' := hA'
  let : Algebra A A' := alg
  let : Algebra.Etale A A' := het
  let : p'.IsPrime := hp'
  let : p'.LiesOver p := hp'p
  let : Q.IsPrime := hQ
  let : Q.LiesOver p' := hQp'
  let : q.asIdeal.LiesOver p := hqLie
  let j : B →ₐ[A] B₁ := Algebra.TensorProduct.includeRight
  have hjq : q.asIdeal.comap j.toRingHom = qB := by
    ext b
    rfl
  obtain ⟨Q', hQ', hQ'p', hQ'q, hQ'e⟩ :=
    exists_prime_lift_avoiding_after_baseChange j p qB q.asIdeal hjq
      p' hres Q hQq e heavoid
  let S' := A' ⊗[A] B₁
  let : Algebra B₁ S' := Algebra.TensorProduct.rightAlgebra
  let swap : B₁ ⊗[A] A' ≃ₐ[B₁] S' := Algebra.TensorProduct.commRight A B₁ A'
  let : Algebra.Etale B₁ (B₁ ⊗[A] A') := inferInstance
  let : Algebra.Etale B₁ S' := Algebra.Etale.of_equiv swap
  let f' : B₁ →+* S' := algebraMap B₁ S'
  have hf' : f'.Flat :=
    (RingHom.flat_algebraMap_iff (R := B₁) (S := S')).mpr inferInstance
  have hff := atPrime_localRingHom_faithfullyFlat f' q.asIdeal Q'
    hQ'q.symm hf'
  let A₂ := A₁ ⊗[A] A'
  let B' := A' ⊗[A] B
  let : Algebra.FiniteType A A' := inferInstance
  let : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing A A'
  let : Module.Flat A A' := Algebra.WeaklyEtale.flat
  let : Algebra A A₂ := Algebra.TensorProduct.leftAlgebra
  let : Algebra A₁ A₂ := Algebra.TensorProduct.leftAlgebra
  let : Algebra A' A₂ := Algebra.TensorProduct.rightAlgebra
  let : Algebra.Etale A₁ A₂ := inferInstance
  let : Module.Flat A₁ A₂ := Algebra.WeaklyEtale.flat
  let : Algebra A' B' := Algebra.TensorProduct.leftAlgebra
  let : Module.Finite A' (Localization.Away e) := hfinite
  let : Module.Projective A' (Localization.Away e) := hproj
  let G := targetAwayFactorization (FiniteOpenFactorization.baseChange F A') e
  have hG := baseChangeLinearMap_bijective_of_finite_projective_target G A₂
  let F' := FiniteOpenFactorization.baseChange F A'
  let : Module.Finite A F.middle := F.finite_middle
  let : Module.FinitePresentation A F.middle :=
    Module.finitePresentation_of_finite A F.middle
  let : Module.Finite A₁ F₁.middle := F₁.finite_middle
  let : Module.FinitePresentation A₁ F₁.middle := by
    change Module.FinitePresentation A₁ (A₁ ⊗[A] F.middle)
    infer_instance
  let : Module.Finite A' F'.middle := F'.finite_middle
  let : Module.FinitePresentation A' F'.middle :=
    Module.finitePresentation_of_finite A' F'.middle
  have hF₁₂ := baseChangeLinearMap_bijective_of_flat_finitePresentation F₁ A₂
  have hFA' := baseChangeLinearMap_bijective_of_flat_finitePresentation F A'
  let B₂ := A₂ ⊗[A] B
  let B'₂ := A₂ ⊗[A'] B'
  let e₂ := (1 : A₂) ⊗ₜ[A'] e
  let U₂ := Localization.Away e₂
  let B₁₂ := A₂ ⊗[A₁] B₁
  let cB₁₂ := Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B
  let cB'₂ := Algebra.TensorProduct.cancelBaseChange A A' A₂ A₂ B
  let : Algebra B' B'₂ := Algebra.TensorProduct.rightAlgebra
  let : Algebra B'₂ U₂ := inferInstance
  let : Algebra B₂ U₂ := Algebra.compHom U₂ cB'₂.symm.toRingHom
  let : Algebra B₁₂ U₂ := Algebra.compHom U₂ cB₁₂.toRingHom
  let : Algebra B₁ B₁₂ := Algebra.TensorProduct.rightAlgebra
  let : Algebra B₁ U₂ := Algebra.compHom U₂ (algebraMap B₁ B₁₂)
  let : Algebra B' U₂ := Algebra.compHom U₂ (algebraMap B' B'₂)
  let : Algebra B U₂ := Algebra.compHom U₂ (algebraMap B B₁)
  let D := Localization.Away e
  let D₂ := A₂ ⊗[A'] D
  let : Algebra D D₂ := Algebra.TensorProduct.rightAlgebra
  let eD := targetAwayBaseChangeRingEquiv F' A₂ e
  let : Algebra D₂ U₂ := eD.toRingHom.toAlgebra
  let : Algebra D U₂ := Algebra.compHom U₂ (algebraMap D D₂)
  have h₁ (b : B) : algebraMap B₁ U₂ (1 ⊗ₜ[A] b) = algebraMap B U₂ b := rfl
  have h₁₂ (b : B₁) : algebraMap B₁₂ U₂ (1 ⊗ₜ[A₁] b) = algebraMap B₁ U₂ b := rfl
  have h'₂ (b : B') : algebraMap B'₂ U₂ (1 ⊗ₜ[A'] b) = algebraMap B' U₂ b := rfl
  have hc₁₂ (b : B₁₂) : algebraMap B₂ U₂ (cB₁₂ b) = algebraMap B₁₂ U₂ b := rfl
  have hc'₂ (b : B'₂) : algebraMap B₂ U₂ (cB'₂ b) = algebraMap B'₂ U₂ b := by
    change algebraMap B'₂ U₂ (cB'₂.symm (cB'₂ b)) = _
    rw [AlgEquiv.symm_apply_apply]
  have h₂ (b : B) : algebraMap B₂ U₂ (1 ⊗ₜ[A] b) = algebraMap B U₂ b := by
    change algebraMap B₂ U₂ (1 ⊗ₜ[A] b) =
      algebraMap B₂ U₂ (cB₁₂ (1 ⊗ₜ[A₁] (1 ⊗ₜ[A] b)))
    simp only [cB₁₂, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  have h' (b : B) : algebraMap B' U₂ (1 ⊗ₜ[A] b) = algebraMap B U₂ b := by
    rw [← h₂]
    change algebraMap B'₂ U₂ (1 ⊗ₜ[A'] (1 ⊗ₜ[A] b)) =
      algebraMap B'₂ U₂ (cB'₂.symm (1 ⊗ₜ[A] b))
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
  have hD (d : D) : algebraMap D₂ U₂ (1 ⊗ₜ[A'] d) = algebraMap D U₂ d := rfl
  have hE (d : D₂) : algebraMap U₂ U₂ (eD d) = algebraMap D₂ U₂ d := rfl
  let : Module B' D := (inferInstance : Algebra B' D).toModule
  let : Module B' U₂ := (inferInstance : Algebra B' U₂).toModule
  let : SMul B' D := (inferInstance : Algebra B' D).toSMul
  let : SMul B' U₂ := (inferInstance : Algebra B' U₂).toSMul
  let : IsScalarTower B' D U₂ := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    change algebraMap B'₂ U₂ (1 ⊗ₜ[A'] b) =
      eD (1 ⊗ₜ[A'] algebraMap B' D b)
    exact (targetAwayBaseChangeAlgEquiv_one_tmul F' A₂ e b).symm
  have hlocal : Function.Bijective (baseChangeTo F' A₂ U₂ h'₂) :=
    baseChangeTo_bijective_of_targetAway F' A₂ U₂ e h'₂ hD hE hG
  have htotal : Function.Bijective (baseChangeTo F A₂ U₂ h₂) :=
    (baseChangeTo_tower_bijective_iff F A' A₂ U₂ h' h'₂ h₂ hc'₂ hlocal).mpr
      (baseChangeTo_bijective F A' U₂ h' hFA')
  have hU : Function.Bijective (LinearMap.lTensor U₂ f) :=
    (baseChangeTo_bijective_iff F A₁ U₂ h₁).mp
      ((baseChangeTo_tower_bijective_iff F A₁ A₂ U₂ h₁ h₁₂ h₂ hc₁₂
        (baseChangeTo_bijective F₁ A₂ U₂ h₁₂ hF₁₂)).mp htotal)
  let ρ : B'₂ ≃+* S' := cB'₂.toRingEquiv.trans
    (towerTargetRingEquiv (A := A) (A₁ := A₁) (A' := A') (B := B))
  have hρe : ρ e₂ = Algebra.TensorProduct.map (AlgHom.id A A') j e := by
    change towerTargetRingEquiv (A := A) (A₁ := A₁) (A' := A') (B := B)
      (Algebra.TensorProduct.cancelBaseChange A A' A₂ A₂ B (1 ⊗ₜ[A'] e)) = _
    generalize e = z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      calc
        _ = towerTargetRingEquiv (A := A) (A₁ := A₁) (A' := A') (B := B)
              (Algebra.TensorProduct.cancelBaseChange A A' A₂ A₂ B (1 ⊗ₜ[A'] x)) +
            towerTargetRingEquiv (A := A) (A₁ := A₁) (A' := A') (B := B)
              (Algebra.TensorProduct.cancelBaseChange A A' A₂ A₂ B (1 ⊗ₜ[A'] y)) := by
          simp only [TensorProduct.tmul_add, map_add]
        _ = _ := by rw [hx, hy, map_add]
    | tmul a b =>
      have hsmul : a • (1 : A₂) = algebraMap A' A₂ a := by simp [Algebra.smul_def]
      simp [towerTargetRingEquiv, Algebra.TensorProduct.cancelBaseChange_tmul, hsmul,
        Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      rfl
  have havoid : ρ e₂ ∉ Q' := by
    rw [hρe]
    exact hQ'e
  let T := Localization.AtPrime Q'
  let u₂T := awayMapToAtPrime e₂ ρ Q' havoid
  let : Algebra U₂ T := u₂T.toAlgebra
  let qToT := Localization.localRingHom q.asIdeal Q' f' hQ'q.symm
  let : Algebra (Localization.AtPrime q.asIdeal) T := qToT.toAlgebra
  let : Algebra B₁ T :=
    Algebra.compHom T (algebraMap B₁ (Localization.AtPrime q.asIdeal))
  let : SMul B₁ (Localization.AtPrime q.asIdeal) :=
    (inferInstance : Algebra B₁ (Localization.AtPrime q.asIdeal)).toSMul
  let : SMul B₁ T := (inferInstance : Algebra B₁ T).toSMul
  let : IsScalarTower B₁ (Localization.AtPrime q.asIdeal) T :=
    IsScalarTower.of_compHom B₁ (Localization.AtPrime q.asIdeal) T
  have hB₁U₂T (b : B₁) :
      algebraMap B₁ T b = algebraMap U₂ T (algebraMap B₁ U₂ b) := by
    change qToT (algebraMap B₁ (Localization.AtPrime q.asIdeal) b) =
      awayMapToAtPrime e₂ (ρ : B'₂ →+* S') Q' havoid
        (algebraMap B'₂ (Localization.Away e₂)
          (cB'₂.symm (cB₁₂ (1 ⊗ₜ[A₁] b))))
    rw [Localization.localRingHom_to_map,
      awayMapToAtPrime_algebraMap e₂ (ρ : B'₂ →+* S') Q' havoid
        (cB'₂.symm (cB₁₂ (1 ⊗ₜ[A₁] b)))]
    congr 1
    change f' b = towerTargetRingEquiv (cB'₂ (cB'₂.symm (cB₁₂ (1 ⊗ₜ[A₁] b))))
    rw [AlgEquiv.apply_symm_apply]
    have hb : cB₁₂ (1 ⊗ₜ[A₁] b) =
        Algebra.TensorProduct.map
          (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := A₁) (B := A'))
          (AlgHom.id A B) b := by
      induction b using TensorProduct.inductionOn with
      | add b c hb hc => simp only [TensorProduct.tmul_add, map_add, hb, hc]
      | tmul a b =>
        simp only [cB₁₂, Algebra.TensorProduct.cancelBaseChange_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        congr 1
        simp [Algebra.smul_def]
        rfl
    rw [hb]
    exact (RingHom.congr_fun
      (towerTargetRingEquiv_include (A := A) (A₁ := A₁) (A' := A') (B := B)) b).symm
  let : IsScalarTower B₁ U₂ T := by
    apply IsScalarTower.of_algebraMap_eq
    exact hB₁U₂T
  let : Module.FaithfullyFlat (Localization.AtPrime q.asIdeal) T := hff
  exact localizedMap_bijective_of_lTensor (T := T) q f (lTensor_bijective_of_lTensor f hU)

end dualizingModule
end Stacks.Discriminant
