module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Finiteness.Projective
public import StacksFrontier.Homology.HomComplex.TensorHom

@[expose] public section

/-!
# The chain-evaluation isomorphism

For cochain complexes `K`, `J`, `I` of `R`-modules, this file constructs the canonical map
`Tot(Hom^•(J, I) ⊗ K) → Hom^•(Hom^•(K, J), I)` sending `f ⊗ k` to `g ↦ f (g k)`, shows that it
is functorial in all three complexes, and shows that it is an isomorphism when `K` has finitely
generated projective terms and suitable boundedness conditions hold.

It also records that the Koszul sign appearing in this direct construction is the sign that the
monoidal construction of the same map produces: on the summand `K^r ⊗ Hom^{a-r}(K, J)`, the
Koszul braiding exponent `r(a-r)` and the evaluation exponent `r + (-a)r` have the same parity.

## Main definitions

* `ChainEvaluation.tensorHomEvaluation`: the evaluation map
  `Hom(J, I) ⊗ K → Hom(Hom(K, J), I)` of modules.
* `ChainEvaluation.chainEvaluation`: the evaluation morphism of cochain complexes
  `Tot(Hom^•(J, I) ⊗ K) → Hom^•(Hom^•(K, J), I)`.

## Main results

* `ChainEvaluation.tensorHomEvaluation_bijective`: the module-level evaluation map is bijective
  when `K` is finitely generated projective.
* `ChainEvaluation.chainEvaluation_tmul`: the homogeneous formula for `chainEvaluation`.
* `ChainEvaluation.chainEvaluation_natural_K`, `ChainEvaluation.chainEvaluation_natural_J`,
  `ChainEvaluation.chainEvaluation_natural_I`: functoriality of `chainEvaluation` in each of the
  three complexes — covariant in `K` and `I`, contravariant in `J`.
* `ChainEvaluation.chainEvaluation_isIso_of_bounded`: the chain-level evaluation map is an
  isomorphism when `K` is bounded with finitely generated projective terms.
* `ChainEvaluation.chainEvaluation_isIso_of_boundedAbove_boundedBelow`: the chain-level
  evaluation map is an isomorphism when `K` is bounded above with finitely generated
  projective terms, `J` is bounded below and `I` is bounded above.
* `ChainEvaluation.homComplex_braiding_sign_eq_evaluation_sign`: the Koszul braiding sign on the
  relevant summand equals the evaluation sign of `chainEvaluation_tmul`.
  The equality of the monoidal and direct constructions (Stacks 0A61) is
  `ChainEvaluation.chainEvaluation_eq_tensorHomEquiv_symm`, in
  `StacksFrontier.Homology.HomComplex.DerivedAdjunction`.

Boundedness is expressed through Mathlib's `CochainComplex.IsStrictlyGE` and
`CochainComplex.IsStrictlyLE` classes, and termwise finite projectivity through
`Module.Finite` and `Module.Projective` instances.

## Implementation notes

Mathlib indexes a degree-`t` cochain by maps `K^a ⟶ L^{a+t}`, so the component used to evaluate
an element of `K^r` lies in degree `a - r` of the Hom complex; this is why the sign comparison of
Stacks 0A61 pits the exponent `r(a-r)` against `r + (-a)r`. The Koszul symmetric structure on
cochain complexes is not a global instance, so
`homComplex_braiding_sign_eq_evaluation_sign` takes it, together with the formula for its
braiding on homogeneous summands, as hypotheses.

## References

* [Stacks Project, Tag 0A60](https://stacks.math.columbia.edu/tag/0A60)
* [Stacks Project, Tag 0A61](https://stacks.math.columbia.edu/tag/0A61)
* [Stacks Project, Tag 0A68](https://stacks.math.columbia.edu/tag/0A68)
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex MonoidalCategory
  CochainComplex.HomComplex HomologicalComplex TensorProduct

namespace ChainEvaluation

universe u

variable {R : Type u} [CommRing R]

/-- The module-level evaluation map
`Hom(J,I) ⊗ K → Hom(Hom(K,J),I)`, sending `f ⊗ k` to `g ↦ f (g k)`. -/
noncomputable def tensorHomEvaluation (K J I : Type*) [AddCommGroup K]
    [AddCommGroup J] [AddCommGroup I] [Module R K] [Module R J] [Module R I] :
    TensorProduct R (J →ₗ[R] I) K →ₗ[R] ((K →ₗ[R] J) →ₗ[R] I) :=
  TensorProduct.lift
    { toFun := fun f =>
        { toFun := fun k =>
            { toFun := fun g => f (g k)
              map_add' _ _ := by simp
              map_smul' _ _ := by simp }
          map_add' _ _ := by ext; simp
          map_smul' _ _ := by ext; simp }
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }

/-- The evaluation map sends `f ⊗ k` to the map `g ↦ f (g k)`. -/
@[simp]
theorem tensorHomEvaluation_tmul (K J I : Type*) [AddCommGroup K]
    [AddCommGroup J] [AddCommGroup I] [Module R K] [Module R J] [Module R I]
    (f : J →ₗ[R] I) (k : K) (g : K →ₗ[R] J) :
    tensorHomEvaluation K J I (f ⊗ₜ[R] k) g = f (g k) :=
  rfl

/-- Evaluation of a tensor product with a finite projective module against an internal Hom. -/
private noncomputable def finiteProjectiveEvaluationEquiv
    (K J I : Type*) [AddCommGroup K] [AddCommGroup J] [AddCommGroup I]
    [Module R K] [Module R J] [Module R I]
    [Module.Finite R K] [Module.Projective R K] :
    ((J →ₗ[R] I) ⊗[R] K) ≃ₗ[R] ((K →ₗ[R] J) →ₗ[R] I) :=
  (TensorProduct.comm R (J →ₗ[R] I) K) ≪≫ₗ
  (TensorProduct.congr (Module.evalEquiv R K) (LinearEquiv.refl R (J →ₗ[R] I))) ≪≫ₗ
  (dualTensorHomEquiv R (Module.Dual R K) (J →ₗ[R] I)) ≪≫ₗ
  (TensorProduct.lift.equiv (RingHom.id R) (Module.Dual R K) J I) ≪≫ₗ
  ((dualTensorHomEquiv R K J).arrowCongr (LinearEquiv.refl R I))

/-- The finite projective evaluation equivalence is the canonical evaluation map. -/
private theorem finiteProjectiveEvaluationEquiv_tmul
    (K J I : Type*) [AddCommGroup K] [AddCommGroup J] [AddCommGroup I]
    [Module R K] [Module R J] [Module R I]
    [Module.Finite R K] [Module.Projective R K]
    (f : J →ₗ[R] I) (k : K) (g : K →ₗ[R] J) :
    finiteProjectiveEvaluationEquiv (R := R) K J I (f ⊗ₜ[R] k) g = f (g k) := by
  simp only [finiteProjectiveEvaluationEquiv, LinearEquiv.trans_apply,
    TensorProduct.comm_tmul, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, Module.evalEquiv_apply,
    LinearEquiv.arrowCongr_apply]
  change ((TensorProduct.lift.equiv (RingHom.id R) (Module.Dual R K) J I)
    ((dualTensorHom R (Module.Dual R K) (J →ₗ[R] I))
      ((Module.Dual.eval R K) k ⊗ₜ[R] f)))
    ((dualTensorHomEquiv R K J).symm g) = f (g k)
  have H (x : Module.Dual R K ⊗[R] J) :
      ((TensorProduct.lift.equiv (RingHom.id R) (Module.Dual R K) J I)
        ((dualTensorHom R (Module.Dual R K) (J →ₗ[R] I))
          ((Module.Dual.eval R K) k ⊗ₜ[R] f))) x =
        f ((dualTensorHom R K J x) k) := by
    induction x using TensorProduct.inductionOn with
    | tmul φ j =>
      rw [TensorProduct.lift.equiv_apply, dualTensorHom_apply,
        dualTensorHom_apply, Module.Dual.eval_apply]
      simp
    | add x y hx hy => simp [map_add, hx, hy]
  rw [H, show dualTensorHom R K J ((dualTensorHomEquiv R K J).symm g) = g from
    (dualTensorHomEquiv R K J).apply_symm_apply g]

/-- If `K` is finitely generated projective, the evaluation map
`Hom(J,I) ⊗ K → Hom(Hom(K,J),I)` is bijective. -/
theorem tensorHomEvaluation_bijective (K J I : Type*) [AddCommGroup K]
    [AddCommGroup J] [AddCommGroup I] [Module R K] [Module R J] [Module R I]
    [Module.Finite R K] [Module.Projective R K] :
    Function.Bijective (tensorHomEvaluation (R := R) K J I) := by
  have h : (finiteProjectiveEvaluationEquiv (R := R) K J I).toLinearMap =
      tensorHomEvaluation K J I :=
    TensorProduct.ext' fun f k => LinearMap.ext (finiteProjectiveEvaluationEquiv_tmul K J I f k)
  rw [← h]
  exact (finiteProjectiveEvaluationEquiv (R := R) K J I).bijective

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private noncomputable def evaluationCochain
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (t r : ℤ)
    (φ : Cochain L M t) (k : K.X r) :
    Cochain (HomComplexR R K L) M (t + r) :=
  Cochain.mk fun s p hsp ↦ ModuleCat.ofHom
    { toFun := fun ψ ↦
        (r + (-(p - t)) * r).negOnePow •
          (φ.v (p - t) p (by omega)).hom
            ((ψ.v r (p - t) (by omega)).hom k)
      map_add' := by intro ψ ψ'; simp
      map_smul' := by
        intro x ψ
        rw [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply, map_smul]
        exact smul_comm _ _ _ }

private lemma evaluationCochain_add_left
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (t r : ℤ)
    (φ φ' : Cochain L M t) (k : K.X r) :
    evaluationCochain K L M t r (φ + φ') k =
      evaluationCochain K L M t r φ k + evaluationCochain K L M t r φ' k := by
  apply Cochain.ext _ _
  intro s p hsp
  rw [Cochain.add_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  dsimp [evaluationCochain]
  change (r + (-(p - t)) * r).negOnePow •
      ((φ.v (p - t) p _).hom ((ψ.v r (p - t) _).hom k) +
        (φ'.v (p - t) p _).hom ((ψ.v r (p - t) _).hom k)) =
    (r + (-(p - t)) * r).negOnePow •
        (φ.v (p - t) p _).hom ((ψ.v r (p - t) _).hom k) +
      (r + (-(p - t)) * r).negOnePow •
        (φ'.v (p - t) p _).hom ((ψ.v r (p - t) _).hom k)
  exact smul_add _ _ _

private lemma evaluationCochain_smul_left
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (t r : ℤ)
    (x : R) (φ : Cochain L M t) (k : K.X r) :
    evaluationCochain K L M t r (x • φ) k =
      x • evaluationCochain K L M t r φ k := by
  apply Cochain.ext _ _
  intro s p hsp
  rw [Cochain.smul_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  dsimp [evaluationCochain]
  change (r + (-(p - t)) * r).negOnePow •
      (x • ((φ.v (p - t) p _).hom ((ψ.v r (p - t) _).hom k)) : M.X p) =
    x • ((r + (-(p - t)) * r).negOnePow •
      (φ.v (p - t) p _).hom ((ψ.v r (p - t) _).hom k))
  exact smul_comm _ _ _

private lemma evaluationCochain_add_right
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (t r : ℤ)
    (φ : Cochain L M t) (k k' : K.X r) :
    evaluationCochain K L M t r φ (k + k') =
      evaluationCochain K L M t r φ k + evaluationCochain K L M t r φ k' := by
  apply Cochain.ext _ _
  intro s p hsp
  rw [Cochain.add_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  dsimp [evaluationCochain]
  change (r + (-(p - t)) * r).negOnePow •
      (φ.v (p - t) p _).hom ((ψ.v r (p - t) _).hom (k + k')) =
    (r + (-(p - t)) * r).negOnePow •
        (φ.v (p - t) p _).hom ((ψ.v r (p - t) _).hom k) +
      (r + (-(p - t)) * r).negOnePow •
        (φ.v (p - t) p _).hom ((ψ.v r (p - t) _).hom k')
  simp only [map_add, smul_add]

private lemma evaluationCochain_smul_right
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (t r : ℤ)
    (x : R) (φ : Cochain L M t) (k : K.X r) :
    evaluationCochain K L M t r φ (x • k) =
      x • evaluationCochain K L M t r φ k := by
  apply Cochain.ext _ _
  intro s p hsp
  rw [Cochain.smul_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  dsimp [evaluationCochain]
  simp only [map_smul]
  exact smul_comm _ _ _

private noncomputable def evaluationMap
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (t r n : ℤ) (h : t + r = n) :
    (HomComplexR R L M).X t ⊗ K.X r ⟶
      (HomComplexR R (HomComplexR R K L) M).X n :=
  match h with
  | rfl => ModuleCat.ofHom (TensorProduct.lift
      { toFun := fun φ ↦
          { toFun := fun k ↦ evaluationCochain K L M t r φ k
            map_add' := evaluationCochain_add_right K L M t r φ
            map_smul' := by intro x k
                            exact evaluationCochain_smul_right K L M t r x φ k }
        map_add' := by intro φ φ'; apply LinearMap.ext; intro k
                       exact evaluationCochain_add_left K L M t r φ φ' k
        map_smul' := by intro x φ; apply LinearMap.ext; intro k
                        exact evaluationCochain_smul_left K L M t r x φ k })

private noncomputable def evaluationFun
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (HomComplexR R L M ⊗ K).X n ⟶
      (HomComplexR R (HomComplexR R K L) M).X n :=
  HomologicalComplex.mapBifunctorDesc fun t r h ↦ evaluationMap K L M t r n h

private lemma evaluationFun_apply
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
    (t r n : ℤ) (h : t + r = n) (φ : Cochain L M t) (k : K.X r)
    (s p : ℤ) (hsp : s + n = p) (ψ : Cochain K L s) :
    ((((ιTensorObj (HomComplexR R L M) K t r n h ≫
          evaluationFun K L M n).hom) (φ ⊗ₜ[R] k)).v s p hsp).hom ψ =
      (r + (-(p - t)) * r).negOnePow •
        (φ.v (p - t) p (by omega)).hom
          ((ψ.v r (p - t) (by omega)).hom k) := by
  subst n
  simp only [evaluationFun, HomologicalComplex.ι_mapBifunctorDesc]
  rfl

private theorem evaluationFun_comm
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n n' : ℤ) :
    evaluationFun K L M n ≫ (HomComplexR R (HomComplexR R K L) M).d n n' =
      (HomComplexR R L M ⊗ K).d n n' ≫ evaluationFun K L M n' := by
  by_cases h : n + 1 = n'
  · subst n'
    apply GradedObject.Monoidal.tensorObj_ext
    intro t r htr
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro φ k
    apply Cochain.ext
    intro s p hsp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ψ
    change (((((HomComplexR R (HomComplexR R K L) M).d n (n + 1)).hom
        ((ιTensorObj (HomComplexR R L M) K t r n htr ≫
          evaluationFun K L M n).hom (φ ⊗ₜ[R] k))).v s p hsp).hom ψ) = _
    change (((δ n (n + 1)
        ((ιTensorObj (HomComplexR R L M) K t r n htr ≫
          evaluationFun K L M n).hom (φ ⊗ₜ[R] k))).v s p hsp).hom ψ) = _
    simp only [δ, Cochain.mk_v]
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_smul,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    have hβ₁ :
        (((evaluationFun K L M n).hom
            ((ιTensorObj (HomComplexR R L M) K t r n htr).hom (φ ⊗ₜ[R] k))).v
            s (s + n) rfl).hom ψ =
          (r + (-(s + n - t)) * r).negOnePow •
            (φ.v (s + n - t) (s + n) (by omega)).hom
              ((ψ.v r (s + n - t) (by omega)).hom k) := by
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
        evaluationFun_apply K L M t r n htr φ k s (s + n) rfl ψ
    have hβ₂ :
        (((evaluationFun K L M n).hom
            ((ιTensorObj (HomComplexR R L M) K t r n htr).hom (φ ⊗ₜ[R] k))).v
            (s + (n + 1) - n) p (by omega)).hom
              (((HomComplexR R K L).d s (s + (n + 1) - n)).hom ψ) =
          (r + (-(p - t)) * r).negOnePow •
            (φ.v (p - t) p (by omega)).hom
              (((((HomComplexR R K L).d s (s + (n + 1) - n)).hom ψ).v
                r (p - t) (by omega)).hom k) := by
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
        evaluationFun_apply K L M t r n htr φ k (s + (n + 1) - n) p (by omega)
          (((HomComplexR R K L).d s (s + (n + 1) - n)).hom ψ)
    rw [hβ₁, hβ₂]
    have hsrc := CochainComplex.ιTensorObj_d R (HomComplexR R L M) K t r n (n + 1)
      htr rfl
    have hsrc_apply := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hsrc)
      (φ ⊗ₜ[R] k)
    rw [show GradedObject.Monoidal.ιTensorObj (HomComplexR R L M).X K.X t r n htr =
      ιTensorObj (HomComplexR R L M) K t r n htr from rfl]
    change _ = (Cochain.v
      ((evaluationFun K L M (n + 1)).hom
        ((ιTensorObj (HomComplexR R L M) K t r n htr ≫
          (HomComplexR R L M ⊗ K).d n (n + 1)).hom (φ ⊗ₜ[R] k)))
      s p hsp).hom ψ
    rw [hsrc_apply]
    simp only [ModuleCat.hom_add, ModuleCat.hom_smul, ModuleCat.hom_comp,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    simp only [map_add, LinearMap.CompatibleSMul.map_smul]
    change _ = (Cochain.v
      ((ιTensorObj (HomComplexR R L M) K (t + 1) r (n + 1) (by omega) ≫
          evaluationFun K L M (n + 1)).hom
          ((((HomComplexR R L M).d t (t + 1)).hom φ) ⊗ₜ[R] k) +
        t.negOnePow •
          (ιTensorObj (HomComplexR R L M) K t (r + 1) (n + 1) (by omega) ≫
            evaluationFun K L M (n + 1)).hom
            (φ ⊗ₜ[R] ((K.d r (r + 1)).hom k))) s p hsp).hom ψ
    let A : Cochain (HomComplexR R K L) M (n + 1) :=
      (ιTensorObj (HomComplexR R L M) K (t + 1) r (n + 1) (by omega) ≫
        evaluationFun K L M (n + 1)).hom
        ((((HomComplexR R L M).d t (t + 1)).hom φ) ⊗ₜ[R] k)
    let B : Cochain (HomComplexR R K L) M (n + 1) :=
      (ιTensorObj (HomComplexR R L M) K t (r + 1) (n + 1) (by omega) ≫
        evaluationFun K L M (n + 1)).hom
        (φ ⊗ₜ[R] ((K.d r (r + 1)).hom k))
    change _ = (A.v s p hsp).hom ψ + t.negOnePow • (B.v s p hsp).hom ψ
    have hA : (A.v s p hsp).hom ψ =
        (r + (-(p - (t + 1))) * r).negOnePow •
          (Cochain.v (((HomComplexR R L M).d t (t + 1)).hom φ)
            (p - (t + 1)) p (by omega)).hom
              ((ψ.v r (p - (t + 1)) (by omega)).hom k) := by
      simpa only [A, ModuleCat.hom_comp, LinearMap.comp_apply] using
        evaluationFun_apply K L M (t + 1) r (n + 1) (by omega)
          (((HomComplexR R L M).d t (t + 1)).hom φ) k s p hsp ψ
    have hB : (B.v s p hsp).hom ψ =
        ((r + 1) + (-(p - t)) * (r + 1)).negOnePow •
          (φ.v (p - t) p (by omega)).hom
            ((ψ.v (r + 1) (p - t) (by omega)).hom
              ((K.d r (r + 1)).hom k)) := by
      simpa only [B, ModuleCat.hom_comp, LinearMap.comp_apply] using
        evaluationFun_apply K L M t (r + 1) (n + 1) (by omega)
          φ ((K.d r (r + 1)).hom k) s p hsp ψ
    rw [hA, hB]
    clear hβ₁ hβ₂ hsrc hsrc_apply A B hA hB
    change Cochain L M t at φ
    change Cochain K L s at ψ
    simp only [HomComplexR_d_apply]
    rw [δ_v s (s + (n + 1) - n) (by omega) ψ r (p - t) (by omega)
        (p - t - 1) (r + 1) (by omega) rfl,
      δ_v t (t + 1) rfl φ (p - (t + 1)) p (by omega)
        (p - 1) (p - t) (by omega) (by omega)]
    simp only [ModuleCat.hom_add, ModuleCat.hom_smul, ModuleCat.hom_comp,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      map_add, smul_add, smul_smul]
    have hsign₁ : (r + -(s + n - t) * r).negOnePow =
        (r + -(p - (t + 1)) * r).negOnePow := by
      have hidx : s + n - t = p - (t + 1) := by omega
      rw [hidx]
    have hsign₂ : (n + 1).negOnePow * (r + -(p - t) * r).negOnePow =
        (r + -(p - (t + 1)) * r).negOnePow * (t + 1).negOnePow := by
      rw [← Int.negOnePow_add, ← Int.negOnePow_add]
      congr 1
      nlinarith [htr]
    have hsign₃ : (n + 1).negOnePow * (r + -(p - t) * r).negOnePow *
        (s + (n + 1) - n).negOnePow =
        t.negOnePow * (r + 1 + -(p - t) * (r + 1)).negOnePow := by
      simp only [← Int.negOnePow_add]
      apply (Int.negOnePow_eq_iff _ _).mpr
      refine ⟨p - t, ?_⟩
      nlinarith [hsp, htr]
    simp only [map_zsmul_unit, smul_smul]
    rw [hsign₃, hsign₂, hsign₁]
    simp only [add_assoc]
    have hidx₁ : s + n = p - 1 := by omega
    have hidx₂ : s + n - t = p - (t + 1) := by omega
    have hidx₃ : p - t - 1 = p - (t + 1) := by omega
    have hMdata :
        (M.d (s + n) p).hom
          ((φ.v (s + n - t) (s + n) (by omega)).hom
            ((ψ.v r (s + n - t) (by omega)).hom k)) =
        (M.d (p - 1) p).hom
          ((φ.v (p - (t + 1)) (p - 1) (by omega)).hom
            ((ψ.v r (p - (t + 1)) (by omega)).hom k)) := by
      have aux (a b c d : ℤ) (hab : a = b) (hcd : c = d)
          (hφa : a + t = c) (hφb : b + t = d)
          (hψa : r + s = a) (hψb : r + s = b) :
          (M.d c p).hom ((φ.v a c hφa).hom ((ψ.v r a hψa).hom k)) =
            (M.d d p).hom ((φ.v b d hφb).hom ((ψ.v r b hψb).hom k)) := by
        subst b; subst d; rfl
      exact aux (s + n - t) (p - (t + 1)) (s + n) (p - 1)
        hidx₂ hidx₁ (by omega) (by omega) (by omega) (by omega)
    have hLdata :
        (φ.v (p - t) p (by omega)).hom
          ((L.d (p - t - 1) (p - t)).hom
            ((ψ.v r (p - t - 1) (by omega)).hom k)) =
        (φ.v (p - t) p (by omega)).hom
          ((L.d (p - (t + 1)) (p - t)).hom
            ((ψ.v r (p - (t + 1)) (by omega)).hom k)) := by
      have aux (a b : ℤ) (hab : a = b)
          (ha : r + s = a) (hb : r + s = b) :
          (φ.v (p - t) p (by omega)).hom
              ((L.d a (p - t)).hom ((ψ.v r a ha).hom k)) =
            (φ.v (p - t) p (by omega)).hom
              ((L.d b (p - t)).hom ((ψ.v r b hb).hom k)) := by
        subst b; rfl
      exact aux (p - t - 1) (p - (t + 1)) hidx₃ (by omega) (by omega)
    rw [hMdata, hLdata]
  · have hrel : ¬ (ComplexShape.up ℤ).Rel n n' := by simpa using h
    rw [(HomComplexR R (HomComplexR R K L) M).shape n n' hrel,
      (HomComplexR R L M ⊗ K).shape n n' hrel]
    simp

/-- **Stacks 0A60**.
The canonical morphism of complexes `Tot(Hom^•(J, I) ⊗ K) ⟶ Hom^•(Hom^•(K, J), I)`. On
homogeneous elements it sends `f ⊗ k` to the map `g ↦ f (g k)`, with the Koszul signs of the
total and Hom complexes. -/
@[stacks 0A60, no_expose]
noncomputable def chainEvaluation
    (K J I : CochainComplex (ModuleCat R) ℤ) :
    (HomComplexR R J I ⊗ K) ⟶ HomComplexR R (HomComplexR R K J) I :=
  { f := evaluationFun K J I
    comm' := fun n n' _ => evaluationFun_comm K J I n n' }

/-- On the summand `A^t ⊗ K^r`, the morphism `A ◁ f` of total complexes restricts to
`A^t ◁ f^r`. This is `CochainComplex.ιTensorObj_tensorHom` for `𝟙 A ⊗ₘ f`. -/
private lemma ιTensorObj_comp_whiskerLeft (A : CochainComplex (ModuleCat.{u} R) ℤ)
    {K K' : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ K') (t r n : ℤ) (h : t + r = n) :
    ιTensorObj A K t r n h ≫ (A ◁ f).f n = (A.X t ◁ f.f r) ≫ ιTensorObj A K' t r n h := by
  rw [← id_tensorHom A f, CochainComplex.ιTensorObj_tensorHom, HomologicalComplex.id_f,
    id_tensorHom]

/-- On the summand `A^t ⊗ K^r`, the morphism `f ▷ K` of total complexes restricts to
`f^t ▷ K^r`. This is `CochainComplex.ιTensorObj_tensorHom` for `f ⊗ₘ 𝟙 K`. -/
private lemma ιTensorObj_comp_whiskerRight {A A' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : A ⟶ A') (K : CochainComplex (ModuleCat.{u} R) ℤ) (t r n : ℤ) (h : t + r = n) :
    ιTensorObj A K t r n h ≫ (f ▷ K).f n = (f.f t ▷ K.X r) ≫ ιTensorObj A' K t r n h := by
  rw [← tensorHom_id f K, CochainComplex.ιTensorObj_tensorHom, HomologicalComplex.id_f,
    tensorHom_id]

/-- **Stacks 0A60**.
Evaluation is natural in the complex `K` being evaluated at: tensoring with `f : K ⟶ K'` and
then evaluating is evaluating and then precomposing the outer Hom complex with `f^* :
Hom^•(K', J) ⟶ Hom^•(K, J)`. -/
@[stacks 0A60]
theorem chainEvaluation_natural_K
    (K K' J I : CochainComplex (ModuleCat.{u} R) ℤ) (f : K ⟶ K') :
    (HomComplexR R J I ◁ f) ≫ chainEvaluation K' J I =
      chainEvaluation K J I ≫ Stacks.HomComplex.TensorHomMap.precomp R (HomComplexR R K' J)
        (HomComplexR R K J) I (Stacks.HomComplex.TensorHomMap.precomp R K K' J f) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply GradedObject.Monoidal.tensorObj_ext
  intro t r htr
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro φ k
  apply Cochain.ext
  intro s p hsp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  simp only [HomologicalComplex.comp_f]
  rw [show GradedObject.Monoidal.ιTensorObj (HomComplexR R J I).X K.X t r n htr =
    ιTensorObj (HomComplexR R J I) K t r n htr from rfl]
  have hwhisk := ιTensorObj_comp_whiskerLeft (HomComplexR R J I) f t r n htr
  have hwhisk_apply := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hwhisk) (φ ⊗ₜ[R] k)
  change (Cochain.v ((evaluationFun K' J I n).hom
    ((ιTensorObj (HomComplexR R J I) K t r n htr ≫
      (HomComplexR R J I ◁ f).f n).hom (φ ⊗ₜ[R] k))) s p hsp).hom ψ = _
  rw [hwhisk_apply]
  change (Cochain.v
    ((ιTensorObj (HomComplexR R J I) K' t r n htr ≫ evaluationFun K' J I n).hom
      (φ ⊗ₜ[R] ((f.f r).hom k))) s p hsp).hom ψ = _
  rw [evaluationFun_apply K' J I t r n htr φ ((f.f r).hom k) s p hsp ψ]
  let g := Stacks.HomComplex.TensorHomMap.precomp R K K' J f
  let β : Cochain (HomComplexR R K J) I n :=
    (ιTensorObj (HomComplexR R J I) K t r n htr ≫ evaluationFun K J I n).hom (φ ⊗ₜ[R] k)
  have hR :
      (Cochain.v
        ((ιTensorObj (HomComplexR R J I) K t r n htr ≫
          (chainEvaluation K J I).f n ≫
            (Stacks.HomComplex.TensorHomMap.precomp R (HomComplexR R K' J) (HomComplexR R K J) I
              g).f n).hom
          (φ ⊗ₜ[R] k)) s p hsp).hom ψ =
        (β.v s p hsp).hom ((g.f s).hom ψ) := by
    change (((Cochain.ofHom g).comp β (zero_add n)).v s p hsp).hom ψ = _
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    rfl
  have hβ := evaluationFun_apply K J I t r n htr φ k s p hsp ((g.f s).hom ψ)
  have hψ :
      ((((g.f s).hom ψ).v r (p - t) (by omega)).hom k) =
        (ψ.v r (p - t) (by omega)).hom ((f.f r).hom k) := by
    clear hR hβ hwhisk hwhisk_apply β
    change Cochain K' J s at ψ
    change (((Cochain.ofHom f).comp ψ (zero_add s)).v r (p - t) (by omega)).hom k = _
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    rfl
  calc
    (r + -(p - t) * r).negOnePow •
        (φ.v (p - t) p (by omega)).hom
          ((ψ.v r (p - t) (by omega)).hom ((f.f r).hom k)) =
      (r + -(p - t) * r).negOnePow •
        (φ.v (p - t) p (by omega)).hom
          ((((g.f s).hom ψ).v r (p - t) (by omega)).hom k) := by rw [hψ]
    _ = _ := (hR.trans hβ).symm

/-- **Stacks 0A60**.
Evaluation is natural in the middle complex `J`: precomposing the inner Hom complex with
`f : J ⟶ J'` on the source corresponds to postcomposing `Hom^•(K, J) ⟶ Hom^•(K, J')` on the
target. -/
@[stacks 0A60]
theorem chainEvaluation_natural_J
    (K J J' I : CochainComplex (ModuleCat.{u} R) ℤ) (f : J ⟶ J') :
    (Stacks.HomComplex.TensorHomMap.precomp R J J' I f ▷ K) ≫ chainEvaluation K J I =
      chainEvaluation K J' I ≫ Stacks.HomComplex.TensorHomMap.precomp R (HomComplexR R K J)
        (HomComplexR R K J') I (Stacks.HomComplex.TensorHomMap.postcomp R K J J' f) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply GradedObject.Monoidal.tensorObj_ext
  intro t r htr
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro φ k
  apply Cochain.ext
  intro s p hsp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  simp only [HomologicalComplex.comp_f]
  rw [show GradedObject.Monoidal.ιTensorObj (HomComplexR R J' I).X K.X t r n htr =
    ιTensorObj (HomComplexR R J' I) K t r n htr from rfl]
  let F := Stacks.HomComplex.TensorHomMap.precomp R J J' I f
  let g := Stacks.HomComplex.TensorHomMap.postcomp R K J J' f
  have hwhisk := ιTensorObj_comp_whiskerRight F K t r n htr
  have hwhisk_apply := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hwhisk) (φ ⊗ₜ[R] k)
  change (Cochain.v ((evaluationFun K J I n).hom
    ((ιTensorObj (HomComplexR R J' I) K t r n htr ≫ (F ▷ K).f n).hom
      (φ ⊗ₜ[R] k))) s p hsp).hom ψ = _
  rw [hwhisk_apply]
  change (Cochain.v
    ((ιTensorObj (HomComplexR R J I) K t r n htr ≫ evaluationFun K J I n).hom
      (((F.f t).hom φ) ⊗ₜ[R] k)) s p hsp).hom ψ = _
  rw [evaluationFun_apply K J I t r n htr ((F.f t).hom φ) k s p hsp ψ]
  let β : Cochain (HomComplexR R K J') I n :=
    (ιTensorObj (HomComplexR R J' I) K t r n htr ≫ evaluationFun K J' I n).hom (φ ⊗ₜ[R] k)
  have hR :
      (Cochain.v
        ((ιTensorObj (HomComplexR R J' I) K t r n htr ≫
          (chainEvaluation K J' I).f n ≫
            (Stacks.HomComplex.TensorHomMap.precomp R (HomComplexR R K J) (HomComplexR R K J') I
              g).f n).hom
          (φ ⊗ₜ[R] k)) s p hsp).hom ψ =
        (β.v s p hsp).hom ((g.f s).hom ψ) := by
    change (((Cochain.ofHom g).comp β (zero_add n)).v s p hsp).hom ψ = _
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    rfl
  have hβ := evaluationFun_apply K J' I t r n htr φ k s p hsp ((g.f s).hom ψ)
  have hφ (x : J.X (p - t)) :
      ((((F.f t).hom φ).v (p - t) p (by omega)).hom x) =
        (φ.v (p - t) p (by omega)).hom ((f.f (p - t)).hom x) := by
    clear hR hβ hwhisk hwhisk_apply β
    change Cochain J' I t at φ
    change (((Cochain.ofHom f).comp φ (zero_add t)).v (p - t) p (by omega)).hom x = _
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    rfl
  have hψ :
      ((((g.f s).hom ψ).v r (p - t) (by omega)).hom k) =
        (f.f (p - t)).hom ((ψ.v r (p - t) (by omega)).hom k) := by
    clear hR hβ hwhisk hwhisk_apply β
    change Cochain K J s at ψ
    change ((ψ.comp (Cochain.ofHom f) (add_zero s)).v r (p - t) (by omega)).hom k = _
    rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
    rfl
  calc
    (r + -(p - t) * r).negOnePow •
        ((((F.f t).hom φ).v (p - t) p (by omega)).hom
          ((ψ.v r (p - t) (by omega)).hom k)) =
      (r + -(p - t) * r).negOnePow •
        (φ.v (p - t) p (by omega)).hom
          ((((g.f s).hom ψ).v r (p - t) (by omega)).hom k) := by
        rw [hφ, hψ]
    _ = _ := (hR.trans hβ).symm

/-- **Stacks 0A60**.
Evaluation is natural in the target complex `I`: postcomposing with `f : I ⟶ I'` commutes with
evaluation. -/
@[stacks 0A60]
theorem chainEvaluation_natural_I
    (K J I I' : CochainComplex (ModuleCat.{u} R) ℤ) (f : I ⟶ I') :
    (Stacks.HomComplex.TensorHomMap.postcomp R J I I' f ▷ K) ≫ chainEvaluation K J I' =
      chainEvaluation K J I ≫ Stacks.HomComplex.TensorHomMap.postcomp R (HomComplexR R K J) I I' f
        := by
  apply HomologicalComplex.hom_ext
  intro n
  apply GradedObject.Monoidal.tensorObj_ext
  intro t r htr
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro φ k
  apply Cochain.ext
  intro s p hsp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  simp only [HomologicalComplex.comp_f]
  rw [show GradedObject.Monoidal.ιTensorObj (HomComplexR R J I).X K.X t r n htr =
    ιTensorObj (HomComplexR R J I) K t r n htr from rfl]
  let F := Stacks.HomComplex.TensorHomMap.postcomp R J I I' f
  have hwhisk := ιTensorObj_comp_whiskerRight F K t r n htr
  have hwhisk_apply := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hwhisk) (φ ⊗ₜ[R] k)
  change (Cochain.v ((evaluationFun K J I' n).hom
    ((ιTensorObj (HomComplexR R J I) K t r n htr ≫ (F ▷ K).f n).hom
      (φ ⊗ₜ[R] k))) s p hsp).hom ψ = _
  rw [hwhisk_apply]
  change (Cochain.v
    ((ιTensorObj (HomComplexR R J I') K t r n htr ≫ evaluationFun K J I' n).hom
      (((F.f t).hom φ) ⊗ₜ[R] k)) s p hsp).hom ψ = _
  rw [evaluationFun_apply K J I' t r n htr ((F.f t).hom φ) k s p hsp ψ]
  let β : Cochain (HomComplexR R K J) I n :=
    (ιTensorObj (HomComplexR R J I) K t r n htr ≫ evaluationFun K J I n).hom (φ ⊗ₜ[R] k)
  have hR :
      (Cochain.v
        ((ιTensorObj (HomComplexR R J I) K t r n htr ≫
          (chainEvaluation K J I).f n ≫
            (Stacks.HomComplex.TensorHomMap.postcomp R (HomComplexR R K J) I I' f).f n).hom
          (φ ⊗ₜ[R] k)) s p hsp).hom ψ =
        (f.f p).hom ((β.v s p hsp).hom ψ) := by
    change ((β.comp (Cochain.ofHom f) (add_zero n)).v s p hsp).hom ψ = _
    rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
    rfl
  have hβ := evaluationFun_apply K J I t r n htr φ k s p hsp ψ
  have hφ (x : J.X (p - t)) :
      ((((F.f t).hom φ).v (p - t) p (by omega)).hom x) =
        (f.f p).hom ((φ.v (p - t) p (by omega)).hom x) := by
    clear hR hβ hwhisk hwhisk_apply β
    change Cochain J I t at φ
    change ((φ.comp (Cochain.ofHom f) (add_zero t)).v (p - t) p (by omega)).hom x = _
    rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
    rfl
  calc
    (r + -(p - t) * r).negOnePow •
        ((((F.f t).hom φ).v (p - t) p (by omega)).hom
          ((ψ.v r (p - t) (by omega)).hom k)) =
      (f.f p).hom ((r + -(p - t) * r).negOnePow •
        (φ.v (p - t) p (by omega)).hom
          ((ψ.v r (p - t) (by omega)).hom k)) := by
        rw [hφ, map_zsmul_unit]
    _ = _ := (hR.trans (congrArg (f.f p).hom hβ)).symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def tensorDualHomEquiv
    (P : Type*) (B : Type*) [AddCommGroup P] [AddCommGroup B]
    [Module R P] [Module R B] [Module.Finite R P] [Module.Projective R P] :
    (B ⊗[R] P) ≃ₗ[R] (Module.Dual R P →ₗ[R] B) :=
  (TensorProduct.comm R B P) ≪≫ₗ
    (TensorProduct.congr (Module.evalEquiv R P) (LinearEquiv.refl R B)) ≪≫ₗ
    (dualTensorHomEquiv R (Module.Dual R P) B)

private noncomputable def tensorPiEquiv
    (P : Type*) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] :
    ((∀ i, A i) ⊗[R] P) ≃ₗ[R] (∀ i, A i ⊗[R] P) :=
  tensorDualHomEquiv P (∀ i, A i) ≪≫ₗ (LinearEquiv.linearMapPi R).symm ≪≫ₗ
    (LinearEquiv.piCongrRight fun i => (tensorDualHomEquiv P (A i)).symm)

private theorem tensorPiEquiv_tmul
    (P : Type*) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (f : ∀ i, A i) (p : P) (i : ι) :
    tensorPiEquiv (R := R) P A (f ⊗ₜ[R] p) i = f i ⊗ₜ[R] p := by
  change (tensorDualHomEquiv P (A i)).symm (((LinearEquiv.linearMapPi R).symm
    (tensorDualHomEquiv P (∀ i, A i) (f ⊗ₜ[R] p))) i) = _
  apply (tensorDualHomEquiv P (A i)).injective
  rw [LinearEquiv.apply_symm_apply]
  ext d
  rfl

/-- Evaluation on all homogeneous components of a cochain. -/
private noncomputable def cochainTensorEvaluationEquiv
    (P : Type*) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (L M : CochainComplex (ModuleCat.{u} R) ℤ) (t : ℤ) :
    (Cochain L M t ⊗[R] P) ≃ₗ[R]
      (∀ T : Triplet t, (P →ₗ[R] L.X T.p) →ₗ[R] M.X T.q) :=
  (TensorProduct.congr
    (LinearEquiv.piCongrRight fun _T : Triplet t =>
      ModuleCat.homLinearEquiv (S := R) : Cochain L M t ≃ₗ[R]
        (∀ T : Triplet t, L.X T.p →ₗ[R] M.X T.q)) (LinearEquiv.refl R P)) ≪≫ₗ
  (tensorPiEquiv P (fun T : Triplet t => L.X T.p →ₗ[R] M.X T.q)) ≪≫ₗ
  (LinearEquiv.piCongrRight fun T => finiteProjectiveEvaluationEquiv P (L.X T.p) (M.X T.q))

private theorem cochainTensorEvaluationEquiv_tmul
    (P : Type*) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (L M : CochainComplex (ModuleCat.{u} R) ℤ) (t : ℤ)
    (φ : Cochain L M t) (p : P) (T : Triplet t) (g : P →ₗ[R] L.X T.p) :
    cochainTensorEvaluationEquiv P L M t (φ ⊗ₜ[R] p) T g = (φ T).hom (g p) := by
  simp [cochainTensorEvaluationEquiv, TensorProduct.congr_tmul, tensorPiEquiv_tmul,
    finiteProjectiveEvaluationEquiv_tmul]
  rfl

/-- Insert a single homogeneous component into a cochain. -/
private noncomputable def cochainSingleLinearMap
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) {q : ℤ} (T : Triplet q) :
    (K.X T.p →ₗ[R] L.X T.q) →ₗ[R] Cochain K L q := by
  classical
  exact (LinearMap.single R (fun T : Triplet q => K.X T.p ⟶ L.X T.q) T).comp
    (ModuleCat.homLinearEquiv (S := R)).symm.toLinearMap

private theorem cochainSingleLinearMap_v_self
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) {q : ℤ} (T : Triplet q)
    (g : K.X T.p →ₗ[R] L.X T.q) :
    ((cochainSingleLinearMap K L T g).v T.p T.q T.hpq).hom = g := by
  classical
  change (Pi.single (M := fun T : Triplet q => K.X T.p ⟶ L.X T.q) T (ModuleCat.ofHom g) T).hom = g
  rw [Pi.single_eq_same]
  rfl

private theorem cochainSingleLinearMap_v_ne
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) {q : ℤ} (T : Triplet q)
    (g : K.X T.p →ₗ[R] L.X T.q) (i j : ℤ) (hij : i + q = j) (h : i ≠ T.p) :
    (cochainSingleLinearMap K L T g).v i j hij = 0 := by
  have hT : (⟨i, j, hij⟩ : Triplet q) ≠ T := fun e => h (congrArg Triplet.p e)
  classical
  change Pi.single (M := fun T : Triplet q => K.X T.p ⟶ L.X T.q) T
    (ModuleCat.ofHom g) ⟨i, j, hij⟩ = 0
  exact Pi.single_eq_of_ne hT _

/-- Restrict an iterated cochain to one degree of its innermost argument, with the
Koszul sign of evaluation. -/
private noncomputable def restrictEvaluation
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n s : ℤ) :
    Cochain (HomComplexR R K L) M n →ₗ[R]
      (∀ T : Triplet (n - s), (K.X s →ₗ[R] L.X T.p) →ₗ[R] M.X T.q) where
  toFun β T := (s + (-T.p) * s).negOnePow •
    ((β.v (T.p - s) T.q (by have := T.hpq; omega)).hom.comp
      (cochainSingleLinearMap K L ⟨s, T.p, by omega⟩))
  map_add' β γ := by
    ext T g
    simp [Cochain.add_v, LinearMap.comp_apply, smul_add]
  map_smul' c β := by
    ext T g
    simp only [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply,
      LinearMap.comp_apply, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

private theorem restrictEvaluation_apply
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n s : ℤ)
    (β : Cochain (HomComplexR R K L) M n) (T : Triplet (n - s))
    (g : K.X s →ₗ[R] L.X T.p) :
    restrictEvaluation K L M n s β T g = (s + (-T.p) * s).negOnePow •
      (β.v (T.p - s) T.q (by have := T.hpq; omega)).hom
        (cochainSingleLinearMap K L ⟨s, T.p, by omega⟩ g) := rfl

/-- **Stacks 0A60**.
The homogeneous formula for `chainEvaluation`: the image of `φ ⊗ k` sends a cochain `ψ`
to `φ (ψ k)`, up to the Koszul sign `(-1)^(s + (-a) s)` of evaluation. -/
@[stacks 0A60]
theorem chainEvaluation_tmul
    (K J I : CochainComplex (ModuleCat.{u} R) ℤ)
    (t s n q p a : ℤ) (hn : t + s = n) (hq : q + n = p)
    (ha : s + q = a) (hp : a + t = p)
    (φ : Cochain J I t) (k : K.X s) (ψ : Cochain K J q) :
    ((((chainEvaluation K J I).f n).hom
      ((ιTensorObj (HomComplexR R J I) K t s n hn).hom (φ ⊗ₜ[R] k))).v
        q p hq).hom ψ =
      (s + (-a) * s).negOnePow •
        (φ.v a p hp).hom ((ψ.v s a ha).hom k) := by
  have ha' : p - t = a := by omega
  change (((ιTensorObj (HomComplexR R J I) K t s n hn ≫
    evaluationFun K J I n).hom (φ ⊗ₜ[R] k)).v q p hq).hom ψ = _
  have he := evaluationFun_apply K J I t s n hn φ k q p hq ψ
  have hcomponent :
      (φ.v (p - t) p (by omega)).hom ((ψ.v s (p - t) (by omega)).hom k) =
        (φ.v a p hp).hom ((ψ.v s a ha).hom k) := by
    have aux (b c : ℤ) (hbc : b = c) (hb : b + t = p) (hc : c + t = p)
        (hψb : s + q = b) (hψc : s + q = c) :
        (φ.v b p hb).hom ((ψ.v s b hψb).hom k) =
          (φ.v c p hc).hom ((ψ.v s c hψc).hom k) := by
      subst c
      rfl
    exact aux (p - t) a ha' (by omega) hp (by omega) ha
  have hsign : (s + (-(p - t)) * s).negOnePow = (s + (-a) * s).negOnePow := by
    rw [ha']
  rw [hsign] at he
  exact he.trans (congrArg ((s + (-a) * s).negOnePow • ·) hcomponent)

private theorem restrictEvaluation_tmul_self
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n s : ℤ)
    [Module.Finite R (K.X s)] [Module.Projective R (K.X s)]
    (φ : Cochain L M (n - s)) (k : K.X s) :
    restrictEvaluation K L M n s
      (((chainEvaluation K L M).f n).hom
        ((ιTensorObj (HomComplexR R L M) K (n - s) s n (by omega)).hom (φ ⊗ₜ[R] k))) =
      cochainTensorEvaluationEquiv (K.X s) L M (n - s) (φ ⊗ₜ[R] k) := by
  ext T g
  rw [restrictEvaluation_apply, chainEvaluation_tmul K L M (n - s) s n (T.p-s) T.q T.p
    (by omega) (by have := T.hpq; omega) (by omega) T.hpq,
    cochainSingleLinearMap_v_self, cochainTensorEvaluationEquiv_tmul]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  rfl

private theorem restrictEvaluation_tmul_ne
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n s r : ℤ) (h : r ≠ s)
    (φ : Cochain L M (n - r)) (k : K.X r) :
    restrictEvaluation K L M n s
      (((chainEvaluation K L M).f n).hom
        ((ιTensorObj (HomComplexR R L M) K (n - r) r n (by omega)).hom (φ ⊗ₜ[R] k))) = 0 := by
  ext T g
  rw [restrictEvaluation_apply, chainEvaluation_tmul K L M (n - r) r n (T.p-s) T.q
    (r + (T.p-s)) (by omega) (by have := T.hpq; omega) rfl (by have := T.hpq; omega)]
  rw [cochainSingleLinearMap_v_ne K L _ _ _ _ _ h]
  simp

private theorem linearMap_eq_zero_of_isZero
    {A B : ModuleCat.{u} R} (f : A →ₗ[R] B) (h : IsZero A ∨ IsZero B) :
    f = 0 := by
  rcases h with h | h
  · have := ModuleCat.isZero_iff_subsingleton.mp h
    ext a
    rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
  · have := ModuleCat.isZero_iff_subsingleton.mp h
    exact Subsingleton.elim _ _

private theorem cochainTensor_eq_zero
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n s : ℤ)
    [Module.Finite R (K.X s)] [Module.Projective R (K.X s)]
    (h : ∀ a p : ℤ, a + (n - s) = p →
      IsZero (K.X s) ∨ IsZero (L.X a) ∨ IsZero (M.X p))
    (x : Cochain L M (n - s) ⊗[R] K.X s) : x = 0 := by
  apply (cochainTensorEvaluationEquiv (K.X s) L M (n - s)).injective
  rw [map_zero]
  ext T g
  rcases h T.p T.q T.hpq with hK | hL | hM
  · rw [linearMap_eq_zero_of_isZero g (Or.inl hK), map_zero]
    rfl
  · rw [linearMap_eq_zero_of_isZero g (Or.inr hL), map_zero]
    rfl
  · have := ModuleCat.isZero_iff_subsingleton.mp hM
    exact Subsingleton.elim _ _

private theorem restrictEvaluation_eq_zero
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n s : ℤ)
    (h : ∀ a p : ℤ, a + (n - s) = p →
      IsZero (K.X s) ∨ IsZero (L.X a) ∨ IsZero (M.X p))
    (β : Cochain (HomComplexR R K L) M n) :
    restrictEvaluation K L M n s β = 0 := by
  ext T g
  rw [restrictEvaluation_apply]
  rcases h T.p T.q T.hpq with hK | hL | hM
  · rw [linearMap_eq_zero_of_isZero g (Or.inl hK), map_zero, map_zero, smul_zero]
    rfl
  · rw [linearMap_eq_zero_of_isZero g (Or.inr hL), map_zero, map_zero, smul_zero]
    rfl
  · have := ModuleCat.isZero_iff_subsingleton.mp hM
    exact Subsingleton.elim _ _

private theorem sum_cochainSingleLinearMap_eq_self
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) (S : Finset ℤ)
    (h : ∀ s ∉ S, IsZero (K.X s) ∨ IsZero (L.X (s + q)))
    (ψ : Cochain K L q) :
    ∑ s ∈ S, cochainSingleLinearMap K L ⟨s, s + q, rfl⟩ ((ψ.v s (s + q) rfl).hom) = ψ := by
  classical
  refine Cochain.ext _ _ fun i j hij => ?_
  subst j
  change (∑ s ∈ S, cochainSingleLinearMap K L ⟨s, s + q, rfl⟩
    ((ψ.v s (s + q) rfl).hom)) ⟨i, i+q, rfl⟩ = ψ ⟨i, i+q, rfl⟩
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · exact ModuleCat.hom_ext (cochainSingleLinearMap_v_self K L _ _)
  · exact fun b _ hbi => cochainSingleLinearMap_v_ne K L _ _ _ _ _ (Ne.symm hbi)
  · intro hi
    rw [show (ψ.v i (i+q) rfl).hom = 0 from
      linearMap_eq_zero_of_isZero _ (h i hi), map_zero]
    rfl

private theorem evaluation_component_eq_zero_of_restrict
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n s a q p : ℤ)
    (ha : s + q = a) (hp : q + n = p) (β : Cochain (HomComplexR R K L) M n)
    (hβ : restrictEvaluation K L M n s β = 0) (g : K.X s →ₗ[R] L.X a) :
    (β.v q p hp).hom (cochainSingleLinearMap K L ⟨s, a, ha⟩ g) = 0 := by
  have hq : q = a - s := by omega
  subst q
  have hz := congrArg (fun f => f ⟨a, p, by omega⟩ g) hβ
  change (s + (-a) * s).negOnePow •
    (β.v (a - s) p hp).hom (cochainSingleLinearMap K L ⟨s, a, ha⟩ g) = 0 at hz
  simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero] using
    congrArg ((s + (-a) * s).negOnePow • ·) hz

/-- The homogeneous restrictions jointly detect an iterated cochain when every degree
outside the finite set `S` contributes zero. -/
private theorem restrictEvaluation_injective
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (S : Finset ℤ)
    (h : ∀ s ∉ S, ∀ a p : ℤ, a + (n - s) = p →
      IsZero (K.X s) ∨ IsZero (L.X a) ∨ IsZero (M.X p)) :
    Function.Injective (fun β : Cochain (HomComplexR R K L) M n =>
      fun s => restrictEvaluation K L M n s β) := by
  change Function.Injective (LinearMap.pi (fun s => restrictEvaluation K L M n s))
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun β hβ => ?_)
  refine Cochain.ext _ _ fun q p hqp => ModuleCat.hom_ext (LinearMap.ext fun ψ => ?_)
  by_cases hp : IsZero (M.X p)
  · have := ModuleCat.isZero_iff_subsingleton.mp hp
    exact Subsingleton.elim _ _
  have hs : ∀ s ∉ S, IsZero (K.X s) ∨ IsZero (L.X (s + q)) := fun s hs =>
    (h s hs (s + q) p (by omega)).imp_right fun h' => h'.resolve_right hp
  rw [← sum_cochainSingleLinearMap_eq_self K L q S hs ψ, map_sum]
  change ∑ s ∈ S, (β.v q p hqp).hom
    (cochainSingleLinearMap K L ⟨s, s + q, rfl⟩ ((ψ.v s (s + q) rfl).hom)) = 0
  exact Finset.sum_eq_zero fun s _ =>
    evaluation_component_eq_zero_of_restrict K L M n s (s + q) q p rfl hqp β (congrFun hβ s) _

/-- Degreewise evaluation is bijective when only finitely many degrees of the finite
projective complex can contribute. -/
private theorem evaluation_bijective_of_support
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ s, Module.Finite R (K.X s)] [∀ s, Module.Projective R (K.X s)]
    (n : ℤ) (S : Finset ℤ)
    (hS : ∀ s ∉ S, ∀ a p : ℤ, a + (n - s) = p →
      IsZero (K.X s) ∨ IsZero (L.X a) ∨ IsZero (M.X p)) :
    Function.Bijective ((chainEvaluation K L M).f n).hom := by
  classical
  let F := ((chainEvaluation K L M).f n).hom
  let E (s : ℤ) := cochainTensorEvaluationEquiv (K.X s) L M (n - s)
  let I (s : ℤ) := (ιTensorObj (HomComplexR R L M) K (n - s) s n (by omega)).hom
  let P (s : ℤ) := (E s).symm.toLinearMap.comp (restrictEvaluation K L M n s)
  have hself (s : ℤ) (x : Cochain L M (n - s) ⊗[R] K.X s) : P s (F (I s x)) = x := by
    induction x using TensorProduct.inductionOn with
    | tmul φ k =>
      change (E s).symm (restrictEvaluation K L M n s (F (I s (φ ⊗ₜ[R] k)))) = _
      rw [restrictEvaluation_tmul_self, LinearEquiv.symm_apply_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hne (s r : ℤ) (h : r ≠ s) (x : Cochain L M (n - r) ⊗[R] K.X r) :
      P s (F (I r x)) = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul φ k =>
      change (E s).symm (restrictEvaluation K L M n s (F (I r (φ ⊗ₜ[R] k)))) = 0
      rw [restrictEvaluation_tmul_ne K L M n s r h, map_zero]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  let G := ∑ s ∈ S, (I s).comp (P s)
  have hG (β : Cochain (HomComplexR R K L) M n) :
      G β = ∑ s ∈ S, I s (P s β) := by
    simp only [G, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  have hGF : G.comp F = LinearMap.id := by
    refine congrArg ModuleCat.Hom.hom (?_ : ModuleCat.ofHom (G.comp F) = ModuleCat.ofHom .id)
    refine mapBifunctor.hom_ext fun t r htr => ?_
    obtain rfl : t = n - r := by change t + r = n at htr; omega
    refine ModuleCat.hom_ext (TensorProduct.ext (LinearMap.ext fun φ => LinearMap.ext fun k => ?_))
    change G (F (I r (φ ⊗ₜ[R] k))) = I r (φ ⊗ₜ[R] k)
    by_cases hr : r ∈ S
    · rw [hG, Finset.sum_eq_single r, hself]
      · exact fun b _ hbr => by rw [hne b r (Ne.symm hbr), map_zero]
      · exact absurd hr
    · simp only [cochainTensor_eq_zero K L M n r (hS r hr) (φ ⊗ₜ[R] k), map_zero]
  have hFG (β : Cochain (HomComplexR R K L) M n) : F (G β) = β := by
    refine restrictEvaluation_injective K L M n S hS (funext fun s => (E s).symm.injective ?_)
    change P s (F (G β)) = P s β
    rw [hG, map_sum, map_sum]
    by_cases hs : s ∈ S
    · rw [Finset.sum_eq_single s, hself]
      · exact fun b _ hbs => hne s b hbs _
      · exact absurd hs
    · rw [Finset.sum_eq_zero (fun b hb => hne s b (fun h => hs (h ▸ hb)) _)]
      change 0 = (E s).symm (restrictEvaluation K L M n s β)
      rw [restrictEvaluation_eq_zero K L M n s (hS s hs), map_zero]
  exact ⟨Function.LeftInverse.injective (LinearMap.congr_fun hGF),
    Function.RightInverse.surjective hFG⟩

/-- If `K` is a bounded complex of finitely generated projective modules, the evaluation
morphism `Hom^•(J, I) ⊗ K → Hom^•(Hom^•(K, J), I)` is an isomorphism. -/
theorem chainEvaluation_isIso_of_bounded
    (K J I : CochainComplex (ModuleCat R) ℤ)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    IsIso (chainEvaluation K J I) := by
  have (n : ℤ) : IsIso ((chainEvaluation K J I).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (evaluation_bijective_of_support K J I n (Finset.Icc a b) fun s hs _ _ _ => Or.inl (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hs
        rcases hs with h | h
        · exact K.isZero_of_isStrictlyGE a s h
        · exact K.isZero_of_isStrictlyLE b s h))
  exact HomologicalComplex.Hom.isIso_of_components _

/-- If `K` is a bounded above complex of finitely generated projective modules, `J` is bounded
below and `I` is bounded above, the evaluation morphism
`Hom^•(J, I) ⊗ K → Hom^•(Hom^•(K, J), I)` is an isomorphism. -/
theorem chainEvaluation_isIso_of_boundedAbove_boundedBelow
    (K J I : CochainComplex (ModuleCat R) ℤ)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    (a b d : ℤ) [K.IsStrictlyLE b] [J.IsStrictlyGE a] [I.IsStrictlyLE d] :
    IsIso (chainEvaluation K J I) := by
  have (n : ℤ) : IsIso ((chainEvaluation K J I).f n) := by
    refine (ConcreteCategory.isIso_iff_bijective _).mpr
      (evaluation_bijective_of_support K J I n (Finset.Icc (a + n - d) b) fun s hs i p hip => ?_)
    by_cases hsb : b < s
    · exact Or.inl (K.isZero_of_isStrictlyLE b s hsb)
    by_cases hia : i < a
    · exact Or.inr (Or.inl (J.isZero_of_isStrictlyGE a i hia))
    · refine Or.inr (Or.inr (I.isZero_of_isStrictlyLE d p ?_))
      simp only [Finset.mem_Icc] at hs
      omega
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Sign comparison behind Stacks 0A61, whose statement is
`ChainEvaluation.chainEvaluation_eq_tensorHomEquiv_symm`.
For any Koszul symmetric structure on cochain complexes — one whose braiding restricts on the
summand `A^p ⊗ B^q` to `(-1)^{pq}` times the symmetry of `ModuleCat R` — the braiding on the
summand `K^r ⊗ Hom^{a-r}(K, J)` carries the sign `(-1)^{r + (-a) r}` that occurs in the direct
construction of evaluation into an iterated Hom complex (`chainEvaluation_tmul`): the sign
introduced by the braiding is the sign of the direct construction. -/
theorem homComplex_braiding_sign_eq_evaluation_sign
    (s : SymmetricCategory (CochainComplex (ModuleCat.{u} R) ℤ))
    (hKoszul : ∀ (A B : CochainComplex (ModuleCat.{u} R) ℤ) (p q n : ℤ) (h : p + q = n),
      ιTensorObj A B p q n h ≫ (s.toBraidedCategory.braiding A B).hom.f n =
        ((p * q).negOnePow : ℤˣ) •
          ((β_ (A.X p) (B.X q)).hom ≫
            ιTensorObj B A q p n (by simpa [add_comm] using h)))
    (K J : CochainComplex (ModuleCat.{u} R) ℤ) (a r : ℤ) :
    ιTensorObj K (HomComplexR R K J) r (a - r) a (by omega) ≫
        (s.toBraidedCategory.braiding K (HomComplexR R K J)).hom.f a =
      ((r + (-a) * r).negOnePow : ℤˣ) •
        ((β_ (K.X r) ((HomComplexR R K J).X (a - r))).hom ≫
          ιTensorObj (HomComplexR R K J) K (a - r) r a (by omega)) := by
  rw [hKoszul K (HomComplexR R K J) r (a - r) a (by omega)]
  congr 1
  rw [Int.negOnePow_eq_iff]
  rw [show r * (a - r) - (r + -a * r) = 2 * (a * r) - r * (r + 1) by ring]
  exact Even.sub (even_two_mul (a * r)) r.even_mul_succ_self

end ChainEvaluation
