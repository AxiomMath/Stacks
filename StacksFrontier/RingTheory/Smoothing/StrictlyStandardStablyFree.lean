module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import StacksFrontier.Algebra.Module.StablyFree
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Smoothing.SingularIdeals
public import StacksFrontier.RingTheory.Smoothing.AlgebraPresentation
public import StacksFrontier.RingTheory.Smoothing.StandardElementsSingular

/-!
# Strictly standard elements have stably free differentials

Let `R → A` be a ring map of finite presentation and let `a ∈ A`. If `a` is
strictly standard in `A` over `R`, then `A_a` is smooth over `R` and the module of Kähler
differentials of the localization `A_a` over `R` is stably free as an `A_a`-module. This is the
implication (5) ⇒ (2) of Stacks 16.3.7.

The proof is the one of the source. Fix a presentation `A = R[x_1, …, x_n]/(f_1, …, f_m)`
and an integer `c` realizing the strict standardness of `a`. The strictly standard
equation supplies an `A`-linear left inverse, up to the factor `a`, of the Jacobian
map of the first `c` relations (Stacks 07ET); after inverting `a` that makes the
Jacobian map injective. Condition 16.2.3.2 makes the classes of the first `c`
relations generate the localized cotangent module, so that module is free on `c`
generators and the localized cotangent complex is injective. The conormal sequence
`Cotangent → CotangentSpace → Ω` then exhibits `Ω_{A_a/R}` as the third term of a
short exact sequence whose other two terms are finite free, and the two-out-of-three
property of stably free modules (Stacks 0BC4) concludes.

## Main definitions

None.

## Main results

* `Stacks.Smoothing.smooth_and_isStablyFree_kaehlerDifferential_of_isStrictlyStandard`: strict
  standardness of the distinguished element implies smoothness of the localization and stable
  freeness of the localized module of differentials, i.e. condition (2).

## Implementation notes

The localization `A_a` is `Localization.Away a` and the module of differentials is
Mathlib's `KaehlerDifferential`, as in the other implications of Stacks 16.3.7 in
`StacksFrontier.RingTheory.Smoothing.StandardnessConditions`. Smoothness of `A_a`, which
is needed to know that the conormal sequence is exact on the right in the required
sense, is the implication (5) ⇒ (1) proved in
`StacksFrontier.RingTheory.Smoothing.StandardElementsSingular`; the source instead quotes the
description of the singular ideal, of which that implication is one half.

## References

* [Stacks Project, Tag 07EZ](https://stacks.math.columbia.edu/tag/07EZ)
* [Stacks Project, Tag 07ET](https://stacks.math.columbia.edu/tag/07ET)
* [Stacks Project, Tag 0BC4](https://stacks.math.columbia.edu/tag/0BC4)
-/

@[expose] public section

namespace Stacks.Smoothing

open MvPolynomial
open scoped TensorProduct

universe u v

/-- In the cotangent module of an extension, a congruence `u x ≡ ∑ bᵢ yᵢ` modulo the square of
the kernel becomes the corresponding relation between the classes. -/
private theorem algebraMap_smul_cotangentMk_eq_sum {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (E : Algebra.Extension R B) {ι : Type*} [Fintype ι] (u : E.Ring) (x : E.ker)
    (b : ι → E.Ring) (y : ι → E.ker) (h : u * x - ∑ i, b i * y i ∈ E.ker ^ 2) :
    algebraMap E.Ring B u • Algebra.Extension.Cotangent.mk x =
      ∑ i, algebraMap E.Ring B (b i) • Algebra.Extension.Cotangent.mk (y i) := by
  simp only [algebraMap_smul, ← map_smul, ← map_sum]
  exact (Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem _ _).2 (by simpa using h)

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- If `a` is strictly standard for `P` and `c`, then `a` times the class of any relation past
the first `c` is a combination of the classes of the first `c` relations. -/
private theorem exists_smul_cotangentMk_eq_sum_of_isStrictlyStandardFor {a : A}
    (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) (hstrict : P.IsStrictlyStandardFor a c hcm)
    (k : Fin P.m) (hk : c ≤ k.1) :
    ∃ b : Fin c → A, a • Algebra.Extension.Cotangent.mk
        (P := (toAlgebraPresentation P).toGenerators.toExtension)
        ⟨P.f k, (toAlgebraPresentation P).relation_mem_ker k⟩ =
      ∑ i, b i • Algebra.Extension.Cotangent.mk
        (P := (toAlgebraPresentation P).toGenerators.toExtension)
        ⟨P.f (Fin.castLE hcm i), (toAlgebraPresentation P).relation_mem_ker _⟩ := by
  let Q := toAlgebraPresentation P
  let eG := generatorsToExtensionRingEquiv Q.toGenerators
  obtain ⟨u, hu⟩ := P.exists_isLift a
  let j : Fin (P.m - c) := ⟨k.1 - c, by omega⟩
  have hjk : (⟨c + j.1, by omega⟩ : Fin P.m) = k := Fin.ext (by dsimp only [j]; omega)
  have hmem : u * P.f k ∈ P.firstRelIdeal c hcm + P.relIdeal ^ 2 := by
    simpa only [hjk] using hstrict.2 j u hu
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hx
  have hb' : ∑ i, b i * P.f (Fin.castLE hcm i) = x := hb
  have hm : eG (u * P.f k - ∑ i, b i * P.f (Fin.castLE hcm i)) ∈
      Q.toGenerators.toExtension.ker ^ 2 := by
    rw [← generatorsToExtensionRingEquiv_map_ker, ← Ideal.map_pow]
    refine Ideal.mem_map_of_mem eG ?_
    rw [ker_toAlgebraPresentation, hb', ← hxy, add_sub_cancel_left]
    exact hy
  have hua : algebraMap Q.toExtension.Ring A (eG u) = a := by
    rw [generatorsToExtensionRingEquiv_algebraMap]
    change MvPolynomial.aeval Q.toGenerators.val u = a
    rw [aeval_toAlgebraPresentation, hu]
  have hfE (j : Fin P.m) : eG (P.f j) ∈ Q.toGenerators.toExtension.ker := by
    rw [← generatorsToExtensionRingEquiv_map_ker]
    exact Ideal.mem_map_of_mem eG (Q.relation_mem_ker j)
  have hd (j : Fin P.m) : Algebra.Extension.Cotangent.mk
      (P := Q.toGenerators.toExtension) ⟨P.f j, Q.relation_mem_ker j⟩ =
      Algebra.Extension.Cotangent.mk ⟨eG (P.f j), hfE j⟩ :=
    congrArg _ (Subtype.ext (generatorsToExtensionRingEquiv_apply _ _).symm)
  refine ⟨fun i => algebraMap Q.toExtension.Ring A (eG (b i)), ?_⟩
  simp only [hd]
  rw [← hua]
  exact algebraMap_smul_cotangentMk_eq_sum _ (eG u) ⟨_, hfE k⟩ (fun i => eG (b i)) _
    (by simpa [map_sub, map_mul, map_sum] using hm)

/-- After any base change, the classes of the relations of a finite presentation span the
cotangent module. -/
private theorem surjective_linearCombination_tmul_relation {T : Type*} [CommRing T] [Algebra A T]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m)) :
    Function.Surjective (Fintype.linearCombination T fun j => (1 : T) ⊗ₜ[A]
      Algebra.Extension.Cotangent.mk (P := P.toGenerators.toExtension)
        ⟨P.relation j, P.relation_mem_ker j⟩) := by
  classical
  let G : (Fin m → A) →ₗ[A] P.toExtension.Cotangent := Fintype.linearCombination A fun j =>
    Algebra.Extension.Cotangent.mk (P := P.toGenerators.toExtension)
      ⟨P.relation j, P.relation_mem_ker j⟩
  let bPi : Module.Basis (Fin m) A (Fin m → A) := Pi.basisFun A (Fin m)
  let ePi : T ⊗[A] (Fin m → A) ≃ₗ[T] (Fin m → T) := (bPi.baseChange T).equivFun
  have h : Fintype.linearCombination T (fun j => (1 : T) ⊗ₜ[A]
      Algebra.Extension.Cotangent.mk (P := P.toGenerators.toExtension)
        ⟨P.relation j, P.relation_mem_ker j⟩) = G.baseChange T ∘ₗ ePi.symm := by
    refine LinearMap.ext fun x => ?_
    change (∑ i : Fin m, x i • ((1 : T) ⊗ₜ[A] Algebra.Extension.Cotangent.mk
        (P := P.toGenerators.toExtension) ⟨P.relation i, P.relation_mem_ker i⟩)) =
      G.baseChange T ((bPi.baseChange T).equivFun.symm x)
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    simp only [map_smul, LinearMap.baseChange_tmul, Module.Basis.baseChange_apply]
    congr 1
    ext i
    simp [G, bPi, Fintype.linearCombination_apply]
  rw [h]
  exact (LinearMap.lTensor_surjective T (relation_classes_surjective P)).comp
    ePi.symm.surjective

/-- If `ψ ∘ J` is multiplication by `a` and `a` becomes a unit in `T`, then the matrix `J`
becomes injective over `T`. -/
private theorem injective_toLin'_map_of_comp_eq_lsmul {B T : Type*} [CommRing B] [CommRing T]
    [Algebra B T] {m n : Type*} [Fintype m] [Finite n] [DecidableEq m]
    {J : Matrix n m B} {ψ : (n → B) →ₗ[B] (m → B)} {a : B}
    (hψ : ψ ∘ₗ Matrix.toLin' J = LinearMap.lsmul B (m → B) a)
    (ha : IsUnit (algebraMap B T a)) :
    Function.Injective (Matrix.toLin' (J.map (algebraMap B T))) := by
  classical
  have := Fintype.ofFinite n
  let JU := Pi.basisFun B m
  let JV := Pi.basisFun B n
  let ψT := (LinearMap.toMatrix JV JU ψ).map (algebraMap B T)
  have hJ : LinearMap.toMatrix JU JV (Matrix.toLin' J) = J := by
    ext i j
    simp [LinearMap.toMatrix_apply, JU, JV, Matrix.toLin'_apply, Matrix.mulVec_single,
      Pi.basisFun_apply]
  have hψJ : LinearMap.toMatrix JV JU ψ * J = Matrix.diagonal fun _ => a := by
    have hmat := LinearMap.toMatrix_comp JU JV JU ψ (Matrix.toLin' J)
    rw [hJ, hψ] at hmat
    have hdiag : LinearMap.toMatrix JU JU (LinearMap.lsmul B (m → B) a) =
        Matrix.diagonal fun _ => a := by
      ext i j
      simp [JU, LinearMap.lsmul_apply, Matrix.diagonal_apply, Pi.single_apply]
    exact hmat.symm.trans hdiag
  have hcomp : Matrix.toLin' ψT ∘ₗ Matrix.toLin' (J.map (algebraMap B T)) =
      LinearMap.lsmul T (m → T) (algebraMap B T a) := by
    rw [← Matrix.toLin'_mul, ← Matrix.map_mul, hψJ, Matrix.diagonal_map (map_zero _)]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, Matrix.diagonal_apply,
      LinearMap.lsmul_apply, dotProduct]
  intro x y hxy
  have h : (Matrix.toLin' ψT ∘ₗ Matrix.toLin' (J.map (algebraMap B T))) x =
      (Matrix.toLin' ψT ∘ₗ Matrix.toLin' (J.map (algebraMap B T))) y :=
    congrArg (Matrix.toLin' ψT) hxy
  rw [hcomp] at h
  exact ha.smul_left_cancel.mp h

/-- In the bases given by the variables, the base change of the cotangent complex restricted to
the classes of the first `c` relations is the Jacobian matrix of those relations. -/
private theorem equivFun_comp_cotangentComplex_comp_linearCombination (P : Presentation R A) (c : ℕ)
    (hcm : c ≤ P.m) (T : Type*) [CommRing T] [Algebra A T] :
    ((toAlgebraPresentation P).toGenerators.cotangentSpaceBasis.baseChange T).equivFun.comp
      (((toAlgebraPresentation P).toGenerators.toExtension.cotangentComplex.baseChange T).comp
        (Fintype.linearCombination T fun j : Fin c => (1 : T) ⊗ₜ[A]
          Algebra.Extension.Cotangent.mk
            (P := (toAlgebraPresentation P).toGenerators.toExtension)
            ⟨P.f (Fin.castLE hcm j), (toAlgebraPresentation P).relation_mem_ker _⟩)) =
      Matrix.toLin' ((jacobianMatrix P c hcm).map (algebraMap A T)) := by
  classical
  let Q := toAlgebraPresentation P
  let E := Q.toGenerators.toExtension
  have hcol (j : Fin c) :
      (Q.toGenerators.cotangentSpaceBasis.baseChange T).equivFun
        (E.cotangentComplex.baseChange T ((1 : T) ⊗ₜ[A] Algebra.Extension.Cotangent.mk
          (P := E) ⟨P.f (Fin.castLE hcm j), Q.relation_mem_ker _⟩)) = fun i =>
        algebraMap A T (P.lift (MvPolynomial.pderiv i (P.f (Fin.castLE hcm j)))) := by
    ext i
    rw [Module.Basis.equivFun_apply]
    change (Q.toGenerators.cotangentSpaceBasis.baseChange T).repr
      (1 ⊗ₜ[A] E.cotangentComplex (Algebra.Extension.Cotangent.mk (P := E)
        ⟨P.f (Fin.castLE hcm j), Q.relation_mem_ker _⟩)) i = _
    rw [Module.Basis.baseChange_repr_tmul, relation_coordinates, ← algebraMap_smul (A := T)
      (R := A) (P.lift (MvPolynomial.pderiv i (P.f (Fin.castLE hcm j)))) (1 : T)]
    simp
  refine (Pi.basisFun T (Fin c)).ext fun j => funext fun i => ?_
  change (Q.toGenerators.cotangentSpaceBasis.baseChange T).equivFun
    (E.cotangentComplex.baseChange T (Fintype.linearCombination T (fun j : Fin c =>
      (1 : T) ⊗ₜ[A] Algebra.Extension.Cotangent.mk (P := E)
        ⟨P.f (Fin.castLE hcm j), Q.relation_mem_ker _⟩) (Pi.basisFun T (Fin c) j))) i = _
  rw [Pi.basisFun_apply, Fintype.linearCombination_apply_single, one_smul, hcol]
  simp [Matrix.toLin'_apply, Matrix.mulVec_single, jacobianMatrix]

/-- The localized cotangent module of a presentation realizing the strict
standardness of `a` is free on the first `c` relations, and the localized cotangent
complex is injective. -/
private theorem localized_cotangent_free (S : SixStandardnessConditions)
    (P : Presentation S.R S.A) (c : ℕ) (hcm : c ≤ P.m)
    (hstrict : P.IsStrictlyStandardFor S.a c hcm) :
    ∃ _b : Module.Basis (Fin c) (Localization.Away S.a)
        (Localization.Away S.a ⊗[S.A]
          (toAlgebraPresentation P).toGenerators.toExtension.Cotangent),
      Function.Injective
        ((toAlgebraPresentation P).toGenerators.toExtension.cotangentComplex.baseChange
          (Localization.Away S.a)) := by
  classical
  let Q := toAlgebraPresentation P
  let T := Localization.Away S.a
  let E := Q.toGenerators.toExtension
  let d : Fin P.m → E.Cotangent := fun j =>
    Algebra.Extension.Cotangent.mk (P := E) ⟨P.f j, Q.relation_mem_ker j⟩
  let v : Fin c → T ⊗[S.A] E.Cotangent := fun j => 1 ⊗ₜ[S.A] d (Fin.castLE hcm j)
  let F : (Fin c → T) →ₗ[T] T ⊗[S.A] E.Cotangent := Fintype.linearCombination T v
  let vall : Fin P.m → T ⊗[S.A] E.Cotangent := fun j => 1 ⊗ₜ[S.A] d j
  have haunit : IsUnit (algebraMap S.A T S.a) := IsLocalization.Away.algebraMap_isUnit S.a
  -- Condition 16.2.3.2 makes every relation class a combination of the first `c`.
  have hrel (k : Fin P.m) : vall k ∈ LinearMap.range F := by
    by_cases hk : k.1 < c
    · refine ⟨Pi.single ⟨k.1, hk⟩ 1, ?_⟩
      simp [F, v, vall, show Fin.castLE hcm (⟨k.1, hk⟩ : Fin c) = k from Fin.ext rfl]
    obtain ⟨b, hb⟩ :=
      exists_smul_cotangentMk_eq_sum_of_isStrictlyStandardFor P c hcm hstrict k (by omega)
    have h₁ : algebraMap S.A T S.a • vall k = ∑ i, algebraMap S.A T (b i) • v i := by
      simp only [vall, v, d, algebraMap_smul, ← TensorProduct.tmul_smul, hb,
        TensorProduct.tmul_sum]
    have hinv : haunit.unit⁻¹.val * algebraMap S.A T S.a = 1 := haunit.unit.inv_mul
    refine ⟨fun i => haunit.unit⁻¹.val * algebraMap S.A T (b i), ?_⟩
    rw [Fintype.linearCombination_apply]
    simp_rw [mul_smul, ← Finset.smul_sum, ← h₁, smul_smul, hinv, one_smul]
  -- Hence the first `c` relation classes generate the localized cotangent module.
  have hFsurj : Function.Surjective F := by
    intro x
    obtain ⟨y, rfl⟩ := surjective_linearCombination_tmul_relation (T := T) Q x
    rw [Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hrel j)
  -- The strictly standard equation makes the Jacobian injective after inverting `a`.
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_lsmul_of_eq_sum_jacobianMinor P S.a c hcm hstrict.1
  have hHinj := injective_toLin'_map_of_comp_eq_lsmul (T := T) hψ haunit
  have hFcoord := equivFun_comp_cotangentComplex_comp_linearCombination P c hcm T
  let f := E.cotangentComplex.baseChange T
  let B := (Q.toGenerators.cotangentSpaceBasis.baseChange T).equivFun
  have key : Function.Injective (f ∘ F) := fun x y hxy => hHinj <| by
    rw [← hFcoord]
    exact congrArg B hxy
  have hfinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := hFsurj x
    obtain ⟨y', rfl⟩ := hFsurj y
    exact congrArg F (key hxy)
  exact ⟨(Pi.basisFun T (Fin c)).map (LinearEquiv.ofBijective F ⟨key.of_comp, hFsurj⟩), hfinj⟩

/-- **Stacks 16.3.7, (5) ⇒ (2).** If the distinguished element is strictly standard,
then its localization is smooth and its module of differentials is stably free. -/
@[stacks 07EZ "clause (d), the implication (5) ⇒ (2): if `a` is strictly standard in `A` over \
`R` then `A_a` is smooth over `R` and `Ω_{A_a/R}` is stably free. Both conjuncts of (2) are \
concluded; the smoothness one is the implication (5) ⇒ (1) of 07CA"]
theorem smooth_and_isStablyFree_kaehlerDifferential_of_isStrictlyStandard
    (S : SixStandardnessConditions)
    (h : IsStrictlyStandard (R := S.R) S.a) :
    Algebra.Smooth S.R (Localization.Away S.a) ∧
      Module.IsStablyFree (Localization.Away S.a)
        (KaehlerDifferential S.R (Localization.Away S.a)) := by
  classical
  obtain ⟨P, c, hcn, hcm, hstrict⟩ := h
  have hsmooth : Algebra.Smooth S.R (Localization.Away S.a) :=
    smooth_localizationAway_of_isStrictlyStandard ⟨P, c, hcn, hcm, hstrict⟩
  let T := Localization.Away S.a
  let E := (toAlgebraPresentation P).toGenerators.toExtension
  let f : T ⊗[S.A] E.Cotangent →ₗ[T] T ⊗[S.A] E.CotangentSpace :=
    E.cotangentComplex.baseChange T
  let g : T ⊗[S.A] E.CotangentSpace →ₗ[T] T ⊗[S.A] Ω[S.A⁄S.R] :=
    E.toKaehler.baseChange T
  have : Module.Flat S.A T := IsLocalization.flat T (.powers S.a)
  have hfg : Function.Exact f g :=
    Module.Flat.lTensor_exact T E.exact_cotangentComplex_toKaehler
  have hg : Function.Surjective g := LinearMap.lTensor_surjective T E.toKaehler_surjective
  obtain ⟨bM, hf⟩ := localized_cotangent_free S P c hcm hstrict
  have : Module.Free T (T ⊗[S.A] E.Cotangent) := Module.Free.of_basis bM
  have : Module.Finite T (T ⊗[S.A] E.Cotangent) := Module.Finite.of_basis bM
  let bN : Module.Basis (Fin P.n) T (T ⊗[S.A] E.CotangentSpace) :=
    (toAlgebraPresentation P).toGenerators.cotangentSpaceBasis.baseChange T
  have : Module.Free T (T ⊗[S.A] E.CotangentSpace) := Module.Free.of_basis bN
  have : Module.Finite T (T ⊗[S.A] E.CotangentSpace) := Module.Finite.of_basis bN
  have : IsLocalizedModule (.powers S.a)
      (KaehlerDifferential.map S.R S.R S.A T) :=
    omega_localization_total S.R S.A (.powers S.a) T
  let eΩ : T ⊗[S.A] Ω[S.A⁄S.R] ≃ₗ[T] Ω[T⁄S.R] :=
    (IsLocalizedModule.isBaseChange (.powers S.a) T
      (KaehlerDifferential.map S.R S.R S.A T)).equiv
  have : Module.Projective T (T ⊗[S.A] Ω[S.A⁄S.R]) := Module.Projective.of_equiv' eΩ.symm
  have : Module.Finite T (T ⊗[S.A] Ω[S.A⁄S.R]) := Module.Finite.equiv eΩ.symm
  have hsf : Module.IsStablyFree T (T ⊗[S.A] Ω[S.A⁄S.R]) :=
    (Module.isStablyFree_two_out_of_three f g hf hfg hg).1 ⟨inferInstance, inferInstance⟩
  exact ⟨hsmooth, hsf.equiv eΩ⟩

end Stacks.Smoothing

end
