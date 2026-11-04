module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Basis.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.Support.DedekindDifferentSetup

/-!
# The generic-fibre trace of a flat finite algebra

In the setup for the Dedekind different, flatness of the finite algebra `B` over `A` implies that
the generic-fibre trace of every element of `B` already belongs to `A`. Equivalently, `1` lies in
the complementary module, which is the hypothesis under which the Dedekind different is an ideal
of `B`.

## Main results

* `Stacks.Discriminant.trace_algebraMap_mem_range_of_flat` says that the generic-fibre trace of
  an element of a flat algebra lies in the canonical image of the base ring in its total quotient
  ring.

## Implementation notes

The assertion that the trace belongs to `A` is expressed as membership in the range of the
canonical map from `A` to `FractionRing A`. Since the generic fibre need not be free over the
total quotient ring, its trace is the contraction trace of a finite projective module; the proof
compares that trace with the ordinary trace on a finite free module containing the algebra as a
direct summand, and then identifies the latter with the base change of a trace computed over `A`.

## References

* [Stacks Project, Tag 0BW1](https://stacks.math.columbia.edu/tag/0BW1)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v

private theorem dualTensorHom_map_split
    {R M F : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid F] [Module R F]
    (i : M →ₗ[R] F) (p : F →ₗ[R] M)
    (z : Module.Dual R M ⊗[R] M) :
    dualTensorHom R F F ((TensorProduct.map p.dualMap i) z) =
      i.comp ((dualTensorHom R M M z).comp p) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul φ m =>
    ext x
    simp [TensorProduct.map_tmul, LinearMap.dualMap_apply, dualTensorHom_apply]
  | add x y hx hy =>
    ext m
    simp [hx, hy]

private theorem contractTensor_map_split
    {R M F : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommGroup F] [Module R F]
    (i : M →ₗ[R] F) (p : F →ₗ[R] M) (h : p.comp i = LinearMap.id)
    (z : Module.Dual R M ⊗[R] M) :
    contractLeft R F ((TensorProduct.map p.dualMap i) z) = contractLeft R M z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul φ m =>
    simp only [TensorProduct.map_tmul, contractLeft_apply, LinearMap.dualMap_apply]
    exact congrArg φ (LinearMap.congr_fun h m)
  | add x y hx hy => simp [hx, hy]

private noncomputable def projTrace
    {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (f : M →ₗ[R] M) : R :=
  contractLeft R M ((dualTensorHomEquiv R M M).symm f)

private theorem projTrace_eq_freeTrace
    {R M F : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
    (i : M →ₗ[R] F) (p : F →ₗ[R] M) (h : p.comp i = LinearMap.id)
    (f : M →ₗ[R] M) :
    projTrace f = LinearMap.trace R F (i.comp (f.comp p)) := by
  let z := (dualTensorHomEquiv R M M).symm f
  have hz : (dualTensorHomEquiv R F F).symm (i.comp (f.comp p)) =
      TensorProduct.map p.dualMap i z := by
    apply (dualTensorHomEquiv R F F).injective
    show (dualTensorHomEquiv R F F)
        ((dualTensorHomEquiv R F F).symm (i.comp (f.comp p))) =
      dualTensorHom R F F (TensorProduct.map p.dualMap i z)
    rw [LinearEquiv.apply_symm_apply, dualTensorHom_map_split,
      show dualTensorHom R M M z = f from (dualTensorHomEquiv R M M).apply_symm_apply f]
  rw [LinearMap.trace_eq_contract' R F]
  show contractLeft R M z =
    contractLeft R F ((dualTensorHomEquiv R F F).symm (i.comp (f.comp p)))
  rw [hz, contractTensor_map_split i p h z]

private theorem projTrace_mem_range_of_split
    {A K L F : Type*} [CommRing A] [CommRing K] [Algebra A K]
    [AddCommGroup L] [Module K L] [Module.Finite K L] [Module.Projective K L]
    [AddCommGroup F] [Module A F] [Module.Free A F] [Module.Finite A F]
    [Module.Free K (K ⊗[A] F)] [Module.Finite K (K ⊗[A] F)]
    (i : L →ₗ[K] K ⊗[A] F) (p : K ⊗[A] F →ₗ[K] L) (h : p.comp i = LinearMap.id)
    {T : L →ₗ[K] L} {r : F →ₗ[A] F} (hT : i.comp (T.comp p) = r.baseChange K) :
    projTrace T ∈ Set.range (algebraMap A K) :=
  ⟨LinearMap.trace A F r, by
    rw [projTrace_eq_freeTrace i p h T, hT]
    exact (LinearMap.trace_baseChange r K).symm⟩

/-- Conjugating multiplication by `b` on `B ⊗[A] K` through `commRight` gives the base change of
multiplication by `b` on `B`. -/
theorem commRight_symm_comp_lmul_comp_commRight
    {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing K] [Algebra A K]
    (b : B) :
    letI : Algebra K (B ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
    (Algebra.TensorProduct.commRight A K B).symm.toLinearMap.comp
        ((Algebra.lmul K (B ⊗[A] K) (algebraMap B (B ⊗[A] K) b)).comp
          (Algebra.TensorProduct.commRight A K B).toLinearMap) =
      (Algebra.lmul A B b).baseChange K := by
  let : Algebra K (B ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
  let e := Algebra.TensorProduct.commRight A K B
  have hx : algebraMap B (B ⊗[A] K) b = e (1 ⊗ₜ[A] b) := by simp [e]
  rw [Algebra.baseChange_lmul b]
  apply LinearMap.ext
  intro q
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul k y =>
    show e.symm (algebraMap B (B ⊗[A] K) b * e (k ⊗ₜ[A] y)) = (1 ⊗ₜ[A] b) * (k ⊗ₜ[A] y)
    rw [hx]
    apply e.injective
    simp
  | add q q' hq hq' =>
    rw [map_add, map_add, hq, hq']

/-- **Stacks Project, Tag 0BW1 (flat trace).** In the setup for the Dedekind
different, if `B` is flat over `A`, then the generic-fibre trace of every
element of `B` belongs to the canonical image of `A` in its total quotient
ring. -/
@[stacks 0BW1 "flat_trace"]
theorem trace_algebraMap_mem_range_of_flat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (setup : DedekindDifferentSetup A B) [Module.Flat A B]
    (b : B) :
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) :=
      Algebra.TensorProduct.rightAlgebra
    setup.trace (algebraMap B (B ⊗[A] FractionRing A) b) ∈
      Set.range (algebraMap A (FractionRing A)) := by
  classical
  have _ : IsNoetherianRing A := setup.isNoetherianRing
  have _ : Module.Finite A B := setup.finite
  have _ : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  have _ : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective A B
  let K := FractionRing A
  let L := B ⊗[A] K
  let M := K ⊗[A] B
  let F := Fin n → A
  let FK := K ⊗[A] F
  let _ : Algebra K L := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra K M := Algebra.TensorProduct.leftAlgebra
  let bFK : Module.Basis (Fin n) K FK :=
    Algebra.TensorProduct.basis K (Pi.basisFun A (Fin n))
  have _ : Module.Free K FK := Module.Free.of_basis bFK
  have _ : Module.Finite K FK := Module.Finite.of_basis bFK
  let e : M ≃ₐ[K] L := Algebra.TensorProduct.commRight A K B
  have : Module.Finite K M := Module.Finite.base_change A K B
  have : Module.Finite K L := Module.Finite.equiv e.toLinearEquiv
  let iK : M →ₗ[K] FK := i.baseChange K
  let pK : FK →ₗ[K] M := p.baseChange K
  let iL : L →ₗ[K] FK := iK.comp e.symm.toLinearMap
  let pL : FK →ₗ[K] L := e.toLinearMap.comp pK
  have hpiK : pK.comp iK = LinearMap.id := by
    dsimp [pK, iK]
    rw [← LinearMap.baseChange_comp, hpi, LinearMap.baseChange_id]
  have hpiL : pL.comp iL = LinearMap.id := by
    ext z
    show e ((pK.comp iK) (e.symm z)) = z
    rw [hpiK]
    exact e.apply_symm_apply z
  have _ : Module.Projective K L := Module.Projective.of_split iL pL hpiL
  let μ : B →ₗ[A] B := Algebra.lmul A B b
  let r : F →ₗ[A] F := i.comp (μ.comp p)
  let μK : M →ₗ[K] M := μ.baseChange K
  let x : L := algebraMap B L b
  let T : L →ₗ[K] L := Algebra.lmul K L x
  have hcomp : iL.comp (T.comp pL) = r.baseChange K := by
    calc
      iL.comp (T.comp pL) =
          iK.comp ((e.symm.toLinearMap.comp (T.comp e.toLinearMap)).comp pK) := by
        simp [iL, pL, LinearMap.comp_assoc]
      _ = iK.comp (μK.comp pK) :=
        congrArg (fun g => iK.comp (g.comp pK)) (commRight_symm_comp_lmul_comp_commRight b)
      _ = r.baseChange K := by
        dsimp [iK, pK, μK, r, μ]
        rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
  show projTrace T ∈ Set.range (algebraMap A K)
  exact projTrace_mem_range_of_split iL pL hpiL hcomp

end Stacks.Discriminant
