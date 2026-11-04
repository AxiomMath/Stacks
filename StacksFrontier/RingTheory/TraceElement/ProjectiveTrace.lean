module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Computation rules for the trace of a finite projective module

`Stacks.Discriminant.finiteProjectiveTrace` assigns a scalar to an endomorphism of a finite
projective module by computing the trace on a finite free module that the module splits off.
This file collects the computation rules the theory of trace elements needs: the behaviour of
the trace in a product, under a change of the base ring, and in the presence of a finite dual
family.

The last of these is the most useful shape. A finite family `(b i, λ i)` with
`∑ i, λ i m • b i = m` for all `m` exhibits the module as a direct summand of a finite free
module, and the trace of `f` is then `∑ i, λ i (f (b i))`. For an algebra `R` over `A` with
`C` finite projective over both, a family presenting the structure map `R → C` computes the
`A`-valued trace of multiplication on `C` by contracting the `R`-valued one, which is the
transitivity of the trace in the form the existence of trace elements uses.

## Main results

* `Stacks.Discriminant.finiteProjectiveTrace_conj_linearEquiv`: invariance under conjugation
  by a linear equivalence.
* `Stacks.Discriminant.finiteProjectiveTrace_prodMap`: the trace of a product of endomorphisms
  is the sum of their traces.
* `Stacks.Discriminant.finiteProjectiveTrace_lmul_of_prodEquiv`: on a direct factor of the
  base ring, the trace of multiplication is the inclusion of the element back into the base.
* `Stacks.Discriminant.exists_finiteProjectiveTrace_of_prodEquiv`: the same computation when
  only the base ring is decomposed, giving in addition the projectivity of the module over the
  factor.
* `Stacks.Discriminant.finiteProjectiveTrace_congr_ringEquiv`: a ring equivalence of bases
  acting by the same scalars carries one trace to the other.
* `Stacks.Discriminant.dualBaseChange_finiteProjectiveTrace_lmul`: the trace form of a finite
  projective algebra commutes with scalar extension.
* `Stacks.Discriminant.finiteProjectiveTrace_lmul_algebraMap`: the trace of multiplication
  over the base is the image of the trace over an intermediate ring, when the scalar extension
  of the module along that ring is the module itself.
* `Stacks.Discriminant.finiteProjectiveTrace_eq_sum`: the trace computed from a finite dual
  family.
* `Stacks.Discriminant.finiteProjectiveTrace_lmul_eq_sum_of_tower`: transitivity of the trace
  against a family presenting the structure map of an intermediate algebra.
* `Stacks.Discriminant.exists_sum_smul_eq_of_flat`: a map from a finitely presented module to
  a flat module factors through a finite free module, in the form of a finite family.

## References

* [Stacks Project, Tag 0BJF](https://stacks.math.columbia.edu/tag/0BJF)
* [Stacks Project, Tag 0BTB](https://stacks.math.columbia.edu/tag/0BTB)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Stacks.Discriminant

section Conj

variable {R : Type u} [CommRing R] {P : Type v} {Q : Type w}
  [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]

/-- The projective trace is invariant under conjugating an endomorphism by a linear
equivalence, stated for `LinearEquiv.conj`. -/
@[sga "6 I 8.4" "special case"]
theorem finiteProjectiveTrace_conj_linearEquiv (e : P ≃ₗ[R] Q) (f : Module.End R P) :
    finiteProjectiveTrace R Q (e.conj f) = finiteProjectiveTrace R P f := by
  have h : e.conj f = e.toLinearMap.comp (f.comp e.symm.toLinearMap) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [h, finiteProjectiveTrace_conj]

end Conj

section Prod

variable (R : Type u) [CommRing R] (P : Type v) (Q : Type w)
  [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]

/-- The trace of an endomorphism of a direct product acting componentwise is the sum of the
traces of its components. -/
theorem finiteProjectiveTrace_prodMap (f : Module.End R P) (g : Module.End R Q) :
    finiteProjectiveTrace R (P × Q) (LinearMap.prodMap f g) =
      finiteProjectiveTrace R P f + finiteProjectiveTrace R Q g := by
  classical
  obtain ⟨n, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  obtain ⟨m, q, j, _, _, hqj⟩ := Module.Finite.exists_comp_eq_id_of_projective R Q
  have hsplit : (LinearMap.prodMap p q).comp (LinearMap.prodMap i j) = LinearMap.id :=
    LinearMap.ext fun ⟨x, y⟩ => Prod.ext (LinearMap.congr_fun hpi x) (LinearMap.congr_fun hqj y)
  have htrace : (LinearMap.prodMap i j).comp ((LinearMap.prodMap f g).comp
      (LinearMap.prodMap p q)) =
      LinearMap.prodMap (i.comp (f.comp p)) (j.comp (g.comp q)) :=
    LinearMap.ext fun ⟨_, _⟩ => rfl
  rw [finiteProjectiveTrace_eq_trace_of_split R (P × Q) ((Fin n → R) × (Fin m → R))
    (LinearMap.prodMap p q) (LinearMap.prodMap i j) hsplit, htrace,
    LinearMap.trace_prodMap' (i.comp (f.comp p)) (j.comp (g.comp q)),
    ← finiteProjectiveTrace_eq_trace_of_split R P _ p i hpi f,
    ← finiteProjectiveTrace_eq_trace_of_split R Q _ q j hqj g]

end Prod

/-- Multiplication by a ring element has trace that element. -/
theorem trace_lmul_self (R : Type u) [CommRing R] (x : R) :
    LinearMap.trace R R (Algebra.lmul R R x) = x :=
  congrArg (fun f : R →ₗ[R] R => f x) (Algebra.trace_self (R := R))

section ProdFactor

variable {S : Type u} {C : Type v} {D : Type w}
  [CommRing S] [CommRing C] [CommRing D] [Algebra S C]

/-- If the base ring decomposes as `S ≃ C × D` with its action on `C` the first projection,
then the trace of multiplication by `c` on `C` is the element of `S` corresponding to
`(c, 0)`: the module `C` is free of rank one over itself and the trace is computed there. -/
theorem finiteProjectiveTrace_lmul_of_prodEquiv [Module.Finite S C] [Module.Projective S C]
    (e : S ≃+* C × D) (hact : ∀ s : S, algebraMap S C s = (e s).1) (c : C) :
    finiteProjectiveTrace S C (Algebra.lmul S C c) = e.symm (c, 0) := by
  let p : S →ₗ[S] C := Algebra.linearMap S C
  let i : C →ₗ[S] S :=
    { toFun := fun c => e.symm (c, 0)
      map_add' := fun x y => e.injective (by simp)
      map_smul' := fun s c => by
        simp only [Algebra.smul_def, RingHom.id_apply]
        refine e.injective ?_
        rw [map_mul]
        exact Prod.ext (by simp [hact, mul_comm]) (by simp) }
  have hpi : p.comp i = LinearMap.id := by
    ext c
    show algebraMap S C (e.symm (c, 0)) = c
    rw [hact]
    simp
  have hcomp : i.comp ((Algebra.lmul S C c).comp p) = Algebra.lmul S S (e.symm (c, 0)) := by
    apply LinearMap.ext
    intro s
    show e.symm (c * algebraMap S C s, 0) = e.symm (c, 0) * s
    refine e.injective ?_
    rw [map_mul]
    exact Prod.ext (by simp [hact]) (by simp)
  rw [finiteProjectiveTrace_eq_trace_of_split S C S p i hpi, hcomp, trace_lmul_self]

end ProdFactor

/-- The trace of an endomorphism of `Fin n → R` is the sum of the diagonal entries. -/
private theorem trace_pi_eq_sum {R : Type*} [CommRing R] {n : ℕ} (f : Module.End R (Fin n → R)) :
    LinearMap.trace R (Fin n → R) f = ∑ i, f (Pi.basisFun R (Fin n) i) i := by
  rw [LinearMap.trace_eq_matrix_trace R (Pi.basisFun R (Fin n))]
  simp [Matrix.trace]

section RingEquivCongr

/-- Two bases identified by a ring equivalence that acts by the same scalars have the same
trace, transported along the equivalence. The two endomorphisms are only required to agree as
functions, since the two module structures on `C` coincide. -/
theorem finiteProjectiveTrace_congr_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (e : R ≃+* S)
    {C : Type w} [CommRing C] [Algebra R C] [Algebra S C]
    [Module.Finite R C] [Module.Projective R C]
    [Module.Finite S C] [Module.Projective S C]
    (hmap : ∀ r : R, algebraMap S C (e r) = algebraMap R C r)
    (fR : Module.End R C) (fS : Module.End S C) (hf : ∀ c, fR c = fS c) :
    e (finiteProjectiveTrace R C fR) = finiteProjectiveTrace S C fS := by
  classical
  obtain ⟨n, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective S C
  have hsmul (r : R) (c : C) : r • c = (e r) • c := by
    rw [Algebra.smul_def, Algebra.smul_def, hmap r]
  let pR : (Fin n → R) →ₗ[R] C :=
    { toFun := fun v => p (fun j => e (v j))
      map_add' := fun v v' => by
        show p (fun j => e (v j + v' j)) = _
        rw [show (fun j => e (v j + v' j)) = (fun j => e (v j)) + (fun j => e (v' j)) by
          ext j; simp]
        exact p.map_add _ _
      map_smul' := fun r v => by
        show p (fun j => e (r • v j)) = r • p (fun j => e (v j))
        rw [show (fun j => e (r • v j)) = (e r) • (fun j => e (v j)) by ext j; simp, p.map_smul]
        exact (hsmul r (p (fun j => e (v j)))).symm }
  let iR : C →ₗ[R] (Fin n → R) :=
    { toFun := fun c j => e.symm (i c j)
      map_add' := fun c d => by ext j; simp [i.map_add]
      map_smul' := fun r c => by
        ext j
        show e.symm (i (r • c) j) = r * e.symm (i c j)
        rw [hsmul, i.map_smul]
        simp }
  have hpiR : pR.comp iR = LinearMap.id := by
    ext c
    show p (fun j => e (e.symm (i c j))) = c
    simpa using LinearMap.congr_fun hpi c
  have hdiag (v : Fin n → R) (j : Fin n) :
      e ((iR.comp (fR.comp pR)) v j) = (i.comp (fS.comp p)) (fun k => e (v k)) j := by
    simp [pR, iR, LinearMap.comp_apply, hf]
  have htrace : e (LinearMap.trace R (Fin n → R) (iR.comp (fR.comp pR))) =
      LinearMap.trace S (Fin n → S) (i.comp (fS.comp p)) := by
    rw [trace_pi_eq_sum, trace_pi_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hbasis : (fun k => e ((Pi.basisFun R (Fin n) j) k)) = Pi.basisFun S (Fin n) j := by
      ext k
      by_cases hk : k = j <;> simp [Pi.basisFun, hk]
    have hcoord := congrArg
      (fun v : Fin n → S => (i.comp (fS.comp p)) v j) hbasis
    exact (hdiag (Pi.basisFun R (Fin n) j) j).trans hcoord
  rwa [finiteProjectiveTrace_eq_trace_of_split R C (Fin n → R) pR iR hpiR fR,
    finiteProjectiveTrace_eq_trace_of_split S C (Fin n → S) p i hpi fS]

end RingEquivCongr

section ProdBase

/-- When only the base ring is decomposed, a finite projective module over it is finite
projective over the first factor and its trace of multiplication is computed there, up to the
inclusion `(·, 0)`. Finiteness and projectivity over the factor are part of the conclusion
because they are consequences of the decomposition rather than hypotheses. -/
theorem exists_finiteProjectiveTrace_of_prodEquiv
    {K : Type u} {R : Type v} {S : Type w} {P : Type*}
    [CommRing K] [CommRing R] [CommRing S] [CommRing P]
    [Algebra K P] [Algebra R P] [Module.Finite K P] [Module.Projective K P]
    (e : K ≃+* R × S) (hmap : ∀ k : K, algebraMap K P k = algebraMap R P (e k).1) :
    ∃ (_ : Module.Finite R P) (_ : Module.Projective R P), ∀ x : P,
      finiteProjectiveTrace K P (Algebra.lmul K P x) =
        e.symm (finiteProjectiveTrace R P (Algebra.lmul R P x), 0) := by
  classical
  let project := (RingHom.fst R S).comp e.toRingHom
  let inclusion : R →+ K :=
    { toFun := fun r => e.symm (r, 0)
      map_zero' := map_zero e.symm
      map_add' := fun x y => by simpa using map_add e.symm (x, 0) (y, 0) }
  have hprojinc (r : R) : project (inclusion r) = r := by
    show (e (e.symm (r, 0))).1 = r
    simp
  have hincmul (x y : R) : inclusion (x * y) = inclusion x * inclusion y := by
    show e.symm (x * y, 0) = e.symm (x, 0) * e.symm (y, 0)
    simpa using map_mul e.symm (x, 0) (y, 0)
  have hsmul (k : K) (x : P) : k • x = project k • x := by
    rw [Algebra.smul_def, Algebra.smul_def, hmap]
    rfl
  have hincsmul (r : R) (x : P) : inclusion r • x = r • x := by rw [hsmul, hprojinc]
  obtain ⟨size, projection, injection, _, _, hsplit⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective K P
  have hsection (x : P) : projection (injection x) = x := LinearMap.congr_fun hsplit x
  have hinjection (x : P) (index : Fin size) :
      inclusion (project (injection x index)) = injection x index := by
    have hsupport := congrFun (injection.map_smul (inclusion 1) x) index
    rw [hincsmul, one_smul] at hsupport
    have heq (k : K) : inclusion (project k) = inclusion 1 * k := by
      refine e.injective ?_
      rw [map_mul]
      show e (e.symm (project k, 0)) = e (e.symm (1, 0)) * e k
      rw [e.apply_symm_apply, e.apply_symm_apply]
      exact Prod.ext (by simp [project]) (by simp)
    rw [heq]
    exact hsupport.symm
  let projectionR : (Fin size → R) →ₗ[R] P :=
    { toFun := fun v => projection (fun index => inclusion (v index))
      map_add' := fun x y => by
        show projection (fun index => inclusion (x index + y index)) = _
        simp_rw [map_add]
        exact projection.map_add _ _
      map_smul' := fun r v => by
        show projection (fun index => inclusion (r * v index)) =
          r • projection (fun index => inclusion (v index))
        simp_rw [hincmul]
        show projection (inclusion r • (fun index => inclusion (v index))) = _
        rw [projection.map_smul, hincsmul] }
  let injectionR : P →ₗ[R] (Fin size → R) :=
    { toFun := fun x index => project (injection x index)
      map_add' := fun x y => by ext index; simp [injection.map_add]
      map_smul' := fun r x => by
        ext index
        rw [← hincsmul r x, injection.map_smul]
        show project (inclusion r * injection x index) = r * project (injection x index)
        rw [map_mul, hprojinc] }
  have hsplitR : projectionR.comp injectionR = LinearMap.id := by
    ext x
    show projection (fun index => inclusion (project (injection x index))) = x
    simp_rw [hinjection]
    exact hsection x
  have hfinite : Module.Finite R P :=
    Module.Finite.of_surjective projectionR fun x => ⟨injectionR x, LinearMap.congr_fun hsplitR x⟩
  have hprojective : Module.Projective R P :=
    Module.Projective.of_split injectionR projectionR hsplitR
  refine ⟨hfinite, hprojective, fun x => ?_⟩
  have hbasis (index : Fin size) :
      (fun other => inclusion (Pi.basisFun R (Fin size) index other)) =
        inclusion 1 • Pi.basisFun K (Fin size) index := by
    ext other
    rw [Pi.basisFun_apply, Pi.basisFun_apply]
    by_cases heq : other = index <;> simp [heq, inclusion]
  have hdiag (index : Fin size) :
      (injection.comp ((Algebra.lmul K P x).comp projection))
          (Pi.basisFun K (Fin size) index) index =
        inclusion ((injectionR.comp ((Algebra.lmul R P x).comp projectionR))
          (Pi.basisFun R (Fin size) index) index) := by
    show injection (x * projection (Pi.basisFun K (Fin size) index)) index =
      inclusion (project (injection
        (x * projection (fun other => inclusion (Pi.basisFun R (Fin size) index other)))
          index))
    rw [hinjection, hbasis, projection.map_smul, hincsmul, one_smul]
  have key (g : Fin size → R) :
      (e.symm (∑ index, g index, 0) : K) = ∑ index, inclusion (g index) :=
    map_sum inclusion g Finset.univ
  rw [finiteProjectiveTrace_eq_trace_of_split K P _ projection injection hsplit,
    finiteProjectiveTrace_eq_trace_of_split R P _ projectionR injectionR hsplitR,
    trace_pi_eq_sum, trace_pi_eq_sum, key]
  exact Finset.sum_congr rfl fun index _ => hdiag index

end ProdBase

section BaseChange

variable (R : Type u) (P : Type v) (S : Type w)
  [CommRing R] [CommRing P] [Algebra R P] [Module.Finite R P] [Module.Projective R P]
  [CommRing S] [Algebra R S]

/-- The trace form of a finite projective algebra commutes with scalar extension: extending
`x ↦ Tr(x ·)` to `S ⊗[R] P` gives the trace form of `S ⊗[R] P` over `S`. -/
theorem dualBaseChange_finiteProjectiveTrace_lmul :
    letI : Algebra S (S ⊗[R] P) := Algebra.TensorProduct.leftAlgebra
    Module.Dual.baseChange S
        ((finiteProjectiveTrace R P).comp (Algebra.lmul R P).toLinearMap) =
      (finiteProjectiveTrace S (S ⊗[R] P)).comp
        (Algebra.lmul S (S ⊗[R] P)).toLinearMap := by
  classical
  let : Algebra S (S ⊗[R] P) := Algebra.TensorProduct.leftAlgebra
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul s b =>
      have hb : (Algebra.lmul R P b).baseChange S = Algebra.lmul S (S ⊗[R] P) (1 ⊗ₜ[R] b) := by
        ext z
        show (1 : S) ⊗ₜ[R] (b * z) = ((1 : S) ⊗ₜ[R] b) * ((1 : S) ⊗ₜ[R] z)
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp
      have hs : Algebra.lmul S (S ⊗[R] P) (s ⊗ₜ[R] b) =
          s • Algebra.lmul S (S ⊗[R] P) (1 ⊗ₜ[R] b) := by
        ext z
        show (s ⊗ₜ[R] b) * ((1 : S) ⊗ₜ[R] z) =
          s • (((1 : S) ⊗ₜ[R] b) * ((1 : S) ⊗ₜ[R] z))
        simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
      rw [Module.Dual.baseChange_apply_tmul]
      show finiteProjectiveTrace R P (Algebra.lmul R P b) • s =
        finiteProjectiveTrace S (S ⊗[R] P) (Algebra.lmul S (S ⊗[R] P) (s ⊗ₜ[R] b))
      rw [hs, map_smul, ← hb, finiteProjectiveTrace_baseChange]
      simp [Algebra.smul_def, smul_eq_mul, mul_comm]

end BaseChange

section Tower

/-- For an intermediate ring `S` whose scalar extension of `C` is `C` itself, the trace of
multiplication over `S` is the image of the trace over `R`. The hypothesis is the linear
equivalence `S ⊗[R] C ≃ C` given by multiplication, which holds whenever `R → S` becomes an
epimorphism in `C`. -/
theorem finiteProjectiveTrace_lmul_algebraMap
    {R : Type u} {S : Type v} {C : Type w} [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
    [Module.Finite R C] [Module.Projective R C]
    [Module.Finite S C] [Module.Projective S C]
    (e : S ⊗[R] C ≃ₗ[S] C) (he : ∀ s c, e (s ⊗ₜ[R] c) = algebraMap S C s * c) (c : C) :
    finiteProjectiveTrace S C (Algebra.lmul S C c) =
      algebraMap R S (finiteProjectiveTrace R C (Algebra.lmul R C c)) := by
  classical
  have hcomm : (Algebra.lmul S C c).comp e.toLinearMap =
      e.toLinearMap.comp ((Algebra.lmul R C c).baseChange S) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        simp only [LinearMap.comp_apply, map_add]
        exact congrArg₂ (· + ·) hz hz'
    | tmul s x =>
        show Algebra.lmul S C c (e (s ⊗ₜ[R] x)) = e ((Algebra.lmul R C c).baseChange S
          (s ⊗ₜ[R] x))
        rw [he]
        simp only [LinearMap.baseChange_tmul, Algebra.coe_lmul_eq_mul]
        rw [he]
        show c * (algebraMap S C s * x) = algebraMap S C s * (c * x)
        ring
  have hconj : e.conj ((Algebra.lmul R C c).baseChange S) = Algebra.lmul S C c := by
    ext x
    simpa [LinearEquiv.conj_apply] using (LinearMap.congr_fun hcomm (e.symm x)).symm
  rw [← hconj, finiteProjectiveTrace_conj_linearEquiv, finiteProjectiveTrace_baseChange]

end Tower

section DualFamily

/-- A map from a finitely presented module to a flat module is given by a finite family of
functionals and a finite family of elements: it factors through a finite free module. -/
theorem exists_sum_smul_eq_of_flat {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] [Module.Flat R N] (q : M →ₗ[R] N) :
    ∃ (n : ℕ) (f : Fin n → Module.Dual R M) (b : Fin n → N), ∀ x, ∑ i, f i x • b i = q x := by
  classical
  obtain ⟨n, a, y, h⟩ := Module.Flat.exists_factorization_of_finitePresentation q
  refine ⟨n, fun i => (Finsupp.lapply i).comp a, fun i => y (Finsupp.single i 1), fun x => ?_⟩
  show ∑ i, a x i • y (Finsupp.single i 1) = q x
  simp_rw [← y.map_smul]
  rw [← map_sum, h]
  refine congrArg y ?_
  ext i
  simp

/-- A finite projective module has a finite dual family: functionals `f i` and elements `b i`
with `∑ i, f i x • b i = x` for every `x`. -/
theorem exists_dualFamily {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (f : Fin n → Module.Dual R M) (b : Fin n → M), ∀ x, ∑ i, f i x • b i = x := by
  have := Module.finitePresentation_of_projective R M
  exact exists_sum_smul_eq_of_flat (LinearMap.id : M →ₗ[R] M)

/-- The trace of an endomorphism computed from a finite dual family. -/
theorem finiteProjectiveTrace_eq_sum {R : Type u} {M : Type v} {ι : Type w}
    [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [Fintype ι] (f : ι → Module.Dual R M) (b : ι → M) (h : ∀ x, ∑ i, f i x • b i = x)
    (q : Module.End R M) :
    finiteProjectiveTrace R M q = ∑ i, f i (q (b i)) := by
  have hq : q = ∑ i, (f i).smulRight (q (b i)) := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
    simp_rw [← q.map_smul]
    rw [← map_sum, h]
  conv_lhs => rw [hq, map_sum]
  exact Finset.sum_congr rfl fun i _ => finiteProjectiveTrace_smulRight _ _

/-- Transitivity of the trace against a presenting family. If `(b i, f i)` is a finite family
with `∑ i, f i r • b i` the image of `r` in `C` for every `r ∈ R`, then contracting the
`R`-valued trace of multiplication along it gives the `A`-valued trace. -/
theorem finiteProjectiveTrace_lmul_eq_sum_of_tower
    {A : Type u} {R : Type v} {C : Type w} {ι : Type*}
    [CommRing A] [CommRing R] [CommRing C] [Algebra A R] [Algebra A C] [Algebra R C]
    [IsScalarTower A R C] [Module.Finite A C] [Module.Projective A C]
    [Module.Finite R C] [Module.Projective R C] [Fintype ι]
    (f : ι → Module.Dual A R) (b : ι → C)
    (h : ∀ r : R, ∑ i, f i r • b i = algebraMap R C r) (c : C) :
    ∑ i, f i (finiteProjectiveTrace R C (Algebra.lmul R C (b i * c))) =
      finiteProjectiveTrace A C (Algebra.lmul A C c) := by
  classical
  obtain ⟨n, p, v, hp⟩ := exists_dualFamily (R := R) (M := C)
  have hd (x : C) :
      ∑ ij : ι × Fin n, ((f ij.1).comp ((p ij.2).restrictScalars A)) x •
        (b ij.1 * v ij.2) = x := by
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    calc
      ∑ j, ∑ i, f i (p j x) • (b i * v j) = ∑ j, (∑ i, f i (p j x) • b i) * v j := by
            simp only [Finset.sum_mul, smul_mul_assoc]
      _ = ∑ j, p j x • v j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h, Algebra.smul_def]
      _ = x := hp x
  rw [finiteProjectiveTrace_eq_sum _ _ hd]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finiteProjectiveTrace_eq_sum p v hp, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  show (b i * c) * v j = c * (b i * v j)
  ring

end DualFamily

end Stacks.Discriminant

end
