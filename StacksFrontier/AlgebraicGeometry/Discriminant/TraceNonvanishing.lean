module

public import Mathlib.RingTheory.Trace.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.FiniteLength.Determinant
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElementUnique
public import StacksFrontier.RingTheory.TraceElement.FiniteFlat
public import StacksFrontier.RingTheory.TraceElement.Independence

/-!
# Nonvanishing of the trace of a finite algebra over a field

For a finite algebra `A` over a field `k` the algebra trace `Tr_{A/k}` is nonzero exactly when
the trace element of the relative dualizing module is nonzero. For a local `A` both are in turn
equivalent to the residue field `κ(A)` being separable over `k` together with the length of `A`
being prime to the characteristic of `k`. These are the three equivalent conditions of Tag 0C13.

## Main results

* `Stacks.Discriminant.trace_ne_zero_iff_isTraceElement_ne_zero` compares the trace with the trace
  element.
* `Stacks.Discriminant.trace_ne_zero_iff_isSeparable_and_length_ne_zero` characterizes
  nonvanishing by the residue extension and the length.
* `Stacks.Discriminant.trace_eq_length_mul_trace_residue` is the formula
  `Tr_{A/k}(a) = length(A) · Tr_{κ(A)/k}(ā)` for a finite local `k`-algebra, which gives the
  second equivalence.

## Implementation notes

The relative dualizing module is represented by an arbitrary finite-open factorization, as in Tag
0BSZ, and the trace element by the predicate `Stacks.Discriminant.IsTraceElement` of Tag 0BT6
rather than by a chosen element: this is strictly more general, because uniqueness (Tag 0BT7) makes
every trace element the same one, and it avoids introducing a second name for an object the library
already determines.

"The length of `A` is prime to the characteristic" is expressed as the nonvanishing in `k` of the
natural number `length_A(A)`, which also covers characteristic zero.

## References

* [Stacks Project, Tag 0C13](https://stacks.math.columbia.edu/tag/0C13)
* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
* [Stacks Project, Tag 0BT7](https://stacks.math.columbia.edu/tag/0BT7)
* [Stacks Project, Tag 0BT8](https://stacks.math.columbia.edu/tag/0BT8)
-/

public noncomputable section

open scoped TensorProduct

open IsLocalRing

universe u v w

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-! ### The trace of a finite local algebra over a field -/

/-- The trace of an endomorphism preserving a subspace is the sum of the traces of its restriction
to the subspace and of the induced endomorphism of the quotient. In a basis adapted to the
subspace the matrix of the endomorphism is block triangular. -/
theorem trace_eq_trace_restrict_add_trace_mapQ (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (W : Submodule k V)
    (φ : Module.End k V) (hφ : W ≤ W.comap φ) :
    LinearMap.trace k V φ =
      LinearMap.trace k W (φ.restrict hφ) + LinearMap.trace k (V ⧸ W) (W.mapQ W φ hφ) := by
  classical
  let bW := Module.Free.chooseBasis k W
  let bQ := Module.Free.chooseBasis k (V ⧸ W)
  let b := bW.sumQuot bQ
  let MA := LinearMap.toMatrix bW bW (φ.restrict hφ)
  let MB := Matrix.of fun i j ↦ b.repr (φ (b (Sum.inr j))) (Sum.inl i)
  let MD := LinearMap.toMatrix bQ bQ (W.mapQ W φ hφ)
  have hm : LinearMap.toMatrix b b φ = Matrix.fromBlocks MA MB 0 MD := by
    ext u v
    match u, v with
    | Sum.inl i, Sum.inl j =>
        simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, MA,
          LinearMap.toMatrix_apply]
        apply Module.Basis.sumQuot_repr_inl_of_mem
    | Sum.inl i, Sum.inr j => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, MB]
    | Sum.inr i, Sum.inl j =>
        suffices W.mkQ (φ (bW j)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact hφ (Submodule.coe_mem (bW j))
    | Sum.inr i, Sum.inr j =>
        simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
          Matrix.fromBlocks_apply₂₂, b, MD]
        rw [← Module.Basis.sumQuot_inr bW bQ j, W.mapQ_apply]
        simp
  rw [LinearMap.trace_eq_matrix_trace _ b, hm, LinearMap.trace_eq_matrix_trace _ bW,
    LinearMap.trace_eq_matrix_trace _ bQ]
  simp [Matrix.trace, Fintype.sum_sum_type, MA, MD]

/-- **Additivity of the trace along an equivariant short exact sequence.** If `0 → W → V → Q → 0`
is exact and an endomorphism `φ_V` of `V` restricts to `φ_W` and descends to `φ_Q`, then the trace
of `φ_V` is the sum of the traces of `φ_W` and `φ_Q`. -/
theorem trace_eq_trace_add_trace_of_exact (k : Type u) [Field k] {V W Q : Type*}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    [AddCommGroup Q] [Module k Q] (i : W →ₗ[k] V) (p : V →ₗ[k] Q)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (φV : Module.End k V) (φW : Module.End k W) (φQ : Module.End k Q)
    (hiφ : ∀ x, φV (i x) = i (φW x)) (hpφ : ∀ x, φQ (p x) = p (φV x)) :
    LinearMap.trace k V φV = LinearMap.trace k W φW + LinearMap.trace k Q φQ := by
  classical
  let U : Submodule k V := LinearMap.range i
  have hU : U ≤ U.comap φV := by
    rintro _ ⟨x, rfl⟩
    exact ⟨φW x, (hiφ x).symm⟩
  let eW : W ≃ₗ[k] U := LinearEquiv.ofInjective i hi
  have hkerp : LinearMap.ker p = U := hex.linearMap_ker_eq
  let eQ : (V ⧸ U) ≃ₗ[k] Q :=
    (Submodule.quotEquivOfEq U (LinearMap.ker p) hkerp.symm).trans
      (p.quotKerEquivOfSurjective hp)
  have heW (x : W) : ((eW x : U) : V) = i x := rfl
  have hW : LinearMap.trace k U (φV.restrict hU) = LinearMap.trace k W φW := by
    rw [← LinearMap.trace_conj' φW eW]
    congr 1
    ext u
    rw [LinearMap.coe_restrict_apply]
    change φV (u : V) = ((eW (φW (eW.symm u)) : U) : V)
    rw [heW, ← hiφ (eW.symm u), ← heW (eW.symm u), eW.apply_symm_apply]
  have hmk (y : V) : eQ (Submodule.Quotient.mk y : V ⧸ U) = p y := by
    change p.quotKerEquivOfSurjective hp
      (Submodule.quotEquivOfEq U (LinearMap.ker p) hkerp.symm
        (Submodule.Quotient.mk y)) = p y
    rw [Submodule.quotEquivOfEq_mk U (LinearMap.ker p) hkerp.symm y,
      LinearMap.quotKerEquivOfSurjective_apply_mk p hp y]
  have hQ : LinearMap.trace k (V ⧸ U) (U.mapQ U φV hU) = LinearMap.trace k Q φQ := by
    rw [← LinearMap.trace_conj' φQ eQ.symm]
    congr 1
    ext y
    change U.mapQ U φV hU (Submodule.Quotient.mk y) =
      eQ.symm (φQ (eQ (Submodule.Quotient.mk y)))
    rw [Submodule.mapQ_apply, hmk, hpφ y, ← hmk (φV y), eQ.symm_apply_apply]
  rw [trace_eq_trace_restrict_add_trace_mapQ k V U φV hU, hW, hQ]

/-- Equal module structures on the same carrier give the same trace, for endomorphisms that agree
pointwise. -/
private theorem trace_eq_of_module_eq (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    (module₀ module₁ : Module R M) (hmodule : module₀ = module₁)
    (φ₀ : @LinearMap R R _ _ (RingHom.id R) M M _ _ module₀ module₀)
    (φ₁ : @LinearMap R R _ _ (RingHom.id R) M M _ _ module₁ module₁)
    (hφ : ∀ x, φ₀ x = φ₁ x) :
    @LinearMap.trace R _ M _ module₀ φ₀ = @LinearMap.trace R _ M _ module₁ φ₁ := by
  cases hmodule
  congr 1
  exact LinearMap.ext hφ

/-- For a finite local `k`-algebra `A` and a finite-length `A`-module `M`, the trace over `k` of
multiplication by `a` on `M` is the length of `M` times the trace over `k` of the residue of `a`
on the residue field. The induction is over a composition series of `M`: on a simple factor
multiplication by `a` is multiplication by its residue. -/
private theorem trace_lsmul_eq_length_mul_trace_residue (k : Type u) (A : Type v) [Field k]
    [CommRing A] [Algebra k A] [Module.Finite k A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) (a : A) :
    letI : IsNoetherian A M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
    letI : Module.Finite A M := Module.IsNoetherian.finite A M
    letI : Module k M := Module.compHom M (algebraMap k A)
    letI : IsScalarTower k A M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : Module.Finite k M := Module.Finite.trans A M
    LinearMap.trace k M ((LinearMap.lsmul A M a).restrictScalars k) =
      ((Module.length A M).toNat : k) *
        Algebra.trace k (ResidueField A) (IsLocalRing.residue A a) := by
  classical
  induction hM generalizing a with
  | @of_subsingleton M _ _ hsub =>
      let : Subsingleton M := hsub
      let : Finite M := Finite.of_subsingleton
      let : Module k M := Module.compHom M (algebraMap k A)
      let : IsScalarTower k A M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      let : Module.Finite k M := Module.Finite.trans A M
      have hf : (LinearMap.lsmul A M a).restrictScalars k = 0 := by
        ext x
        exact Subsingleton.elim _ _
      simp [hf, Module.length_eq_zero]
  | @of_simple_quotient M _ _ N _ hN ih =>
      let : IsNoetherian A M :=
        (isFiniteLength_iff_isNoetherian_isArtinian.mp (IsFiniteLength.of_simple_quotient hN)).1
      let : Module k M := Module.compHom M (algebraMap k A)
      let : IsScalarTower k A M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      let : Module.Finite k M := Module.Finite.trans A M
      let : IsNoetherian A N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1
      let φM : Module.End k M := (LinearMap.lsmul A M a).restrictScalars k
      let φN : Module.End k N := (LinearMap.lsmul A N a).restrictScalars k
      let φQ : Module.End k (M ⧸ N) := (LinearMap.lsmul A (M ⧸ N) a).restrictScalars k
      have htrace := trace_eq_trace_add_trace_of_exact k (N.subtype.restrictScalars k)
        (N.mkQ.restrictScalars k) N.subtype_injective N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N) φM φN φQ (fun _ ↦ rfl) (fun _ ↦ rfl)
      rw [htrace, ih a]
      obtain ⟨I, hI, ⟨eI⟩⟩ :=
        isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A (M ⧸ N))
      rw [IsLocalRing.eq_maximalIdeal hI] at eI
      change (M ⧸ N) ≃ₗ[A] ResidueField A at eI
      have hconj : (eI.restrictScalars k).conj φQ =
          (Algebra.lmul k (ResidueField A) (IsLocalRing.residue A a)).restrictScalars k := by
        ext x
        change eI (a • eI.symm x) = (IsLocalRing.residue A a) * x
        rw [eI.map_smul]
        simp only [eI.apply_symm_apply]
        change (algebraMap A (ResidueField A) a) * x = (IsLocalRing.residue A a) * x
        rw [IsLocalRing.ResidueField.algebraMap_eq]
      rw [← LinearMap.trace_conj' φQ (eI.restrictScalars k), hconj,
        show LinearMap.trace k (ResidueField A)
            ((Algebra.lmul k (ResidueField A) (IsLocalRing.residue A a)).restrictScalars k) =
            Algebra.trace k (ResidueField A) (IsLocalRing.residue A a) by
          rw [Algebra.trace_apply (R := k) (S := ResidueField A)]
          rfl,
        Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective N.mkQ_surjective
          (LinearMap.exact_iff.mpr (by rw [N.ker_mkQ, Submodule.range_subtype])),
        Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule A (M ⧸ N)), ENat.toNat_add]
      all_goals simp [Module.length_ne_top_iff.mpr hN, add_mul]

/-- **The trace of a finite local algebra over a field.** For a finite local `k`-algebra `A`,
`Tr_{A/k}(a) = length_A(A) · Tr_{κ(A)/k}(ā)`, where `κ(A)` is the residue field of `A`. -/
theorem trace_eq_length_mul_trace_residue (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [IsLocalRing A] [Module.Finite k A] (a : A) :
    Algebra.trace k A a =
      ((Module.length A A).toNat : k) *
        Algebra.trace k (ResidueField A) (IsLocalRing.residue A a) := by
  classical
  let : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  let : IsArtinianRing A := (Module.finite_iff_isArtinianRing k A).mp inferInstance
  have hAA : IsFiniteLength A A :=
    Module.length_ne_top_iff.mp (Module.length_ne_top (R := A) (M := A))
  let module₀ : Module k A := inferInstance
  let module₁ : Module k A := Module.compHom A (algebraMap k A)
  have hmodule : module₀ = module₁ := by
    apply Module.ext
    funext c x
    exact Algebra.smul_def c x
  let φ₁ : @LinearMap k k _ _ (RingHom.id k) A A _ _ module₁ module₁ := by
    let : Module k A := Module.compHom A (algebraMap k A)
    let : SMul k A := (Module.compHom A (algebraMap k A)).toSMul
    let : IsScalarTower k A A := by
      refine ⟨fun c x y ↦ ?_⟩
      change (algebraMap k A c * x) * y = algebraMap k A c * (x * y)
      exact mul_assoc _ _ _
    exact (LinearMap.lsmul A A a).restrictScalars k
  rw [Algebra.trace_apply (R := k) (S := A) a]
  change @LinearMap.trace k _ A _ module₀ (Algebra.lmul k A a) = _
  calc
    @LinearMap.trace k _ A _ module₀ (Algebra.lmul k A a) =
        @LinearMap.trace k _ A _ module₁ φ₁ :=
      trace_eq_of_module_eq k A module₀ module₁ hmodule _ _ fun _ ↦ rfl
    _ = _ := trace_lsmul_eq_length_mul_trace_residue k A A hAA a

/-! ### The three equivalent conditions -/

/-- **Stacks Project, Tag 0C13, (1) ⟺ (2).** For a finite algebra `A` over a field `k`, the
algebra trace `Tr_{A/k}` is nonzero exactly when a trace element of the relative dualizing module
is nonzero.

The trace element is given by the predicate `Stacks.Discriminant.IsTraceElement` rather than
chosen; by uniqueness (Tag 0BT7) this is a statement about a single determined element. -/
@[stacks 0C13 "conditions (1) and (2)"]
theorem trace_ne_zero_iff_isTraceElement_ne_zero (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Module.Finite k A] (F : FiniteOpenFactorization.{u, v, w} k A)
    (τ : dualizingModule F) :
    letI : IsNoetherianRing A := IsNoetherianRing.of_finite k A
    IsTraceElement.{u, v, w, u, max u v, max u v} F τ → (Algebra.trace k A ≠ 0 ↔ τ ≠ 0) := by
  classical
  let : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  intro hτ
  let G := selfFactorization k A
  let e : dualizingModule G ≃+ Module.Dual k A :=
    (TensorProduct.rid A (Module.Dual k A)).toAddEquiv
  have hunique : dualizingModuleEquiv F G τ = finiteFlatTraceElement k A :=
    isTraceElement_unique G ((isTraceElement_congr F G τ).mp hτ)
      (isTraceElement_finiteFlatTraceElement k A)
  have he : e (finiteFlatTraceElement k A) = Algebra.trace k A := by
    change e (dualizingModule.tmul G
      ((finiteProjectiveTrace k A).comp (Algebra.lmul k A).toLinearMap) 1) = _
    rw [finiteProjectiveTrace_eq_trace k A]
    ext a
    change (TensorProduct.rid A (Module.Dual k A)
      (((LinearMap.trace k A).comp (Algebra.lmul k A).toLinearMap) ⊗ₜ[A] (1 : A))) a = _
    rw [TensorProduct.rid_tmul]
    simp only [one_smul, LinearMap.comp_apply]
    exact (Algebra.trace_apply k a).symm
  let E : dualizingModule F ≃+ Module.Dual k A :=
    (dualizingModuleEquiv F G).toAddEquiv.trans e
  have hE : E τ = Algebra.trace k A := by
    change e (dualizingModuleEquiv F G τ) = _
    rw [hunique, he]
  rw [← hE]
  exact map_ne_zero_iff E E.injective

/-- **Stacks Project, Tag 0C13, (1) ⟺ (3).** For a finite local algebra `A` over a field `k`, the
algebra trace `Tr_{A/k}` is nonzero exactly when the residue field of `A` is separable over `k`
and the length of `A` is prime to the characteristic of `k`.

"Prime to the characteristic" is the nonvanishing in `k` of the natural number `length_A(A)`, a
condition that also covers characteristic zero. -/
@[stacks 0C13 "conditions (1) and (3)"]
theorem trace_ne_zero_iff_isSeparable_and_length_ne_zero (k : Type u) (A : Type v) [Field k]
    [CommRing A] [Algebra k A] [IsLocalRing A] [Module.Finite k A] :
    Algebra.trace k A ≠ 0 ↔
      Algebra.IsSeparable k (ResidueField A) ∧ ((Module.length A A).toNat : k) ≠ 0 := by
  classical
  let : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  have hformula := trace_eq_length_mul_trace_residue k A
  constructor
  · intro hne
    have hlen : ((Module.length A A).toNat : k) ≠ 0 := fun hzero ↦
      hne <| LinearMap.ext fun a ↦ by rw [hformula a, hzero]; simp
    have hres : Algebra.trace k (ResidueField A) ≠ 0 := fun hzero ↦
      hne <| LinearMap.ext fun a ↦ by rw [hformula a, hzero]; simp
    exact ⟨((traceForm_nondegenerate_tfae k (ResidueField A)).out 2 1).mp hres, hlen⟩
  · rintro ⟨hsep, hlen⟩ hzero
    obtain ⟨x, hx⟩ : ∃ x : ResidueField A, Algebra.trace k (ResidueField A) x ≠ 0 :=
      not_forall.mp fun h ↦ Algebra.trace_ne_zero k (ResidueField A) (LinearMap.ext h)
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective x
    have hmul : ((Module.length A A).toNat : k) * Algebra.trace k (ResidueField A) x = 0 := by
      have hz := congrArg (fun φ : A →ₗ[k] k ↦ φ a) hzero
      rw [hformula a, ha] at hz
      simpa using hz
    exact hx ((mul_eq_zero.mp hmul).resolve_left hlen)

end Stacks.Discriminant

end
