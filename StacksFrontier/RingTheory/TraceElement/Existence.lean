module

public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceCondition
public import StacksFrontier.RingTheory.TraceElement.Construction
public import StacksFrontier.RingTheory.TraceElement.FiniteFactor
public import StacksFrontier.RingTheory.TraceElement.ProjectiveTrace

/-!
# Existence of trace elements

For a flat quasi-finite map `A → B` of Noetherian rings, the relative dualizing module
`ω_{B/A}` contains a trace element in the sense of Tag 0BT6.

The element is produced from a *dual family* for the structure map of a finite-open
factorization `A → C → B`: since `C` is a finitely presented `A`-module and `B` is flat over
`A`, the map `C → B` factors through a finite free `A`-module, giving finitely many
functionals `λ i : Hom_A(C, A)` and elements `b i ∈ B` with `∑ λ i (c) b i` the image of `c`.
The element `∑ λ i ⊗ b i` of `ω_{B/A}` is then a trace element: after any Noetherian base
change `A₁` and any decomposition `A₁ ⊗_A B ≃ C₁ × D` with `C₁` finite over `A₁`, the family
`(λ i ⊗ 1, (b i)₁)` presents the structure map of the base-changed factorization, and
contracting the trace over the intermediate algebra against it gives the trace over `A₁`.

The canonical choice of such an element is
`Stacks.Discriminant.dualizingModule.traceCandidate`, and
`Stacks.Discriminant.isTraceElement_traceCandidate` identifies it as a trace element; by the
uniqueness of Tag 0BT7 it is therefore the only one.

## Main results

* `Stacks.Discriminant.isTraceElement_of_dualFamily`: a dual family for the structure map of a
  finite-open factorization produces a trace element.
* `Stacks.Discriminant.isTraceElement_traceCandidate`: the canonical element of the relative
  dualizing module is a trace element.
* `Stacks.Discriminant.exists_isTraceElement`: Tag 0BTB, existence of a trace element.
* `Stacks.Discriminant.exists_not_isTraceElement_zero`: the trace-element property is not
  vacuous — for `ℤ → ℤ × ℤ` the zero element is not a trace element.

## References

* [Stacks Project, Tag 0BTB](https://stacks.math.columbia.edu/tag/0BTB)
* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y z

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]

/-- A finite flat module over a Noetherian ring is projective. -/
private theorem projective_of_finite_flat (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] [Module.Flat R M] : Module.Projective R M := by
  have := Module.finitePresentation_of_finite R M
  exact Module.Flat.projective_of_finitePresentation

/-- A finite family of functionals `f i` on the intermediate algebra and elements `b i` of the
target with `∑ i, f i c • b i` the image of `c` for every `c` produces a trace element of the
relative dualizing module, namely `∑ i, f i ⊗ b i`.

Such a family presents the structure map `C → B` as an element of `Hom_A(C, A) ⊗_A B`; it is
the map `ψ` of the Stacks project's proof of Tag 0BTB with the denominator already cleared. -/
theorem isTraceElement_of_dualFamily (F : FiniteOpenFactorization.{u, v, w} A B)
    {ι : Type*} [Fintype ι] (f : ι → Module.Dual A F.middle) (b : ι → B)
    (h : ∀ c : F.middle, ∑ i, f i c • b i = algebraMap F.middle B c) :
    IsTraceElement.{u, v, w, x, y, z} F (∑ i, dualizingModule.tmul F (f i) (b i)) := by
  classical
  intro A₁ _ _ _ C D _ _ _ _ e hfinite
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let : Algebra F₁.middle C :=
    ((RingHom.fst C D).comp (e.toRingEquiv.toRingHom.comp F₁.algebraTarget.algebraMap)).toAlgebra
  have : Module.Finite A₁ C := hfinite
  have : Module.Flat A₁ C := flat_of_prodRingEquiv e.toRingEquiv (by
    intro a
    show (e (algebraMap A₁ (A₁ ⊗[A] B) a)).1 = algebraMap A₁ C a
    rw [e.commutes]
    rfl)
  have := projective_of_finite_flat A₁ C
  refine ⟨inferInstance, ?_⟩
  have : IsScalarTower A₁ F₁.middle C := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    show algebraMap A₁ C a =
      (e (algebraMap F₁.middle (A₁ ⊗[A] B) (algebraMap A₁ F₁.middle a))).1
    rw [← IsScalarTower.algebraMap_apply, e.commutes]
    rfl
  have : Module.Finite F₁.middle C := Module.Finite.of_restrictScalars_finite A₁ _ C
  have : IsNoetherianRing F₁.middle := IsNoetherianRing.of_finite A₁ F₁.middle
  have : Module.Flat F₁.middle (A₁ ⊗[A] B) := flat_of_finiteOpenFactorization F₁
  have : Module.Flat F₁.middle C := flat_of_prodRingEquiv e.toRingEquiv (by intro; rfl)
  have := projective_of_finite_flat F₁.middle C
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hbc (r : F₁.middle) :
      ∑ i, (f i).baseChange A₁ r • ((1 : A₁) ⊗ₜ[A] b i) =
        algebraMap F₁.middle (A₁ ⊗[A] B) r := by
    show ∑ i, (f i).baseChange A₁ r • ((1 : A₁) ⊗ₜ[A] b i) =
      (Algebra.TensorProduct.map (AlgHom.id A A₁) (IsScalarTower.toAlgHom A F.middle B)) r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add r s hr hs => simp [map_add, add_smul, Finset.sum_add_distrib, hr, hs]
    | tmul a r =>
      simpa [TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul'] using
        congrArg (fun z : B => a ⊗ₜ[A] z) (h r)
  have hc (r : F₁.middle) :
      ∑ i, (f i).baseChange A₁ r • (e ((1 : A₁) ⊗ₜ[A] b i)).1 = algebraMap F₁.middle C r := by
    show ∑ i, (f i).baseChange A₁ r • (e ((1 : A₁) ⊗ₜ[A] b i)).1 =
      (e (algebraMap F₁.middle (A₁ ⊗[A] B) r)).1
    simpa only [map_sum, map_smul, Prod.fst_sum, Prod.smul_fst] using
      congrArg (fun z => (e z).1) (hbc r)
  ext c
  simp only [map_sum, dualizingModule.baseChange_tmul, LinearMap.sum_apply, LinearMap.comp_apply]
  calc
    _ = ∑ i, (f i).baseChange A₁ (finiteProjectiveTrace F₁.middle C
        (Algebra.lmul F₁.middle C ((e ((1 : A₁) ⊗ₜ[A] b i)).1 * c))) :=
      Finset.sum_congr rfl fun i _ =>
        (finiteFactorRestriction F A₁ C D e (by intro; rfl) hfinite inferInstance
          inferInstance inferInstance).2 _ _ _
    _ = _ := finiteProjectiveTrace_lmul_eq_sum_of_tower (A := A₁) (R := F₁.middle)
      (fun i => (f i).baseChange A₁) (fun i => (e ((1 : A₁) ⊗ₜ[A] b i)).1) hc c

/-- **The canonical element of the relative dualizing module is a trace element.** This
completes `Stacks.Discriminant.dualizingModule.traceCandidate`: the element constructed there
by a universal property satisfies the finite-factor trace condition of Tag 0BT6, and so by the
uniqueness of Tag 0BT7 it is the trace element. -/
theorem isTraceElement_traceCandidate (F : FiniteOpenFactorization.{u, v, w} A B)
    [Module.FinitePresentation A F.middle] :
    IsTraceElement.{u, v, w, x, y, z} F (dualizingModule.traceCandidate F) := by
  classical
  obtain ⟨S, hsum, hrepr⟩ := dualizingModule.exists_traceCandidate_repr F
  rw [hrepr, ← S.sum_coe_sort (f := fun p => dualizingModule.tmul F p.2 p.1)]
  refine isTraceElement_of_dualFamily F (fun p : ↥S => (p : B × Module.Dual A F.middle).2)
    (fun p : ↥S => (p : B × Module.Dual A F.middle).1) fun c => ?_
  exact (S.sum_coe_sort (f := fun p => p.2 c • p.1)).trans (hsum c)

/-- **Stacks Project, Tag 0BTB.** A flat quasi-finite map of Noetherian rings has a trace
element in its relative dualizing module. -/
@[stacks 0BTB]
theorem exists_isTraceElement (F : FiniteOpenFactorization.{u, v, w} A B) :
    ∃ τ : dualizingModule F, IsTraceElement.{u, v, w, x, y, z} F τ := by
  have : Module.FinitePresentation A F.middle := Module.finitePresentation_of_finite A F.middle
  exact ⟨dualizingModule.traceCandidate F, isTraceElement_traceCandidate F⟩

/-- **The trace-element property is a genuine constraint.** For the finite flat map
`ℤ → ℤ × ℤ` and a finite-open factorization of it, the zero element of the relative
dualizing module is not a trace element.

This is the non-vacuity check for `Stacks.Discriminant.IsTraceElement`: the predicate
quantifies over all Noetherian base changes and all product decompositions with a finite
factor, so it would read as a theorem about trace elements even if it held of everything.
It does not. The factorization is kept inside the proof, since only its existence matters
here. -/
theorem exists_not_isTraceElement_zero :
    ∃ F : FiniteOpenFactorization.{0, 0, 0} ℤ (ℤ × ℤ),
      ¬ IsTraceElement.{0, 0, 0, 0, 0, 0} F 0 := by
  refine ⟨{ middle := ℤ × ℤ
            commRingMiddle := inferInstance
            algebraMiddle := inferInstance
            algebraTarget := inferInstance
            scalarTower := inferInstance
            finite_middle := inferInstance
            isOpenEmbedding_comap := ?_
            awayMap_bijective := ?_ }, ?_⟩
  · show Topology.IsOpenEmbedding (fun q : PrimeSpectrum (ℤ × ℤ) => q)
    exact ⟨.id, IsOpenMap.id.isOpen_range⟩
  · intro g _
    constructor
    · rw [Localization.awayMap_injective_iff]
      intro a ha
      exact ⟨0, by simpa using ha⟩
    · rw [Localization.awayMap_surjective_iff]
      intro a
      exact ⟨a, 0, by simp⟩
  · intro hτ
    obtain ⟨hp, hmf, hmp, heq⟩ :=
      hτ ℤ ℤ ℤ (Algebra.TensorProduct.lid ℤ (ℤ × ℤ)) inferInstance
    have h1 := LinearMap.congr_fun heq 1
    rw [map_zero, map_zero] at h1
    simp only [LinearMap.zero_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h1
    rw [finiteProjectiveTrace_eq_trace ℤ ℤ] at h1
    have hid : (Algebra.lmul ℤ ℤ) 1 = LinearMap.id := by
      ext
      simp
    rw [hid, LinearMap.trace_id] at h1
    simp at h1

end Stacks.Discriminant

end
