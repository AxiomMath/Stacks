module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical element of a relative dualizing module

Let `A → B` be a map of commutative rings admitting a finite-open factorization
`A → C → B`, so that the relative dualizing module is `ω_{B/A} = Hom_A(C, A) ⊗_C B`.
This file constructs a canonical element of `ω_{B/A}` whenever `B` is flat as an
`A`-module, and records the concrete data that presents it.

The construction is the one in the Stacks project's proof of Tag 0BTB. Since `C` is a
finitely presented `A`-module and `B` is a flat `A`-module, the natural map
`Hom_A(C, A) ⊗_A B → Hom_A(C, B)` is an isomorphism; the element of
`Hom_A(C, A) ⊗_A B` corresponding to the structure map `C → B` is pushed forward along
the natural surjection `Hom_A(C, A) ⊗_A B → Hom_A(C, A) ⊗_C B`.

Written this way the construction is uniform in the factorization: the source reduces to
the case `B = C_g` of a single away localization and then clears a denominator `g ^ n`,
whose choice it has to argue is immaterial, whereas the element below is defined by a
universal property and so requires no such choice.

## Main definitions

* `Stacks.Discriminant.dualBaseChangeEquiv` is the isomorphism
  `B ⊗_A Hom_A(C, A) ≅ Hom_A(C, B)` for `C` a finitely presented `A`-module and `B` a
  flat `A`-algebra.
* `Stacks.Discriminant.dualizingModule.ofBaseChangeTensor` is the natural surjection
  `B ⊗_A Hom_A(C, A) → ω_{B/A}` forgetting that the tensor product is taken over `A`
  rather than over `C`.
* `Stacks.Discriminant.dualizingModule.traceCandidate` is the resulting element of
  `ω_{B/A}`.

## Main results

* `Stacks.Discriminant.dualBaseChangeEquiv_tmul` evaluates the isomorphism on a pure
  tensor, which pins it down.
* `Stacks.Discriminant.dualizingModule.exists_traceCandidate_repr` presents the
  canonical element by a finite family `(λ_i, b_i)` with `∑ λ_i(c) b_i` the image of `c`
  in `B` for every `c ∈ C`. This finite family is the map `ψ` of the source, and it is
  the form in which a proof that the element is a trace element consumes it.
* `Stacks.Discriminant.finiteProjectiveTrace_eq_sum_of_dualFamily` computes the trace of
  an endomorphism of a finite projective module from such a family.
* `Stacks.Discriminant.sum_apply_mul_eq_finiteProjectiveTrace` is the resulting check on
  the construction: when the factorization is already finite, contracting the presenting
  family returns the trace of multiplication.

## Implementation notes

`Hom_A(C, A) ⊗_C B` is a tensor product over `C` while `Hom_A(C, A) ⊗_A B` is one over
`A`, and the comparison between them is only additive for the structures that are
available without further hypotheses, so `ofBaseChangeTensor` is built with
`TensorProduct.liftAddHom`. That is enough: the element it is applied to is produced by
`dualBaseChangeEquiv`, which carries all the linearity the construction uses.

The `C`-action on `Hom_A(C, A)` is `Stacks.Discriminant.algebraDualModule`, which the
library deliberately keeps off the instance graph, so it is installed here as a local
instance.

## References

* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
* [Stacks Project, Tag 0BTB](https://stacks.math.columbia.edu/tag/0BTB)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

section DualBaseChange

variable (A : Type u) (B : Type v) (C : Type w)
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- For `C` a finitely presented `A`-module and `B` a flat `A`-algebra, the natural map
`B ⊗_A Hom_A(C, A) → Hom_A(C, B)` sending `b ⊗ λ` to `c ↦ λ(c) b` is an isomorphism of
`B`-modules.

This is the base-change isomorphism for the functor `Hom_A(C, -)`: it is evident when `C`
is finite free, and finite presentation plus flatness propagate it from a presentation of
`C` by finite free modules. -/
def dualBaseChangeEquiv [Module.Flat A B] [Module.FinitePresentation A C] :
    B ⊗[A] Module.Dual A C ≃ₗ[B] (C →ₗ[A] B) :=
  (Module.FinitePresentation.isBaseChange_map A C A B).equiv ≪≫ₗ
    LinearEquiv.congrRight (TensorProduct.AlgebraTensorModule.rid A B B) ≪≫ₗ
    (LinearMap.liftBaseChangeEquiv (R := A) B (M := C) (N := B)).symm

/-- The isomorphism `Stacks.Discriminant.dualBaseChangeEquiv` sends `b ⊗ l` to the map
`c ↦ l(c) b`. -/
@[simp]
lemma dualBaseChangeEquiv_tmul [Module.Flat A B] [Module.FinitePresentation A C]
    (b : B) (l : Module.Dual A C) (c : C) :
    dualBaseChangeEquiv A B C (b ⊗ₜ l) c = l c • b := by
  simp [dualBaseChangeEquiv, LinearEquiv.congrRight, LinearMap.baseChangeHom]

/-- If `f : C → B` corresponds to a finite sum of pure tensors, then `f c = ∑ λ_i(c) b_i`. -/
private theorem sum_apply_smul_eq_of_symm_eq [Module.Flat A B] [Module.FinitePresentation A C]
    (f : C →ₗ[A] B) (S : Finset (B × Module.Dual A C))
    (hS : (dualBaseChangeEquiv A B C).symm f = ∑ p ∈ S, p.1 ⊗ₜ[A] p.2) (c : C) :
    ∑ p ∈ S, p.2 c • p.1 = f c := by
  rw [← LinearEquiv.apply_symm_apply (dualBaseChangeEquiv A B C) f, hS, map_sum,
    LinearMap.sum_apply]
  simp

end DualBaseChange

section Trace

/-- The trace of an endomorphism of a finite projective module, computed from any finite
family `(b_i, λ_i)` with `∑ λ_i(m) b_i = m`: it is `∑ λ_i (f b_i)`.

Such a family is the same data as a splitting of `P` off a finite free module, and the
trace of `f` is the trace of the induced endomorphism of that free module, whose diagonal
entries are the stated values. -/
@[sga "6 I 8.1.1" "special case"]
theorem finiteProjectiveTrace_eq_sum_of_dualFamily (A : Type u) (P : Type w)
    [CommRing A] [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P]
    (S : Finset (P × Module.Dual A P)) (hS : ∀ m : P, ∑ p ∈ S, p.2 m • p.1 = m)
    (f : Module.End A P) :
    finiteProjectiveTrace A P f = ∑ p ∈ S, p.2 (f p.1) := by
  classical
  set p₀ : (↥S → A) →ₗ[A] P :=
    Fintype.linearCombination A (fun j : ↥S ↦ (j : P × Module.Dual A P).1) with hp₀
  set i₀ : P →ₗ[A] (↥S → A) :=
    LinearMap.pi (fun j : ↥S ↦ (j : P × Module.Dual A P).2) with hi₀
  have hpi : p₀.comp i₀ = LinearMap.id := by
    ext m
    simp only [hp₀, hi₀, LinearMap.comp_apply, LinearMap.id_apply, LinearMap.pi_apply,
      Fintype.linearCombination_apply, Finset.univ_eq_attach]
    rw [Finset.sum_attach S fun q ↦ q.2 m • q.1]
    exact hS m
  rw [finiteProjectiveTrace_eq_trace_of_split A P (↥S → A) p₀ i₀ hpi f,
    LinearMap.trace_eq_matrix_trace A (Pi.basisFun A ↥S), Matrix.trace]
  rw [← S.sum_coe_sort (f := fun q ↦ q.2 (f q.1))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [hp₀, hi₀, Fintype.linearCombination_apply, Pi.single_apply]

/-- **The canonical element is the trace, in the finite case.** If `C` is a finitely
presented projective `A`-algebra and a finite family `(b_i, λ_i)` presents the identity of
`C` under `C ⊗_A Hom_A(C, A) ≅ Hom_A(C, C)`, then `∑ λ_i(x b_i)` is the trace of
multiplication by `x` for every `x ∈ C`.

This is the remark in the Stacks project's proof of Tag 0BTB that the composition
`C → Hom_A(C, C) ← Hom_A(C, A) ⊗_A C → A` is the usual trace, and it is the reason the
element of `Stacks.Discriminant.dualizingModule.traceCandidate` deserves its name: by
`Stacks.Discriminant.dualizingModule.exists_traceCandidate_repr` that element is presented
by exactly such a family, for the structure map `C → B` in place of the identity. -/
theorem sum_apply_mul_eq_finiteProjectiveTrace (A : Type u) (C : Type w)
    [CommRing A] [CommRing C] [Algebra A C] [Module.FinitePresentation A C]
    [Module.Projective A C] (S : Finset (C × Module.Dual A C))
    (hS : (dualBaseChangeEquiv A C C).symm (LinearMap.id (R := A) (M := C)) =
      ∑ p ∈ S, p.1 ⊗ₜ[A] p.2) (x : C) :
    ∑ p ∈ S, p.2 (x * p.1) = finiteProjectiveTrace A C (Algebra.lmul A C x) := by
  have hfam : ∀ c : C, ∑ p ∈ S, p.2 c • p.1 = c :=
    sum_apply_smul_eq_of_symm_eq A C C _ S hS
  rw [finiteProjectiveTrace_eq_sum_of_dualFamily A C S hfam (Algebra.lmul A C x)]
  simp

end Trace

namespace dualizingModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The intermediate algebra of a finite-open factorization over a Noetherian ring is a
finitely presented module, which is the hypothesis under which
`Stacks.Discriminant.dualBaseChangeEquiv` applies to it. -/
lemma finitePresentation_middle [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Module.FinitePresentation A F.middle :=
  Module.finitePresentation_of_finite A F.middle

/-- The `C`-action of `Stacks.Discriminant.algebraDualModule` restricts along `A → C` to
the pointwise `A`-action on `Hom_A(C, A)`. -/
lemma algebraMap_smul_dual {C : Type w} [CommRing C] [Algebra A C] (a : A)
    (l : Module.Dual A C) : (algebraMap A C a) • l = a • l := by
  ext x
  rw [algebraDualModule_smul_apply, ← Algebra.smul_def, map_smul, LinearMap.smul_apply]

/-- A pure tensor of the relative dualizing module is additive in its `B`-factor. The
library supplies the companion `Stacks.Discriminant.dualizingModule.add_tmul` for the dual
factor. -/
lemma tmul_add (F : FiniteOpenFactorization.{u, v, w} A B) (l : Module.Dual A F.middle)
    (b₁ b₂ : B) :
    dualizingModule.tmul F l (b₁ + b₂) =
      dualizingModule.tmul F l b₁ + dualizingModule.tmul F l b₂ :=
  TensorProduct.tmul_add l b₁ b₂

/-- Pure tensors of the relative dualizing module, as an additive map in the dual factor
for a fixed element of `B`. -/
def tmulAddHomRight (F : FiniteOpenFactorization.{u, v, w} A B) (b : B) :
    Module.Dual A F.middle →+ dualizingModule F :=
  AddMonoidHom.mk' (fun l ↦ dualizingModule.tmul F l b) fun l₁ l₂ ↦ add_tmul F l₁ l₂ b

/-- Pure tensors of the relative dualizing module, as a biadditive map. -/
def tmulAddHom (F : FiniteOpenFactorization.{u, v, w} A B) :
    B →+ (Module.Dual A F.middle →+ dualizingModule F) :=
  AddMonoidHom.mk' (tmulAddHomRight F) fun b₁ b₂ ↦
    AddMonoidHom.ext fun l ↦ tmul_add F l b₁ b₂

/-- The natural surjection `B ⊗_A Hom_A(C, A) → ω_{B/A}` of a finite-open factorization
`A → C → B`, forgetting that the tensor product is taken over `A` rather than over `C`.

It is additive rather than linear because the two sides carry no common ring action that
the structures on `Stacks.Discriminant.dualizingModule` supply. -/
def ofBaseChangeTensor (F : FiniteOpenFactorization.{u, v, w} A B) :
    B ⊗[A] Module.Dual A F.middle →+ dualizingModule F :=
  TensorProduct.liftAddHom (tmulAddHom F) fun a b l ↦ by
    change dualizingModule.tmul F l (a • b) = dualizingModule.tmul F (a • l) b
    rw [← algebraMap_smul_dual (C := F.middle) a l]
    change l ⊗ₜ[F.middle] (a • b) = (algebraMap A F.middle a • l) ⊗ₜ[F.middle] b
    rw [TensorProduct.smul_tmul, algebraMap_smul]

/-- The map `ofBaseChangeTensor` sends `b ⊗ l` to the pure tensor `l ⊗ b` of the relative
dualizing module. -/
@[simp]
lemma ofBaseChangeTensor_tmul (F : FiniteOpenFactorization.{u, v, w} A B) (b : B)
    (l : Module.Dual A F.middle) :
    ofBaseChangeTensor F (b ⊗ₜ l) = dualizingModule.tmul F l b :=
  TensorProduct.liftAddHom_tmul _ _ b l

/-- **The canonical element of a relative dualizing module.** For a finite-open
factorization `A → C → B` with `B` flat over `A`, the element of
`ω_{B/A} = Hom_A(C, A) ⊗_C B` obtained by transporting the structure map `C → B` through
the isomorphism `B ⊗_A Hom_A(C, A) ≅ Hom_A(C, B)` and projecting to the tensor product
over `C`.

This is the element the Stacks project constructs in the proof of Tag 0BTB. That it is a
trace element in the sense of Tag 0BT6 is not proved here. -/
def traceCandidate (F : FiniteOpenFactorization.{u, v, w} A B) [Module.Flat A B]
    [Module.FinitePresentation A F.middle] : dualizingModule F :=
  ofBaseChangeTensor F
    ((dualBaseChangeEquiv A B F.middle).symm
      ((Algebra.linearMap F.middle B).restrictScalars A))

/-- The element of `B ⊗_A Hom_A(C, A)` underlying the canonical element of the dualizing
module corresponds to the structure map `C → B`. -/
lemma dualBaseChangeEquiv_symm_algebraLinearMap
    (F : FiniteOpenFactorization.{u, v, w} A B) [Module.Flat A B]
    [Module.FinitePresentation A F.middle] (c : F.middle) :
    dualBaseChangeEquiv A B F.middle
        ((dualBaseChangeEquiv A B F.middle).symm
          ((Algebra.linearMap F.middle B).restrictScalars A)) c =
      algebraMap F.middle B c := by
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- **The data presenting the canonical element.** For a finite-open factorization
`A → C → B` with `B` flat over `A` there is a finite family of pairs `(b, λ) ∈ B × Hom_A(C, A)`
such that `∑ λ(c) b` is the image of `c` in `B` for every `c ∈ C`, and such that
`∑ λ ⊗ b` is the canonical element of `ω_{B/A}`.

The first condition says that the family presents the structure map `C → B` as an element
of `Hom_A(C, A) ⊗_A B`; it is the map `ψ` of the Stacks project's proof of Tag 0BTB, with
the denominator `g ^ n` already cleared. -/
theorem exists_traceCandidate_repr (F : FiniteOpenFactorization.{u, v, w} A B)
    [Module.Flat A B] [Module.FinitePresentation A F.middle] :
    ∃ S : Finset (B × Module.Dual A F.middle),
      (∀ c : F.middle, ∑ p ∈ S, p.2 c • p.1 = algebraMap F.middle B c) ∧
        traceCandidate F = ∑ p ∈ S, dualizingModule.tmul F p.2 p.1 := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset
    ((dualBaseChangeEquiv A B F.middle).symm
      ((Algebra.linearMap F.middle B).restrictScalars A))
  refine ⟨S, fun c ↦ ?_, ?_⟩
  · exact sum_apply_smul_eq_of_symm_eq A B F.middle _ S hS c
  · rw [traceCandidate, hS, map_sum]
    simp

end dualizingModule

end Stacks.Discriminant
