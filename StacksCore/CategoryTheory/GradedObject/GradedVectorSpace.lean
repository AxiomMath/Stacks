module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import StacksCore.Algebra.Category.ModuleCat.Dualizable
public import StacksCore.CategoryTheory.GradedObject.Monoidal.Dual

/-! # Dualizable graded vector spaces are finite dimensional

Stacks 0FFV: if a graded `F`-vector space `V` has a dual `W`, then every `Vⁿ` is finite
dimensional, only finitely many are nonzero, and each induced pairing `W⁻ⁿ × Vⁿ → F` is perfect.

A naming warning, checked rather than assumed: Stacks' "`W` is a *left* dual of `V`" is
`η : 1 ⟶ V ⊗ W`, `ε : W ⊗ V ⟶ 1` with the two triangles (Stacks 0FFP), which is exactly
Mathlib's `ExactPairing V W` — even though Mathlib calls that same `W` the *right* dual `Vᘁ`.
The orientation below is therefore the tag's, not its transpose.

Two of the three clauses are not really about grading: by
`CategoryTheory.GradedObject.Monoidal.exactPairingApply`, `W (-n)` is a dual of `V n` in
`ModuleCat F`, so they follow from the ungraded results in
`StacksCore.Algebra.Category.ModuleCat.Dualizable`. Only "almost all degrees vanish" needs a graded
argument, and it is the one place where an element is touched: the coevaluation is an element of
a direct sum, hence has finite support.

Note the monoidal structure on `GradedObject ℤ (ModuleCat F)` — Stacks 0FFX — needs no glue of
its own: it follows from Mathlib's `GradedObject.monoidalCategory` once the imports above are in
scope. The subtlety is that Mathlib registers "tensoring on the left preserves colimits" (it is a
left adjoint, via `MonoidalClosed`) but not the right-handed version, which arrives only through
`Mathlib.CategoryTheory.Monoidal.Limits.Preserves`.

The general-purpose half of 0FFX — the monoidal structure and the sign-free symmetry on
`GradedObject I C` — is attributed in `StacksCore.CategoryTheory.GradedObject.Monoidal`, next to the
Mathlib file it comes from. What is tagged here is the tag's own degreewise formula over a field.
-/

@[expose] public section

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory Category Limits MonoidalCategory GradedObject ModuleCat
open scoped TensorProduct

universe uF

/-- Index type of the degree-`n` part of a tensor product. -/
abbrev Idx (n : ℤ) : Type := ((fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {n})

variable {F : Type uF} [Field F] (V W : GradedObject ℤ (ModuleCat.{uF} F))

/-- **Stacks 0FFX**, the tag's degreewise formula: `(V ⊗ W)ⁿ` is the direct sum of `Vᵖ ⊗_F W^q`
over the pairs with `p + q = n`. The identification is the coproduct one, hence compatible with the
`ιTensorObj` inclusions — which a bare existence statement would forget. -/
@[stacks 0FFX "the degreewise formula for graded `F`-vector spaces, via the coproduct inclusions"]
noncomputable def tensorDegreeIso (n : ℤ) :
    (V ⊗ W) n ≅ ModuleCat.of F (DirectSum (Idx n) (fun a : Idx n => (V a.1.1) ⊗[F] (W a.1.2))) :=
  ModuleCat.coprodIsoDirectSum (fun a : Idx n => V a.1.1 ⊗ W a.1.2)

/-- The components of an element of `(V ⊗ W) n`. -/
noncomputable def comps (n : ℤ) (x : (V ⊗ W) n) :
    DirectSum (Idx n) (fun a : Idx n => V a.1.1 ⊗[F] W a.1.2) :=
  (tensorDegreeIso V W n).hom.hom x

open scoped Classical in
lemma sum_ι_comps (n : ℤ) (x : (V ⊗ W) n) :
    ∑ a ∈ (comps V W n x).support,
        (ιTensorObj V W a.1.1 a.1.2 n a.2).hom (comps V W n x a) = x := by
  have hx : (tensorDegreeIso V W n).inv.hom (comps V W n x) = x :=
    (tensorDegreeIso V W n).hom_inv_id_apply x
  conv_rhs => rw [← hx, ← DirectSum.sum_support_of (comps V W n x), map_sum]
  exact Finset.sum_congr rfl fun a _ => (ModuleCat.lof_coprodIsoDirectSum_inv_apply _ a _).symm

variable [ExactPairing V W]

/-- The coevaluation as an element of the degree-0 part. -/
noncomputable def coevElt : (V ⊗ W) 0 :=
  ((η_ V W) 0).hom ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{uF} F)).inv.hom 1)

open scoped Classical in
/-- If the `(n, -n)` component of the coevaluation vanishes then so does `coevApply`. -/
lemma coevApply_eq_zero_of_notMem (n : ℤ)
    (h : (⟨(n, -n), by simp⟩ : Idx (0 : ℤ)) ∉ (comps V W 0 (coevElt V W)).support) :
    coevApply V W n = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  change (πTensorObj V W n (-n) 0 (add_neg_cancel n)).hom (coevElt V W) = 0
  rw [← sum_ι_comps V W 0 (coevElt V W), map_sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hane : ¬ (a.1.1 = n ∧ a.1.2 = -n) := fun ⟨h1, h2⟩ =>
    h ((Subtype.ext (Prod.ext h1 h2) : a = ⟨(n, -n), by simp⟩) ▸ ha)
  simpa using ConcreteCategory.congr_hom (ιTensorObj_πTensorObj_ne V W n (-n) a.1.1 a.1.2 0 a.2
    (add_neg_cancel n) hane) (comps V W 0 (coevElt V W) a)

open scoped Classical in
theorem finite_support_coevApply : {n : ℤ | coevApply V W n ≠ 0}.Finite :=
  ((comps V W 0 (coevElt V W)).support.image fun a : Idx (0 : ℤ) => a.1.1).finite_toSet.subset
    fun n hn => not_not.1 fun hcon => hn (coevApply_eq_zero_of_notMem V W n fun hm =>
      hcon (Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, hm, rfl⟩)))

/-- Outside the finite support, the degree vanishes. -/
theorem isZero_of_coevApply_eq_zero (n : ℤ) (h : coevApply V W n = 0) : Limits.IsZero (V n) :=
  letI := exactPairingApply V W n; isZero_of_coevaluation_eq_zero (X := V n) (Y := W (-n)) h

theorem support_finite (V W : GradedObject ℤ (ModuleCat.{uF} F)) [ExactPairing V W] :
    {n : ℤ | ¬ Limits.IsZero (V n)}.Finite :=
  (finite_support_coevApply V W).subset fun n hn hc => hn (isZero_of_coevApply_eq_zero V W n hc)

/-- **Stacks 0FFV**, the finite-dimensionality clause on its own. -/
@[stacks 0FFV "the finite-dimensionality clause"]
theorem finiteDimensional_apply (V W : GradedObject ℤ (ModuleCat.{uF} F)) [ExactPairing V W]
    (n : ℤ) : FiniteDimensional F (V n) :=
  letI := exactPairingApply V W n; finite_of_exactPairing (V n) (W (-n))

/-- The pairing `W^{-n} × V^n → F` induced by the evaluation. -/
noncomputable def gradedPairing (n : ℤ) : W (-n) →ₗ[F] V n →ₗ[F] F :=
  TensorProduct.curry ((evalApply V W n).hom : (W (-n) ⊗[F] V n) →ₗ[F] F)

/-- **Stacks 0FFV**: a graded vector space with a dual is finite dimensional in each degree,
nonzero in only finitely many degrees, and its evaluation is degreewise a perfect pairing.

Together the first two clauses say `∑ₙ dim_F Vⁿ < ∞`, which is the tag's own phrasing. -/
@[stacks 0FFV]
theorem finiteDimensional_and_isPerfPair_of_exactPairing :
    (∀ n, FiniteDimensional F (V n)) ∧ {n : ℤ | ¬ Limits.IsZero (V n)}.Finite ∧
      ∀ n, (gradedPairing V W n).IsPerfPair :=
  ⟨finiteDimensional_apply V W, support_finite V W, fun n =>
    letI := exactPairingApply V W n; pairingU_isPerfPair (V n) (W (-n))⟩

end CategoryTheory.GradedObject.Monoidal
