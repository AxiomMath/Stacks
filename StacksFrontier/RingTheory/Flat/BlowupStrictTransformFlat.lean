module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import StacksFrontier.RingTheory.AffineBlowup.ChartEquiv
public import StacksFrontier.RingTheory.Blowup.StrictTransform
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic

/-!
# The strict transform of a flat base change, and base change of a presentation

Let `R` be a commutative ring, `I ⊆ R` an ideal, `a ∈ I`, and let `R[I/a] = Blowup I a` be the
affine blowup chart.  The strict transform `strictTransform I a M` of an `R`-module `M`
(Stacks Tag 053H) is the scalar extension `R[I/a] ⊗[R] M` with its `a`-power torsion removed.

This file contains two independent steps of the proof of Stacks Tag 053I.

The first is that the torsion removal is vacuous as soon as the scalar extension is *flat* over
`R[I/a]` and `R[I/a]` is a domain: a flat module over a domain is torsion free (Stacks Tag 0538,
`Module.Flat.isTorsionFree`), and the image of `a` in `R[I/a]` is a nonzerodivisor
(Stacks Tag 07Z3 (1)), hence nonzero.  So the strict transform *is* the scalar extension, and
flatness and finite presentation transfer to it.

The second is the identity expressing that base change of a finite presentation is the base-changed
presentation: if `π : Sʳ → M` is a surjection of `S`-modules whose kernel is spanned by `k₁, …,
k_t`, and `N` is the base change of `M` along an `S`-algebra `T`, then `N ≅ Tʳ / ⟨k₁, …, k_t⟩`, the
relations being read in `Tʳ` through `algebraMap S T`. This is right exactness of the tensor
product and is assembled from `Stacks.QuasiregularSequence.FlatBaseChange.isBaseChange_of_quotient`
together with `IsBaseChange.finitePow` for the free part.

## Main results

* `Blowup.isDomain`: for `R` a domain and `a ≠ 0`, the chart `R[I/a]` is a domain.
* `strictTransform.torsionSubmodule_eq_bot`: the `a`-power torsion of `R[I/a] ⊗[R] M` vanishes
  when that scalar extension is flat over a chart that is a domain.
* `strictTransform.linearEquivBaseChange`: consequently the strict transform is the scalar
  extension.
* `strictTransform.flat`, `strictTransform.finitePresentation`: flatness and finite presentation
  of the scalar extension transfer to the strict transform.
* `Stacks.Flatness.BlowupFlattening.relSubmodule`: the relation submodule of the base-changed
  presentation.
* `Stacks.Flatness.BlowupFlattening.baseChangeQuotEquiv`: base change of a finite presentation is
  the base-changed
  presentation, together with `Stacks.Flatness.BlowupFlattening.baseChangeQuotEquiv_apply`
    describing it on
  generators and `Stacks.Flatness.BlowupFlattening.finitePresentation_of_baseChange`.
* `Stacks.Flatness.BlowupFlattening.tensorQuotEquiv`: the same identity for the tensor product `T
  ⊗[S] M` itself.

## References

* [Stacks Project, Tag 053H](https://stacks.math.columbia.edu/tag/053H) (the strict transform)
* [Stacks Project, Tag 0538](https://stacks.math.columbia.edu/tag/0538) (flat implies torsion
  free over a domain)
* [Stacks Project, Tag 053I](https://stacks.math.columbia.edu/tag/053I) (blowing up and flatness)
-/

@[expose] public section

universe u v w

open TensorProduct

/-! ### The chart of a domain is a domain -/

namespace Blowup

/-- **The affine blowup chart of a domain is a domain.** For `R` a domain, `I ⊆ R` an ideal and
`0 ≠ a ∈ I`, the chart `R[I/a] = Blowup I a` is isomorphic to a subalgebra of the fraction field
of `R` by `Stacks.AffineBlowup.blowupEquivAffineBlowupImage'`, hence is a domain. -/
theorem isDomain {R : Type u} [CommRing R] [IsDomain R] (I : Ideal R) (a : R) [Fact (a ∈ I)]
    (ha0 : a ≠ 0) : IsDomain (Blowup I a) :=
  MulEquiv.isDomain _
    (Stacks.AffineBlowup.blowupEquivAffineBlowupImage' (K := FractionRing R) (I := I) (a := a)
      ha0).toRingEquiv.toMulEquiv

end Blowup

/-! ### The torsion vanishes under flatness -/

namespace strictTransform

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) [ha : Fact (a ∈ I)]
  (M : Type v) [AddCommGroup M] [Module R M]

/-- **The image of `a` in the chart is nonzero** whenever the chart is nontrivial: it is a
nonzerodivisor by Stacks Tag 07Z3 (1), and `0` is a nonzerodivisor only in the zero ring. -/
theorem algebraMap_a_ne_zero [Nontrivial (Blowup I a)] :
    algebraMap R (Blowup I a) a ≠ 0 :=
  nonZeroDivisors.ne_zero (blowup_image_a_mem_nonZeroDivisors I a ha.out)

/-- **A flat scalar extension has no `a`-power torsion.** If the scalar extension
`R[I/a] ⊗[R] M` is flat over the chart `R[I/a]` and that chart is a domain, then the submodule
of elements killed by a power of the image of `a` — the submodule by which the strict transform
of Stacks Tag 053H is the quotient — is zero.

Indeed a flat module over a domain is torsion free (Stacks Tag 0538,
`Module.Flat.isTorsionFree`), and the image of `a` is a nonzerodivisor by Stacks Tag 07Z3 (1),
hence nonzero, hence so is each of its powers. -/
theorem torsionSubmodule_eq_bot [IsDomain (Blowup I a)]
    [Module.Flat (Blowup I a) (TensorProduct R (Blowup I a) M)] :
    strictTransform.torsionSubmodule I a M = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  obtain ⟨n, hn⟩ := (strictTransform.mem_torsionSubmodule_iff I a M).mp hx
  rcases Module.isTorsionFree_iff_smul_eq_zero.mp
    (inferInstance :
      Module.IsTorsionFree (Blowup I a) (TensorProduct R (Blowup I a) M)) _ _ hn with h | h
  · exact absurd h (pow_ne_zero n (strictTransform.algebraMap_a_ne_zero I a))
  · exact h

/-- **A flat strict transform is the scalar extension.** Under the hypotheses of
`strictTransform.torsionSubmodule_eq_bot` the strict transform of Stacks Tag 053H is a quotient
by the zero submodule, hence is identified with the scalar extension `R[I/a] ⊗[R] M` itself. -/
noncomputable def linearEquivBaseChange [IsDomain (Blowup I a)]
    [Module.Flat (Blowup I a) (TensorProduct R (Blowup I a) M)] :
    strictTransform I a M ≃ₗ[Blowup I a] TensorProduct R (Blowup I a) M :=
  Submodule.quotEquivOfEqBot (strictTransform.torsionSubmodule I a M)
    (strictTransform.torsionSubmodule_eq_bot I a M)

/-- The identification of a flat strict transform with the scalar extension sends the class of
`x` to `x`. -/
@[simp]
theorem linearEquivBaseChange_mkQ [IsDomain (Blowup I a)]
    [Module.Flat (Blowup I a) (TensorProduct R (Blowup I a) M)]
    (x : TensorProduct R (Blowup I a) M) :
    strictTransform.linearEquivBaseChange I a M (strictTransform.mkQ I a M x) = x :=
  rfl

/-- **The strict transform of a flat base change is flat.** If `R[I/a] ⊗[R] M` is flat over the
chart `R[I/a]` and that chart is a domain, then so is the strict transform, being isomorphic to
it by `strictTransform.linearEquivBaseChange`. -/
theorem flat [IsDomain (Blowup I a)]
    [Module.Flat (Blowup I a) (TensorProduct R (Blowup I a) M)] :
    Module.Flat (Blowup I a) (strictTransform I a M) :=
  Module.Flat.of_linearEquiv (strictTransform.linearEquivBaseChange I a M)

/-- **The strict transform of a flat base change of finite presentation is of finite
presentation.** Under the hypotheses of `strictTransform.torsionSubmodule_eq_bot`, finite
presentation of the scalar extension transfers to the strict transform along
`strictTransform.linearEquivBaseChange`. -/
theorem finitePresentation [IsDomain (Blowup I a)]
    [Module.Flat (Blowup I a) (TensorProduct R (Blowup I a) M)]
    [Module.FinitePresentation (Blowup I a) (TensorProduct R (Blowup I a) M)] :
    Module.FinitePresentation (Blowup I a) (strictTransform I a M) :=
  Module.FinitePresentation.of_equiv (strictTransform.linearEquivBaseChange I a M).symm

end strictTransform

/-! ### Base change of a finite presentation -/

namespace Stacks.Flatness.BlowupFlattening

section Presentation

variable (S : Type u) [CommRing S] (T : Type v) [CommRing T] [Algebra S T]

/-- **The base change of the free module of rank `r`**: apply `algebraMap S T` componentwise to
an `r`-tuple over `S`. -/
def freeBaseChange (r : ℕ) : (Fin r → S) →ₗ[S] (Fin r → T) :=
  (Algebra.linearMap S T).compLeft (Fin r)

/-- The `i`-th component of `freeBaseChange S T r v` is `algebraMap S T (v i)`. -/
@[simp]
theorem freeBaseChange_apply {r : ℕ} (v : Fin r → S) (i : Fin r) :
    freeBaseChange S T r v i = algebraMap S T (v i) :=
  rfl

/-- Componentwise application of `algebraMap S T` exhibits `Tʳ` as the base change of `Sʳ`; this
is `IsBaseChange.finitePow` applied to `IsBaseChange.linearMap`. -/
theorem isBaseChange_freeBaseChange (r : ℕ) : IsBaseChange T (freeBaseChange S T r) :=
  IsBaseChange.finitePow (Fin r) (IsBaseChange.linearMap S T)

/-- **The relation submodule of the base-changed presentation**: the `T`-span inside `Tʳ` of the
images of the relation vectors `k₁, …, k_t ∈ Sʳ`. -/
noncomputable def relSubmodule {r t : ℕ} (k : Fin t → (Fin r → S)) : Submodule T (Fin r → T) :=
  Submodule.span T (Set.range fun j => freeBaseChange S T r (k j))

variable {S T}

/-- The relation submodule of the base-changed presentation is the `T`-span of the image of the
whole kernel, not merely of the chosen generators: spans commute with the base change of the
generating family. -/
theorem relSubmodule_eq_span_image {M : Type w} [AddCommGroup M] [Module S M] {r t : ℕ}
    {π : (Fin r → S) →ₗ[S] M} (k : Fin t → (Fin r → S))
    (hk : LinearMap.ker π = Submodule.span S (Set.range k)) :
    relSubmodule S T k =
      Submodule.span T (freeBaseChange S T r '' (LinearMap.ker π : Set (Fin r → S))) := by
  rw [hk, ← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower S,
    ← Set.range_comp]
  rfl

variable {M : Type w} [AddCommGroup M] [Module S M] {r t : ℕ}
  {π : (Fin r → S) →ₗ[S] M} {k : Fin t → (Fin r → S)}
  (hk : LinearMap.ker π = Submodule.span S (Set.range k))

/-- **The comparison map of the presentations**: the map from `Sʳ / ker π` to
`Tʳ / relSubmodule S T k` induced by componentwise application of `algebraMap S T`. -/
noncomputable def quotComparison :
    ((Fin r → S) ⧸ LinearMap.ker π) →ₗ[S] ((Fin r → T) ⧸ relSubmodule S T k) :=
  Submodule.liftQ (LinearMap.ker π)
    (((relSubmodule S T k).mkQ.restrictScalars S).comp (freeBaseChange S T r)) <| by
      intro x hx
      have : freeBaseChange S T r x ∈ relSubmodule S T k := by
        rw [relSubmodule_eq_span_image (T := T) k hk]
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero (relSubmodule S T k)).mpr this

/-- The comparison map of the presentations sends the class of a tuple `v` over `S` to the class
of its componentwise image over `T`. -/
@[simp]
theorem quotComparison_mk (v : Fin r → S) :
    quotComparison (T := T) hk (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (freeBaseChange S T r v) :=
  rfl

/-- **The base-changed presentation is a base change.** The comparison map of the presentations
exhibits `Tʳ / relSubmodule S T k` as the base change of `Sʳ / ker π` along `S → T`.  This is
right exactness of the tensor product, in the form
`Stacks.QuasiregularSequence.FlatBaseChange.isBaseChange_of_quotient`; no flatness is needed. -/
theorem isBaseChange_quotComparison : IsBaseChange T (quotComparison (T := T) hk) :=
  Stacks.QuasiregularSequence.FlatBaseChange.isBaseChange_of_quotient (isBaseChange_freeBaseChange S
      T r) (LinearMap.ker π)
    (relSubmodule S T k) (relSubmodule_eq_span_image k hk) _ fun _ => rfl

variable {N : Type*} [AddCommGroup N] [Module S N] [Module T N] [IsScalarTower S T N]
  {bc : M →ₗ[S] N}

/-- **Base change of a finite presentation is the base-changed presentation.** Let `S` be a
commutative ring, `π : Sʳ → M` a surjection of `S`-modules whose kernel is spanned by finitely
many vectors `k₁, …, k_t`, and let `bc : M → N` exhibit `N` as the base change of `M` along a
commutative `S`-algebra `T`.  Then `N` is isomorphic, as a `T`-module, to `Tʳ` modulo the
`T`-span of the images of `k₁, …, k_t`.

The isomorphism is described on generators by
`Stacks.Flatness.BlowupFlattening.baseChangeQuotEquiv_apply`. -/
noncomputable def baseChangeQuotEquiv (hbc : IsBaseChange T bc)
    (hπ : Function.Surjective π) :
    N ≃ₗ[T] ((Fin r → T) ⧸ relSubmodule S T k) :=
  hbc.equiv.symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T)
      (π.quotKerEquivOfSurjective hπ).symm ≪≫ₗ
      (isBaseChange_quotComparison hk).equiv

/-- The identification of `Stacks.Flatness.BlowupFlattening.baseChangeQuotEquiv` carries the image
  of `π v` in the
base change to the class of the componentwise image of `v`; since the elements `bc (π v)`
generate `N` over `T`, this pins the isomorphism down. -/
@[simp]
theorem baseChangeQuotEquiv_apply (hbc : IsBaseChange T bc) (hπ : Function.Surjective π)
    (v : Fin r → S) :
    baseChangeQuotEquiv hk hbc hπ (bc (π v)) =
      Submodule.Quotient.mk (freeBaseChange S T r v) := by
  have hv : (π.quotKerEquivOfSurjective hπ).symm (π v) = Submodule.Quotient.mk v :=
    (LinearEquiv.symm_apply_eq _).mpr
      (π.quotKerEquivOfSurjective_apply_mk hπ v).symm
  rw [baseChangeQuotEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    hbc.equiv_symm_apply, TensorProduct.AlgebraTensorModule.congr_tmul, hv,
    LinearEquiv.refl_apply, IsBaseChange.equiv_tmul, one_smul, quotComparison_mk]

/-- **The base-changed presentation is of finite presentation**, being the quotient of a finite
free module by a submodule spanned by finitely many elements. -/
theorem finitePresentation_relSubmodule :
    Module.FinitePresentation T ((Fin r → T) ⧸ relSubmodule S T k) := by
  refine Module.finitePresentation_of_surjective (relSubmodule S T k).mkQ
    (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_span (Set.finite_range _)

include hk in
/-- **Base change preserves finite presentation**, in the explicit form given by
`Stacks.Flatness.BlowupFlattening.baseChangeQuotEquiv`: the base change `N` of a finitely presented
  `S`-module is a
finitely presented `T`-module. -/
theorem finitePresentation_of_baseChange (hbc : IsBaseChange T bc)
    (hπ : Function.Surjective π) : Module.FinitePresentation T N :=
  have : Module.FinitePresentation T ((Fin r → T) ⧸ relSubmodule S T k) :=
    finitePresentation_relSubmodule
  Module.FinitePresentation.of_equiv (baseChangeQuotEquiv hk hbc hπ).symm

/-- **Base change of a finite presentation is the base-changed presentation**, for the tensor
product itself.  This is `Stacks.Flatness.BlowupFlattening.baseChangeQuotEquiv` at the tautological
  base change
`TensorProduct.isBaseChange`: if `π : Sʳ → M` is a surjection of `S`-modules whose kernel is
spanned by `k₁, …, k_t`, then `T ⊗[S] M` is `Tʳ` modulo the `T`-span of the images of
`k₁, …, k_t`, for every commutative `S`-algebra `T`. -/
noncomputable def tensorQuotEquiv (hπ : Function.Surjective π) :
    T ⊗[S] M ≃ₗ[T] ((Fin r → T) ⧸ relSubmodule S T k) :=
  baseChangeQuotEquiv hk (TensorProduct.isBaseChange (R := S) (M := M) (S := T)) hπ

/-- The identification of `Stacks.Flatness.BlowupFlattening.tensorQuotEquiv` carries `1 ⊗ π v` to
  the class of the
componentwise image of `v`. -/
@[simp]
theorem tensorQuotEquiv_tmul (hπ : Function.Surjective π) (v : Fin r → S) :
    tensorQuotEquiv (T := T) hk hπ ((1 : T) ⊗ₜ[S] π v) =
      Submodule.Quotient.mk (freeBaseChange S T r v) :=
  baseChangeQuotEquiv_apply hk (TensorProduct.isBaseChange (R := S) (M := M) (S := T)) hπ v

end Presentation

end Stacks.Flatness.BlowupFlattening
