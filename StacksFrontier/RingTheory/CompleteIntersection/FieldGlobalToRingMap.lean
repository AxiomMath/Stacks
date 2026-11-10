module

public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksFrontier.RingTheory.RingHom.FinitePresentation

/-!
# From a global complete intersection over a field to a local complete intersection ring map

A global complete intersection over a field `k` (Definition 00S9 (1), in the spelling
`IsGlobalCompleteIntersectionOver` of Section 10.136) is a `k`-algebra `C` presented as
`C = k[x_1, …, x_n]/(f_1, …, f_c)` with `dim C + c = n`. A relative global complete intersection
(Definition 00SP) is a ring map `R → S` with a presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)`
all of whose nonempty fibres have dimension `n - c`. A local complete intersection ring map
(Definition 07D0) is a ring map of finite type one of whose polynomial presentations has
Koszul-regular kernel.

Over a field the first notion is a special case of the second, and the second implies the third.

## Main results

* `Algebra.IsRelativeGlobalCompleteIntersection.of_isGlobalCompleteIntersectionOver`: a global
  complete intersection over a field `k` is a relative global complete intersection over `k`.
* `RingHom.IsLocalCompleteIntersection.of_isRelativeGlobalCompleteIntersection`: the structure map
  of a relative global complete intersection is a local complete intersection ring map.

## References

* [Stacks 00S9](https://stacks.math.columbia.edu/tag/00S9), Definition 10.135.1
* [Stacks 00SP](https://stacks.math.columbia.edu/tag/00SP), Definition 10.136.5
* [Stacks 07D0](https://stacks.math.columbia.edu/tag/07D0), Definition 10.137.1
* [Stacks 07D2](https://stacks.math.columbia.edu/tag/07D2), Lemma 10.137.3
-/

@[expose] public section

open MvPolynomial

/-! ### Packaging a surjection with prescribed kernel as a presentation -/

/-- The presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)` attached to a surjective `R`-algebra map
`π : R[x_1, …, x_n] → S` whose kernel is spanned by `f_1, …, f_c`. The generators are the images
`π(x_i)` of the variables. -/
private noncomputable def presentationOfKerEqSpanRange {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {n c : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S)
    (f : Fin c → MvPolynomial (Fin n) R) (hπ : Function.Surjective π)
    (hker : RingHom.ker π.toRingHom = Ideal.span (Set.range f)) :
    Algebra.Presentation R S (Fin n) (Fin c) where
  __ := Algebra.Generators.ofSurjective (fun i ↦ π (X i)) (by convert! hπ; ext; simp)
  relation := f
  span_range_relation_eq_ker := hker.symm.trans (by congr; ext; simp)

/-! ### The fibres of an algebra over a field -/

/-- The isomorphism `κ(p) ⊗_k C ≃ C` between the fibre of a `k`-algebra `C` at a prime `p` of a
field `k` and `C` itself. -/
noncomputable def fiberAlgEquivOfField' {k : Type*} [Field k] (C : Type*) [CommRing C]
    [Algebra k C] (p : Ideal k) [p.IsPrime] : p.Fiber C ≃ₐ[k] C :=
  (Algebra.TensorProduct.congr (S := k) p.algEquivResidueFieldOfField.symm
    (AlgEquiv.refl (R := k) (A₁ := C))).trans (Algebra.TensorProduct.lid k C)

/-- Over a field, every fibre has the Krull dimension of the algebra itself. -/
private theorem ringKrullDim_fiber_eq_of_field {k : Type*} [Field k] (C : Type*) [CommRing C]
    [Algebra k C] (p : Ideal k) [p.IsPrime] : ringKrullDim (p.Fiber C) = ringKrullDim C :=
  ringKrullDim_eq_of_ringEquiv (fiberAlgEquivOfField' C p).toRingEquiv

/-! ### A global complete intersection over a field is a relative one -/

/-- A global complete intersection over a field `k` (Definition 00S9 (1)) is a relative global
complete intersection over `k` (Definition 00SP). -/
theorem Algebra.IsRelativeGlobalCompleteIntersection.of_isGlobalCompleteIntersectionOver
    (k : Type*) [Field k] (C : Type*) [CommRing C] [Algebra k C]
    (h : IsGlobalCompleteIntersectionOver k C) :
    Algebra.IsRelativeGlobalCompleteIntersection k C := by
  rcases h with hsub | ⟨n, c, π, f, hπ, hker, hdim⟩
  · have hker : RingHom.ker (aeval (R := k) (fun _ : Fin 0 ↦ (0 : C))).toRingHom =
        Ideal.span (Set.range (fun _ : Fin 1 ↦ (1 : MvPolynomial (Fin 0) k))) := by
      rw [Set.range_const, Ideal.span_singleton_one]
      exact (Ideal.eq_top_iff_one _).mpr (RingHom.mem_ker.mpr (Subsingleton.elim _ _))
    have hP : (presentationOfKerEqSpanRange (aeval (R := k) (fun _ : Fin 0 ↦ (0 : C)))
        (fun _ : Fin 1 ↦ (1 : MvPolynomial (Fin 0) k))
        (fun x ↦ ⟨0, Subsingleton.elim _ _⟩) hker).IsRelativeGlobalCompleteIntersection :=
      ⟨fun p _ hnt ↦ absurd (fiberAlgEquivOfField' C p).toEquiv.subsingleton
        (not_subsingleton_iff_nontrivial.mpr hnt)⟩
    exact Algebra.IsRelativeGlobalCompleteIntersection.of_presentation _ (hP := hP)
  · have hP : (presentationOfKerEqSpanRange π f hπ hker).IsRelativeGlobalCompleteIntersection := by
      refine ⟨fun p _ _ ↦ ?_⟩
      rwa [ringKrullDim_fiber_eq_of_field C p, Nat.card_eq_fintype_card,
        Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin]
    exact Algebra.IsRelativeGlobalCompleteIntersection.of_presentation _ (hP := hP)

/-! ### A relative global complete intersection is a local complete intersection ring map -/

/-- An ideal spanned by a Koszul-regular sequence is a Koszul-regular ideal.
Alias of `RingHom.isKoszulRegularIdeal_span`. -/
alias isKoszulRegularIdeal_span_range := RingHom.isKoszulRegularIdeal_span

/-- The structure map `A → S` of a relative global complete intersection (Definition 00SP) is a
local complete intersection ring map (Definition 07D0). -/
theorem RingHom.IsLocalCompleteIntersection.of_isRelativeGlobalCompleteIntersection
    {A : Type*} {S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.IsRelativeGlobalCompleteIntersection A S] :
    RingHom.IsLocalCompleteIntersection (algebraMap A S) := by
  obtain ⟨n, c, P, hP⟩ := ‹Algebra.IsRelativeGlobalCompleteIntersection A S›.out
  have : Algebra.FinitePresentation A S := P.finitePresentation_of_isFinite
  rw [RingHom.IsLocalCompleteIntersection, _root_.toAlgebra_algebraMap]
  refine ⟨RingHom.finiteType_algebraMap.mpr inferInstance, n, aeval P.val,
    P.aeval_val_surjective, ?_⟩
  change Ideal.IsKoszulRegular (RingHom.ker (aeval (R := A) P.val))
  rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
  exact isKoszulRegularIdeal_span_range P.relation
    (RingHom.isKoszulRegular_relation_of_isRelativeGlobalCompleteIntersection P hP)

end
