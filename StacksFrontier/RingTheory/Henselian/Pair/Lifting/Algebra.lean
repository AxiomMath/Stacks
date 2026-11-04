module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.LiftSmoothMap
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

@[expose] public section

/-!
# Lifting smooth algebra maps along a henselian pair

For a henselian pair `(A, I)` and a smooth `R`-algebra `S`, every `R`-algebra map `S → A ⧸ I`
lifts to an `R`-algebra map `S → A`. The proof base changes `S` to the smooth `A`-algebra
`A ⊗[R] S`, uses the étale lift of a smooth algebra map to replace `A` by an étale `A`-algebra
`A'` with `A ⧸ I ≃ A' ⧸ IA'`, and then applies the henselian lifting criterion to the resulting
section `A' → A ⧸ I`.

## Main results

* `exists_lift_of_smooth_of_henselianPair`: an `R`-algebra map from a smooth `R`-algebra to
  `A ⧸ I` lifts to `A` when `(A, I)` is a henselian pair.

## References

* [Stacks: Tag 0H74](https://stacks.math.columbia.edu/tag/0H74)
-/

open scoped TensorProduct

universe u v w

/-- **Stacks 0H74.** Every map from a smooth algebra to the quotient of a henselian pair lifts
to the original ring. -/
@[stacks 0H74]
theorem exists_lift_of_smooth_of_henselianPair
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    [Algebra.Smooth R S] (I : Ideal A) (hI : HenselianPair A I)
    (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := by
  let B := TensorProduct R A S
  let g : B →ₐ[A] A ⧸ I := Algebra.TensorProduct.lift
    (Algebra.ofId A (A ⧸ I)) f (fun _ _ ↦ Commute.all _ _)
  let _ : Algebra.Smooth A B := Algebra.Smooth.baseChange R S A
  obtain ⟨A', instRing, instAlg, hEtale, hq, fB⟩ :=
    exists_etale_lift_of_smooth I g
  obtain ⟨fB, hfB⟩ := fB
  let J := I.map (algebraMap A A')
  let qₐ : (A ⧸ I) →ₐ[A] (A' ⧸ J) :=
    Ideal.quotientMapₐ J (Algebra.ofId A A') Ideal.le_comap_map
  have hqₐ : Function.Bijective qₐ := hq
  let e : (A ⧸ I) ≃ₐ[A] (A' ⧸ J) := AlgEquiv.ofBijective qₐ hqₐ
  let sigma : A' →ₐ[A] A ⧸ I := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A J)
  have hlift := ((henselianPair_tfae A I).out 1 2).mp hI
  obtain ⟨t, ht⟩ := hlift A' sigma
  let f' : S →ₐ[R] A :=
    ((t.comp fB).restrictScalars R).comp Algebra.TensorProduct.includeRight
  refine ⟨f', ?_⟩
  ext s
  show Ideal.Quotient.mk I (t (fB (1 ⊗ₜ[R] s))) = f s
  rw [show fB (1 ⊗ₜ[R] s) = fB (Algebra.TensorProduct.includeRight s) by rfl]
  have ht' := DFunLike.congr_fun ht (fB (Algebra.TensorProduct.includeRight s))
  change Ideal.Quotient.mk I (t (fB (Algebra.TensorProduct.includeRight s))) =
    sigma (fB (Algebra.TensorProduct.includeRight s)) at ht'
  show Ideal.Quotient.mk I (t (fB (Algebra.TensorProduct.includeRight s))) = f s
  rw [ht']
  show e.symm (Ideal.Quotient.mk J (fB (Algebra.TensorProduct.includeRight s))) = f s
  apply e.injective
  rw [e.apply_symm_apply]
  show Ideal.Quotient.mk J (fB (Algebra.TensorProduct.includeRight s)) = qₐ (f s)
  have hfBs := DFunLike.congr_fun hfB (Algebra.TensorProduct.includeRight s)
  have hg : g (Algebra.TensorProduct.includeRight s) = f s := by
    show (1 : A ⧸ I) * f s = f s
    simp
  rw [← hg]
  exact hfBs.symm

end
