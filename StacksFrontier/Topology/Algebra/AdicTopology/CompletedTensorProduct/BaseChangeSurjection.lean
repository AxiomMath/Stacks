module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Finite
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientSurjection

/-!
# The completed tensor product along a surjection is an ordinary base change

Let `π : R ↠ C` be a continuous open surjection of linearly topologized `A`-algebras and let
`B` be a third one.  If `B ⊗̂[A] R` is Noetherian and adic — which it is in the situation of
Tag 0GGR, by Tag 0GB4 — then

  `B ⊗̂[A] C  ≃  (B ⊗̂[A] R) ⊗[R] (R ⧸ ker π)`,

an *uncompleted* tensor product over `R`.  This is the transitivity of the completed tensor
product that the third paragraph of Tag 0GGR needs, in the only case it needs: the second
factor is a quotient of the base, hence a cyclic module, so no completion is required on the
right-hand side and the ordinary base change for flatness
(`Rig.flat_atPrime_tensorProduct_of_flat`) applies to it directly.

The three steps are: `B ⊗̂[A] C` is the quotient of `B ⊗̂[A] R` by the closure of the extension
of `ker (id ⊗ π)` (`TopologicalRing.exists_completedTensorProductQuotientRingEquiv`); that
ideal is the extension of `ker π` and the closure is redundant
(`TopologicalRing.ker_tensorProduct_map_of_surjective` and
`Ideal.closure_eq_of_isAdic_of_isNoetherianRing`); and a quotient of a ring by the extension of
an ideal of its base is the base change along the quotient of the base (Mathlib's
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`).

## Main results

* `TopologicalRing.exists_ringEquiv_tensorProduct_completedTensorProduct`: the isomorphism,
  together with its compatibility with the structure maps out of `R ⧸ ker π` and `C`.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
-/

@[expose] public section

namespace TopologicalRing

section

universe u

open UniformSpace
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
  [Algebra A B] [Algebra A R] [Algebra A C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- **`B ⊗̂[A] C` is the ordinary base change of `B ⊗̂[A] R` along `R ↠ C`.**  For a continuous
open surjection `π : R ↠ C` of linearly topologized `A`-algebras with `B ⊗̂[A] R` Noetherian and
adic,

  `(B ⊗̂[A] R) ⊗[R] (R ⧸ ker π)  ≃  B ⊗̂[A] C`,

and the isomorphism carries the class of `r` on the left to the image of `π r` on the right.
This is the transitivity of the completed tensor product used by the third paragraph of
Tag 0GGR, specialised to a second factor that is a quotient of the base — where the tensor
product on the left needs no completion. -/
public theorem exists_ringEquiv_tensorProduct_completedTensorProduct
    (π : R →ₐ[A] C) (hsurj : Function.Surjective π) (hcont : Continuous π) (hopen : IsOpenMap π)
    (I : Ideal A) (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (hK : _root_.IsAdic (I.map (algebraMap A R)))
    [IsNoetherianRing (CompletedTensorProduct (R := A) (M := B) (N := R))]
    (hB' : ∃ 𝔦 : Ideal (CompletedTensorProduct (R := A) (M := B) (N := R)), _root_.IsAdic 𝔦) :
    ∃ e : (CompletedTensorProduct (R := A) (M := B) (N := R)) ⊗[R]
            (R ⧸ RingHom.ker (π : R →+* C)) ≃+*
          CompletedTensorProduct (R := A) (M := B) (N := C),
      ∀ r : R,
        e (algebraMap (R ⧸ RingHom.ker (π : R →+* C))
            ((CompletedTensorProduct (R := A) (M := B) (N := R)) ⊗[R]
              (R ⧸ RingHom.ker (π : R →+* C)))
            (Ideal.Quotient.mk (RingHom.ker (π : R →+* C)) r)) =
          algebraMap C (CompletedTensorProduct (R := A) (M := B) (N := C)) (π r) := by
  classical
  set B' := CompletedTensorProduct (R := A) (M := B) (N := R) with hB'def
  set K : Ideal R := RingHom.ker (π : R →+* C) with hKdef
  have : T2Space B' := by
    set_option synthInstance.maxHeartbeats 200000 in infer_instance
  let : TopologicalSpace (B ⊗[A] R) := tensorProductTopology (R := A) (M := B) (N := R)
  let : UniformSpace (B ⊗[A] R) := tensorProductUniformSpace (R := A) (M := B) (N := R)
  have hcount : (nhds (0 : B ⊗[A] R)).IsCountablyGenerated :=
    isCountablyGenerated_nhds_zero_of_isAdic (isAdic_tensorProduct_map_algebraMap I hJ hK)
  obtain ⟨E, hE⟩ :=
    exists_completedTensorProductQuotientRingEquiv (B := B) π hsurj hcont hopen hcount
  obtain ⟨𝔦, h𝔦⟩ := hB'
  have hcoe : (Completion.coeRingHom : (B ⊗[A] R) →+* B').comp
      (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom =
      algebraMap R B' := rfl
  -- the ideal of the quotient presentation is the extension of `ker π`, closure and all
  have hideal : Ideal.closure
        ((RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A B) π).toRingHom).map
          (Completion.coeRingHom : (B ⊗[A] R) →+* B')) =
      K.map (algebraMap R B') := by
    rw [ker_tensorProduct_map_of_surjective (B := B) π hsurj, Ideal.map_map, hcoe]
    exact Ideal.closure_eq_of_isAdic_of_isNoetherianRing h𝔦 _
  -- the quotient of `B ⊗̂[A] R` by `(ker π) · (B ⊗̂[A] R)` is `B ⊗̂[A] C`
  set E' : (B' ⧸ K.map (algebraMap R B')) ≃+*
      CompletedTensorProduct (R := A) (M := B) (N := C) :=
    (Ideal.quotEquivOfEq hideal.symm).trans E with hE'def
  -- and that quotient is the base change of `B ⊗̂[A] R` along `R ↠ R ⧸ ker π`
  refine ⟨(Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (A := R) B' K).symm.toRingEquiv.trans E', fun r => ?_⟩
  have h₁ : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R) B' K).symm
      (algebraMap (R ⧸ K) (B' ⊗[R] (R ⧸ K)) (Ideal.Quotient.mk K r)) =
      Ideal.Quotient.mk (K.map (algebraMap R B')) (algebraMap R B' r) := by
    change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R) B' K).symm
        ((1 : B') ⊗ₜ[R] (Ideal.Quotient.mk K r)) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
      ← Algebra.algebraMap_eq_smul_one]
    rfl
  have h₂ : E' (Ideal.Quotient.mk (K.map (algebraMap R B')) (algebraMap R B' r)) =
      algebraMap C (CompletedTensorProduct (R := A) (M := B) (N := C)) (π r) := by
    rw [hE'def, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact hE ((1 : B) ⊗ₜ[A] r)
  rw [RingEquiv.trans_apply]
  change E' ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R) B' K).symm _) = _
  rw [h₁, h₂]

end

end TopologicalRing

end
