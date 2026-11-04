module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Flat

/-!
# Descent of invertibility along an adic completion

Let `R` be a Noetherian ring, `I ⊆ R` an ideal contained in the Jacobson radical and `M` a
finite `R`-module. This file shows that invertibility of the `I`-adic completion `M^∧` as a
module over `R^∧` descends to invertibility of `M` over `R`.

The two inputs are already available: the completion map `R → R^∧` is faithfully flat
(`AdicCompletion.faithfullyFlat_of_le_ringJacobson`), and for a finite module over a Noetherian
ring the completion `M^∧` is the base change `R^∧ ⊗_R M`
(`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`); invertibility descends
along a faithfully flat ring map by `Module.Invertible.of_isBaseChange_of_faithfullyFlat`.

For a Noetherian local ring the hypothesis on `I` is automatic for `I = 𝔪`, and the conclusion
can be read as freeness of rank one, since the Picard group of a local ring is trivial.

## Main results

* `AdicCompletion.isBaseChange_of` — for a finite module over a Noetherian ring the completion
  map `M → M^∧` exhibits `M^∧` as the base change of `M` along `R → R^∧`.
* `Module.Invertible.of_adicCompletion` — invertibility of `M^∧` over `R^∧` implies
  invertibility of `M` over `R`.
* `Module.Invertible.of_nonempty_linearEquiv_adicCompletion` — the same with the hypothesis in
  the form `M^∧ ≅ R^∧`.
* `Module.Invertible.of_maximalIdeal_adicCompletion` and
  `Module.Invertible.nonempty_linearEquiv_of_maximalIdeal_adicCompletion` — the local case, the
  second concluding `M ≅ R`.

## References

* [Stacks Project, Tag 00MC](https://stacks.math.columbia.edu/tag/00MC)
* [Stacks Project, Tag 058S](https://stacks.math.columbia.edu/tag/058S)
-/

@[expose] public noncomputable section

open TensorProduct

universe u

/-- For a finite module `M` over a Noetherian ring `R` the completion map `M → M^∧` exhibits
the `R^∧`-module `M^∧` as the base change of `M` along `R → R^∧`. -/
theorem AdicCompletion.isBaseChange_of {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsBaseChange (AdicCompletion I R) (AdicCompletion.of I M) :=
  IsBaseChange.of_equiv (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M) fun x => by
    rw [AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
      AdicCompletion.ofTensorProduct_tmul, one_smul]

/-- **Invertibility descends along an adic completion.** Let `I` be an ideal of a Noetherian
ring `R` contained in the Jacobson radical and let `M` be a finite `R`-module. If the `I`-adic
completion `M^∧` is an invertible `R^∧`-module, then `M` is an invertible `R`-module. -/
theorem Module.Invertible.of_adicCompletion {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Invertible (AdicCompletion I R) (AdicCompletion I M)] :
    Module.Invertible R M :=
  let := AdicCompletion.faithfullyFlat_of_le_ringJacobson I hI
  Module.Invertible.of_isBaseChange_of_faithfullyFlat (AdicCompletion.of I M)
    (AdicCompletion.isBaseChange_of I M)

/-- A finite module over a Noetherian ring whose adic completion along an ideal inside the
Jacobson radical is free of rank one is an invertible module. -/
theorem Module.Invertible.of_nonempty_linearEquiv_adicCompletion {R : Type u} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R) (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M]
    (hM : Nonempty (AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicCompletion I R)) :
    Module.Invertible R M :=
  let := AdicCompletion.faithfullyFlat_of_le_ringJacobson I hI
  Module.Invertible.of_trivial_baseChange_of_faithfullyFlat (AdicCompletion.of I M)
    (AdicCompletion.isBaseChange_of I M) hM

/-- The local case of descent of invertibility along completion: for a Noetherian local ring the
maximal ideal lies in the Jacobson radical, so invertibility of the `𝔪`-adic completion of a
finite module descends. -/
theorem Module.Invertible.of_maximalIdeal_adicCompletion {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    [Module.Invertible (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (AdicCompletion (IsLocalRing.maximalIdeal R) M)] :
    Module.Invertible R M :=
  Module.Invertible.of_adicCompletion (IsLocalRing.maximalIdeal R)
    (IsLocalRing.ringJacobson_eq_maximalIdeal R).ge M

/-- Over a Noetherian local ring a finite module with invertible completion is free of rank one.
This is the step of Tag 0EHE which turns invertibility of the completed stalk of a coherent
module into invertibility, hence triviality, of the stalk itself. -/
theorem Module.Invertible.nonempty_linearEquiv_of_maximalIdeal_adicCompletion {R : Type u}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    [Module.Invertible (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (AdicCompletion (IsLocalRing.maximalIdeal R) M)] :
    Nonempty (M ≃ₗ[R] R) :=
  let : Module.Invertible R M := Module.Invertible.of_maximalIdeal_adicCompletion M
  Module.Invertible.free_iff_linearEquiv.mp (inferInstanceAs (Module.Free R M))

end
