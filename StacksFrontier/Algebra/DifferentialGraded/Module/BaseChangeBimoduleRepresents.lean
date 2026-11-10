module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeRepresents

/-! # Base change over the target ring is computed by a K-flat module

Let `R` be a commutative ring, let `(A, d)` and `(C, d)` be differential graded `R`-algebras and
let `{}_A(A ⊗_R C)_C` be the base-change bimodule of Tag 0BZ4. This file records the form of
**Stacks 0BYZ, part (3)** for that bimodule — the right action taken over `C` rather than over
`A ⊗_R C` — which is the form the commuting square of part (2) is read in, since the square's
right-hand column is restriction of the action from `A ⊗_R R'` to `R'`.

It also records the K-flatness of the base ring in degree zero, which is the hypothesis part (3)
asks of the algebra when the algebra is the base ring: the complex underlying the regular module
of `degreeZero R S` is `S` in degree zero, bounded above and termwise flat.

## Main results

* `DifferentialGradedModule.kFlat_regularModule_degreeZero`: for `S` flat over `R`, the complex
  of `R`-modules underlying the regular module of `degreeZero R S` is K-flat.
* `DifferentialGraded.Bimodule.isIso_derivedTensorBimoduleCounit_app_of_kFlat`: **Stacks 0BYZ,
  part (3) for the bimodule of Tag 0BZ4**: if `A` and `M` are K-flat as complexes of `R`-modules,
  then the comparison of Tag 09LS from `M ⊗_A^𝐋 {}_A(A ⊗_R C)_C` to the ordinary tensor product
  is invertible at `M`.

## Implementation notes

The proof is that of `DifferentialGraded.Bimodule.isIso_derivedBaseChangeCounit_app_of_kFlat`
verbatim, with `DifferentialGraded.quasiIso_tensorCompFunctor_baseChangeBimodule_map_of_kFlat` in
place of its restriction-free companion: that lemma is already stated for the bimodule of
Tag 0BZ4, and part (3) as formalized transports it to `A ⊗_R R'` instead. Nothing is assumed of `C`;
in particular, for `C = degreeZero R R'` no flatness of `R'` enters.

For the K-flatness of the degree-zero algebra, `CochainComplex.KFlat.kFlat_of_flat` (Tag 064K)
asks for a bounded above complex of flat modules. The degree-`n` part of `degreeZero R S` is `⊤`
for `n = 0` and `⊥` otherwise, so the complex is strictly concentrated in degrees `≤ 0` and its
only nonzero term is `R`-linearly isomorphic to `S`.

## References

* [Stacks Project, Tag 0BYZ](https://stacks.math.columbia.edu/tag/0BYZ), part (3).
* [Stacks Project, Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4), the base-change
  bimodule.
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K), a bounded above complex
  of flat modules is K-flat.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

/-- **The base ring in degree zero is K-flat over the base ring.** For an `R`-algebra `S` flat
over `R`, the complex of `R`-modules underlying the regular right differential graded module over
`degreeZero R S` is `S` placed in degree zero, which is bounded above and termwise flat. -/
theorem kFlat_regularModule_degreeZero {R : Type u} [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] [Module.Flat R S] :
    CochainComplex.KFlat.{u, u} (regularModule (degreeZero R S)).toCochainComplex := by
  set K := (regularModule (degreeZero R S)).toCochainComplex with hK
  have hLE : K.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    refine ModuleCat.isZero_iff_subsingleton.mpr ?_
    change Subsingleton (degreeZeroGrading R S i)
    rw [degreeZeroGrading_eq_bot R S (by omega)]
    infer_instance
  have hflat (i : ℤ) : Module.Flat R (K.X i) := by
    change Module.Flat R (degreeZeroGrading R S i)
    by_cases hi : i = 0
    · subst hi
      rw [degreeZeroGrading_zero R S]
      exact Module.Flat.of_linearEquiv (Submodule.topEquiv : (⊤ : Submodule R S) ≃ₗ[R] S)
    · rw [degreeZeroGrading_eq_bot R S hi]
      infer_instance
  exact CochainComplex.KFlat.kFlat_of_flat K 0

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A C : DifferentialGradedAlgebra.{u, u} R)

/-- **Stacks 0BYZ, part (3) for the base-change bimodule of Tag 0BZ4.** Let `(A, d)` be a
differential graded `R`-algebra which is K-flat as a complex of `R`-modules and let `(C, d)` be a
differential graded `R`-algebra. For a differential graded `A`-module `M` which is K-flat as a
complex of `R`-modules, the ordinary tensor product `M ⊗_A {}_A(A ⊗_R C)_C` — which is `M ⊗_R C`
by `DifferentialGraded.absBalanceIso` — already computes the derived one: the comparison of
Tag 09LS is invertible at `M`.

This is `DifferentialGraded.Bimodule.isIso_derivedBaseChangeCounit_app_of_kFlat` with the right
action taken over `C` instead of over `A ⊗_R C`, which is the form in which the right-hand column
of the commuting square of part (2) reads it. Nothing is assumed of `C`. -/
theorem isIso_derivedTensorBimoduleCounit_app_of_kFlat
    (hA : CochainComplex.KFlat.{u, u} (regularModule A).toCochainComplex)
    (M : DifferentialGradedModule.{u, u, u} A)
    (hM : CochainComplex.KFlat.{u, u} M.toCochainComplex) :
    IsIso ((derivedTensorFunctorCounit (baseChangeBimodule A C)).app
      ((toHomotopyCategory A).obj M)) := by
  obtain ⟨P, f, hf, hFP⟩ := DifferentialGradedModule.exists_propertyP_resolution A M
  exact (isIso_derivedTensorFunctorCounit_app_iff_quasiIso_of_propertyP
    (baseChangeBimodule A C) f hf hFP).2
    (DifferentialGraded.quasiIso_tensorCompFunctor_baseChangeBimodule_map_of_kFlat A C f hf
      (DifferentialGradedModule.kFlat_toCochainComplex_of_propertyPFiltration hA hFP.some) hM)

end DifferentialGraded.Bimodule

end
