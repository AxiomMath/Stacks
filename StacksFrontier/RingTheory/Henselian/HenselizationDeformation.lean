module

public import Mathlib.RingTheory.Smooth.Locus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion.ScalarExtension
public import StacksFrontier.Deformation.SquareZero.ConormalTorsion
public import StacksFrontier.RingTheory.Henselian.HenselizationExtBaseChange
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization

/-!
# Deformations of henselizations

Let `k` be a field, let `B` be a finite type `k`-algebra, let `J ⊆ B` be an ideal such that
`Spec(B) → Spec(k)` is smooth on the complement of `V(J)`, and let `N` be a `B`-module.
Writing `(Bʰ, Jʰ)` for the henselization of the pair `(B, J)` and `Nʰ = Bʰ ⊗_B N`, the
square-zero extensions of `B` by `N` and those of `Bʰ` by `Nʰ` are in canonical bijection.

The bijection is the one induced on `Ext¹_B(NL_{B/k}, N)` by extension of scalars along
`B → Bʰ`. Smoothness away from `V(J)` makes that `Ext` group `J`-power torsion, and `B → Bʰ`
is flat and induces an isomorphism `B/Jⁿ ≅ Bʰ/JⁿBʰ` for every `n`, so scalar extension along
it does not change a `J`-power torsion module.

## Main results

* `Stacks.Deformation.exists_squareZeroAlgebraExtensionClassesHenselizationEquiv`:
  **Stacks 0DZC**, the canonical bijection between the isomorphism classes of square-zero
  extensions of `B` by `N` and those of `Bʰ` by `Nʰ`.

## Implementation notes

The source's `Exal` sets are the isomorphism classes of
`Stacks.Deformation.algebraExtensionProblem`, identified with `Ext¹_B(NL_{B/k}, N)` by
Stacks 0GPT; the conormal-functional model `Stacks.Deformation.extOneCokernel` is used for
that `Ext` group, because it is literally a `B`-module. Smoothness on the complement of
`V(J)` is expressed as the containment of the non-smooth locus in `V(J)` through Mathlib's
`Algebra.IsSmoothAt`, which lets `k` and `B` live in independent universes, and the pair
`(Bʰ, Jʰ)` is described by the henselian-pair condition together with its universal property
rather than by a chosen model.

Both inputs of the source's proof are proved, so nothing is assumed. The base change
isomorphism `Ext¹_{Bʰ}(NL_{Bʰ/k}, Nʰ) ≅ Ext¹_B(NL_{B/k}, N) ⊗_B Bʰ` is
`Stacks.Deformation.extOneCokernelHenselizationFlatBaseChangeEquiv`: Stacks 0D08 — the
invertibility of the comparison `NL_{B/k} ⊗_B Bʰ ⟶ NL_{Bʰ/k}`, which is
`Algebra.naiveCotangentComplex_quasiIso_henselizationPair` — replaces `NL_{Bʰ/k}` by
`NL_{B/k} ⊗_B Bʰ`, Stacks 0GPY moves the base change from the complex onto the coefficients, and
flat base change of the conormal cokernel moves it back out, `Bʰ` being flat over `B`.

The other input, that `Ext¹_B(NL_{B/k}, N)` is `J`-power torsion, is
`Deformation.Examples.exists_pow_smul_eq_zero_extOneCokernel`, Stacks 00S1 read on `Ext¹`:
the conormal differential of a finite presentation of `B` splits after inverting any element
outside the non-smooth locus, so smoothness away from `V(J)` puts a power of `J` in the
splitting ideal, and a scalar there annihilates the conormal cokernel with any coefficients.
That is the only use the smoothness hypothesis is put to.

The finiteness assumption that the source places on `N` is not needed: the argument applies
to every `B`-module, so the statement proved here is more general than the source's.

## References

* [Stacks Project, Tag 0DZC](https://stacks.math.columbia.edu/tag/0DZC)
-/

@[expose] public section

universe uk uB uN

namespace Stacks.Deformation

open scoped TensorProduct

/-- **Stacks 0DZC.** Let `k` be a field, `B` a finite type `k`-algebra and `J ⊆ B` an ideal
containing the non-smooth locus of `B` over `k` in its vanishing locus, and let `(Bʰ, Jʰ)` be
the henselization of the pair `(B, J)`. For a `B`-module `N` with `Nʰ = Bʰ ⊗_B N` there is a
bijection between the isomorphism classes of square-zero extensions of `B` by `N` and those of
`Bʰ` by `Nʰ`, namely the one inducing extension of scalars along `B → Bʰ` on the groups
`Ext¹_B(NL_{B/k}, N)` and `Ext¹_{Bʰ}(NL_{Bʰ/k}, Nʰ)` that classify those classes. -/
@[stacks 0DZC]
public theorem exists_squareZeroAlgebraExtensionClassesHenselizationEquiv
    (k : Type uk) [Field k] (B : Type uB) [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B]
    (J : Ideal B)
    (hsmooth : ∀ q : PrimeSpectrum B, ¬ Algebra.IsSmoothAt k q.asIdeal → J ≤ q.asIdeal)
    (N : Type uN) [AddCommGroup N] [Module B N]
    (Bh : Type uB) [CommRing Bh] [Algebra B Bh] [Algebra k Bh] [IsScalarTower k B Bh]
    (hhens : HenselianPair Bh (J.map (algebraMap B Bh)))
    (huniv : ∀ (C : Type uB) (_ : CommRing C) (JC : Ideal C), HenselianPair C JC →
      ∀ f : B →+* C, J ≤ JC.comap f →
        ∃! g : Bh →+* C, g.comp (algebraMap B Bh) = f ∧
          J.map (algebraMap B Bh) ≤ JC.comap g) :
    ∃ e : SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB, uN,
          max uB uN} (algebraExtensionProblem k B N) ≃
        SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB,
          max uB uN, max uB uN} (algebraExtensionProblem k Bh (Bh ⊗[B] N)),
      ∀ x, extOneCokernelHenselizationFlatBaseChangeEquiv.{uk, uB, uN} k B N Bh J hhens huniv
              (extCokernelIso k Bh (Bh ⊗[B] N)
                (squareZeroAlgebraExtensionClassesEquivExtOne k Bh (Bh ⊗[B] N) (e x)))
            = extCokernelIso k B N (squareZeroAlgebraExtensionClassesEquivExtOne k B N x)
                ⊗ₜ[B] (1 : Bh) := by
  set hExtBaseChange :=
    extOneCokernelHenselizationFlatBaseChangeEquiv.{uk, uB, uN} k B N Bh J hhens huniv
  obtain ⟨n, hn⟩ := Deformation.Examples.exists_pow_smul_eq_zero_extOneCokernel k B J
    (fun q hq ↦ by_contra fun hs ↦ hq (hsmooth q hs)) N
  have htors : ∀ x : extOneCokernel k B N, ∃ n : ℕ, ∀ r ∈ J ^ n, r • x = 0 :=
    fun x ↦ ⟨n, fun r hr ↦ hn r hr x⟩
  have hQ := (flat_henselization_and_bijective_quotientMap B J Bh hhens huniv).2
  have hbij : Function.Bijective
      (fun m : extOneCokernel k B N ↦
        TensorProduct.mk B (extOneCokernel k B N) Bh m (1 : Bh)) :=
    (tensorProduct_mk_bijective_of_ideal_power_torsion B J (extOneCokernel k B N) htors).1
      Bh (fun n _ ↦ hQ n)
  refine ⟨((squareZeroAlgebraExtensionClassesEquivExtOne k B N).trans
    ((extCokernelIso k B N).toEquiv.trans
      ((Equiv.ofBijective _ hbij).trans
        (hExtBaseChange.toEquiv.symm.trans
          ((extCokernelIso k Bh (Bh ⊗[B] N)).toEquiv.symm.trans
            (squareZeroAlgebraExtensionClassesEquivExtOne k Bh (Bh ⊗[B] N)).symm))))), ?_⟩
  intro x
  simp only [CategoryTheory.Functor.mapHomologicalComplex_obj_X,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d, Int.reduceNeg, AddEquiv.toEquiv_eq_coe,
    TensorProduct.mk_apply, Equiv.trans_apply, EquivLike.coe_coe, Equiv.ofBijective_apply,
    AddEquiv.coe_toEquiv_symm, Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end Stacks.Deformation

end
