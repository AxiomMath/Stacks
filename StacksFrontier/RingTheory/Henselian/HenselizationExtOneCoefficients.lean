module

public import StacksFrontier.Algebra.Module.IPowerTorsion.ScalarExtension
public import StacksFrontier.Deformation.SquareZero.ConormalCokernelBaseChange
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization

/-!
# The coefficient comparison of Stacks 0DZD, in canonical form

Let `k` be a field, let `B` be a finite type `k`-algebra which is smooth over `k` outside the
zero set of an ideal `J ⊆ B`, let `(Bʰ, Jʰ)` be the henselization of the pair `(B, J)` and let
`N` be a `B`-module.  This file proves that the map

`Ext¹_B(NL_{B/k}, N) ⟶ Ext¹_B(NL_{B/k}, Bʰ ⊗_B N)`

*induced by the coefficient map* `n ↦ 1 ⊗ n` is bijective.

This is the henselization analogue of the first half of Stacks 0DZ4,
`Deformation.Examples.bijective_naiveCotangentExtOneMap_adicCompletion`, and it is the form in
which Stacks 0DZD needs it: the tangent-space conclusion of Stacks 0DZD compares the two
tangent spaces through the maps *induced* by the functor of Stacks 0DYT, so the comparison has
to be the canonical map `Stacks.Deformation.naiveCotangentExtOneMap` and not merely some
bijection between the two groups.  The bijection of Stacks 0DZC,
`Stacks.Deformation.exists_squareZeroAlgebraExtensionClassesHenselizationEquiv`, is built from
the scalar extension `m ↦ m ⊗ 1` of the `Ext` group and is not of that form.

## Main results

* `Deformation.Examples.bijective_naiveCotangentExtOneMap_tensorBaseChange`: the coefficient
  comparison is bijective for any flat `B`-algebra inducing an isomorphism `B/Jⁿ ≅ Bʰ/JⁿBʰ`.
* `Deformation.Examples.bijective_naiveCotangentExtOneMap_henselization`: the same for the
  henselization of the pair `(B, J)`, described by the henselian-pair condition together with
  its universal property.

## Implementation notes

The argument is the one Stacks 0DZC runs, read on the canonical map.  `Ext¹_B(NL_{B/k}, N)` is
annihilated by a power of `J` (Stacks 00S1, in the form
`Deformation.Examples.exists_pow_le_conormalSplittingIdeal`), and `B → Bʰ` is flat and an
isomorphism modulo every power of `J`, so the scalar extension `m ↦ m ⊗ 1` of a `J`-power
torsion module is bijective.  What converts that into a statement about the canonical
coefficient map is `Deformation.Examples.homCokernelBaseChangeEquiv_compRight`: the flat
base-change comparison of the conormal cokernel carries the class of `(1 ⊗ -) ∘ δ` to
`1 ⊗ [δ]`, so postcomposition with `n ↦ 1 ⊗ n` *is* the scalar extension read through that
comparison.

Both the splitting of the conormal differential and the base-change comparison need a *finite*
presentation of `B`, whose conormal module is finite and whose cotangent space is finite
projective; the canonical presentation `Algebra.Generators.self` has neither.  So the whole
argument is run at `Algebra.Presentation.ofFinitePresentation` and moved to the canonical
presentation at the end, by `Deformation.Examples.bijective_conormalCokernelPushAt_iff`.

## References

* [Stacks Project, Tag 0DZD](https://stacks.math.columbia.edu/tag/0DZD)
* [Stacks Project, Tag 0DZ4](https://stacks.math.columbia.edu/tag/0DZ4)
* [Stacks Project, Tag 0DZC](https://stacks.math.columbia.edu/tag/0DZC)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public section

open scoped TensorProduct

universe uk uB uN

namespace Deformation.Examples

open Stacks.Deformation

noncomputable section

variable (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B]
  (N : Type uN) [AddCommGroup N] [Module B N]
  (Bh : Type uB) [CommRing Bh] [Algebra B Bh]

/-- **The coefficient comparison `Ext¹_B(NL_{B/k}, N) → Ext¹_B(NL_{B/k}, Bʰ ⊗_B N)` is
bijective.**  For a finite type algebra `B` over a field `k` which is smooth over `k` outside the
zero set of `J`, and a flat `B`-algebra `Bʰ` with `B/Jⁿ ≅ Bʰ/JⁿBʰ` for every `n`, the map on
first extension groups induced by the coefficient map `n ↦ 1 ⊗ n` is bijective.

The group is `J`-power torsion, so its scalar extension along `B → Bʰ` is bijective, and the
induced map on coefficients is that scalar extension read through the flat base-change
comparison of the conormal cokernel. -/
public theorem bijective_naiveCotangentExtOneMap_tensorBaseChange
    (J : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (hflat : Module.Flat B Bh)
    (hquot : ∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap (Ideal.map (algebraMap B Bh) (J ^ n))
        (algebraMap B Bh) Ideal.le_comap_map)) :
    Function.Bijective (naiveCotangentExtOneMap k B (TensorProduct.mk B Bh N 1)) := by
  have := hflat
  let : Algebra.FinitePresentation k B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let P₀ := Algebra.Presentation.ofFinitePresentation k B
  let Q := P₀.reindex (Equiv.ulift.{uB}) (Equiv.refl _)
  let : Module.Finite B Q.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite Q.fg_ker
  let : Module.FinitePresentation B Q.toExtension.Cotangent :=
    Module.finitePresentation_of_finite B Q.toExtension.Cotangent
  let : Module.Finite B Q.toExtension.CotangentSpace :=
    Module.Finite.of_basis Q.toGenerators.cotangentSpaceBasis
  let : Module.FinitePresentation B Q.toExtension.CotangentSpace :=
    Module.finitePresentation_of_projective B Q.toExtension.CotangentSpace
  let : Algebra.FormallySmooth k Q.toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth k (MvPolynomial _ k))
  have hsurj := Submodule.mkQ_surjective
    (LinearMap.range (LinearMap.lcomp B N Q.toExtension.cotangentComplex))
  -- a power of `J` annihilates the conormal cokernel of the finite presentation
  obtain ⟨n, hn⟩ := exists_pow_le_conormalSplittingIdeal Q.toExtension J hsm
  have htors : ∀ x : conormalCokernelAt Q.toExtension N, ∃ m : ℕ, ∀ r ∈ J ^ m, r • x = 0 := by
    refine fun x ↦ ⟨n, fun r hr ↦ ?_⟩
    obtain ⟨δ, hδ⟩ := hsurj x
    rw [← hδ, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact smul_mem_range_lcomp_of_mem_conormalSplittingIdeal Q.toExtension (hn hr) N δ
  -- hence the scalar extension of that cokernel along `B → Bʰ` is bijective
  have hmkb : Function.Bijective
      (fun x : conormalCokernelAt Q.toExtension N ↦
        TensorProduct.mk B (conormalCokernelAt Q.toExtension N) Bh x (1 : Bh)) :=
    (tensorProduct_mk_bijective_of_ideal_power_torsion B J
      (conormalCokernelAt Q.toExtension N) htors).1 Bh fun m _ ↦ hquot m
  have hone : Function.Bijective
      (fun x : conormalCokernelAt Q.toExtension N ↦ (1 : Bh) ⊗ₜ[B] x) :=
    (TensorProduct.comm B (conormalCokernelAt Q.toExtension N) Bh).bijective.comp hmkb
  -- the coefficient push at the finite presentation is that scalar extension
  have hQb : Function.Bijective
      (conormalCokernelPushAt Q.toExtension (TensorProduct.mk B Bh N 1)) := by
    have hkey : ∀ x, homCokernelBaseChangeEquiv Bh Q.toExtension.cotangentComplex
        (conormalCokernelPushAt Q.toExtension (TensorProduct.mk B Bh N 1) x)
          = (1 : Bh) ⊗ₜ[B] x := by
      intro x
      obtain ⟨δ, hδ⟩ := hsurj x
      rw [← hδ, Submodule.mkQ_apply, conormalCokernelPushAt_mk]
      exact homCokernelBaseChangeEquiv_compRight Bh Q.toExtension.cotangentComplex δ
    refine (Function.Bijective.of_comp_iff'
      (homCokernelBaseChangeEquiv Bh Q.toExtension.cotangentComplex (N := N)).bijective
      (conormalCokernelPushAt Q.toExtension (TensorProduct.mk B Bh N 1))).mp ?_
    have hcomp : ((homCokernelBaseChangeEquiv Bh Q.toExtension.cotangentComplex (N := N)) ∘
        (conormalCokernelPushAt Q.toExtension (TensorProduct.mk B Bh N 1)) : _ → _)
          = fun x ↦ (1 : Bh) ⊗ₜ[B] x := funext hkey
    rwa [hcomp]
  -- move it to the canonical presentation, and read it on `Ext¹`
  have hself : Function.Bijective (conormalCokernelPushAt
      (Algebra.Generators.self k B).toExtension (TensorProduct.mk B Bh N 1)) :=
    (bijective_conormalCokernelPushAt_iff
      (Algebra.Generators.defaultHom (Algebra.Generators.self k B) Q.toGenerators).toExtensionHom
      (Algebra.Generators.defaultHom Q.toGenerators
        (Algebra.Generators.self k B)).toExtensionHom (TensorProduct.mk B Bh N 1)).2 hQb
  have hpush : (conormalCokernelPush k B (TensorProduct.mk B Bh N 1) : _ → _) =
      (conormalCokernelPushAt (Algebra.Generators.self k B).toExtension
        (TensorProduct.mk B Bh N 1) : _ → _) := by
    funext x
    obtain ⟨δ, rfl⟩ := Submodule.mkQ_surjective _ x
    rfl
  have hb : Function.Bijective (conormalCokernelPush k B (TensorProduct.mk B Bh N 1)) := by
    rw [hpush]
    exact hself
  have hfun : (naiveCotangentExtOneMap k B (TensorProduct.mk B Bh N 1) : _ → _) =
      (extCokernelIso k B (Bh ⊗[B] N)).symm ∘
        (conormalCokernelPush k B (TensorProduct.mk B Bh N 1)) ∘ (extCokernelIso k B N) := rfl
  rw [hfun]
  exact ((extCokernelIso k B (Bh ⊗[B] N)).symm.bijective.comp hb).comp
    (extCokernelIso k B N).bijective

/-- **The coefficient comparison of Stacks 0DZD at the henselization of a pair.**  For a field
`k`, a finite type `k`-algebra `B` smooth over `k` outside the zero set of `J`, and the
henselization `(Bʰ, Jʰ)` of the pair `(B, J)`, the map

`Ext¹_B(NL_{B/k}, N) ⟶ Ext¹_B(NL_{B/k}, Bʰ ⊗_B N)`

induced by `n ↦ 1 ⊗ n` is bijective.

The henselization is flat over `B` and an isomorphism modulo every power of `J`, by
`flat_henselization_and_bijective_quotientMap`. -/
public theorem bijective_naiveCotangentExtOneMap_henselization
    (J : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (hhens : HenselianPair Bh (J.map (algebraMap B Bh)))
    (huniv : ∀ (C : Type uB) (_ : CommRing C) (JC : Ideal C), HenselianPair C JC →
      ∀ f : B →+* C, J ≤ JC.comap f →
        ∃! g : Bh →+* C, g.comp (algebraMap B Bh) = f ∧
          J.map (algebraMap B Bh) ≤ JC.comap g) :
    Function.Bijective (naiveCotangentExtOneMap k B (TensorProduct.mk B Bh N 1)) :=
  bijective_naiveCotangentExtOneMap_tensorBaseChange k B N Bh J hsm
    (flat_henselization_and_bijective_quotientMap B J Bh hhens huniv).1
    (flat_henselization_and_bijective_quotientMap B J Bh hhens huniv).2

end

end Deformation.Examples

end
