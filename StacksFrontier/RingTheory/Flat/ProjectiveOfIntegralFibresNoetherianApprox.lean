module

public import StacksFrontier.Algebra.MittagLeffler.BaseChange
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.Flat.GeometricFibresStage

/-!
# Noetherian approximation for Stacks 05FT

Stacks 05FS proves that a flat ring map `R → S` of finite type with geometrically integral
fibres and `R` *Noetherian* makes `S` a projective `R`-module. Stacks 05FT drops the Noetherian
hypothesis, at the cost of asking for finite presentation, and deduces itself from 05FS by
Noetherian approximation: write the pair `R → S` as the base change of a pair `R₀ → S₀` with
`R₀` of finite type over `ℤ`, hence Noetherian, so that `R₀ → S₀` is still flat of finite type
with geometrically integral fibres; then `S₀` is a projective `R₀`-module by 05FS and
`S = R ⊗_{R₀} S₀` is a projective `R`-module by base change (Stacks 05A3,
`Module.Projective` of a base change, which is an instance).

This file carries out that deduction. It takes the Noetherian case as the explicit hypothesis
`hNoeth`, stated exactly as the conclusion of 05FS, so that 05FT follows by supplying it once
05FS lands.

## The second hypothesis, and why it is there

The approximation is run inside the directed system `Algebra.FiniteTypeSystem` of Stacks 00R1:
`R₀ ⊆ R` is a subring of finite type over `ℤ`, the stages `R_λ` are the finite type
`ℤ`-subalgebras of `R` containing `R₀`, and `S_λ = R_λ ⊗_{R₀} S₀`. Flatness reaches a stage by
`Algebra.FiniteTypeSystem.exists_flat_stage_self`, which is Stacks 02JO and is already proved;
this is the content of Stacks 05FE and 05FB, and no scheme-level statement is needed for it.
Geometrically integral fibres, however, do *not* reach a stage by a descent argument alone:
`Spec R → Spec R_λ` is never surjective in the cases that matter, so the primes of `R_λ`
outside its image are not constrained by any hypothesis on `R → S`. The unit ideal argument
that moves to a later stage needs the locus of good primes in `Spec R_λ` to be open, and that
is the geometric input — EGA IV 12.2.4, in Stacks the constructibility of the geometrically
reduced and geometrically irreducible loci (tags 0579, 055B) together with the limit lemma
05F4. It appears here as the hypothesis `hOpen` and is discussed in the module docstring of
`StacksFrontier.RingTheory.Flat.GeometricFibresStage`.

So the statement below is a *conditional* 05FT: it is 05FT granted 05FS and granted openness of
the geometrically integral fibre locus over a Noetherian base. What it buys is that nothing else
is left: the scheme-level tower of Stacks 05FB, 05FE and 05FL is gone, and the two remaining
inputs are each a single named theorem.

## Main results

* `Algebra.projective_of_flat_of_geometricallyIntegral_of_finitePresentation`: Stacks 05FT,
  conditional on the Noetherian case 05FS and on openness of the geometrically integral fibre
  locus over a Noetherian base.

## References

* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 05FS](https://stacks.math.columbia.edu/tag/05FS)
* [Stacks Project, Tag 00R1](https://stacks.math.columbia.edu/tag/00R1)
* [Stacks Project, Tag 05A3](https://stacks.math.columbia.edu/tag/05A3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat
open scoped TensorProduct

universe u

namespace Algebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Algebra.FiniteTypeSystem in
/-- **Stacks 05FT from the Noetherian case 05FS.** Let `R → S` be flat of finite presentation
with geometrically integral fibres. Assume

* `hNoeth`, the statement of Stacks 05FS: a flat ring map of finite type with geometrically
  integral fibres out of a Noetherian ring makes its target a projective module; and
* `hOpen`: for such a ring map the geometrically integral fibre locus is open in the spectrum of
  the base.

Then `S` is a projective `R`-module.

Write `R → S` as the base change of `R₀ → S₀` with `R₀ ⊆ R` of finite type over `ℤ` (Stacks
00R1). Flatness holds at a stage `R_λ → S_λ` of the system of finite type `ℤ`-subalgebras of
`R` (Stacks 02JO), the stage is Noetherian, and `hOpen` feeds
`Algebra.FiniteTypeSystem.exists_geometricallyIntegral_stage` to move to a stage `R_μ → S_μ`
which moreover has geometrically integral fibres. It is still flat, by base change along
`R_λ → R_μ`. So `S_μ` is a projective `R_μ`-module by `hNoeth`, and `S = R ⊗_{R_μ} S_μ` is a
projective `R`-module by Stacks 05A3. -/
theorem projective_of_flat_of_geometricallyIntegral_of_finitePresentation
    (hNoeth : ∀ (R₀ S₀ : Type u) [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
      [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Module.Flat R₀ S₀]
      [GeometricallyIntegral (Spec.map (ofHom (algebraMap R₀ S₀)))], Module.Projective R₀ S₀)
    (hOpen : ∀ (R₀ S₀ : Type u) [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
      [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Module.Flat R₀ S₀],
      IsOpen (geometricallyIntegralFibreLocus R₀ S₀))
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [Algebra.FinitePresentation R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] :
    Module.Projective R S := by
  obtain ⟨R₀, S₀, -, _, _, _, _, -, -, -, -, -, hZ, hS₀, -, hpush, -⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := R) (S := S) S
  obtain ⟨i, hi⟩ := exists_flat_stage_self R₀ S₀ (B := S)
  have hN (k) : IsNoetherianRing (Base R₀ k) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨j, hij, hj⟩ := exists_geometricallyIntegral_stage R₀ S₀ i (hOpen _ _) ‹_›
  have : Fact (i ≤ j) := ⟨hij⟩
  have : Module.Flat (Base R₀ j) (Ring R₀ S₀ j) :=
    Module.Flat.isBaseChange (Base R₀ i) (Base R₀ j) (Ring R₀ S₀ i) (Ring R₀ S₀ j)
      (ringMap_isPushout R₀ S₀ (i := i) (j := j)).out
  have := hNoeth (Base R₀ j) (Ring R₀ S₀ j)
  have : Algebra.IsPushout (Base R₀ j) R (Ring R₀ S₀ j) S := ringToRing_isPushout R₀ S₀ j
  exact Module.Projective.of_equiv'
    (Algebra.IsPushout.equiv (Base R₀ j) R (Ring R₀ S₀ j) S).toLinearEquiv

end Algebra

end
