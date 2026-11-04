module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Deformation.SquareZero.ExtBaseChange
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.RingTheory.NaiveCotangent.PresentationHomology

/-!
# The cochain presentation of the naive cotangent complex, and its pseudo-coherence

`Stacks.Deformation.naiveCotangentCochainComplex k B` is the naive cotangent complex `NL_{B/k}`
read in cohomological degrees `-1` and `0`, with both terms lifted into a common module
universe.  It is the complex the `Ext` groups of `Stacks.Deformation.naiveCotangentExtOne` and
`Stacks.Deformation.extOneCokernel` are taken out of.  This file records what that complex is
made of and proves that it is pseudo-coherent when `B` is of finite type over a Noetherian base.

## Main definitions

* `Stacks.Deformation.naiveCotangentUliftedChainComplex`: `NL_{B/k}` with its two terms lifted,
  as a chain complex; the cochain presentation is the two-term complex of its differential.

## Main results

* `Stacks.Deformation.naiveCotangentCochainComplexHomologyNegOneIso`,
  `Stacks.Deformation.naiveCotangentCochainComplexHomologyZeroIso`: the two cohomology modules
  of the cochain presentation are the universe lifts of `H₁(NL_{B/k})` and `H₀(NL_{B/k})`.
* `Stacks.Deformation.isPseudoCoherent_naiveCotangentCochainComplex`: **the cochain presentation
  of `NL_{B/k}` is pseudo-coherent** for `B` of finite type over a Noetherian ring `k`.

## Implementation notes

The terms of `naiveCotangentCochainComplex k B` are *not* finite modules, so pseudo-coherence
cannot be read off them.  `Algebra.naiveCotangentComplex` is built from the canonical
presentation `k[B] → B`, whose cotangent space is free on a basis indexed by **all of `B`**; for
`B` of finite type over a field that index set is infinite, so neither term is finitely
generated and the term-wise criterion (Stacks 064Y) does not apply.

Pseudo-coherence is a property of the object of `D(B)`, so it is read off the *cohomology*
instead, by Stacks 066E (`pseudoCoherent_iff_boundedAbove_finite_homology`): over a Noetherian
ring an object with bounded-above, finitely generated cohomology is pseudo-coherent.  The two
cohomology modules are identified with those of `Algebra.naiveCotangentComplex` in four steps —
`HomologicalComplex.doubleHomologyIsoKernel`/`doubleHomologyIsoCokernel` in the cochain shape,
the same two lemmas in the chain shape (they are generic in the complex shape, which is what
makes this a four-line chain rather than a separate computation),
`HomologicalComplex.doubleSelfIso`, and
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso` for the universe lift — and are
finitely generated because `NaiveCotangent.naiveCotangentComplexHomologyOneEquiv` and
`...HomologyZeroEquiv` compute them from *any* presentation, in particular from a finite one,
whose cotangent and cotangent-space modules are finite.  The finite presentation exists because
finite type over a Noetherian ring is finitely presented.

This is the universe-polymorphic counterpart of
`Stacks.Deformation.Artin.isPseudoCoherent_derivedNaiveCotangentComplex`, which proves the same
thing for the un-lifted complex with both rings in a single universe; Stacks 0DZC keeps `k` and
`B` in independent universes, so that statement does not transfer to this one.

## References

* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public section

open CategoryTheory Category Limits HomologicalComplex
open StacksDraft.PseudoCoherence

universe uk uB v

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable (k : Type uk) [CommRing k] (B : Type uB) [CommRing B] [Algebra k B]

/-- `NL_{B/k}` with both terms lifted into the module universe `max uk uB v`, as a chain complex
in degrees `1` and `0`.  The cochain presentation
`Stacks.Deformation.naiveCotangentCochainComplex` is the two-term complex of its differential. -/
public abbrev naiveCotangentUliftedChainComplex :
    ChainComplex (ModuleCat.{max uk uB v} B) ℕ :=
  ((ModuleCat.uliftFunctor.{v} B).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (Algebra.naiveCotangentComplex k B)

/-- The two-term cochain complex of the differential of the lifted `NL_{B/k}` is the cochain
presentation of the naive cotangent complex. -/
public theorem double_naiveCotangentUliftedChainComplex_d :
    HomologicalComplex.double
        ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).d 1 0)
        ComplexShape.upIntRelNegOneZero =
      naiveCotangentCochainComplex.{uk, uB, v} k B :=
  rfl

/-- The lifted `NL_{B/k}` has no differential out of degree `0`: degree `0` has no successor in
`ComplexShape.down ℕ`. -/
public theorem d_eq_zero_naiveCotangentUliftedChainComplex (j : ℕ)
    (hj : (ComplexShape.down ℕ).Rel 0 j) :
    (naiveCotangentUliftedChainComplex.{uk, uB, v} k B).d 0 j = 0 :=
  absurd hj (by simp [ComplexShape.down])

/-- The lifted `NL_{B/k}` is zero outside degrees `1` and `0`. -/
public theorem isZero_naiveCotangentUliftedChainComplex_X (j : ℕ) (h₁ : j ≠ 1) (h₀ : j ≠ 0) :
    IsZero ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).X j) :=
  Functor.map_isZero (ModuleCat.uliftFunctor.{v} B)
    (HomologicalComplex.isZero_double_X _ _ j h₁ h₀)

/-- **The degree `-1` cohomology of the cochain presentation of `NL_{B/k}` is the universe lift
of `H₁(NL_{B/k})`.** -/
public def naiveCotangentCochainComplexHomologyNegOneIso :
    (naiveCotangentCochainComplex.{uk, uB, v} k B).homology (-1) ≅
      (ModuleCat.uliftFunctor.{v} B).obj ((Algebra.naiveCotangentComplex k B).homology 1) :=
  HomologicalComplex.doubleHomologyIsoKernel
      ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).d 1 0)
      ComplexShape.upIntRelNegOneZero (by decide) ≪≫
    (HomologicalComplex.doubleHomologyIsoKernel
      ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).d 1 0)
      ComplexShape.downNatRelOneZero one_ne_zero).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{max uk uB v} B)
      (ComplexShape.down ℕ) 1).mapIso
      (HomologicalComplex.doubleSelfIso ComplexShape.downNatRelOneZero one_ne_zero _
        (d_eq_zero_naiveCotangentUliftedChainComplex.{uk, uB, v} k B)
        (isZero_naiveCotangentUliftedChainComplex_X.{uk, uB, v} k B)) ≪≫
    (Functor.mapHomologicalComplexHomologyIso (ModuleCat.uliftFunctor.{v} B)
      (ComplexShape.down ℕ) 1).app (Algebra.naiveCotangentComplex k B)

/-- **The degree `0` cohomology of the cochain presentation of `NL_{B/k}` is the universe lift of
`H₀(NL_{B/k}) = Ω_{B/k}`.** -/
public def naiveCotangentCochainComplexHomologyZeroIso :
    (naiveCotangentCochainComplex.{uk, uB, v} k B).homology 0 ≅
      (ModuleCat.uliftFunctor.{v} B).obj ((Algebra.naiveCotangentComplex k B).homology 0) :=
  HomologicalComplex.doubleHomologyIsoCokernel
      ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).d 1 0)
      ComplexShape.upIntRelNegOneZero (by decide) ≪≫
    (HomologicalComplex.doubleHomologyIsoCokernel
      ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).d 1 0)
      ComplexShape.downNatRelOneZero one_ne_zero).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{max uk uB v} B)
      (ComplexShape.down ℕ) 0).mapIso
      (HomologicalComplex.doubleSelfIso ComplexShape.downNatRelOneZero one_ne_zero _
        (d_eq_zero_naiveCotangentUliftedChainComplex.{uk, uB, v} k B)
        (isZero_naiveCotangentUliftedChainComplex_X.{uk, uB, v} k B)) ≪≫
    (Functor.mapHomologicalComplexHomologyIso (ModuleCat.uliftFunctor.{v} B)
      (ComplexShape.down ℕ) 0).app (Algebra.naiveCotangentComplex k B)

section Finite

variable [IsNoetherianRing k] [Algebra.FiniteType k B]

/-- Some generators of `B` over `k` have finite cotangent module and finite cotangent space. -/
private theorem exists_generators_finite_cotangent :
    ∃ (ι : Type uB) (G : Algebra.Generators k B ι),
      Module.Finite B G.toExtension.Cotangent ∧ Module.Finite B G.toExtension.CotangentSpace := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : Algebra.FinitePresentation k B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let G : Algebra.Generators k B
      (ULift.{uB} (Fin (Algebra.Presentation.ofFinitePresentationVars k B))) :=
    (Algebra.Presentation.ofFinitePresentation k B).toGenerators.reindex Equiv.ulift
  exact ⟨_, G, Algebra.Extension.Cotangent.finite G.fg_ker_of_finitePresentation,
    Module.Finite.of_basis G.cotangentSpaceBasis⟩

/-- `H₁(NL_{B/k})` is a finite `B`-module: it is the kernel of the conormal differential of any
presentation, computed at a finite one, whose cotangent module is finite. -/
public theorem finite_naiveCotangentComplexHomologyOne :
    Module.Finite B ((Algebra.naiveCotangentComplex k B).homology 1) := by
  have := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨_, G, h, -⟩ := exists_generators_finite_cotangent k B
  exact Module.Finite.equiv (NaiveCotangent.naiveCotangentComplexHomologyOneEquiv G).symm

/-- `H₀(NL_{B/k}) = Ω_{B/k}` is a finite `B`-module: it is the cokernel of the conormal
differential of any presentation, computed at a finite one, whose cotangent space is finite. -/
public theorem finite_naiveCotangentComplexHomologyZero :
    Module.Finite B ((Algebra.naiveCotangentComplex k B).homology 0) := by
  obtain ⟨_, G, -, h⟩ := exists_generators_finite_cotangent k B
  exact Module.Finite.equiv (NaiveCotangent.naiveCotangentComplexHomologyZeroEquiv G).symm

/-- **The cochain presentation of `NL_{B/k}` is pseudo-coherent.**  For `B` of finite type over a
Noetherian ring `k` the object `NL_{B/k}` of `D(B)` has bounded-above, finitely generated
cohomology, which over a Noetherian ring is pseudo-coherence (Stacks 066E).

This is the hypothesis Stacks 0A6A needs of the source object in order to pull a flat base
change out of `Ext¹_B(NL_{B/k}, -)`. -/
public theorem isPseudoCoherent_naiveCotangentCochainComplex :
    IsPseudoCoherent
      (DerivedCategory.Q.obj (naiveCotangentCochainComplex.{uk, uB, v} k B)) := by
  have hNo : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  set C := naiveCotangentCochainComplex.{uk, uB, v} k B with hC
  have hiso : ∀ i : ℤ, (DerivedCategory.homologyFunctor (ModuleCat.{max uk uB v} B) i).obj
      (DerivedCategory.Q.obj C) ≅ C.homology i :=
    fun i => (DerivedCategory.homologyFunctorFactors (ModuleCat.{max uk uB v} B) i).app C
  have hz : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max uk uB v} B) i).obj
        (DerivedCategory.Q.obj C)) := fun i h₁ h₀ =>
    (hiso i).isZero_iff.mpr (HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_double_X _ ComplexShape.upIntRelNegOneZero i h₁
        h₀)).isZero_homology
  have hfin : ∀ (i : ℤ) (M : ModuleCat.{max uk uB} B), Module.Finite B M →
      (C.homology i ≅ (ModuleCat.uliftFunctor.{v} B).obj M) →
      Module.Finite B ((DerivedCategory.homologyFunctor (ModuleCat.{max uk uB v} B) i).obj
        (DerivedCategory.Q.obj C)) := fun i M _ e =>
    Module.Finite.equiv ((ULift.moduleEquiv (R := B) (M := M)).symm.trans
      ((hiso i).trans e).toLinearEquiv.symm)
  refine (pseudoCoherent_iff_boundedAbove_finite_homology
    (DerivedCategory.Q.obj C) 0 (ULift.{max uk uB v} B)).2.1.mpr ⟨⟨0, fun i hi => ?_⟩, fun i => ?_⟩
  · exact hz i (by omega) (by omega)
  · by_cases h₁ : i = -1
    · subst h₁
      exact hfin _ _ (finite_naiveCotangentComplexHomologyOne.{uk, uB} k B)
        (naiveCotangentCochainComplexHomologyNegOneIso.{uk, uB, v} k B)
    · by_cases h₀ : i = 0
      · subst h₀
        exact hfin _ _ (finite_naiveCotangentComplexHomologyZero.{uk, uB} k B)
          (naiveCotangentCochainComplexHomologyZeroIso.{uk, uB, v} k B)
      · have := ModuleCat.isZero_iff_subsingleton.mp (hz i h₁ h₀)
        exact Module.Finite.of_finite

end Finite

end

end Stacks.Deformation

end
