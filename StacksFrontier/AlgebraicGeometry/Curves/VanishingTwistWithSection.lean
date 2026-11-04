module

public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafUnitSections

/-!
# A high twist of an ample module on a proper curve: no `H¹`, and a global section

Let `k` be a field and let `X` be a proper curve over `k`. This file produces an invertible
`𝒪_X`-module `ℒ` with `H¹(X, ℒ) = 0` and `dim_k H⁰(X, ℒ) > 0`.

This is the starting line bundle of the induction of
[Stacks, Tag 0B8Z](https://stacks.math.columbia.edu/tag/0B8Z). The source gets it by embedding
the curve in `𝐏ⁿ_k` ([Stacks, Tag 0A26]) and taking `ℒ = i^* 𝒪(d)` for `d ≫ 0`, citing
[Stacks, Tag 0B5U] for the vanishing. Only the *ampleness* of such an `ℒ` is used in that
argument, and on an integral curve an ample invertible module is available directly, from
[Stacks, Tag 09ND]; so the projective embedding is bypassed here.

## Main results

* `AlgebraicGeometry.exists_invertible_isZero_cohomologyOverField_one_and_zero_lt_finrank`:
  on a proper curve over a field there is an invertible `𝒪_X`-module whose `H¹` vanishes and
  whose `H⁰` has positive dimension.

## The three steps

1. **An ample invertible module.** A curve is integral, and over a field it is Noetherian and
   separated as a scheme
   (`Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field` and
   `…isSeparated_of_isSeparated_over_field`), so [Stacks, Tag 09ND] —
   `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one` — gives an ample
   invertible `L`.
2. **Vanishing of `H¹` of a high power.** This is the implication (1) ⟹ (2) of
   [Stacks, Tag 0B5U], i.e. clause (4) of [Stacks, Tag 0B5T], formalized as
   `Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`: for the
   coherent module `𝒪_X` there is a `d₀` with `Hᵖ(X, 𝒪_X ⊗ L^{⊗ d}) = 0` for `d ≥ d₀` and
   `p > 0`.
3. **A nonzero global section of a high power.** Ampleness itself supplies, at any point of `X`,
   an exponent `n ≥ 1` and a global section `s` of `L^{⊗ n}` whose nonvanishing locus contains
   that point. Its powers do not move that locus — `X_{s^j} = X_s`, which is
   `Stacks.SheafOfModules.Invertible.nonvanishingOpen_sectionPow'` — so `s^j` is a nonzero global
   section of `L^{⊗ n j}` for every `j ≥ 1`. Taking `j = max 1 d₀` puts the exponent `n j` at or
   above `d₀`, where step 2 applies.

## Implementation notes

**Spellings.** `dim_k Hⁱ(X, ℱ)` is `Module.finrank k (cohomologyOverField k f ℱ i)` and vanishing
is `CategoryTheory.Limits.IsZero`, as in
`StacksFrontier/AlgebraicGeometry/Curves/PrescribedLowCohomology.lean`. Invertibility is stated at
`X.sheaf.obj X.ringCatSheaf.property`, which is the spelling the cohomological results of that
file use; `AlgebraicGeometry.Scheme.Modules.IsAmple` and [Stacks, Tag 09ND] are stated at
`X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property` and
[Stacks, Tag 0B5T] at `Stacks.Ample.IsInvertibleModule`. The three are the same proposition --
the sheaf of rings is the same term by `Stacks.SchemeCohomology.ringSheaf_ringedSpace` and the
sheaf condition is a proposition -- so they are crossed by `exact`, not by a transport; but
instance search does not cross them, which is why the invertibility of the tensor power is
named (`Scheme.Modules.algebraicGeometryIsInvertible_tensorPowerModules`) rather than inferred.

**Two cohomology spellings meet once.** [Stacks, Tag 0B5T] clause (4) is stated for the
abelian-group-valued `Hgroup`; `AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup`
([Stacks, Tag 01F1] part (1)) carries its vanishing to `cohomologyOverField`. The twist it
vanishes on is `𝒪_X ⊗ L^{⊗ d}` over `Stacks.Ample.tensorPowModule`, and the conclusion is about
`Stacks.SheafOfModules.Invertible.tensorPower`; the left unitor
`AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso` and the power comparison
`Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso` identify the two, and
`AlgebraicGeometry.cohomologyOverFieldIso` transports the vanishing along the result.

**Why `dim_k H⁰ > 0` and not merely `H⁰ ≠ 0`.** `Module.finrank` is zero on a module that is not
finite-dimensional, so the positivity statement carries finite dimensionality with it. That is
[Stacks, Tag 02O6] over a field, `finiteDimensional_cohomologyOverField_of_isProper`, applied to
the tensor power, which is coherent because it is invertible on a locally Noetherian scheme.

## References

* [Stacks Project, Tag 0B8Z](https://stacks.math.columbia.edu/tag/0B8Z)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The starting line bundle of the induction of [Stacks, Tag 0B8Z].** On a proper curve over a
field there is an invertible `𝒪_X`-module `ℒ` with `H¹(X, ℒ) = 0` and `dim_k H⁰(X, ℒ) > 0`.

Take `ℒ = L^{⊗ n j}` for `L` an ample invertible module ([Stacks, Tag 09ND]), `n` and `s` an
exponent and a global section of `L^{⊗ n}` furnished by ampleness at a point of `X`, and
`j = max 1 d₀` for `d₀` the threshold beyond which clause (4) of [Stacks, Tag 0B5T] kills the
higher cohomology of the twists of `𝒪_X`. Then `H¹(X, ℒ) = 0` because `n j ≥ d₀`, and `s^j` is a
nonzero global section of `ℒ` because `X_{s^j} = X_s` is nonempty. -/
public theorem exists_invertible_isZero_cohomologyOverField_one_and_zero_lt_finrank
    [IsProper f] [IsCurve k f] :
    ∃ L₀ : X.Modules,
      SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L₀ ∧
        IsZero (cohomologyOverField k f L₀ 1) ∧
          0 < Module.finrank k (cohomologyOverField k f L₀ 0) := by
  have hN : AlgebraicGeometry.IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field f
  have hS : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field f
  obtain ⟨L, hLinv, hLamp⟩ := Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one X
    (IsCurve.topologicalKrullDim_eq_one (k := k) f)
  have _ := hLinv
  have hunit : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist f
      (SheafOfModules.unit X.ringCatSheaf) L
      (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X L hLamp)
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨n, hn, s, hxs, -⟩ := hLamp.exists_affine_nonvanishingLocus x₀
  set m : ℕ := n * max 1 d₀ with hm
  have hmd : d₀ ≤ m := le_trans (le_max_right 1 d₀) (Nat.le_mul_of_pos_left _ hn)
  set M : X.Modules := Scheme.Modules.tensorPowerModules L (m : ℤ) with hM
  have hMinv : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    Scheme.Modules.algebraicGeometryIsInvertible_tensorPowerModules L (m : ℤ)
  have _ := hMinv
  have hMcoh : SheafOfModules.IsCoherent M :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X M
  refine ⟨M, hMinv, ?_, ?_⟩
  · -- `H¹(X, M) = 0`, since `m ≥ d₀`.
    refine ((isZero_cohomologyOverField_iff_isZero_hgroup k f _ 1).mpr
      (hd₀ m 1 hmd Nat.one_pos)).of_iso (cohomologyOverFieldIso k f ?_ 1)
    exact Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X L (m : ℤ) ≪≫
      (AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso X.toRingedSpace _).symm
  · -- `dim_k H⁰(X, M) > 0`, since the `max 1 d₀`-th power of `s` is a nonzero global section.
    have hsne : (Stacks.SheafOfModules.Invertible.sectionPow' L s (max 1 d₀)).eval (op ⊤) ≠ 0 := by
      refine eval_top_ne_zero_of_mem_nonvanishingLocus (X := X) M _ (x := x₀) ?_
      show x₀ ∈ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
        (Stacks.SheafOfModules.Invertible.tensorPowerModule' L ((n * max 1 d₀ : ℕ) : ℤ))
        (Stacks.SheafOfModules.Invertible.sectionPow' L s (max 1 d₀))
      rw [Stacks.SheafOfModules.Invertible.nonvanishingOpen_sectionPow'
        (X := X.toRingedSpace) L s (max 1 d₀) (le_max_left 1 d₀)]
      exact hxs
    have _ := finiteDimensional_cohomologyOverField_of_isProper k f M 0
    have : Nontrivial Γ(M, ⊤) :=
      ⟨⟨(Stacks.SheafOfModules.Invertible.sectionPow' L s (max 1 d₀)).eval (op ⊤), 0, hsne⟩⟩
    exact Module.finrank_pos_iff.mpr (cohomologyOverFieldZeroEquivSections k f M).nontrivial

end AlgebraicGeometry

end
