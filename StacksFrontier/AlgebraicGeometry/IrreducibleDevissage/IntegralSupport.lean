module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Support
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.RingTheory.Nagata.Japanese

/-!
# The integral closed subscheme on an irreducible closed set, and 01Y9 absolutely

Step 4 of the proof of [Stacks, Tag 01YF] forms the reduced induced closed subscheme on the
support of a coherent module and uses that it is **integral**, the support being irreducible;
step 3 uses that a power of that subscheme's ideal sheaf **annihilates** the module. Neither
statement existed in this repository in the absolute form those steps need, although both are
short given what is in the library, and this file supplies them.

## Main results

* `isIntegral_subscheme_vanishingIdeal_of_isIrreducible`, in the namespace
  `Stacks.AlgebraicGeometry.IrreducibleDevissage`: **the reduced induced structure on an
  irreducible closed subset is integral.**
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_isIntegral_isClosedImmersion_range_eq`:
  **every irreducible closed subset of a scheme is the range of a closed immersion from an
  integral scheme** — the packaging the quotient class
  `Stacks.AlgebraicGeometry.DevissageBounded.IsIdealPushforward` is stated over.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_isZero_idealPowSmul`: **[Stacks, Tag
  01Y9] absolutely** — for a coherent module whose support lies in a closed set `Z`, some power
  of the ideal sheaf of `Z` cuts the module down to zero.

## Implementation notes

**The integral subscheme is assembled, not proved.** Each of the four inputs is available:
`AlgebraicGeometry.IsClosedImmersion` of `Scheme.IdealSheafData.subschemeι` and
`AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced` are Mathlib's;
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι_vanishingIdeal` and the
`IsReduced` instance are in `StacksFrontier/AlgebraicGeometry/Limits/ReducedInducedSubscheme.lean`;
and `AlgebraicGeometry.Scheme.IdealSheafData.irreducibleSpace_subscheme` is in
`StacksFrontier/RingTheory/Nagata/Japanese.lean`. What was missing is only the composite. The two
integral closed subschemes that *were* available are special cases — the closure of a single
point (`StacksFrontier/AlgebraicGeometry/CoherentPushforwardCriteria/ClosureSubscheme.lean`) and a
one-dimensional component (`StacksFrontier/AlgebraicGeometry/ComponentDegrees/Basic.lean`) —
and neither covers the support of a coherent module.

**01Y9 absolutely is the two-closed-set form at `Z₁ = ⊥`.**
`Stacks.AlgebraicGeometry.IdealPowerSmul.exists_supp_idealPowSmul_subset` produces, for a support
contained in `Z₁ ∪ Z₂`, an exponent `n` with `supp (I_{Z₂} ^ n • F) ⊆ Z₁`. Taking `Z₁` to be the
empty closed set makes the conclusion an empty support, and
`Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty` turns that into
vanishing. The specialisation is worth recording because the two-set form is strictly more general
and
its absolute instance is easy to overlook.

**No `@[stacks]` attribute is attached.** No declaration below reproduces the statement of any
of 01Y9, 01J3, 01YE, 01YF and 01YG.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.IrreducibleDevissage

variable {X : Scheme.{u}}

/-- **The reduced induced structure on an irreducible closed subset is integral.** It is
reduced by `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`, and
irreducible because the closed immersion is a homeomorphism onto its range, which is the given
set. -/
theorem isIntegral_subscheme_vanishingIdeal_of_isIrreducible (Z : Closeds X)
    (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have hirr : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X _
      (by rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]; exact hZ)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **Every irreducible closed subset of a scheme is the range of a closed immersion from an
integral scheme.** This is the shape in which the quotient class of [Stacks, Tag 01YF],
`Stacks.AlgebraicGeometry.DevissageBounded.IsIdealPushforward`, asks for its subscheme. -/
theorem exists_isIntegral_isClosedImmersion_range_eq (Z : Closeds X)
    (hZ : IsIrreducible (Z : Set X)) :
    ∃ (W : Scheme.{u}) (i : W ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral W),
      Set.range i.base = (Z : Set X) :=
  ⟨(Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι, inferInstance,
    isIntegral_subscheme_vanishingIdeal_of_isIrreducible Z hZ,
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Z⟩

/-- **[Stacks, Tag 01Y9] absolutely.** For a coherent module on a Noetherian scheme whose
support is contained in a closed set `Z`, some power of the ideal sheaf of the reduced induced
structure on `Z` cuts the module down to the zero module. This is step 3 of the proof of
[Stacks, Tag 01YF] in the form that step consumes it: it is what makes the `I`-adic filtration
of the module finite. -/
theorem exists_isZero_idealPowSmul [IsNoetherian X] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsCoherent] (Z : Closeds X) (hZ : SheafOfModules.supp F ⊆ (Z : Set X)) :
    ∃ n : ℕ, IsZero
      (IdealPowerSmul.idealPowSmul (IdealPowerSmul.closedIdeal Z) n F).toSheafOfModules := by
  obtain ⟨n, hn⟩ := IdealPowerSmul.exists_supp_idealPowSmul_subset F ⊥ Z (by simpa using hZ)
  refine ⟨n, DevissageNoetherian.isZero_of_supp_eq_empty _ ?_⟩
  simpa using Set.subset_empty_iff.mp (by simpa using hn)

end Stacks.AlgebraicGeometry.IrreducibleDevissage

end
