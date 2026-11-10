module

public import StacksFrontier.AlgebraicGeometry.Algebraization.StrictDepthMixedComponents

/-!
# The depth-two locus of an algebraization situation

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. The *depth-two locus* is the set

  `T = {x ∈ U | \overline{\{x\}} ∩ Y ⊆ Z}`

of points of `U` whose closure in `X` meets the adic subscheme `Y` only inside `Z`. It is the
subset along which [Stacks, Tag 0EJ8] improves a coherent `𝒪_U`-module to one of depth at
least two.

This file collects the elementary properties of `T` and the first of the two depth bounds that
[Stacks, Tag 0EJ8] needs about it: at a point `x ∉ T` whose closed fibre has an irreducible
component inside `Z`, the stalk has depth at least one.

## Main definitions

* `Stacks.Algebraization.depthTwoLocus` — the locus `T`.

## Main results

* `Stacks.Algebraization.depthTwoLocus_stableUnderSpecialization` — `T` is stable under
  specialization, so it is a legitimate subset along which to run [Stacks, Tag 0EI3].
* `Stacks.Algebraization.notMem_depthTwoLocus_of_mem_range_Yι` — a point of `U` lying on `Y` is
  outside `T`; equivalently `T` misses the support of `I𝒪_U`.
* `Stacks.Algebraization.one_le_depth_stalk_of_component_subset_Z` — the depth bound above, by
  [Stacks, Tag 0EJ5].

## Implementation notes

The closure of a point of `U` is taken in `X`, as in the source, and `Y` and `Z` enter through
the ranges of `Stacks.Algebraization.AlgebraizationSituation.Yι` and
`Stacks.Algebraization.AlgebraizationSituation.Zι` rather than as zero loci: that is the form
the geometric inputs of [Stacks, Tag 0EJ5] are stated in.

`Stacks.Algebraization.one_le_depth_stalk_of_component_subset_Z` is [Stacks, Tag 0EJ5] applied;
the comparison of [Stacks, Tag 0EIF] that [Stacks, Tag 0EG5] uses there is
`Stacks.Algebraization.serreOneAlternativeComparison`, so nothing is assumed beyond the
hypotheses stated.

## References

* [Stacks Project, Tag 0EJ8](https://stacks.math.columbia.edu/tag/0EJ8)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5)
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- The locus `T = {x ∈ U | \overline{\{x\}} ∩ Y ⊆ Z}` of points of `U` whose closure in `X`
meets the adic subscheme only inside the excluded locus. -/
public def depthTwoLocus (S : AlgebraizationSituation.{u}) : Set S.U.toScheme :=
  {x | closure ({S.U.ι.base x} : Set S.X) ∩ Set.range S.Yι.base ⊆ Set.range S.Zι.base}

/-- Membership in the depth-two locus, unfolded: `x ∈ T` if and only if the closure of `x` in `X`
meets `Y` only inside `Z`. -/
public theorem mem_depthTwoLocus_iff {S : AlgebraizationSituation.{u}} {x : S.U.toScheme} :
    x ∈ depthTwoLocus S ↔
      closure ({S.U.ι.base x} : Set S.X) ∩ Set.range S.Yι.base ⊆ Set.range S.Zι.base :=
  Iff.rfl

/-- The depth-two locus is stable under specialization: the closure of a specialization of `x`
is contained in the closure of `x`. -/
public theorem depthTwoLocus_stableUnderSpecialization (S : AlgebraizationSituation.{u}) :
    StableUnderSpecialization (depthTwoLocus S) := by
  intro x x' hxx' hx
  have hx'closure : S.U.ι.base x' ∈ closure ({S.U.ι.base x} : Set S.X) := by
    have himage : S.U.ι.base x' ∈ closure (S.U.ι.base '' ({x} : Set S.U.toScheme)) :=
      image_closure_subset_closure_image S.U.ι.continuous
        ⟨x', specializes_iff_mem_closure.mp hxx', rfl⟩
    simpa using himage
  have hclosure : closure ({S.U.ι.base x'} : Set S.X) ⊆ closure ({S.U.ι.base x} : Set S.X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hx'closure) isClosed_closure
  exact fun y hy => hx ⟨hclosure hy.1, hy.2⟩

/-- A point of `U` which lies on `Y` is not in the depth-two locus: it is a point of its own
closure meeting `Y`, and it is outside `Z` because it is in `U`. -/
public theorem notMem_depthTwoLocus_of_mem_range_Yι (S : AlgebraizationSituation.{u})
    (x : S.U.toScheme) (z : S.Y) (hxz : S.U.ι.base x = S.Yι.base z) :
    x ∉ depthTwoLocus S := by
  intro hx
  obtain ⟨w, hw⟩ : S.Yι.base z ∈ Set.range S.Zι.base :=
    hx ⟨hxz ▸ subset_closure rfl, ⟨z, rfl⟩⟩
  have hwV : S.Zι.base w ∈ PrimeSpectrum.zeroLocus (S.a : Set S.A) := by
    intro r hr
    change Ideal.Quotient.mk S.a r ∈ w.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact Ideal.zero_mem _
  have hxU : S.U.ι.base x ∈ (PrimeSpectrum.zeroLocus (S.a : Set S.A))ᶜ := x.2
  exact hxU ((hxz.trans hw.symm) ▸ hwV)

/-- If the closed fibre `\overline{\{x\}} ∩ Y` of a point `x ∈ U` is not contained in `Z`, then
it has an irreducible component not contained in `Z`. -/
public theorem exists_irreducibleComponent_not_subset_Z (S : AlgebraizationSituation.{u})
    (x : S.U.toScheme) (hx : x ∉ depthTwoLocus S) :
    ∃ C : Set (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)),
      C ∈ irreducibleComponents (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) ∧
        ¬ C ⊆ {y | S.Yι.base y.1 ∈ Set.range S.Zι.base} := by
  classical
  by_contra hcon
  refine hx fun y hy => ?_
  obtain ⟨hyclosure, z, rfl⟩ := hy
  have hzW : z ∈ S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X) := hyclosure
  have hall : ∀ C : Set (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)),
      C ∈ irreducibleComponents (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) →
      C ⊆ {y | S.Yι.base y.1 ∈ Set.range S.Zι.base} := by
    intro C hC
    by_contra hC'
    exact hcon ⟨C, hC, hC'⟩
  exact hall (irreducibleComponent (⟨z, hzW⟩ :
      S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)))
    (irreducibleComponent_mem_irreducibleComponents _) mem_irreducibleComponent

/-- **The first depth bound of [Stacks, Tag 0EJ8].** In an algebraization situation with `A`
`I`-adically complete, carrying a dualizing complex, and with `cd(A, I) ≤ d` for some `d ≥ 1`,
let `ℱ` be a coherent `𝒪_U`-module whose completion satisfies the strict
`(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3]. Let `x ∈ U` be outside the depth-two locus
whose closed fibre `\overline{\{x\}} ∩ Y` has an irreducible component contained in `Z`. Then

  `depth(ℱ_x) ≥ 1`.

Being outside the depth-two locus produces an irreducible component of the closed fibre *not*
contained in `Z`, so the components lie on both sides of `Z` and [Stacks, Tag 0EJ5] applies. -/
public theorem one_le_depth_stalk_of_component_subset_Z (S : AlgebraizationSituation.{u})
    [IsAdicComplete S.I S.A]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (d : ℤ) (hd : 1 ≤ d)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      S.I.fg_of_isNoetherianRing ≤ d)
    (hstrict : SatisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) 1 (1 + d))
    (x : S.U.toScheme) (hx : x ∉ depthTwoLocus S)
    (hcomponent :
      ∃ C : Set (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)),
        C ∈ irreducibleComponents (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) ∧
          C ⊆ {y | S.Yι.base y.1 ∈ Set.range S.Zι.base}) :
    1 ≤ Module.depth (S.U.toScheme.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (S.U.toScheme.presheaf.stalk x))
      ((stalkModuleFunctor x).obj F.obj) :=
  one_le_depth_stalk_of_mixed_irreducibleComponents S F d hd K hK hcd hstrict x
    ⟨hcomponent, exists_irreducibleComponent_not_subset_Z S x hx⟩

end Stacks.Algebraization

end
