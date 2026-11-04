module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.QuasiCoherentExtension
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.LocalizationData
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.HgroupAndCechComplement
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a quasi-coherent module on the complement of a zero locus

Let `I` be a finitely generated ideal of a commutative ring `R`, let `X = Spec R`, let
`Z = V(I)`, let `U = X \ Z` and let `F` be a quasi-coherent module on `U`. There is an
`R`-module `M` with `F = M̃|U`, and for such an `M` the cohomology of `F` on `U` is the local
cohomology of `M` along `Z`, shifted by one: a four-term exact sequence
`0 ⟶ H⁰_Z(M) ⟶ M ⟶ Γ(U, F) ⟶ H¹_Z(M) ⟶ 0`
in low degrees, and `Hᵖ(U, F) ≅ H^{p+1}_Z(M)` for `p ≥ 1`.

## Main results

* `Stacks.LocalCohomology.exists_module_iso_lowDegreeExactSequence_hgroup_iso` — the above, for
  every quasi-coherent `F`, with the module and the identification produced rather than assumed.

## Implementation notes

The three ingredients already exist and are only assembled here:
`Stacks.LocalCohomology.exists_module_iso_restrict_tilde` produces the module `M` and the
isomorphism `F ≅ M̃|U`, `Stacks.LocalCohomology.lowDegreeExactSequence` is the four-term exact
sequence at any such pair, and
`Stacks.Cohomology.ModuleComparison.nonempty_hgroup_iso_localCohomologyModule_of_iso` is the
comparison above degree zero. Nothing here assumes `R` Noetherian.

Above degree zero the comparison is an isomorphism of abelian groups rather than of `R`-modules:
`Hgroup` is by construction a derived functor into `AddCommGrpCat`. The `R`-linear form of the
same comparison, for a finitely generated `I` of an arbitrary `R` and every `F ≅ M̃|U`, is
`Stacks.LocalCohomology.nonempty_complementSheafCohomology_iso_localCohomologyModule`. In low
degrees the exact sequence is a sequence of `R`-linear maps.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.ModuleComparison

universe u

namespace Stacks.LocalCohomology

/-- **Parts (1) and (2) of Stacks 0DWR, with the comparison above degree zero as groups.** Let
`I` be a finitely generated ideal of a commutative ring `R`, let `Z = V(I)` inside `X = Spec R`,
let `U = X \ Z` and let `F` be a quasi-coherent module on `U`. Then there is an `R`-module `M` and
an identification `F ≅ M̃|U` for which

* the sequence `0 ⟶ H⁰_Z(M) ⟶ M ⟶ Γ(U, F) ⟶ H¹_Z(M) ⟶ 0` built from the restriction map and
  the connecting map of the localization triangle is exact, and
* `Hᵖ(U, F) ≅ H^{p+1}_Z(M)` for every `p ≥ 1`, **as abelian groups**.

The second clause is an isomorphism of groups. The source reads its isomorphisms off a triangle
in `D(Γ(X, 𝒪_X)) = D(R)` (Stacks 0G71) and so asserts them `R`-linearly; that form, for every
`F ≅ M̃|U`, is
`Stacks.LocalCohomology.nonempty_complementSheafCohomology_iso_localCohomologyModule`, which
carries the tag together with `Stacks.LocalCohomology.exists_module_iso_restrict_tilde`,
`Stacks.LocalCohomology.exact_lowDegreeSequence` and the clause (3) declarations.

The module is not unique; the canonical choice `M = Γ(U, F)` of part (3) of the tag is
`Stacks.LocalCohomology.iso_restrict_tilde_globalSectionsModule`. -/
theorem exists_module_iso_lowDegreeExactSequence_hgroup_iso
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    (F : (complementZeroLocus R I : Scheme).Modules) [F.IsQuasicoherent] :
    ∃ (M : ModuleCat.{u} R) (D : LocalizationTriangleData.{u, u} R I hI)
      (e : F ≅ complementTilde R I M),
      (Function.Injective (localCohomologyZeroToModule R I hI M) ∧
        Function.Exact (localCohomologyZeroToModule R I hI M)
          (restrictionToComplement D M F e) ∧
        Function.Exact (restrictionToComplement D M F e) (localizationBoundary D M F e) ∧
        Function.Surjective (localizationBoundary D M F e)) ∧
      ∀ p : ℕ, 1 ≤ p →
        Nonempty (Hgroup (complementZeroLocus R I : Scheme).ringCatSheaf ⊤ p F ≅
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
            (localCohomologyModule R I hI M ((p : ℤ) + 1))) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_module_iso_restrict_tilde R I hI F
  obtain ⟨D, hD⟩ := lowDegreeExactSequence.{u, u} R I hI
  refine ⟨M, D, e, hD M F e, fun p hp => ?_⟩
  match p, hp with
  | q + 1, _ =>
    have hdeg : ((q + 1 : ℕ) : ℤ) + 1 = (q : ℤ) + 2 := by push_cast; ring
    rw [hdeg]
    exact nonempty_hgroup_iso_localCohomologyModule_of_iso I M F hI ⟨e⟩ q

end Stacks.LocalCohomology

end
