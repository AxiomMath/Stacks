module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalVanishingHypotheses
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelLimitAcyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorRestrictionVanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorSheafGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemDerived

/-!
# The terms of the de Rham complex of a crystal at the levels of the system of Tag 07JN

Let `(p, (S, I, γ), X)` be a global crystalline situation with `X` and `S` affine, `T(n)_e` the
system `...SmallSite.wholeSpaceSystem` of [Stacks, Proposition 60.20.1, Tag 07JN] and `F` a crystal
in quasi-coherent `𝒪_{X/S}`-modules, with de Rham complex
`K^• = F ⊗ Ω^•_{X/S}` (`(...SmallSite.crystalDeRhamSheafData hF).natComplex`).  Every term
`K^a = F ⊗ Ω^a_{X/S}` satisfies the two level hypotheses of the Čech comparisons of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechResolutionGood07Q9.lean`:

* its higher cohomology vanishes at the level objects `T(n)_e`
  (`vanishingOnLevels07Q9_crystalDeRhamSheafData`), by [Stacks, Tag 07JJ] for `F ⊗ Ω^a`
  (`...SmallSite.vanishing07JJ_tensorDifferentialFormsSheaf`);
* its restriction maps along the towers `T(n)_e ⟶ T(n)_{e + 1}` are surjective
  (`hasSurjectiveLevelTransitions_crystalDeRhamSheafData`), by
  `...SmallSite.hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf`.

These are the hypotheses `hK` and `hKs` of
`...SmallSite.quasiIso_openAugmentationNat_of_quasiIso` for the de Rham complex.  The system is
the one of the default (tautological) presentation `...SmallSite.instWholeSpacePresentation`, the
presentation for which the surjectivity of the level transitions is in the library
(`...SmallSite.surjective_wholeSpaceSystem_level_map_of_abelian`).

## References

* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)

/-- **The terms of the de Rham complex of a crystal have vanishing higher cohomology at the level
objects** of the system of [Stacks, Tag 07JN]. -/
theorem vanishingOnLevels07Q9_crystalDeRhamSheafData (a : ℕ) :
    VanishingOnLevels07Q9 (wholeSpaceSystem S hp) ((crystalDeRhamSheafData hF).natComplex.X a) :=
  vanishingOnLevels07Q9_of_vanishing07JJ (hasAffineMonoLevels_wholeSpaceSystem hp)
    (vanishing07JJ_tensorDifferentialFormsSheaf
      (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).1 a)

/-- **The terms of the de Rham complex of a crystal have surjective restriction maps along the
towers** of the system of [Stacks, Tag 07JN]. -/
theorem hasSurjectiveLevelTransitions_crystalDeRhamSheafData (a : ℕ) :
    HasSurjectiveLevelTransitions (wholeSpaceSystem S hp)
      ((crystalDeRhamSheafData hF).natComplex.X a) := fun n e =>
  surjective_wholeSpaceSystem_level_map_of_abelian hp _
    (hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf F a
      (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).1
      (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).2) n e

end Crystalline.GlobalCrystallineSituation.SmallSite

end
