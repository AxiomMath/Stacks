module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmoothPresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalCosimplicialPair

/-!
# The cosimplicial degrees of the pair of a crystal as modules with connection

Let `ℱ` be a crystal in quasi-coherent `𝒪_{X/S}`-modules, in the situation of
[Stacks, Proposition 60.20.1, Tag 07JN], and `(M(•), ∇_•)` its cosimplicial pair
(`...SmallSite.crystalCosimplicialPair`): `M(b) = lim_e Γ(T(b)_e, ℱ)` with the base change `∇_b`
of the connection of [Stacks, Lemma 60.17.3, Tag 07JG] along the coprojection `⦋0⦌ ⟶ ⦋b⦌`.

This module packages each cosimplicial degree `b` as a module with integrable connection
(`Crystalline.FormsData.ConnModule`) over the ring with forms
`Crystalline.presTowerFormsData` of the divided power envelope `D(b)`
(`...SmallSite.crystalPairDegreeConnModule`), and records that its completed de Rham complex is the
row `b` of the double complex of [Stacks, Proposition 60.21.3, Tag 07LG],
`M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` (`...SmallSite.crystalPairDegreeConnModule_complex`, by `rfl`).  The
point of the packaging is that the comparison morphisms of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompletedDeRhamNilpotentReduction.lean` are
stated for a `ConnModule`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Simplicial

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp] (Fc : QuasiCoherentCrystal S)

/-- **The cosimplicial degree `b` of the pair of a crystal, as a module with integrable
connection**: `M(b)` with the base change `∇_b` of the connection of [Stacks, Tag 07JG] along the
coprojection, which is integrable by
`Crystalline.CosimplicialCompletedModule.hasIntegrableConnection_baseChangeConnection`. -/
def crystalPairDegreeConnModule (b : ℕ) :
    FormsData.ConnModule
      (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) b) where
  carrier := (wholeSpaceCosimplicialModule hp Fc).carrier b
  addCommGroup := inferInstance
  module := (wholeSpaceCosimplicialModule hp Fc).module b
  isPAdicallyComplete := wholeSpaceCosimplicialModuleIsAdicComplete hp Fc b
  nabla := (crystalCosimplicialPair hp Fc).nabla b
  isCurvatureZero :=
    (wholeSpaceCosimplicialModule hp Fc).hasIntegrableConnection_baseChangeConnection
      (crystalPairFormsConnection hp Fc) (crystalCoprojectionBeta hp Fc)
      (crystalCoprojectionBeta_of_tmul hp Fc)
      (hasIntegrableConnection_crystalPairFormsConnection hp Fc) b

/-- The carrier of the degree-`b` module with connection is `M(b)`. -/
theorem crystalPairDegreeConnModule_carrier (b : ℕ) :
    (crystalPairDegreeConnModule hp Fc b).carrier = wholeSpaceSections hp Fc ⦋b⦌ := rfl

/-- The connection of the degree-`b` module is the connection `∇_b` of the cosimplicial pair. -/
theorem crystalPairDegreeConnModule_nabla (b : ℕ) :
    (crystalPairDegreeConnModule hp Fc b).nabla = (crystalCosimplicialPair hp Fc).nabla b := rfl

/-- **The completed de Rham complex of the degree-`b` module is the row `b` of the double complex
of [Stacks, Tag 07LG]**, `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}`. -/
theorem crystalPairDegreeConnModule_complex (b : ℕ) :
    (crystalPairDegreeConnModule hp Fc b).complex =
      (crystalCosimplicialPair hp Fc).degreeDeRhamComplex b := rfl

end Crystalline.GlobalCrystallineSituation.SmallSite

end
