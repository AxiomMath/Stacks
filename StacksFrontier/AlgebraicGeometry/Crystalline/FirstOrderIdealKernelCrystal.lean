module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderAmbientCrystalComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderProjectionFormulaUnitSection

/-!
# The identification of [Stacks, Tag 07J6] for a crystal

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site and let `(U, T, δ)` be an object of `CRIS(X/S)`
with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2], projections
`p₀, p₁ : T' ⟶ T` and diagonal `i : T ⟶ T'`.

[Stacks, Tag 07J6] reads the connection `∇(s) = p₁^* s - c (p₀^* s)` inside

`F_T ⊗_{𝒪_T} Ω_{T/S,δ}`

on the ground that this module *is* the kernel of `p₁^* F_T ⟶ F_T`, because
`𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`.  This module is where that identification becomes a theorem: for a
sheaf crystal `F`, with no further hypothesis, the canonical morphism

`F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker(i^* : p₀_* F_{T'} ⟶ F_T)`

of `Crystalline.GlobalCrystallineSituation.firstOrderKernelComparison` is an isomorphism.

## The three inputs, and where each comes from

`Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison` of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealKernelIso.lean` proves this from two
statements, both of which are theorems:

* the invertibility of the comparison map of [Stacks, Tag 07IQ] at `p₀`, read between sheaves of
  modules on the *ambient schemes* rather than over the restrictions of `𝒪_{X/S}` — that is
  `Crystalline.GlobalCrystallineSituation.isIso_ambientSchemeCrystalComparison` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderAmbientCrystalComparison.lean`, proved
  from `Crystalline.GlobalCrystallineSituation.IsSheafCrystal`, which is the tag's own
  hypothesis;
* the normalisation of the projection-formula map on the unit section of `𝒪_{T'}` — that is
  `Crystalline.GlobalCrystallineSituation.firstOrderTensorToAmbient_whiskerLeft_inlSheaf'` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderProjectionFormulaUnitSection.lean`,
  unconditional.

Behind the first of those sits the invertibility of the projection-formula map at `p₀`,
`Crystalline.isIso_firstOrderThickeningProjectionFormulaMap` of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderProjectionFormulaIso.lean`, which is
[Stacks, Tag 0FZE] at `p₀` — unconditional on the module, because `p₀` is the identity on
underlying topological spaces.

So this module only composes what those three supply; nothing new is proved here.

## Main results

* `Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison_of_isSheafCrystal` —
  **the identification of [Stacks, Tag 07J6]** for a sheaf crystal.
* `Crystalline.GlobalCrystallineSituation.firstOrderKernelIsoOfIsSheafCrystal` — the same as an
  isomorphism, with `firstOrderKernelIsoOfIsSheafCrystal_hom` identifying its forward map with
  the canonical morphism.

## What is and is not proved

[Stacks, Tag 07J6] itself — a crystal on the small site `Cris(X/S)` has a canonical integrable
connection — is formalized, with no quasi-coherence hypothesis, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalIntegrableConnectionCris.lean`,
in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`: the connection
`crystalConnectionCris : F ⟶ F ⊗ Ω_{X/S}`, a morphism of abelian sheaves on `Cris(X/S)`, and the
theorems `crystalConnectionCris_isConnection` and `crystalConnectionCris_isIntegrable`.  This
module is about the big site `CRIS(X/S)` and carries no attribute for that tag.

The conclusion holds for a sheaf crystal, and the crystal condition is the tag's own hypothesis;
nothing else is assumed; in particular no local quasi-coherence is needed, although
[Stacks, Tag 0FZE] asks for it.  Since `p₀` is the identity on underlying topological spaces
(`Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteP₀_base`), the
projection-formula map at `p₀` is invertible for every sheaf of modules, and that is proved
in `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderProjectionFormulaIso.lean`.

The identification is at the level of **sheaves** of `𝒪_T`-modules, which is where
[Stacks, Tag 07J6] puts it.  The global-sections form is a different statement and is *false* on
a general object; the counterexample is recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean`.

**Integrability is not proved here**, but it is proved: the degree-two analogue of the
identification above — that the canonical morphism

`F_T ⊗_{𝒪_T} Ω²_{T/S,δ} ⟶ q₀_* F_{T''}`

on the second-order universal thickening of [Stacks, Tag 07J3] is a monomorphism — is
`Crystalline.GlobalCrystallineSituation.mono_secondOrderTensorComparison` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderIdealTensorMono.lean`, for a sheaf crystal;
the step that moves `∇(s)` onto that thickening is unconditional, as
`Crystalline.GlobalCrystallineSituation.crystalConnection_restrict_q₁₂'`; and integrability
itself, at the level of sheaves where the source states it, is
`Crystalline.GlobalCrystallineSituation.crystalConnectionSheaf_isIntegrable` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionSheafIntegrable.lean`.  Two earlier
versions of this paragraph described first the degree-two identification and then integrability
as still owed; **both claims are withdrawn**.

What does *not* follow is the global-sections form: both inputs of
`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_comp_self_eq_zero` are statements
about the *algebraic tensor product of global sections*, and neither the degree-one
identification above nor the degree-two one gives such a statement, `Γ` not commuting with `⊗`
on a non-affine `T`.  That is a statement the source does not make.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)

/-- **Stacks Project, Tag 07J6: the identification by which the tag reads `∇(s)` inside
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}`.**  For a sheaf crystal `F` the canonical morphism

`F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker(i^* : p₀_* F_{T'} ⟶ F_T)`

is an isomorphism, so the kernel of restriction along the diagonal — where the values of
`Crystalline.GlobalCrystallineSituation.crystalConnection` live, by
`Crystalline.GlobalCrystallineSituation.crystalConnection_map_ι` — is the module the tag names.

This is `Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison_of_isIso` with
its one input supplied by
`Crystalline.GlobalCrystallineSituation.isIso_ambientSchemeCrystalComparison`, which is the
tag's own crystal hypothesis. -/
theorem isIso_firstOrderKernelComparison_of_isSheafCrystal
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)
    (hM : IsSheafCrystal M) :
    IsIso (firstOrderKernelComparison M A) :=
  isIso_firstOrderKernelComparison_of_isIso M A
    (isIso_ambientSchemeCrystalComparison hM A)

/-- **The identification of [Stacks, Tag 07J6] as an isomorphism**

`F_T ⊗_{𝒪_T} Ω_{T/S,δ} ≅ ker(i^* : p₀_* F_{T'} ⟶ F_T)`,

for a sheaf crystal.  Its forward map is the canonical morphism, by
`Crystalline.GlobalCrystallineSituation.firstOrderKernelIsoOfIsSheafCrystal_hom`. -/
def firstOrderKernelIsoOfIsSheafCrystal (hM : IsSheafCrystal M) :
    firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A) ≅
      firstOrderAmbientKernel M A :=
  firstOrderKernelIsoOfIsIso M A (isIso_ambientSchemeCrystalComparison hM A)

/-- The isomorphism of
`Crystalline.GlobalCrystallineSituation.firstOrderKernelIsoOfIsSheafCrystal` is the canonical
morphism `Crystalline.GlobalCrystallineSituation.firstOrderKernelComparison`. -/
theorem firstOrderKernelIsoOfIsSheafCrystal_hom (hM : IsSheafCrystal M) :
    (firstOrderKernelIsoOfIsSheafCrystal M A hM).hom = firstOrderKernelComparison M A := rfl

end Crystalline.GlobalCrystallineSituation

end

end
