module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DifferentialFormsSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.UnderlineSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Vanishing07LMProof

/-!
# Remark 60.23.2 of the Stacks project: the vanishing for non-crystals

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF].  [Stacks, Tag 07LN]
observes that the proof of [Stacks, Tag 07LM] gives

`Ru_{X/S, *}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0` for `i > 0`

for every sheaf of `𝒪_{X/S}`-modules `F` satisfying conditions (1) and (2) of
[Stacks, Tag 07JN], and that this applies to two families of sheaves which are not crystals:
the sheaves `Ω^j_{X/S}`, and the sheaves `F̲` attached to a quasi-coherent `𝒪_X`-module `F`, in
particular to `𝒪_X̲ = G_a̲`.

The remark is formalized by four declarations, each stating one whole assertion of it, in the
setting of [Stacks, Tag 07MF] and with no hypothesis beyond the source's:

1. the general statement, for every sheaf of `𝒪_{X/S}`-modules satisfying conditions (1) and (2)
   of [Stacks, Tag 07JN] — `...SmallSite.isZero_derivedZariskiDirectImage_of_vanishingHypotheses`
   of `SmallSite/Vanishing07LMProof.lean`, which is the proof of [Stacks, Tag 07LM] run under
   those two conditions;
2. `Ω^j_{X/S}`, for every `j`, satisfies the two conditions and so has the vanishing —
   `crysFormsSheaf_vanishing`;
3. `F̲`, for every quasi-coherent `𝒪_X`-module `F`, satisfies the two conditions and so has the
   vanishing — `underlineModules_vanishing`;
4. in particular `𝒪_X̲ = G_a̲` does — `underlineStructure_vanishing`.

The remark ends by observing that the *leading* assertion of [Stacks, Tag 07LM] needs a de Rham
complex `F ⊗ Ω^•_{X/S}`, which is produced from the connection of [Stacks, Tag 07J6] and so needs
`F` to be a crystal, and that "(currently)" the sheaves for which the full proposition holds are
the crystals in quasi-coherent modules.  That sentence reports what is known rather than asserting
a mathematical statement — the qualifier "currently" is part of it — so it has no formal
counterpart; the vanishing clause, which is what the remark extends, needs no differential and is
stated above for every sheaf in question.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `...SmallSite.isZero_derivedZariskiDirectImage_of_vanishingHypotheses` of
  `SmallSite/Vanishing07LMProof.lean` — the remark's general statement, for every sheaf of
  modules satisfying conditions (1) and (2).
* `crysFormsSheaf_vanishing` — **the remark for `Ω^j_{X/S}`**: for every `j`, the sheaf
  `Ω^j_{X/S}` satisfies conditions (1) and (2), and `Ru_{X/S, *}(Ω^j_{X/S} ⊗ Ω^i_{X/S}) = 0` for
  `i > 0`.
* `underlineModules_vanishing` — **the remark for `F̲`**: for a quasi-coherent `𝒪_X`-module `F`,
  the sheaf `F̲` satisfies conditions (1) and (2), and `Ru_{X/S, *}(F̲ ⊗ Ω^i_{X/S}) = 0` for
  `i > 0`.
* `underlineStructure_vanishing` — **the remark for `𝒪_X̲ = G_a̲`**, the case `F = 𝒪_X`.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07LN](https://stacks.math.columbia.edu/tag/07LN)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-! ### The sheaves `Ω^j_{X/S}` -/

/-- **Stacks Project, Remark 60.23.2, Tag 07LN, for the sheaves `Ω^j_{X/S}`.**  For every `j`,
the sheaf of `𝒪_{X/S}`-modules `Ω^j_{X/S}` on `Cris(X/S)` — `crysFormsSheaf S j`, the sheaf
associated with the presheaf `Ω^j_{X/S} = ⋀^j Ω_{X/S}` (`toCrysFormsSheaf` is locally bijective,
`isLocallyInjective_toCrysFormsSheaf` and `isLocallySurjective_toCrysFormsSheaf`) — satisfies
conditions (1) and (2) of [Stacks, Tag 07JN], and therefore, for every `i > 0`,

`Ru_{X/S, *}(Ω^j_{X/S} ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`.

Condition (1) is `isLocallyQuasiCoherent_crysFormsSheaf`: the restriction of `Ω^j_{X/S}` to the
ambient scheme `T` of an object is the sheaf associated with the restriction of the presheaf,
that is `Ω^j_{T/S, δ}` ([Stacks, Tag 07IZ]), which is quasi-coherent ([Stacks, Tag 07IY]).
Condition (2) is `isSurjectiveComparison_crysFormsSheaf`: the comparison maps of the presheaf
`Ω^j_{X/S}` are locally surjective ([Stacks, Tag 07KM]), and so are those of its sheaf.  The
vanishing is then `isZero_derivedZariskiDirectImage_of_vanishingHypotheses`. -/
@[stacks 07LN "the sheaves Ω^j_{X/S}, every j: Ω^j_{X/S} satisfies conditions (1) and (2) of \
07JN, hence Ru_{X/S,*}(Ω^j_{X/S} ⊗ Ω^i_{X/S}) = 0 for every i > 0"]
theorem crysFormsSheaf_vanishing (j : ℕ) :
    IsLocallyQuasiCoherent (crysFormsSheaf S j) ∧
      CohomologyRestriction.IsSurjectiveComparison (crysFormsSheaf S j).val ∧
      ∀ i : ℕ, 0 < i →
        IsZero ((derivedZariskiDirectImage S).obj
          (tensorDifferentialFormsSheaf (crysFormsSheaf S j) i)) :=
  ⟨isLocallyQuasiCoherent_crysFormsSheaf j, isSurjectiveComparison_crysFormsSheaf j,
    fun i hi ↦ isZero_derivedZariskiDirectImage_of_vanishingHypotheses S _
      (isLocallyQuasiCoherent_crysFormsSheaf j) (isSurjectiveComparison_crysFormsSheaf j) i hi⟩

/-! ### The sheaves `F̲` -/

/-- **Stacks Project, Remark 60.23.2, Tag 07LN, for the sheaves `F̲`.**  Let `F` be a
quasi-coherent `𝒪_X`-module and `F̲` the sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` with
`F̲(U, T, δ) = F(U)`.  Then `F̲` satisfies conditions (1) and (2) of [Stacks, Tag 07JN] — it is
locally quasi-coherent, and its comparison morphisms `c_f` along the morphisms of `Cris(X/S)`
whose map on ambient schemes is a closed immersion are surjective — and therefore, for every
`i > 0`,

`Ru_{X/S, *}(F̲ ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`.

Condition (1) is `isLocallyQuasiCoherent_underlineModules`: the restriction of `F̲` to the ambient
scheme `T` of `(U, T, δ)` is the direct image of `F|_U` along the closed immersion `U ↪ T`.
Condition (2) is `isSurjectiveComparison_underlineModules`.  The vanishing is then
`isZero_derivedZariskiDirectImage_of_vanishingHypotheses`. -/
@[stacks 07LN "the sheaves F-underline: for F a quasi-coherent O_X-module, F-underline satisfies \
conditions (1) and (2) of 07JN, hence Ru_{X/S,*}(F-underline ⊗ Ω^i_{X/S}) = 0 for every i > 0"]
theorem underlineModules_vanishing (F : S.X.Modules) [F.IsQuasicoherent] :
    IsLocallyQuasiCoherent (underlineModules S F) ∧
      CohomologyRestriction.IsSurjectiveComparison (underlineModules S F).val ∧
      ∀ i : ℕ, 0 < i →
        IsZero ((derivedZariskiDirectImage S).obj
          (tensorDifferentialFormsSheaf (underlineModules S F) i)) :=
  ⟨isLocallyQuasiCoherent_underlineModules F, isSurjectiveComparison_underlineModules F,
    fun i hi ↦ isZero_derivedZariskiDirectImage_of_vanishingHypotheses S _
      (isLocallyQuasiCoherent_underlineModules F) (isSurjectiveComparison_underlineModules F)
      i hi⟩

/-! ### The sheaf `𝒪_X̲ = G_a̲` -/

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] in
/-- **The abelian sheaf underlying `𝒪_X̲` is `G_a̲`**: the sections of `𝒪_X̲` over `(U, T, δ)` are
`Γ(U, 𝒪_U)`, with the restriction maps of `𝒪_X`; that is the sheaf of rings
`underlineRingSheaf` read as a sheaf of abelian groups. -/
theorem underlineModules_unit_presheaf :
    (underlineModules S (SheafOfModules.unit S.X.ringCatSheaf)).val.presheaf =
      (underlineRingSheaf S).obj ⋙ forget₂ RingCat AddCommGrpCat := rfl

/-- **Stacks Project, Remark 60.23.2, Tag 07LN, for `𝒪_X̲ = G_a̲`.**  The sheaf `𝒪_X̲` of
`𝒪_{X/S}`-modules on `Cris(X/S)`, whose sections over `(U, T, δ)` are `Γ(U, 𝒪_U)` — the sheaf
`G_a̲`, `underlineModules_unit_presheaf` — satisfies conditions (1) and (2) of
[Stacks, Tag 07JN], and for every `i > 0`

`Ru_{X/S, *}(𝒪_X̲ ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`.

This is `underlineModules_vanishing` at the quasi-coherent module `𝒪_X`. -/
@[stacks 07LN "the sheaf O_X-underline = G_a-underline: it satisfies conditions (1) and (2) of \
07JN, hence Ru_{X/S,*}(O_X-underline ⊗ Ω^i_{X/S}) = 0 for every i > 0"]
theorem underlineStructure_vanishing :
    IsLocallyQuasiCoherent (underlineModules S (SheafOfModules.unit S.X.ringCatSheaf)) ∧
      CohomologyRestriction.IsSurjectiveComparison
        (underlineModules S (SheafOfModules.unit S.X.ringCatSheaf)).val ∧
      ∀ i : ℕ, 0 < i →
        IsZero ((derivedZariskiDirectImage S).obj
          (tensorDifferentialFormsSheaf (underlineModules S (SheafOfModules.unit S.X.ringCatSheaf))
            i)) :=
  underlineModules_vanishing S _

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
