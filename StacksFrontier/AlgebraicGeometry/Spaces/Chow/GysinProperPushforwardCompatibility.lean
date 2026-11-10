module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardContained
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardNonContained
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardRationalEquivalence

/-!
# Stacks 0ER5: the refined Gysin map and proper pushforward

In Situation 0EDT let `f : X' ⟶ X` be a proper morphism of good algebraic spaces over `B`, let
`(ℒ, s, i : D → X)` be as in Definition 0ER1 and form the diagram of Remark 0ER3, with
`ℒ' = f^*ℒ`, `s' = f^*s`, `D' = Z(s') = X' ×_X D` and `g : D' ⟶ D`. **Stacks 0ER5**:

`i^* f_* α' = g_* (i')^* α'` in `CH_k(D)` for every `α' ∈ Z_{k+1}(X')`.

The letter `D` is taken by the dimension situation, so the vanishing loci are `E = Z(s)` and
`E' = Z(s')` in the code.

## Main results

* `AlgebraicGeometry.Space.sectionGysin_properPushforward_eq_chowGroupCanonicalProperPushforward`:
  **Stacks 0ER5**, with `g_*` the proper pushforward on Chow groups of Stacks 0EQC.
* `AlgebraicGeometry.Space.chowClassCanonical_sectionGysin_properPushforward_eq`: the same, with
  `g_*` read on the representative cycle `(i')^* α'`.

## References

* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Assembly

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hfbase : f.hom ≫ p = p') (hf : IsProper D.site D.base D.base_mem f.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

include hL in
/-- **Stacks 0ER5, with `g_*` read on the representative cycle.** In Situation 0EDT let
`f : X' ⟶ X` be a proper morphism of good algebraic spaces over `B`, let `ℒ` be an invertible
`𝒪_X`-module with a global section `s`, `E = Z(s)` with `i : E → X`, and form the diagram of
Remark 0ER3 with `ℒ' = f^*ℒ`, `s' = f^*s`, `E' = Z(s') = X' ×_X E`, `i' : E' → X'` and
`g : E' ⟶ E`. For every `(k+1)`-cycle `α'` on `X'`, the class of `i^* f_* α'` in `CH_k(E)` is the
class of `g_*` of the cycle `(i')^* α'`. -/
theorem chowClassCanonical_sectionGysin_properPushforward_eq (α' : CycleGroup D p' (k + 1)) :
    chowClassCanonical.{u + 1} D ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s) k
        (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (sectionGysinRule D p hp L s k hL)
          (properCyclePushforward D p' hp' p hp hfbase hf.2.1.2 (k + 1) α')) =
      chowClassCanonical.{u + 1} D ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s) k
        (properCyclePushforward D ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
          (isGood_vanishingLocus D p' hp' _ _) ((vanishingLocus D p hp L s).1.ι ≫ p)
          (isGood_vanishingLocus D p hp L s)
          (pullbackVanishingLocusProjection_comp_structure D p hp p' hp' f L s hL hfbase)
          (isProper_pullbackVanishingLocusProjection D p hp p' hp' f L s hL hf).2.1.2 k
          (gysinCycleMap D p' (pullbackSectionVanishingLocus D p hp p' hp' f L s)
            (isGood_vanishingLocus D p' hp' _ _) k
            (sectionGysinRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
              (pullbackGlobalSection D p hp p' hp' f L s) k
              (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL)) α')) :=
  chowClassCanonical_gysin_properPushforward_eq_of_defects D p hp p' hp' f hfbase hf L s hL k
    (fun W' hW' hW'E' =>
      properPushforwardChernDefect_sectionGysinChernRule_eq_zero_of_not_le D p hp p' hp' f hfbase
        hf L s hL k W' hW' hW'E')
    (fun W' hW' hW'E' a =>
      isRationallyEquivalentToZeroWithinCanonical_zsmul_chernDefect_sectionGysinChernRule_of_le
        D p hp p' hp' f hfbase hf L s hL k W'
        (fun g hg hdim c hc => isPrincipalDivisorCycleOfGood_subspaceProperCyclePushforward D p'
          hp' p hp hfbase hf k W' g hg hW' hdim c hc) hW' hW'E' a)
    α'

include hL in
/-- In Situation 0EDT let `f : X' ⟶ X` be a proper morphism of good algebraic spaces over `B`.
Let `(ℒ, s, i : D → X)` be as in Definition 0ER1: `ℒ` an invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)`,
`D = Z(s)` its vanishing locus (here `E`, the letter `D` being the dimension situation) and `i`
the closed immersion. Form the diagram of Remark 0ER3

```
E' --i'--> X'
|          |
g          f
|          |
v          v
E  --i-->  X
```

with `ℒ' = f^*ℒ`, `s' = f^*s` and `E' = Z(s') = X' ×_X E`
(`AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus`). Then for every `(k+1)`-cycle `α'`
on `X'`

`i^* f_* α' = g_* (i')^* α'` in `CH_k(E)`,

where `i^*` and `(i')^*` are the refined Gysin homomorphisms `Z_{k+1}(·) → CH_k(·)` of
Stacks 0ER1 of the two triples, at their constructed component rules
(`AlgebraicGeometry.Space.sectionGysinRule`: clause (1)(a) the cycle `[E ∩ W]_k` of Stacks 0EE9,
clause (1)(b) `c₁(ℒ|_W) ∩ [W]`), `f_*` is proper pushforward of cycles (Stacks 0EP1), the Chow
groups are those of Stacks 0EQ6 (`AlgebraicGeometry.Space.chowGroupCanonical`, `div(f)` read at
the canonical embeddings of Stacks 0ENK) and `g_*` is proper pushforward on Chow groups,
Stacks 0EQC (`AlgebraicGeometry.Space.chowGroupCanonicalProperPushforward`). -/
@[stacks 0ER5 "i^* f_* α' = g_* (i')^* α' in CH_k(D) for f : X' → X proper between good \
algebraic spaces over B, (L, s, i : D → X) as in 0ER1 and the diagram of 0ER3 (L' = f^*L, \
s' = f^*s, D' = Z(s') = X' ×_X D): both Gysin maps are 0ER1's at the constructed rules \
sectionGysinRule, CH_k = chowGroupCanonical of 0EQ6, f_* the proper pushforward of cycles of 0EP1 \
and g_* the proper pushforward on Chow groups of 0EQC; unconditional"]
theorem sectionGysin_properPushforward_eq_chowGroupCanonicalProperPushforward
    (α' : CycleGroup D p' (k + 1)) :
    chowClassCanonical.{u + 1} D ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s) k
        (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (sectionGysinRule D p hp L s k hL)
          (properCyclePushforward D p' hp' p hp hfbase hf.2.1.2 (k + 1) α')) =
      chowGroupCanonicalProperPushforward.{u + 1} D
        ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _)
        ((vanishingLocus D p hp L s).1.ι ≫ p) (isGood_vanishingLocus D p hp L s)
        (pullbackVanishingLocusProjection_comp_structure D p hp p' hp' f L s hL hfbase)
        (isProper_pullbackVanishingLocusProjection D p hp p' hp' f L s hL hf) k
        (chowClassCanonical.{u + 1} D
          ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
          (isGood_vanishingLocus D p' hp' _ _) k
          (gysinCycleMap D p' (pullbackSectionVanishingLocus D p hp p' hp' f L s)
            (isGood_vanishingLocus D p' hp' _ _) k
            (sectionGysinRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
              (pullbackGlobalSection D p hp p' hp' f L s) k
              (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL)) α')) := by
  rw [chowGroupCanonicalProperPushforward_chowClassCanonical]
  exact chowClassCanonical_sectionGysin_properPushforward_eq D p hp p' hp' f hfbase hf L s hL k α'

end Assembly

end AlgebraicGeometry.Space

end
