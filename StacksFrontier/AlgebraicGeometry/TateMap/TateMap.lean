module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.TateMap.SheafClause
public import StacksFrontier.AlgebraicGeometry.TateMap.BaseChange
public import StacksFrontier.AlgebraicGeometry.TateMap.Uniqueness

/-!
# The Tate map

Let `f : Y ⟶ X` be a locally quasi-finite syntomic morphism of locally Noetherian schemes. The
naive cotangent complex `NL_{Y/X}` has an invertible determinant `det(NL_{Y/X})` with a canonical
global section `δ(NL_{Y/X})`, and the relative dualizing module `ω_{Y/X}` has its trace section
`τ_{Y/X}`. This file proves Stacks 0FKD: there is a unique rule assigning to every such `f` an
isomorphism `c_{Y/X} : det(NL_{Y/X}) ≅ ω_{Y/X}` which carries `δ(NL_{Y/X})` to `τ_{Y/X}` and is
compatible with restriction to opens and with base change.

## Main definitions

* `AlgebraicGeometry.TateMap.IsTateRule`: the two properties of a rule.
* `AlgebraicGeometry.TateMap.tateRule`: the rule, the *Tate map*.

## Main results

* `AlgebraicGeometry.TateMap.existsUnique_tateRule`: **Stacks 0FKD.**
* `AlgebraicGeometry.TateMap.isTateRule_tateRule`: the Tate map has the two properties.
* `AlgebraicGeometry.TateMap.isTateRule_iff`: the two properties are equivalent to their form on
  affine charts.

## Implementation notes

A rule is an element of the Π-type `AlgebraicGeometry.TateMap.TateRule`, so two rules are equal
when they assign the same isomorphism to every morphism. The objects of the rule are
`det(NL_{Y/X})` (`AlgebraicGeometry.TateMap.detNL`, the invertible `𝒪_Y`-module whose sections over
every affine chart `Spec B ⊆ Y` over `Spec A ⊆ X` are the determinant of the naive cotangent
complex `NL_{B/A}`, with its section `δ`), `ω_{Y/X}` and `τ_{Y/X}`
(`AlgebraicGeometry.TateMap.omega`, `AlgebraicGeometry.TateMap.tau`, Tags 0BVG and 0BVJ).

Property (2) is the equation `b^* c_{Y/X} = c_{Y'/X'}` of morphisms of `𝒪_{Y'}`-modules for every
morphism `b/a : Y'/X' → Y/X` of the category of Section 0FKB
(`AlgebraicGeometry.TateMap.OpenBaseChangeSquare`), read through the canonical identifications
`AlgebraicGeometry.TateMap.detNLPullbackIso` of `b^* det(NL_{Y/X})` with `det(NL_{Y'/X'})` and
`AlgebraicGeometry.TateMap.omegaPullbackIso` of `b^* ω_{Y/X}` with `ω_{Y'/X'}`. Restriction to
opens is the morphism `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.ofOpens`, base change the
morphism `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.ofIsPullback`.

## References

* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.TateMap

/-- **The two properties of Stacks 0FKD** for a rule `c` assigning to every locally quasi-finite
syntomic morphism `f : Y ⟶ X` with `X` locally Noetherian an isomorphism
`c_{Y/X} : det(NL_{Y/X}) ≅ ω_{Y/X}`:

1. `c_{Y/X}` maps the section `δ(NL_{Y/X})` to `τ_{Y/X}`;
2. for every morphism `b/a : Y'/X' → Y/X` of the category of Section 0FKB, the pullback
   `b^* c_{Y/X}` is `c_{Y'/X'}` under the canonical identifications `b^* det(NL_{Y/X}) ≅
   det(NL_{Y'/X'})` and `b^* ω_{Y/X} ≅ ω_{Y'/X'}`. -/
def IsTateRule (c : TateRule.{u}) : Prop :=
  (∀ (X Y : Scheme.{u}) [IsLocallyNoetherian X] (f : Y ⟶ X) (hf : IsQuasiFiniteSyntomic f),
    (c X Y f hf).hom.app ⊤ (deltaNL f hf) = tau f hf) ∧
  (∀ (X Y X' Y' : Scheme.{u}) [IsLocallyNoetherian X] [IsLocallyNoetherian X']
      (f : Y ⟶ X) (f' : Y' ⟶ X') (hf : IsQuasiFiniteSyntomic f)
      (hf' : IsQuasiFiniteSyntomic f') (sq : OpenBaseChangeSquare f f'),
    (Scheme.Modules.pullback sq.cover).map (c X Y f hf).hom ≫ (omegaPullbackIso hf hf' sq).hom =
      (detNLPullbackIso hf hf' sq).hom ≫ (c X' Y' f' hf').hom)

/-- The two properties are equivalent to their form on compatible affine charts. -/
theorem isTateRule_iff (c : TateRule.{u}) : IsTateRule c ↔ IsTateRuleOnCharts c :=
  ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun _ _ _ _ _ _ f f' hf hf' sq U V U' V' hVU hU'U hV'U' hV'V ↦
      pullbackTate_chartValue_of_comp_eq hf hf' sq _ _ (h₂ _ _ _ _ f f' hf hf' sq) U V U' V'
        hVU hU'U hV'U' hV'V⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun _ _ _ _ _ _ f f' hf hf' sq ↦
      comp_eq_of_pullbackTate_chartValue hf hf' sq _ _ fun U V U' V' hVU hU'U hV'U' hV'V ↦
        h₂ _ _ _ _ f f' hf hf' sq U V U' V' hVU hU'U hV'U' hV'V⟩⟩

/-- **The Tate map**: the rule assigning to a locally quasi-finite syntomic morphism `f : Y ⟶ X`
with `X` locally Noetherian the isomorphism `c_{Y/X} : det(NL_{Y/X}) ≅ ω_{Y/X}`. -/
def tateRule : TateRule.{u} := fun _ _ _ f hf ↦ tateIso f hf

/-- The Tate map carries `δ(NL_{Y/X})` to `τ_{Y/X}` and is compatible with restriction to opens and
with base change. -/
theorem isTateRule_tateRule : IsTateRule tateRule.{u} :=
  (isTateRule_iff _).2 ⟨fun _ _ _ f hf ↦ tateIso_deltaNL f hf,
    fun _ _ _ _ _ _ f f' hf hf' sq U V U' V' hVU hU'U hV'U' hV'V ↦
      tateIso_baseChange f f' hf hf' sq U V U' V' hVU hU'U hV'U' hV'V⟩

/-- **Stacks Project, Tag 0FKD.** There exists a unique rule that to every locally quasi-finite
syntomic morphism of locally Noetherian schemes `Y → X` assigns an isomorphism
`c_{Y/X} : det(NL_{Y/X}) ≅ ω_{Y/X}` such that

1. the section `δ(NL_{Y/X})` is mapped to `τ_{Y/X}`, and
2. the rule is compatible with restriction to opens and with base change.

The source of a locally quasi-finite morphism to a locally Noetherian scheme is locally
Noetherian, so the hypothesis is placed on the target only. -/
@[stacks 0FKD "the unique rule c_{Y/X} : det(NL_{Y/X}) ≅ ω_{Y/X} carrying δ(NL_{Y/X}) to τ_{Y/X}
and compatible with restriction to opens and with base change"]
theorem existsUnique_tateRule : ∃! c : TateRule.{u}, IsTateRule c :=
  ⟨tateRule, isTateRule_tateRule, fun c hc ↦
    eq_of_isTateRule c tateRule ((isTateRule_iff c).1 hc)
      ((isTateRule_iff _).1 isTateRule_tateRule)⟩

end AlgebraicGeometry.TateMap
