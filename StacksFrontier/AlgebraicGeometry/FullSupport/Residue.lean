module

public import StacksFrontier.AlgebraicGeometry.FullSupport.Basic
public import StacksFrontier.AlgebraicGeometry.StalkBridge.Basic
public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.KilledSupport

/-!
# [Stacks, Tag 01YH] from exactly two hypotheses: [Stacks, Tag 01YE] and the top-stratum ideals

`ConfinedDevissage.property_of_irreducible_support_of_topIdeals_of_genericIsoSub`
proves the conclusion of Tag 01YH from
`Stacks.AlgebraicGeometry.ConfinedDevissage.HasKilledIdealGenericIsoSubIn`
and `htop`, and, in the namespace `Stacks.AlgebraicGeometry`,
`Tag01YEStalkBridge.hasKilledIdealGenericIsoSubIn_of_hasGenericStalkIdealCoproductSub`
derives the first of those from
`Stacks.AlgebraicGeometry.Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub`, which is the conclusion of Tag
01YE restated over library names. As the implementation notes of
`StacksFrontier/AlgebraicGeometry/StalkBridge/Basic.lean` explain, the composite reduces Tag 01YH to
Tag 01YE plus `htop`. This file states the composite, so that what remains of Tag 01YH is a single
theorem with two hypotheses.

## Main results

* `Stacks.AlgebraicGeometry.Tag01YHFullSupport.property_of_irreducible_support_of_tag01YE`:
  **the conclusion of Tag 01YH from its own hypotheses together with exactly two further
  assumptions** — the conclusion of [Stacks, Tag 01YE], and `htop`.

## Implementation notes

`hexact`, `hproper` and the module `G` are copied verbatim from the statement of Tag 01YH; `G` is all
that is used of its hypothesis (3), because the length-one and annihilation conditions are what a
proof of `htop` would consume. Neither `IsClosed Z₀` nor `IsIrreducible Z₀` nor the tag's
generic point `ξ` appears, for the reason given with
`ConfinedDevissage.property_of_irreducible_support_of_topIdeals_of_genericIsoSub`: the source
uses the irreducibility of `Z₀` only inside the two hypotheses that remain.

**What `htop` needs.** Three steps, of which the third is discharged here:

1. the conclusion of [Stacks, Tag 01YE] applied to `G` — the hypothesis `h01YE` here;
2. that the multiplicity `r` it produces is `1`, which is where the length-one condition of
   hypothesis (3) of Tag 01YH is consumed. No statement relating `Module.length` of a stalk to a
   finite coproduct of module sheaves exists in the library; the condition is recorded in prose
   only;
3. the intersection argument of the source's last paragraph, whose geometric input — a nonzero
   quasi-coherent sheaf of ideals on an integral scheme has full support — is
   `Stacks.AlgebraicGeometry.Tag01YHFullSupport.supp_eq_univ_of_not_isZero` in `./Basic.lean`.
   What is still missing there is sheaf-level plumbing rather than geometry: quasi-coherence of the
   intersection of two quasi-coherent submodules of the structure sheaf, and the passage from
   full support to strict containment of the support of the two quotients.

**No `@[stacks]` attribute is attached.** Tag 01YH has a single unlabelled assertion, and the
theorem below carries two hypotheses the tag does not grant.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.Tag01YHFullSupport

variable {X : Scheme.{u}} (P : X.Modules → Prop)

/-- **[Stacks, Tag 01YH] from the conclusion of [Stacks, Tag 01YE] and the top-stratum ideals.**
The conclusion of Tag 01YH — `P` on every coherent module supported inside `Z₀` — from its
two-out-of-three hypothesis `hexact`, its hypothesis `hproper` on integral closed subschemes
strictly inside `Z₀`, one coherent module `G` satisfying `P`, and exactly two further
assumptions: `h01YE`, the conclusion of [Stacks, Tag 01YE] as a predicate on `X`, and `htop`,
`P` on the direct image of every quasi-coherent ideal sheaf on every integral closed subscheme
whose range is **all** of `Z₀`.

This is the composite of
`ConfinedDevissage.property_of_irreducible_support_of_topIdeals_of_genericIsoSub`
with
`Tag01YEStalkBridge.hasKilledIdealGenericIsoSubIn_of_hasGenericStalkIdealCoproductSub`;
no new mathematics is added, and the point of recording it is that what remains of Tag 01YH is
then exactly these two propositions. -/
theorem property_of_irreducible_support_of_tag01YE [IsNoetherian X]
    (h01YE : Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub X)
    {Z₀ : Set X}
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hproper : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base ⊂ Z₀ →
      ∀ (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
        [I.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (htop : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base = Z₀ →
      ∀ (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
        [I.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (G : X.Modules) (hG : G.IsCoherent) (hPG : P G) :
    ∀ F : X.Modules, F.IsCoherent → SheafOfModules.supp F ⊆ Z₀ → P F :=
  ConfinedDevissage.property_of_irreducible_support_of_topIdeals_of_genericIsoSub P
    (Tag01YEStalkBridge.hasKilledIdealGenericIsoSubIn_of_hasGenericStalkIdealCoproductSub X h01YE)
    hexact hproper htop G hG hPG

end Stacks.AlgebraicGeometry.Tag01YHFullSupport

end
