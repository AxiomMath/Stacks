module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.ChartDescent
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Chart generators from generating sections, and Tag 0BD7 reduced to its chart datum

`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/ChartDescent.lean` descends an invertible
module from a cover of the base by opens `chart y ∋ y`, a `Stacks.SheafOfModules.GeneratorSections`
over each `f ⁻¹ᵁ chart y`, and transition units chosen on the base.
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/SectionGenerator.lean` produces, from a
section of `ℒ` whose germ at a point generates the stalk, bijectivity of `c ↦ c • t|_V` for every
small enough `V`. This file turns the second into the first, and uses it to state the conclusion
of [Stacks, Tag 0BD7] in the hypothesis list of the tag itself.

## Main definitions

* `Stacks.SheafOfModules.generatorSectionsOfSubsetNonvanishingLocus`: a global section generating
  everywhere on an open `V`, read as a `GeneratorSections` over `V`.
* `Stacks.SheafOfModules.generatorSectionsOfForallGermNotMemMaximalIdeal`: the same for a section
  over an open `U`, generating at every point of a `V ≤ U` — which is what the chart step of
  Tag 0BD7 has, since `φ^*(g_y) s` is regular only near the fibre and is never global.

## Main results

* `Stacks.SheafOfModules.bijective_smul_congr`: bijectivity of multiplication by a section
  transported along an equality of sections.
* `Stacks.SheafOfModules.exists_generatorSections_of_germ_notMem_maximalIdeal_smul_top`: a section
  whose germ at `x` generates the stalk is, on a neighbourhood of `x`, a `GeneratorSections` —
  and the statement records that it is the restriction of the given section, which is what makes
  the transition units of two such generators computable.
* `Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isIntegral_fiber`: the conclusion
  of Tag 0BD7, from the tag's own hypotheses on `f` together with a chart datum.

## Implementation notes

The last result takes the chart datum as a hypothesis; constructing `chart`, the generators and
the units from the hypotheses of Tag 0BD7 is the content of the first four paragraphs of its
proof. The tag's `IsLocallyNoetherian`, `IsIntegral`, normality and finiteness hypotheses are not
used by the descent, and the fibre hypothesis is used only through
`AlgebraicGeometry.IsIntegral.nonempty`.

`Stacks.SheafOfModules.GeneratorSections` is indexed on `structureSheaf X.sheaf` while the
generating lemmas of `SectionGenerator.lean` are stated over
  `structureSheafRing X`
and multiply by scalars written at `X.presheaf`. The three spellings are equal by `rfl`, but they
are *not* interchangeable for instance search: `HSMul ↑((structureSheaf X.sheaf).obj.obj (op W))`
fails to synthesize where `HSMul ↑(X.presheaf.obj (op W))` succeeds, so a bijectivity statement
written at the first spelling cannot be elaborated at all. Both joins are therefore made by
`bijective_smul_congr`, whose conclusion is *declared* at the synthesizable spelling and whose
section arguments are free variables whose equality `subst` eliminates; the crossing is then a
defeq check against the expected type, which is where the three spellings do agree. A `rw` on the
same equation fails, reporting a goal that is not type-correct at `implicit` transparency.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} (L : SheafOfModules.{u} (structureSheafRing X))

/-- **Bijectivity of multiplication by a section, transported along an equality of sections.**
The two sections are free variables, so `subst` eliminates one of them and the conclusion is
checked against the expected type rather than rewritten into it: that is what crosses the
`structureSheaf X.sheaf` spelling of `GeneratorSections` to the `X.presheaf` spelling at which
the scalar action can be synthesized. -/
theorem bijective_smul_congr {W : Opens X.carrier} {a b : L.val.obj (op W)} (hab : a = b)
    (hb : Function.Bijective fun c : X.presheaf.obj (op W) => c • b) :
    Function.Bijective fun c : X.presheaf.obj (op W) => c • a := hab ▸ hb

/-- Restricting twice along `homOfLE` is restricting once along the composite. -/
private theorem map_map_homOfLE {U V W : Opens X.carrier} (hVU : V ≤ U) (hWV : W ≤ V)
    (t : L.val.obj (op U)) :
    L.val.map (homOfLE hWV).op (L.val.map (homOfLE hVU).op t)
      = L.val.map (homOfLE (hWV.trans hVU)).op t := by
  rw [← L.val.map_comp_apply]
  congr 1

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- **A global section generating everywhere on `V`, as a chart generator over `V`.** If every
point of an open `V` lies in the nonvanishing locus of a global section `s` of an invertible `ℒ`,
then `s|_V` trivializes `ℒ` over `V`, hence over every smaller open, which is exactly a
`Stacks.SheafOfModules.GeneratorSections` over `V`. -/
@[ega "0 5.5.2" "partial"]
def generatorSectionsOfSubsetNonvanishingLocus
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections)
    (V : Opens X.carrier) (hV : (V : Set X.carrier) ⊆ nonvanishingLocus L s) :
    GeneratorSections X L V :=
  ⟨s.eval (op V), fun W hW => by
    have key : L.val.restrictₛₗ (homOfLE hW).op (s.eval (op V)) = s.eval (op W) := by
      rw [PresheafOfModules.restrictₛₗ_apply]
      exact PresheafOfModules.sections_property s (homOfLE hW).op
    exact bijective_smul_congr L key
      (bijective_smul_of_subset_nonvanishingLocus L s W fun _ hw => hV (hW hw))⟩

/-- **A section over `U` generating at every point of `V ≤ U`, as a chart generator over `V`.**
The generalisation of `Stacks.SheafOfModules.generatorSectionsOfSubsetNonvanishingLocus` off
global sections, and the form the chart step of [Stacks, Tag 0BD7] actually needs: there the
generator is `φ^*(g_y) s`, regular only on a neighbourhood `U` of the fibre and never global,
while the chart `V = f ⁻¹ᵁ chart y` is an open neighbourhood of the whole fibre inside `U`. -/
def generatorSectionsOfForallGermNotMemMaximalIdeal
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    {U : Opens X.carrier} (t : L.val.obj (op U)) (V : Opens X.carrier) (hVU : V ≤ U)
    (ht : ∀ (y : X.carrier) (hy : y ∈ V), grpGerm X L.val y U (hVU hy) t ∉
      maximalIdeal (ringStalk X y) • (⊤ : Submodule (ringStalk X y) (grpStalk X L.val y))) :
    GeneratorSections X L V :=
  ⟨L.val.restrictₛₗ (homOfLE hVU).op t, fun K hK => by
    have key : L.val.restrictₛₗ (homOfLE hK).op (L.val.restrictₛₗ (homOfLE hVU).op t)
        = L.val.map (homOfLE (hK.trans hVU)).op t := by
      change L.val.map (homOfLE hK).op (L.val.map (homOfLE hVU).op t) = _
      rw [← L.val.map_comp_apply]
      congr 1
    exact bijective_smul_congr L key
      (bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top L t K (hK.trans hVU)
        fun y hy => ht y (hK hy))⟩

/-- **A section whose germ generates is a chart generator near that point.** This is
`Stacks.SheafOfModules.exists_bijective_smul_of_germ_notMem_maximalIdeal_smul_top` packaged as a
`Stacks.SheafOfModules.GeneratorSections`, which is the form in which the descent of
`ChartDescent.lean` consumes the generators produced by the penultimate paragraph of
[Stacks, Tag 0BD7].

The conclusion records that the generator is the *restriction of the given section* `t` and not
merely some generator over `W`: the transition unit of two chart generators is computed from the
sections themselves, so a generator with no stated relation to `t` would be useless downstream. -/
theorem exists_generatorSections_of_germ_notMem_maximalIdeal_smul_top
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    {U : Opens X.carrier} (t : L.val.obj (op U)) (x : X.carrier) (hxU : x ∈ U)
    (ht : grpGerm X L.val x U hxU t ∉
      maximalIdeal (ringStalk X x) • (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x))) :
    ∃ (W : Opens X.carrier) (_ : x ∈ W) (hWU : W ≤ U) (g : GeneratorSections X L W),
      g.val = L.val.map (homOfLE hWU).op t := by
  obtain ⟨W, hxW, hWU, hbij⟩ :=
    exists_bijective_smul_of_germ_notMem_maximalIdeal_smul_top L t x hxU ht
  refine ⟨W, hxW, hWU, ⟨L.val.map (homOfLE hWU).op t, fun V hV => ?_⟩, rfl⟩
  exact bijective_smul_congr L (map_map_homOfLE L hWU hV t) (hbij V hV)

end Stacks.SheafOfModules

namespace Stacks.InvertiblePullback

open Stacks.SheafOfModules

/-- **The conclusion of [Stacks, Tag 0BD7] from the tag's hypotheses on `f` together with a chart
datum.** For `f` flat with nonempty — in particular integral — fibres, a cover of the base by
opens `chart y ∋ y`, a generator of `ℒ` over each `f ⁻¹ᵁ chart y`, and a unit of
`Γ(Y, chart i ⊓ chart j)` pulling back to the ratio of two chart generators, `ℒ` is the pullback
of an invertible module on the base.

This is `Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_flat_of_inf` restated in
the tag's hypothesis list and conclusion spelling; the fibre hypothesis is used only through
`AlgebraicGeometry.IsIntegral.nonempty`. -/
theorem exists_isInvertible_pullback_iso_of_isIntegral_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (hfiber : ∀ y : Y, IsIntegral (f.fiber y))
    (L : X.Modules) (chart : Y → Y.Opens) (hmem : ∀ y, y ∈ chart y)
    (gen : ∀ y, GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ chart y))
    (hu : ∀ i j : Y, ∃ w : (Γ(Y, chart i ⊓ chart j))ˣ,
      Stacks.PicFinite.pull f (chart i ⊓ chart j) w.val =
        generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ (chart i ⊓ chart j))
          (chartGen gen j inf_le_right) (chartGen gen i inf_le_left)) :
    ∃ (N : Y.Modules) (_ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf) N),
      Nonempty ((Scheme.Modules.pullback f).obj N ≅ L) := by
  obtain ⟨N, hN, hiso⟩ :=
    exists_isInvertible_pullback_iso_of_flat_of_inf gen (fun y => (hfiber y).nonempty) hmem hu
  exact ⟨N, hN, hiso⟩

end Stacks.InvertiblePullback

end
