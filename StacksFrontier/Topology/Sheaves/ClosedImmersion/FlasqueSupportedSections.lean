module

public import Mathlib.Topology.Sheaves.Flasque
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.SupportedSectionsOnClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections supported on a closed subset of a flasque abelian sheaf

Let `Z` be a closed subset of a topological space `X`, let `F` be an abelian sheaf on `X` and
let `W` be an open subset of `X`. A section of `F` over `W` is supported on `Z` exactly when it
restricts to zero on `W ∖ Z`, so the sections of `F` over `W` supported on `Z` are the kernel of

`F(W) ⟶ F(W ∖ Z)`.

When `F` is **flasque** that restriction map is surjective, so the kernel sits in a short exact
sequence

`0 ⟶ H_Z(F)(W) ⟶ F(W) ⟶ F(W ∖ Z) ⟶ 0`.

## Main results

* `ClosedImmersionSheaves.mem_supportedSections_iff_restrict_eq_zero`: a section over `W` is
  supported on `Z` if and only if it restricts to zero on `W ∖ Z`.
* `ClosedImmersionSheaves.supportedSections_restriction_shortExact`: for a flasque abelian sheaf
  the inclusion of supported sections and the restriction to `W ∖ Z` form a short exact sequence
  of abelian groups.

## Implementation notes

The complement of `Z` inside `W` is spelled `W ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩` as an open subset of
`X`, so that both ends of the sequence are sections of `F` itself rather than of a restriction
of `F`.

Flasqueness is taken as an explicit hypothesis `TopCat.Presheaf.IsFlasque F.presheaf` rather
than as an instance argument.

## References

* [Stacks Project, Remark 17.5.4 (Tag 01AY)](https://stacks.math.columbia.edu/tag/01AY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry.SheafOfModules (supportedSections supportedSectionsPresheafι)

universe u

namespace ClosedImmersionSheaves

variable {X : TopCat.{u}}

/-- **A section is supported on `Z` exactly when it dies on the complement of `Z`.** For an
abelian sheaf `F` on `X`, a closed subset `Z` and an open `U`, a section of `F` over `U` has all
its germs outside `Z` equal to zero if and only if its restriction to the open set `U ∖ Z`
vanishes. -/
@[sga "2 I 1.8" "partial"]
lemma mem_supportedSections_iff_restrict_eq_zero (Z : Set X) (hZ : IsClosed Z)
    (F : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) (s : F.presheaf.obj (op U)) :
    s ∈ supportedSections Z F (op U) ↔
      F.presheaf.map (homOfLE (inf_le_left : U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ ≤ U)).op s = 0 := by
  refine ⟨fun hs => TopCat.Presheaf.section_ext F _ _ _ fun x hx => ?_, fun hs x hx hxZ => ?_⟩
  · simpa only [map_zero, TopCat.Presheaf.germ_res_apply] using hs x hx.1 hx.2
  · rw [← TopCat.Presheaf.germ_res_apply (F := F.presheaf)
      (homOfLE (inf_le_left : U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ ≤ U)) x ⟨hx, hxZ⟩ s, hs, map_zero]

/-- A supported section restricts to zero on the complement of `Z`, so the inclusion of
supported sections followed by restriction to `W ∖ Z` is the zero map. -/
lemma supportedSections_restriction_zero (Z : Set X) (hZ : IsClosed Z)
    (F : X.Sheaf AddCommGrpCat.{u}) (W : Opens X) :
    (supportedSectionsPresheafι Z F).app (op W) ≫
        F.presheaf.map (homOfLE (inf_le_left : W ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ ≤ W)).op = 0 := by
  ext s
  exact (mem_supportedSections_iff_restrict_eq_zero Z hZ F W s.val).mp s.property

/-- **Supported sections of a flasque abelian sheaf, as a short exact sequence.** Let `Z` be a
closed subset of `X`, let `F` be a flasque abelian sheaf on `X` and let `W` be open. Then

`0 ⟶ H_Z(F)(W) ⟶ F(W) ⟶ F(W ∖ Z) ⟶ 0`

is short exact. -/
@[sga "2 I 1.8" "special case", sga "2 I 1.9" "special case"]
lemma supportedSections_restriction_shortExact (Z : Set X) (hZ : IsClosed Z)
    (F : X.Sheaf AddCommGrpCat.{u}) (hF : TopCat.Presheaf.IsFlasque F.presheaf)
    (W : Opens X) :
    (ShortComplex.mk ((supportedSectionsPresheafι Z F).app (op W))
      (F.presheaf.map (homOfLE (inf_le_left : W ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ ≤ W)).op)
      (supportedSections_restriction_zero Z hZ F W)).ShortExact := by
  have := hF
  refine
    { exact := (ShortComplex.ab_exact_iff_function_exact _).2 fun s => ?_
      mono_f := (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective
      epi_g := inferInstance }
  change _ = 0 ↔ ∃ t : supportedSections Z F (op W), t.val = s
  refine ⟨fun hs => ⟨⟨s, (mem_supportedSections_iff_restrict_eq_zero Z hZ F W s).2 hs⟩, rfl⟩, ?_⟩
  rintro ⟨t, rfl⟩
  exact (mem_supportedSections_iff_restrict_eq_zero Z hZ F W t.val).1 t.2

end ClosedImmersionSheaves

end
