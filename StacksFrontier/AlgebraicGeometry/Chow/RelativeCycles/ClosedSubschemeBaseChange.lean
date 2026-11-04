module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleGeneralBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the family of cycles associated to a closed subscheme

Let `f : X ⟶ S` be locally of finite type, let `i : Z ⟶ X` be a closed subscheme whose fibres
over `S` satisfy `dim(Z_s) ≤ r`, and let `g : S' ⟶ S` be an arbitrary morphism of schemes. The
inverse image `Z ×_X (X ×_S S')` of `Z` in `X ×_S S'` is a closed subscheme whose fibres over
`S'` are the base changes of the fibres of `Z` along the extensions `κ(t)/κ(g t)` of residue
fields, so it again satisfies the dimension bound, and the family
`[Z ×_X (X ×_S S')/X ×_S S'/S']_r` of Example 0H4S is the base change of the family `[Z/X/S]_r`.

## Main results

* `Stacks.Chow.fibreDim_baseChangeClosedSubscheme_le` — the fibrewise dimension bound on a closed
  subscheme survives base change along an arbitrary morphism of bases.
* `Stacks.Chow.familyAssociatedToClosedSubscheme_baseChange` — **Tag 0H4T, base change.**

## Implementation notes

The proof is the one of the source: with `F = (Z ⟶ X)_* 𝒪_Z` the family `[Z/X/S]_r` is the
family `[F/X/S]_r` of Example 0H4Q, which is
`Stacks.Chow.familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule` — Chow Homology,
Lemma 02QY, on each fibre — so the statement is the base-change clause of Lemma 0H4R,
`Stacks.Chow.familyAssociatedToModule_baseChange_general`, applied to that module. The inverse
image of `i_* 𝒪_Z` along `X ×_S S' ⟶ X` is the direct image of the structure sheaf of the base
change of `Z`, by `Stacks.Chow.pullbackPushforwardStructureSheafIso`, which needs no flatness
because a closed immersion is affine; isomorphic modules have the same associated family.

The same isomorphism supplies the dimension bound on the base-changed subscheme, which is not
assumed: the support of `i_* 𝒪_Z` on a fibre is the image of the fibre of `Z`, homeomorphic to it
because the immersion of fibres is closed, so the bound on the fibrewise supports produced by
`Stacks.Chow.supportDimension_le_of_baseChange_general` is a bound on the fibres themselves.

## References

* [Stacks Project, Tag 0H4T](https://stacks.math.columbia.edu/tag/0H4T)
* [Stacks Project, Tag 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
* [Stacks Project, Tag 0H4S](https://stacks.math.columbia.edu/tag/0H4S)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S S' Z : Scheme.{u}}

/-! ### The dimension bound on the base-changed subscheme -/

/-- **Stacks Project, Tag 0H4T.** The hypothesis `dim(Z_s) ≤ r` of Example 0H4S survives base
change along an arbitrary morphism `g : S' ⟶ S` of bases: the fibre over `t` of the inverse image
of `Z` in `X ×_S S'` is the base change of `Z_{g t}` along `κ(t)/κ(g t)`, whose dimension does
not grow.

Through `Stacks.Chow.supp_pullback_fiberι_pushforwardStructureSheaf` the fibre of the inverse
image is homeomorphic to the support of the restriction of `(pullback.fst f g)^*(i_* 𝒪_Z)` to the
fibre, so this is the module statement
`Stacks.Chow.supportDimension_le_of_baseChange_general`. -/
theorem fibreDim_baseChangeClosedSubscheme_le (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ)
    (hZ : ∀ s : S, topologicalKrullDim (pullback i (f.fiberι s) : Scheme.{u}) ≤
      (r : WithBot ℕ∞)) (t : S') :
    topologicalKrullDim (pullback (pullback.snd i (pullback.fst f g))
        ((pullback.snd f g).fiberι t) : Scheme.{u}) ≤ (r : WithBot ℕ∞) := by
  have hb := supportDimension_le_of_baseChange_general f g
    ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) r
    (topologicalKrullDim_supp_pullback_fiberι_le i f hZ) t
  rw [SheafOfModules.supp_eq_of_iso
      ((Scheme.Modules.pullback ((pullback.snd f g).fiberι t)).mapIso
        (pullbackPushforwardStructureSheafIso
          (IsPullback.of_hasPullback i (pullback.fst f g)))),
    supp_pullback_fiberι_pushforwardStructureSheaf (pullback.snd i (pullback.fst f g))
      (pullback.snd f g) t] at hb
  exact le_of_eq_of_le (IsHomeomorph.topologicalKrullDim_eq _
    (IsClosedImmersion.isClosedEmbedding (pullback.snd (pullback.snd i (pullback.fst f g))
      ((pullback.snd f g).fiberι t))).isEmbedding.toHomeomorph.isHomeomorph) hb

/-! ### Tag 0H4T: base change -/

/-- **Stacks Project, Tag 0H4T (base change).** The construction of Example 0H4S is compatible
with base change: let `f : X ⟶ S` be locally of finite type, let `i : Z ⟶ X` be a closed
subscheme with `dim(Z_s) ≤ r` for every `s ∈ S`, and let `g : S' ⟶ S` be an arbitrary morphism of
schemes. Then the base change of the family `[Z/X/S]_r` along `g` is the family attached to the
inverse image `Z ×_X (X ×_S S')` of `Z` in `X ×_S S'`.

With `F = i_* 𝒪_Z` the family `[Z/X/S]_r` is `[F/X/S]_r` by Chow Homology, Lemma 02QY, read on
each fibre, so this is the base-change clause of Lemma 0H4R applied to `F`, together with the
identification of the inverse image of `F` with the direct image of the structure sheaf of the
base change of `Z`. -/
@[stacks 0H4T "base change"]
theorem familyAssociatedToClosedSubscheme_baseChange (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ)
    (hZ : ∀ s : S, topologicalKrullDim (pullback i (f.fiberι s) : Scheme.{u}) ≤
      (r : WithBot ℕ∞)) :
    baseChangeFamily f g r (familyAssociatedToClosedSubscheme f i r) =
      familyAssociatedToClosedSubscheme (pullback.snd f g)
        (pullback.snd i (pullback.fst f g)) r := by
  rw [familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule f i r hZ,
    familyAssociatedToModule_baseChange_general f g
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) r
      (topologicalKrullDim_supp_pullback_fiberι_le i f hZ),
    familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule (pullback.snd f g)
      (pullback.snd i (pullback.fst f g)) r (fibreDim_baseChangeClosedSubscheme_le f g i r hZ)]
  exact familyAssociatedToModule_eq_of_iso (pullback.snd f g)
    (pullbackPushforwardStructureSheafIso (IsPullback.of_hasPullback i (pullback.fst f g))) r _ _

end Stacks.Chow

end
