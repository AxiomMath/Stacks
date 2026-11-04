module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleFlatPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback of the family of cycles associated to a closed subscheme

Let `f : X ⟶ S` be locally of finite type, let `i : Z ⟶ X` be a closed subscheme whose fibres
over `S` satisfy `dim(Z_s) ≤ r`, and let `j : U ⟶ X` be flat, locally of finite type and of
relative dimension `e`, viewed as a morphism of schemes over `S` through an identity
`j ≫ f = f_U`. The scheme-theoretic inverse image `Z ∩ U = Z ×_X U` is a closed subscheme of `U`
whose fibres over `S` are the inverse images of the fibres of `Z` along the morphisms
`U_s ⟶ X_s`, which are flat of relative dimension `e`, so those fibres have dimension at most
`r + e` and the family `[Z ×_X U / U / S]_{r+e}` of Example 0H4S is the flat pullback of the
family `[Z/X/S]_r`.

## Main results

* `Stacks.Chow.fibreDim_flatPullbackClosedSubscheme_le` — the fibrewise dimension bound on a
  closed subscheme passes to its inverse image along `j` with `r` replaced by `r + e`.
* `Stacks.Chow.familyAssociatedToClosedSubscheme_flatPullback` — the flat pullback of `[Z/X/S]_r`
  along `j` is `[Z ×_X U / U / S]_{r+e}`.

## References

* [Stacks Project, Tag 0H4T](https://stacks.math.columbia.edu/tag/0H4T)
* [Stacks Project, Tag 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
* [Stacks Project, Tag 0H4S](https://stacks.math.columbia.edu/tag/0H4S)
* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S U Z : Scheme.{u}}

/-! ### The dimension bound on the inverse image -/

/-- The hypothesis `dim(Z_s) ≤ r` of Example 0H4S passes to the scheme-theoretic inverse image
`Z ×_X U` of `Z` along a flat morphism `j : U ⟶ X` of schemes over `S`, locally of finite type and
of relative dimension `e`, with `r` replaced by `r + e`: the fibre over `s` of the inverse image is
the inverse image of `Z_s` along `U_s ⟶ X_s`, which is again flat of relative dimension `e`. -/
theorem fibreDim_flatPullbackClosedSubscheme_le (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ S)
    [LocallyOfFiniteType fU] (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU)
    (e : ℕ) (he : AlgebraicGeometry.RelativeDimension j e) (i : Z ⟶ X) [IsClosedImmersion i]
    (r : ℕ)
    (hZ : ∀ s : S, topologicalKrullDim (pullback i (f.fiberι s) : Scheme.{u}) ≤
      (r : WithBot ℕ∞)) (s : S) :
    topologicalKrullDim (pullback (pullback.snd i j) (fU.fiberι s) : Scheme.{u}) ≤
      ((r + e : ℕ) : WithBot ℕ∞) := by
  have hb := supportDimension_le_of_flatPullback f fU j h e he
    ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) r
    (topologicalKrullDim_supp_pullback_fiberι_le i f hZ) s
  rw [SheafOfModules.supp_eq_of_iso
      ((Scheme.Modules.pullback (fU.fiberι s)).mapIso
        (pullbackPushforwardStructureSheafIso (IsPullback.of_hasPullback i j))),
    supp_pullback_fiberι_pushforwardStructureSheaf (pullback.snd i j) fU s] at hb
  exact le_of_eq_of_le (IsHomeomorph.topologicalKrullDim_eq _
    (IsClosedImmersion.isClosedEmbedding
      (pullback.snd (pullback.snd i j) (fU.fiberι s))).isEmbedding.toHomeomorph.isHomeomorph) hb

/-! ### Tag 0H4T: flat pullback -/

/-- The construction of Example 0H4S is compatible with flat pullback: let `f : X ⟶ S` be locally
of finite type, let `i : Z ⟶ X` be a closed subscheme with `dim(Z_s) ≤ r` for every `s ∈ S`, and
let `j : U ⟶ X` be flat, locally of finite type and of relative dimension `e`, a morphism of
schemes over `S` through `j ≫ f = f_U`. Then the flat pullback of the family `[Z/X/S]_r` along `j`
is the family `[Z ×_X U / U / S]_{r+e}` attached to the scheme-theoretic inverse image of `Z` in
`U`. -/
@[stacks 0H4T "flat pullback"]
theorem familyAssociatedToClosedSubscheme_flatPullback (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j]
    (h : j ≫ f = fU) (e : ℕ) (he : AlgebraicGeometry.RelativeDimension j e) (i : Z ⟶ X)
    [IsClosedImmersion i] (r : ℕ)
    (hZ : ∀ s : S, topologicalKrullDim (pullback i (f.fiberι s) : Scheme.{u}) ≤
      (r : WithBot ℕ∞)) :
    flatPullbackFamily f fU j h e he r (familyAssociatedToClosedSubscheme f i r) =
      familyAssociatedToClosedSubscheme fU (pullback.snd i j) (r + e) := by
  rw [familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule f i r hZ,
    familyAssociatedToModule_flatPullback f fU j h e he
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) r
      (topologicalKrullDim_supp_pullback_fiberι_le i f hZ),
    familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule fU (pullback.snd i j) (r + e)
      (fibreDim_flatPullbackClosedSubscheme_le f fU j h e he i r hZ)]
  exact familyAssociatedToModule_eq_of_iso fU
    (pullbackPushforwardStructureSheafIso (IsPullback.of_hasPullback i j)) (r + e) _ _

end Stacks.Chow

end
