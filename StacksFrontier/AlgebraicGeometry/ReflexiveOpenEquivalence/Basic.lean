module

public import StacksFrontier.AlgebraicGeometry.InternalHomLocalKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveDepth.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation

/-!
# Tag 0EBJ from the two preservation statements alone

Let `X` be an integral locally Noetherian scheme and let `U` be an open subscheme whose
complement consists of points where the local ring has depth at least two.  Restriction and
direct image are then inverse equivalences between the coherent reflexive modules on `X` and
those on `U`.  That is [Stacks, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ).

`Stacks.AlgebraicGeometry.ReflexiveModules.reflexiveCoherentEquivalenceOfCoherentDual` states
that conclusion from three hypotheses beyond the ones the source has: Tag 0EBF clause (2), the
direct-image extension step, and finite presentation of the dual of a coherent module.  The
third is not needed as a hypothesis: it is the internal-Hom clause of Tag 01Y2 at `𝒢 = 𝒪_X`, which
`Stacks.AlgebraicGeometry.InternalHomLocalKernel.isCoherent_dualSheaf` proves outright, so it is
discharged here and the statement is reduced to the first two.

## Main results

* `reflexiveCoherentEquivalenceOfPullbackPushforward`: the statement of Tag 0EBJ from the two
  remaining hypotheses.

## Implementation notes

**No `@[stacks 0EBJ]` attribute is attached**: two hypotheses remain, and the tag asserts the
equivalence unconditionally.  They are exactly

* `hpullback` — Tag 0EBF clause (2), that restriction along `U.ι` preserves reflexivity.  Clause
  (1), coherence of a pullback, is `AlgebraicGeometry.isCoherent_pullback` and is already
  discharged inside `reflexiveCoherentEquivalenceOfPreservation`;
* `hpushforward` — the extension step, that the direct image along `U.ι` of a coherent reflexive
  module is again coherent and reflexive.

Everything else the source's proof uses is available: invertibility of the unit is Tag 0E9I,
invertibility of the counit is unconditional, Tag 0EBI part (1) is
`two_le_depth_stalk_of_isReflexive`, and the finite presentation of the dual that part (1) needs
is `isFinitePresentation_dualSheaf` of
`StacksFrontier/AlgebraicGeometry/Reflexive/ExtensionChain/Depth.lean`.

## References

* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- **The statement of Stacks, Tag 0EBJ, from the two preservation hypotheses.**  On an integral
locally Noetherian scheme, restriction to an open subscheme whose complement has structure-sheaf
depth at least two is an equivalence on coherent reflexive modules, with direct image as its
inverse, and both identifications are natural.

This is `reflexiveCoherentEquivalenceOfCoherentDual` with its third hypothesis discharged by
`isFinitePresentation_dualSheaf`.  The hypotheses that remain, `hpullback` and
`hpushforward`, are the two statements the library still lacks; the tag is **withheld** for that
reason. -/
-- stacks attribute for 0EBJ withheld: the tag asserts the equivalence unconditionally, and Tag
-- 0EBF clause (2) and the direct-image extension step are assumed here.
public noncomputable def reflexiveCoherentEquivalenceOfPullbackPushforward (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hpullback : ∀ F : X.Modules, F.IsCoherent → IsReflexive F →
      IsReflexive ((Scheme.Modules.pullback U.ι).obj F))
    (hpushforward : ∀ G : U.toScheme.Modules, G.IsCoherent → IsReflexive G →
      ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent ∧
        IsReflexive ((Scheme.Modules.pushforward U.ι).obj G)) :
    Σ e : ReflexiveCoherentModules X ≌ ReflexiveCoherentModules U.toScheme,
      (e.functor ⋙ ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pullback U.ι) ×
      (e.inverse ⋙ ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pushforward U.ι) :=
  reflexiveCoherentEquivalenceOfCoherentDual X U hdepth hpullback hpushforward
    (fun F hF => have : F.IsCoherent := hF; isFinitePresentation_dualSheaf F)

end Stacks.AlgebraicGeometry.ReflexiveModules

end
