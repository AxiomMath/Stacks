module

public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper pushforward of the cycle of a coherent sheaf on a variety

Let `k` be a field, let `X` and `Y` be varieties over `k` and let `f : X ⟶ Y` be a proper
morphism over `k`. For a coherent `𝒪_X`-module `F` whose support has dimension at most `n`,
proper pushforward of `n`-cycles carries the cycle of `F` to the cycle of its direct image:
`f_* [F]_n = [f_* F]_n`. In particular, for a closed subscheme `i : Z ⟶ X` of dimension at most
`n` this reads `f_* [Z]_n = [f_* 𝒪_Z]_n`.

This is the intersection-theory chapter's reading of Chow homology's
`Stacks.Chow.properPushforward_cycleAssociatedToCoherentSheaf` (Stacks 02R6): the chapter works
over a fixed field with the Chow situation whose base is `Spec k` and whose dimension function
vanishes, which is `Stacks.Chow.fieldChowSituation`. Over that base the delta-dimension of a
scheme locally of finite type over `k` is its topological dimension, so the chapter's hypothesis
`dim(Supp(F)) ≤ n` is the delta-dimension bound appearing below; the identification is
`Stacks.Chow.schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq`.

## Main results

* `Stacks.Intersection.properPushforward_coherentSheafCycle` — Stacks 0AZD for a coherent sheaf.
* `Stacks.Intersection.properPushforward_closedSubschemeCycle` — Stacks 0AZD for a closed
  subscheme.

## Implementation notes

A variety over `k` is `AlgebraicGeometry.IsVariety`: an integral scheme whose structure morphism
to `Spec k` is separated and of finite type. The structure morphisms are written with target
`(Stacks.Chow.fieldChowSituation k).S` rather than `Spec k`, which is the spelling the cycle
groups of the situation are formed at; the two schemes agree definitionally.

The degree of the cycle is written `n`, since `k` denotes the ground field here; the source
writes it `k`.

The conventions of the source chapter fix an algebraically closed ground field. Neither clause
below needs that, so both are stated over an arbitrary field and specialise to the source's
setting; likewise neither needs `f` to be projective, finite, flat or surjective.

Coherence of the direct image `f_* F` is the proper mapping theorem, Stacks 02O5, proved as
`AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward`; it is what makes the
right-hand cycle `[f_* F]_n` expressible at all. Neither statement assumes it: each installs it
with `haveI` inside the statement, using that `Y`, being of finite type over a field, is locally
Noetherian. The delta-dimension bound on the support of the direct image is not assumed either:
it is supplied by `Stacks.Chow.schemeDeltaDimension_reducedSupport_pushforward_le`.

## References

* [Stacks Project, Tag 0AZD](https://stacks.math.columbia.edu/tag/0AZD)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Serre, *Algèbre locale*, Chapter V](Serre_algebre_locale)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.Chow

universe u

namespace Stacks.Intersection

variable {X Y : Scheme.{u}}

/-- **Stacks 0AZD.** Let `f : X ⟶ Y` be a proper morphism of varieties over a field `k` and let
`F` be a coherent `𝒪_X`-module whose support has dimension at most `n`. Then proper pushforward
of `n`-cycles carries the cycle of `F` to the cycle of its direct image: `f_* [F]_n = [f_* F]_n`.

This is Stacks 02R6 at the Chow situation `Stacks.Chow.fieldChowSituation k`, whose base is
`Spec k` and whose dimension function vanishes; over that base the delta-dimension of the
support of `F` is its dimension. -/
@[stacks 0AZD "cycle identity for a coherent sheaf"]
theorem properPushforward_coherentSheafCycle (k : Type u) [Field k]
    (sX : X ⟶ (fieldChowSituation k).S) [IsVariety k sX]
    (sY : Y ⟶ (fieldChowSituation k).S) [IsVariety k sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (F : X.Modules) [F.IsCoherent] (n : ℤ)
    (hFn : schemeDeltaDimension (fieldChowSituation k)
      ((reducedSupport F).subschemeι ≫ sX) ≤ (n : EInt)) :
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI := ProperCoherenceWitness.isCoherent_pushforward f F
    properPushforward (fieldChowSituation k) sX sY f hf n
        (cycleAssociatedToCoherentSheaf (fieldChowSituation k) sX F n hFn) =
      cycleAssociatedToCoherentSheaf (fieldChowSituation k) sY
        ((Scheme.Modules.pushforward f).obj F) n
        (schemeDeltaDimension_reducedSupport_pushforward_le
          (fieldChowSituation k) sX sY f hf F hFn) :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have := ProperCoherenceWitness.isCoherent_pushforward f F
  Stacks.Chow.properPushforward_cycleAssociatedToCoherentSheaf
    (fieldChowSituation k) sX sY f hf F n hFn

/-- **Stacks 0AZD.** Let `f : X ⟶ Y` be a proper morphism of varieties over a field `k` and let
`i : Z ⟶ X` be a closed subscheme of dimension at most `n`. Then proper pushforward of
`n`-cycles carries the cycle of `Z` to the cycle of the direct image of its structure sheaf:
`f_* [Z]_n = [f_* 𝒪_Z]_n`.

Here `𝒪_Z` is read as the coherent `𝒪_X`-module `i_* 𝒪_Z`, and `f_* 𝒪_Z` as the direct image of
that module along `f`. This is Stacks 02R6, part (1), at the Chow situation
`Stacks.Chow.fieldChowSituation k`. -/
@[stacks 0AZD "closed subscheme"]
theorem properPushforward_closedSubschemeCycle (k : Type u) [Field k] {Z : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [IsVariety k sX]
    (sY : Y ⟶ (fieldChowSituation k).S) [IsVariety k sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℤ)
    (hZ : schemeDeltaDimension (fieldChowSituation k) (i ≫ sX) ≤ (n : EInt)) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI := ProperCoherenceWitness.isCoherent_pushforward f
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
    properPushforward (fieldChowSituation k) sX sY f hf n
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX i n) =
      cycleAssociatedToCoherentSheaf (fieldChowSituation k) sY
        ((Scheme.Modules.pushforward f).obj
          ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))) n
        (schemeDeltaDimension_reducedSupport_pushforward_le (fieldChowSituation k) sX sY f hf
          ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
          (schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le
            (fieldChowSituation k) sX i hZ)) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have := ProperCoherenceWitness.isCoherent_pushforward f
    ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
  Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme
    (fieldChowSituation k) sX sY f hf i n hZ

end Stacks.Intersection

end
