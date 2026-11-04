module

public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.PointClosureSquare
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureCoherence
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.StructureSheafMono
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.ResidueField

/-!
# The comparison monomorphism of [Stacks, Tag 0AWA] over an open subscheme

Let `X` be a locally Noetherian scheme, `V : X.Opens` an open subscheme, `x` a point of `V` and
`p = V.ι x` its image. Let `π : Y ⟶ X` be the normalization of `X` in `Spec κ(p)` and
`G = π_* 𝒪_Y`. The second paragraph of [Stacks, Tag 0AWA] uses that the module
`i_{x,*} 𝒪_{W_x}` of the reduced closure of `{x}` in `V` is a submodule of `G|_V`. This file
proves exactly that.

Over `X` the statement is the dominance of `Y ⟶ closure{p}`: that factorization is
scheme-theoretically dominant, so `i_{p,*} 𝒪_{Z_p} ⟶ G` is a monomorphism of `𝒪_X`-modules by
[Stacks, Tag 0AVL]. Restricting to `V` keeps it monic because restriction along an open
immersion is left exact, and `(i_{p,*} 𝒪_{Z_p})|_V` is `i_{x,*} 𝒪_{W_x}` by the inverse-image
comparison across the cartesian square of point closures of [Stacks, Tag 0BK2].

## Main results

* `Stacks.LocalCohomology.exists_mono_pullback_residueFieldNormalizationPushforward`:
  `i_{x,*} 𝒪_{W_x}` is a submodule of the restriction to `V` of `G = π_* 𝒪_Y`.

## Implementation notes

The monomorphism over `X` is `AlgebraicGeometry.Scheme.Hom.exists_mono_pushforward_unit_of_comp_eq`
applied to the factorization `AlgebraicGeometry.Scheme.residueFieldNormalizationToPointClosure`,
and the identification of the restricted point closure is
`AlgebraicGeometry.Scheme.Modules.pullbackPointClosureIso`. Monicity is transported from
restriction to the inverse image along the natural isomorphism
`Scheme.Modules.restrictFunctorIsoPullback`, so that the conclusion is stated for
`Scheme.Modules.pullback V.ι`, which is the functor the consumers use.

`AlgebraicGeometry.Scheme.Modules` is a `def`, so a monomorphism of `𝒪_V`-modules is not found
by instance search at the sheaf-of-modules spelling; the intermediate monomorphisms are pinned
with `Mono (C := V.toScheme.Modules)`.

## References

* [Stacks Project, Tag 0AWA](https://stacks.math.columbia.edu/tag/0AWA)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
* [Stacks Project, Tag 0BK2](https://stacks.math.columbia.edu/tag/0BK2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.LocalCohomology

/-- **The comparison monomorphism of the second paragraph of [Stacks, Tag 0AWA].** For a point
`x` of an open subscheme `V` of a locally Noetherian scheme `X`, the module `i_{x,*} 𝒪_{W_x}` of
the reduced closure of `{x}` in `V` is a submodule of the restriction to `V` of `G = π_* 𝒪_Y`,
for `π : Y ⟶ X` the normalization of `X` in `Spec κ(V.ι x)`. -/
theorem exists_mono_pullback_residueFieldNormalizationPushforward {X : Scheme.{u}}
    [IsLocallyNoetherian X] (V : X.Opens) (x : V.toScheme) :
    ∃ φ : pointClosureStructureSheaf x ⟶ (Scheme.Modules.pullback V.ι).obj
        ((Scheme.Modules.pushforward
          (X.fromSpecResidueField (V.ι.base x)).fromNormalization).obj
          (SheafOfModules.unit.{u}
            (X.fromSpecResidueField (V.ι.base x)).normalization.ringCatSheaf)),
      Mono φ := by
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  obtain ⟨j', _, hcomm⟩ := Scheme.IdealSheafData.exists_isOpenImmersion_pointClosure V.ι x
  obtain ⟨ψ, hψ⟩ := Scheme.Hom.exists_mono_pushforward_unit_of_comp_eq _ _ _
    (Scheme.residueFieldNormalizationToPointClosure_subschemeι X (V.ι.base x))
  have hpf : PreservesFiniteLimits (Scheme.Modules.restrictFunctor V.ι) :=
    AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor V.ι
  have hres : (Scheme.Modules.restrictFunctor V.ι).PreservesMonomorphisms := by
    have := hpf.preservesFiniteLimits WalkingCospan
    infer_instance
  have hpull : (Scheme.Modules.pullback V.ι).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso (Scheme.Modules.restrictFunctorIsoPullback V.ι)
  refine ⟨(Scheme.Modules.pullbackPointClosureIso V x j' hcomm).inv ≫
    (Scheme.Modules.pullback V.ι).map ψ, ?_⟩
  have h1 : Mono (C := V.toScheme.Modules) ((Scheme.Modules.pullback V.ι).map ψ) :=
    @Functor.map_mono _ _ _ _ _ hpull _ _ _ hψ
  infer_instance

end Stacks.LocalCohomology

end
