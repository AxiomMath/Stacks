module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputQuasiCompact

/-!
# The completion of a proper modification is a formal modification

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of algebraic
spaces over `S`, let `T ⊆ |X|` be closed, `U = X ∖ T` and `U' = f⁻¹U`, as in Section 0GDB.
**Stacks 0GDM** says that if `X` is locally Noetherian, `f` is proper and `U' → U` is an
isomorphism, then `f_{/T} : X'_{/T'} ⟶ X_{/T}` is a formal modification.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalModification_completionSheafMap`: **Stacks 0GDM**.

## Implementation notes

The source's proof cites Stacks 0AQ1 for the local Noetherianity of both completions and Stacks
0GDD, 0AR2, 0AQW and 0GDI for the four conditions of Definition 0GDK. All but 0AR2 are assembled
in `AlgebraicGeometry.FormalSpace.isFormalModification_completionSheafMap_of_isRigEtale`; 0AR2 is
`AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap_of_isEtale`, applied to the proper,
hence locally of finite type, morphism `f`, whose restriction `U' → U` is an isomorphism and so
étale. The isomorphism `U' → U` is recorded as the base change of `f` along `U ⊆ X`, which is
`U' → U` by `AlgebraicGeometry.Space.isPullback_openComplementRestriction`.

## References

* [Stacks Project, Tag 0GDM](https://stacks.math.columbia.edu/tag/0GDM)
* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- **Stacks 0GDM.** Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S`, let `T ⊆ |X|`
be closed and let `U ⊆ X` be the open subspace with `|U| = |X| ∖ T`. If `X` is locally
Noetherian, `f` is proper and `U' = f⁻¹U ⟶ U` is an isomorphism, then
`f_{/T} : X'_{/T'} ⟶ X_{/T}` is a formal modification. -/
@[stacks 0GDM]
theorem isFormalModification_completionSheafMap {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X) (f : X' ⟶ X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (hf : Space.IsProper B S hS f)
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι)) :
    IsFormalModification B S hS (Space.completionSheafMap B S hS f T) :=
  isFormalModification_completionSheafMap_of_isRigEtale hX' hX hXN f T hT hf hfU
    (isRigEtale_completionSheafMap_of_isEtale hX' hX f T hT hXN hf.2.1.1
      (Space.isEtale_openComplementRestriction B S hS f T hfU))

end AlgebraicGeometry.FormalSpace

end
