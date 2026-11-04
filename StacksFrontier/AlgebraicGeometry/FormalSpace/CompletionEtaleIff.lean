module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartLocalizationDiagram
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleFromCompletionSpace

/-!
# Étaleness of a modification and of its completion

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian algebraic
space over `S`, let `T ⊆ |X|` be a closed subset and let `U ⊂ X` be the open subspace with
`|U| = |X| ∖ T`. **Stacks 0GI4** says that a morphism `f : X' ⟶ X` of algebraic spaces which is
locally of finite type and an isomorphism over `U` is étale exactly when the morphism
`g : W ⟶ X_{/T}` of formal algebraic spaces corresponding to it under the equivalence of
Stacks 0ARB (`AlgebraicGeometry.FormalSpace.isEquivalence_completionModificationFunctor`) is
étale.

## Main results

* `AlgebraicGeometry.FormalSpace.isEtale_iff_isRepresentableEtale_of_overIso`:
  **Stacks 0GI4**.

## Implementation notes

*The correspondence.* The functor of Stacks 0AR5 and 0ARB,
`AlgebraicGeometry.FormalSpace.completionModificationFunctor`, sends `f` to its completion
`f_{/T} : X'_{/T'} ⟶ X_{/T}` (`AlgebraicGeometry.Space.completionSheafMap`), so `g` corresponds
to `f` exactly when `g` is isomorphic over `X_{/T}` to `f_{/T}`. The statement takes that
isomorphism `e` as its datum, as Stacks 0ARU does in
`AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_isQuasiCompact_of_overIso`. No condition is put
on `W` or `g`: being isomorphic to `f_{/T}`, the morphism `g` automatically lies in the target
category of Stacks 0ARB.

*Étaleness of `g`* is the Bootstrap condition of Stacks 03XZ for étaleness,
`AlgebraicGeometry.FormalSpace.IsRepresentableEtale`: `g` is representable by algebraic spaces
and each of its base changes along a scheme-valued point is étale. This is the notion of
Stacks 0GI0 (`AlgebraicGeometry.FormalSpace.isEtale_completionSheafMap`).

*The proof* is the source's. If `f` is étale, so is `f_{/T}` by Stacks 0GI0. Conversely, `f` is
étale over `U` since it is an isomorphism there, and above `T` the étaleness of `f_{/T}` makes
every base change `Xₙ' = X' ×_X Zₙ ⟶ Zₙ` to an infinitesimal neighbourhood of the reduced
closed subspace on `T` étale, so `f` is étale above `T` by Stacks 0APQ. This is the étale clause
of Stacks 0AR4 for algebraic spaces,
`AlgebraicGeometry.FormalSpace.isEtale_of_isEtale_completionSheafMap_space`, which carries out
the reduction to étale charts and runs the scheme form of Stacks 0APQ (Stacks 0A43,
`AlgebraicGeometry.etaleAt_of_etale_infinitesimalNeighbourhoods`) on them.

## References

* [Stacks Project, Tag 0GI4](https://stacks.math.columbia.edu/tag/0GI4)
* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0GI0](https://stacks.math.columbia.edu/tag/0GI0)
* [Stacks Project, Tag 0APQ](https://stacks.math.columbia.edu/tag/0APQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- **Stacks 0GI4.** Let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be
a closed subset and let `U ⊂ X` be the open subspace with `|U| = |X| ∖ T`. Let `f : X' ⟶ X` be
a morphism of algebraic spaces which is locally of finite type and such that `f⁻¹U ⟶ U` is an
isomorphism, and let `g : W ⟶ X_{/T}` correspond to `f` under the equivalence of Stacks 0ARB,
that is, be isomorphic over `X_{/T}` to `f_{/T} : X'_{/T'} ⟶ X_{/T}`. Then `f` is étale if and
only if `g` is étale. -/
@[stacks 0GI4]
theorem isEtale_iff_isRepresentableEtale_of_overIso
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    {W : FppfSheaf B S hS} (g : W ⟶ Space.completionSheaf B S hS X T)
    (e : Over.mk g ≅ Over.mk (Space.completionSheafMap B S hS M.obj.hom T)) :
    Space.IsEtale B S hS M.obj.hom ↔ IsRepresentableEtale B S hS g := by
  let φ : W ≅ Space.completionSheaf B S hS M.obj.left
      (Space.pointsMap B S hS M.obj.left M.obj.hom ⁻¹' T) := (Over.forget _).mapIso e
  have hw : φ.hom ≫ Space.completionSheafMap B S hS M.obj.hom T = g := Over.w e.hom
  have hw' : φ.inv ≫ g = Space.completionSheafMap B S hS M.obj.hom T := Over.w e.inv
  refine ⟨fun hf => ?_, fun hg => ?_⟩
  · rw [← hw]
    exact IsRepresentableEtale.comp B S hS (isRepresentableEtale_iso_hom B S hS φ)
      (isEtale_completionSheafMap B S hS M.property.1.1 hX M.obj.hom T hf)
  · have hcomp : IsRepresentableEtale B S hS (Space.completionSheafMap B S hS M.obj.hom T) := by
      rw [← hw']
      exact IsRepresentableEtale.comp B S hS (isRepresentableEtale_iso_hom B S hS φ.symm) hg
    exact isEtale_of_isEtale_completionSheafMap_space B S hS M.property.1.1 hX M.obj.hom T hT
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian hX hXN) M.property.2
      (Space.isEtale_openComplementRestriction B S hS M.obj.hom T M.property.1.2) hcomp

end AlgebraicGeometry.FormalSpace

end
