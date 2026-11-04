module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerFibre
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRepresents

/-!
# A solution of the equalizer situation of Stacks 0GHD represents the diagonal fibre

In the situation of Stacks 0GH8, recorded by `AlgebraicGeometry.Artin.ContractionSituation`, let
`V` be a locally Noetherian scheme over `S` and let `(Zᵢ, u'ᵢ, x̂ᵢ) ∈ F(V)`, `i = 1, 2`, with
chosen compatibility witnesses (`AlgebraicGeometry.Artin.ContractionEqualizer`). Assertion (4)
of **Stacks 0GHD** is that `E'`, `(E' ⟶ V)⁻¹Z` and `E'_{/Z} ⟶ E_W` form a situation as in
Stacks 0GH8 over `V` (`AlgebraicGeometry.Artin.ContractionEqualizer.situation`). The remark
concludes:

> We conclude, using Lemmas 0GHB and 0GHC, that if there is a solution `E → V` for the triple in
> (4), then `E` represents `F ×_{Δ, F × F} V` on the category of locally Noetherian schemes over
> `V`.

The functor of the situation of (4) is `F ×_{Δ, F × F} V` on locally Noetherian schemes over `V`
(`AlgebraicGeometry.Artin.ContractionEqualizer.contractionFunctorSituationIso`, through
assertion (5)), and a solution represents the functor of its situation by Stacks 0GHB. Stacks
0GHB holds for solutions whose open subspace `U` is the complement of `T`, which is what its
proof uses, and is false for the literal notion of solution
(`AlgebraicGeometry.Artin.ContractionSituation.not_forall_nonempty_iso_of_solution`), so the
conclusion is stated for such solutions
(`AlgebraicGeometry.Artin.ContractionEqualizer.morIsoDiagonalFibre`).

## References

* [Stacks Project, Tag 0GHB](https://stacks.math.columbia.edu/tag/0GHB)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionEqualizer

open ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    (d : ContractionEqualizer c V) (hVN : IsLocallyNoetherian V.left.obj)

/-- **Stacks 0GHD, the final conclusion.** For the data of Stacks 0GHD over a locally Noetherian
scheme `V`, a solution `E ⟶ V` of the situation of assertion (4) whose open subspace `U` is the
complement of `T` (the notion of solution for which Stacks 0GHB holds) represents the fibre
`F ×_{Δ, F × F} V` on the category of locally Noetherian schemes over `V`: there is an
isomorphism of functors `Mor_V(-, E) ≅ F ×_{Δ, F × F} V`. -/
@[stacks 0GHD "final conclusion (with the corrected notion of solution, see 0GHB: the open \
subspace U of the solution is the complement of T): a solution E → V of the triple of (4) \
represents F ×_{Δ, F × F} V on locally Noetherian schemes over V, by corrected 0GHB for the \
situation of (4) and the identification of its functor with F ×_{Δ, F × F} V through (5)"]
noncomputable def morIsoDiagonalFibre
    {E : (BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u}
    (s : Solution (d.situation hVN) E)
    (hU : Set.range (Space.pointsMap B V.left.obj V.left.property s.U.toFunctor s.U.ι) =
      s.Tᶜ) :
    morOnLocallyNoetherian B V.left.obj V.left.property E ≅ d.diagonalFibre :=
  (s.contractionFunctorIso hU).symm ≪≫ d.contractionFunctorSituationIso hVN

end AlgebraicGeometry.Artin.ContractionEqualizer

end
