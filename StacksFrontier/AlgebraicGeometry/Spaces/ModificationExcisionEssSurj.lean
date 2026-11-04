module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsSinglePoint

/-!
# Essential surjectivity of the excision base change, and the equivalence of Stacks 0BHB

Let `f : V ⟶ W` be an étale morphism of algebraic spaces over a scheme `S` and let `T` be a
closed subspace of `W` which `f` carries isomorphically onto its preimage. Stacks 0BGY asserts
that base change along `f` is an equivalence from the algebraic spaces over `W` which are
unchanged over `W ∖ T` onto the algebraic spaces over `V` which are unchanged over the preimage
of `W ∖ T`. Its essential surjectivity is the content of this file: the pushforward
`AlgebraicGeometry.Space.excisionPushforward` of a space over `V` is an algebraic space
(`AlgebraicGeometry.Space.isAlgebraicSpace_of_isIso_pullback_snd_of_isAlgebraicSpace_pullback`),
it is unchanged over `W ∖ T`, and its base change along `f` is the given space over `V`.

For the chosen elementary étale neighborhoods of finitely many closed points of a decent
algebraic space this gives the essential surjectivity of the functor `F` of Stacks 0BHA, which
together with its full faithfulness
(`AlgebraicGeometry.Space.ClosedPointNeighborhoods.full_restrictionFunctor` and
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.faithful_restrictionFunctor`) is Stacks 0BHB.

## Main results

* `AlgebraicGeometry.Space.exists_isModification_pullback_iso`: the essential surjectivity of the
  base change of Stacks 0BGY.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.essSurj_restrictionFunctor_of_excision`: the
  essential surjectivity of the functor `F` of Stacks 0BHA.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isEquivalence_restrictionFunctor`:
  **Stacks 0BHB**, that `F` is an equivalence.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The essential surjectivity of the base change of Stacks 0BGY.** An algebraic space `Y`
over `V` which is unchanged over the preimage of `W ∖ T` is the base change of an algebraic
space over `W` which is unchanged over `W ∖ T`, namely of the pushforward of `Y` along `f`. -/
theorem exists_isModification_pullback_iso
    (hV : IsAlgebraicSpace B S hS V) (hY : IsAlgebraicSpace B S hS Y)
    (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W) (hf : IsEtale B S hS f)
    (hsep : IsSeparated B S hS f)
    (T : Subfunctor W) (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f))
    (h : Y ⟶ V)
    (hY₀ : IsIso (pullback.snd h ((openComplement B S hS T).preimage f).ι)) :
    ∃ M : Over W, IsModification B S hS (openComplement B S hS T) M ∧
      Nonempty ((Over.pullback f).obj M ≅ Over.mk h) := by
  obtain ⟨e, he⟩ := exists_iso_pullback_excisionProjection B S hS f h hV hY hW hf hsep T hfT hY₀
  have hiso := isIso_pullback_snd_excisionProjection B S hS f h hV hY hW hY₀
  refine ⟨Over.mk (excisionProjection B S hS f h hV hY hW), ⟨?_, hiso⟩,
    ⟨Over.isoMk e he⟩⟩
  exact isAlgebraicSpace_of_isIso_pullback_snd_of_isAlgebraicSpace_pullback B S hS hV hW hY f hf
    T hT hfT _ (isSheaf_excisionPushforward B S hS f h hV hY hW) hiso e

namespace ClosedPointNeighborhoods

variable {B S hS} {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- **The essential surjectivity of the functor `F` of Stacks 0BHA.** An algebraic space over
`Uᵢ` which is unchanged over `Uᵢ ∖ {uᵢ}` is the base change of its pushforward along
`Uᵢ ⟶ X`, which is unchanged over `X ∖ {xᵢ}`; the fibre product over `X` of those pushforwards
then has the prescribed base change to every neighborhood. -/
theorem essSurj_restrictionFunctor_of_excision : D.restrictionFunctor.EssSurj := by
  refine D.essSurj_restrictionFunctor_of_exists fun i N hN ↦ ?_
  have hpre : IsModification B S hS
      ((openComplement B S hS (D.pointSubspace i)).preimage (D.toSpaceHom i).hom) N := by
    rwa [D.openComplement_pointSubspace_eq i, D.preimage_openAwayFromSinglePoint i]
  obtain ⟨M, hM, he⟩ := exists_isModification_pullback_iso B S hS
    (D.neighborhoodSpace i).property hN.1 D.space.property (D.toSpaceHom i).hom
    (D.neighborhood i).etale_toSpace (D.isSeparated_toSpaceHom i)
    (D.pointSubspace i) (D.isClosedSubspace_pointSubspace i)
    (D.isIso_fromPreimage_pointSubspace i) N.hom hpre.2
  exact ⟨M, by rwa [← D.openComplement_pointSubspace_eq i], he⟩

/-- **Stacks 0BHB.** The functor `F` of Stacks 0BHA, base change of the modifications of `X`
away from the chosen closed points to the chosen elementary étale neighborhoods, is an
equivalence of categories. -/
@[stacks 0BHB]
theorem isEquivalence_restrictionFunctor : D.restrictionFunctor.IsEquivalence where
  faithful := D.faithful_restrictionFunctor
  full := D.full_restrictionFunctor
  essSurj := D.essSurj_restrictionFunctor_of_excision

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
