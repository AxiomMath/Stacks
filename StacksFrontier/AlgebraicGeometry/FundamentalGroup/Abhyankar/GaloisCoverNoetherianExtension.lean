module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.GaloisCoverNoetherian
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularPurity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullbackRamification
public import StacksCore.Tactic.StacksAttribute

/-!
# Extending a Galois cover of the generic fibre over a Noetherian base

[Stacks, Tag 0EYJ]: let `S` be an integral normal Noetherian scheme with generic point `η`, let
`f : X ⟶ S` be a smooth morphism with geometrically connected fibres and `σ` a section of `f`,
and let `Z ⟶ X_η` be a finite étale Galois cover with group `G` of order invertible on `S` with
a `κ(η)`-rational point over `σ(η)`. Then there is a finite étale Galois cover `Y ⟶ X` with
group `G` whose restriction to `X_η` is `Z`.

## Main results

* `AlgebraicGeometry.FiniteEtaleGaloisCover.exists_extension_of_genericFiber_of_isNoetherian`:
  the statement above.

## References

* [Stacks Project, Tag 0BMA](https://stacks.math.columbia.edu/tag/0BMA)
* [Stacks Project, Tag 0EYD](https://stacks.math.columbia.edu/tag/0EYD)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.FiniteEtaleGaloisCover

/-- **Extending a Galois cover of the generic fibre.** Let `S` be an integral normal Noetherian
scheme with generic point `η`, let `f : X ⟶ S` be a smooth morphism with geometrically connected
fibres and let `σ : S ⟶ X` be a section of `f`. Let `Z ⟶ X_η` be a finite étale Galois cover
with group `G` whose order is invertible on `S` (a unit in every residue field `κ(s)`), such that
`Z` has a `κ(η)`-rational point `z` mapping to `σ(η)`. Then there is a finite étale Galois cover
`Y ⟶ X` with group `G` whose restriction to `X_η` is `Z`: an isomorphism `Y ×_X X_η ≅ Z` over
`X_η` compatible with the actions of `G`. -/
@[stacks 0EYJ "the full statement under the tag's hypotheses and nothing else: `S` integral \
(`IsIntegral S`), normal (`IsNormal S`) and Noetherian (`IsNoetherian S`); `f` smooth with \
geometrically connected fibres (`Smooth f`, `GeometricallyConnected f`); a section `σ` of `f` \
(`hσ`); a finite étale Galois cover `Z` of the generic fibre `X_η` with group `G`, `G` finite of \
order invertible on `S` (`hG`: a unit in every residue field); a `κ(η)`-rational point `z` of \
`Z` over `σ(η)` (`hz`). The conclusion is a finite étale Galois cover `Y` of `X` with group `G` \
and a `G`-equivariant isomorphism `Y ×_X X_η ≅ Z` over `X_η`."]
theorem exists_extension_of_genericFiber_of_isNoetherian
    {S X : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsIntegral S] [IsNormal S]
    [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (G : Type v) [Group G] [Finite G]
    (hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
    (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ) :
    ∃ (Y : FiniteEtaleGaloisCover X G)
      (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map (Y.action g).asIso.hom ≫
        e.hom = e.hom ≫ (Z.action g).asIso.hom :=
  exists_finiteEtaleGaloisCover_extending_genericFiber_of_isNoetherian
    Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne
    f σ hσ G hG Z z hz

end AlgebraicGeometry.FiniteEtaleGaloisCover

end
