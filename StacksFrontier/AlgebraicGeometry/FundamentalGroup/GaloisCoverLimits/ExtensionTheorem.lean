module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.Extension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularPurity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullbackRamification
public import StacksCore.Tactic.StacksAttribute

/-!
# Extending a Galois cover from the generic fibre over a qcqs base

[Stacks, Tag 0EZJ]: let `S` be a quasi-compact and quasi-separated integral normal scheme with
generic point `η`, let `f : X ⟶ S` be a quasi-compact and quasi-separated smooth morphism with
geometrically connected fibres, and let `σ` be a section of `f`. Let `Z ⟶ X_η` be a finite étale
Galois cover with group `G` of order invertible on `S` such that `Z` has a `κ(η)`-rational point
mapping to `σ(η)`. Then there exists a finite étale Galois cover `Y ⟶ X` with group `G` whose
restriction to `X_η` is `Z`.

The limit argument of the source is
`AlgebraicGeometry.exists_finiteEtaleGaloisCover_extending_genericFiber`, which reduces to the
Noetherian case [Stacks, Tag 0EYJ] and carries that case's input. It is supplied here by a
proved theorem, the tame half of [Stacks, Tag 0EYD],
`Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne`.

## Main results

* `AlgebraicGeometry.FiniteEtaleGaloisCover.exists_extending_genericFiber`: Tag 0EZJ.

## References

* [Stacks Project, Tag 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.FiniteEtaleGaloisCover

/-- **Stacks Project, Tag 0EZJ.** Let `S` be a quasi-compact and quasi-separated integral normal
scheme with generic point `η`, let `f : X ⟶ S` be a quasi-compact and quasi-separated smooth
morphism with geometrically connected fibres and `σ` a section of `f`. Let `Z ⟶ X_η` be a finite
étale Galois cover (Section 03SF) with group `G` of order invertible on `S` such that `Z` has a
`κ(η)`-rational point `z` mapping to `σ(η)`. Then there is a finite étale Galois cover `Y ⟶ X`
with group `G` whose restriction to `X_η` is `Z`: the restriction is isomorphic to `Z` by an
isomorphism compatible with the two actions of `G`.

The order of `G` is invertible on `S` when it is a unit in every residue field of `S`. -/
@[stacks 0EZJ "the full statement under the tag's hypotheses: S qcqs integral normal; f qcqs \
smooth with geometrically connected fibres and a section σ; Z a finite étale Galois cover of X_η \
with group G of order invertible on S and a κ(η)-point over σ(η); the extension Y is \
G-equivariantly a Galois cover restricting to Z"]
theorem exists_extending_genericFiber
    {S X : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsIntegral S] [IsNormal S]
    [QuasiCompact f] [QuasiSeparated f] [Smooth f] [GeometricallyConnected f]
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
  exists_finiteEtaleGaloisCover_extending_genericFiber
    (fun D hD ↦ Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne D hD)
    f σ hσ G hG Z z hz

end AlgebraicGeometry.FiniteEtaleGaloisCover

end
