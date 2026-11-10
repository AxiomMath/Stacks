module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverEnlargement.Enlargement
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSpreading.QuasiCompactReduction

/-!
# Extending a Galois cover of the generic fibre over a Noetherian base

[Stacks, Tag 0EYJ]: let `S` be an integral normal Noetherian scheme with generic point `η`, let
`f : X ⟶ S` be a smooth morphism with geometrically connected fibres and `σ` a section of `f`,
and let `Z ⟶ X_η` be a finite étale Galois cover with group `G` of order invertible on `S` with
a `κ(η)`-rational point over `σ(η)`. Then `Z` is the restriction of a finite étale Galois cover
of `X` with group `G`.

## Main results

* `exists_finiteEtaleGaloisCover_extending_genericFiber_of_isNoetherian_of_quasiCompact`:
  the statement above for quasi-compact `f`.
* `exists_finiteEtaleGaloisCover_extending_genericFiber_of_isNoetherian`:
  the statement above.

## Implementation notes

Both results take one further result as a hypothesis: `h0EYD`, the tame half of
[Stacks, Tag 0EYD].

## References

* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Algebraization (IsInfinitesimalSectionsComplete
  CompletionFullyFaithfulOnFiniteLocallyFree)

universe v u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EYJ, for quasi-compact `f`.** The statement of
`exists_finiteEtaleGaloisCover_extending_genericFiber_of_isNoetherian` under the further
assumption that `f` is quasi-compact. -/
theorem exists_finiteEtaleGaloisCover_extending_genericFiber_of_isNoetherian_of_quasiCompact
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover) :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsIntegral S] [IsNormal S]
      [QuasiCompact f] [Smooth f] [GeometricallyConnected f]
      (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
      (G : Type v) [Group G] [Finite G]
      (_hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
      (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
      (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
      (_hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ),
      ∃ (Y : FiniteEtaleGaloisCover X G)
        (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
        ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map
          (Y.action g).asIso.hom ≫ e.hom = e.hom ≫ (Z.action g).asIso.hom := by
  intro S X f _ _ _ _ _ _ σ hσ G _ _ hG Z z hz
  exact Abhyankar.exists_of_galoisExtendsOver_top f Z
    (Abhyankar.galoisExtendsOver_top f Z
      (Abhyankar.exists_galoisExtendsOver f σ hσ G hG Z z hz)
      (Abhyankar.exists_galoisExtendsOver_gt h0EYD f σ hσ G hG Z z hz))

/-- **Stacks Project, Tag 0EYJ.** Let `S` be an integral normal Noetherian scheme with generic
point `η`, `f : X ⟶ S` smooth with geometrically connected fibres and a section `σ`, and
`Z ⟶ X_η` a finite étale Galois cover with group `G` of order invertible on `S` with a
`κ(η)`-point over `σ(η)`. Then `Z` is the restriction of a finite étale Galois cover of `X` with
group `G`, equivariantly.

The named argument is `h0EYD` (the tame half of [Stacks, Tag 0EYD]). -/
theorem exists_finiteEtaleGaloisCover_extending_genericFiber_of_isNoetherian
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover) :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsIntegral S] [IsNormal S]
      [Smooth f] [GeometricallyConnected f]
      (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
      (G : Type v) [Group G] [Finite G]
      (_hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
      (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
      (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
      (_hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ),
      ∃ (Y : FiniteEtaleGaloisCover X G)
        (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
        ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map
          (Y.action g).asIso.hom ≫ e.hom = e.hom ≫ (Z.action g).asIso.hom :=
  Abhyankar.exists_finiteEtaleGaloisCover_extending_genericFiber_of_quasiCompact_case
    (exists_finiteEtaleGaloisCover_extending_genericFiber_of_isNoetherian_of_quasiCompact
      h0EYD)

end AlgebraicGeometry
