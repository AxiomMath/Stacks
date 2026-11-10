module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverEnlargement.LocalClaim
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverEnlargement.NearPoint

/-!
# Enlarging the open over which a generic Galois cover extends

Let `S` be a normal integral Noetherian scheme with generic point `η` and `f : X ⟶ S` a
quasi-compact smooth morphism with geometrically connected fibres and a section `σ`. Let
`Z ⟶ X_η` be a finite étale Galois cover with group `G` of order invertible on `S`, having a
`κ(η)`-point over `σ(η)`. If `Z` extends over a proper open `U ⊂ S`, it extends over a strictly
larger open. This is the inductive step of the maximal-open argument in the proof of
[Stacks, Tag 0EYJ], `AlgebraicGeometry.Abhyankar.galoisExtendsOver_top`.

The proof follows the source. Let `s` be the generic point of an irreducible component of `S ∖ U`
(`AlgebraicGeometry.exists_point_with_punctured_local_open`), so that `U` pulls back to the
punctured spectrum of `𝒪_{S, s}`. The restriction of the cover to `X ×_S (Spec 𝒪_{S, s} ∖ {s})`
extends to `X ×_S Spec 𝒪_{S, s}`
(`AlgebraicGeometry.Abhyankar.exists_finiteEtale_extension_to_stalk`: the discrete valuation ring
case if `dim 𝒪_{S, s} = 1`, the local claim at a point of codimension at least two otherwise); the
two covers glue over `U ∪ W` for an open neighbourhood `W` of `s`
(`AlgebraicGeometry.exists_finiteEtale_extension_of_stalk`); and the glued cover carries a Galois
structure extending that over `U` (`AlgebraicGeometry.Abhyankar.galoisExtendsOver_of_extension`).

## Main results

* `AlgebraicGeometry.Abhyankar.exists_galoisExtendsOver_gt`.

## References

* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Algebraization (IsInfinitesimalSectionsComplete
  CompletionFullyFaithfulOnFiniteLocallyFree)

universe v u

namespace AlgebraicGeometry.Abhyankar

/-- **The inductive step of the proof of [Stacks, Tag 0EYJ].** Let `S` be a normal integral
Noetherian scheme, `f : X ⟶ S` quasi-compact and smooth with geometrically connected fibres and a
section `σ`, and `Z ⟶ X_η` a finite étale Galois cover with group `G` of order invertible on `S`
with a `κ(η)`-point over `σ(η)`. If `Z` extends over a proper open `U` of `S`, it extends over a
strictly larger open. The argument is the tame half of [Stacks, Tag 0EYD] (`h0EYD`), for the
discrete valuation ring case; the local claim at points of codimension at least two needs no
further input. -/
theorem exists_galoisExtendsOver_gt
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsIntegral S] [IsNormal S]
    [QuasiCompact f] [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (G : Type v) [Group G] [Finite G]
    (hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
    (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ)
    (U : S.Opens) : GaloisExtendsOver f Z U → U ≠ ⊤ →
      ∃ U' : S.Opens, U < U' ∧ GaloisExtendsOver f Z U' := by
  rintro ⟨hη, Y, e, he⟩ hU
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNormal X := isNormal_of_smooth f
  obtain ⟨s, hs, hP⟩ := exists_point_with_punctured_local_open S U hU
  have hP' (p : Spec (S.presheaf.stalk s)) :
      S.fromSpecStalk s p ∈ U ↔ p ≠ IsLocalRing.closedPoint (S.presheaf.stalk s) := by
    change p ∈ S.fromSpecStalk s ⁻¹ᵁ U ↔ _
    rw [hP]
    exact Iff.rfl
  obtain ⟨YO, ⟨θ⟩⟩ :=
    exists_finiteEtale_extension_to_stalk f h0EYD σ hσ G hG Z z hz hη Y e s hP'
  obtain ⟨W, hsW, F, ⟨eF⟩⟩ := exists_finiteEtale_extension_of_stalk f s U hη Y.obj YO θ
  refine ⟨U ⊔ W, lt_of_le_of_ne le_sup_left fun h ↦ hs ?_,
    galoisExtendsOver_of_extension f Z le_sup_left hη Y e he F eF⟩
  rw [h]
  exact (le_sup_right : W ≤ U ⊔ W) hsW

end AlgebraicGeometry.Abhyankar
