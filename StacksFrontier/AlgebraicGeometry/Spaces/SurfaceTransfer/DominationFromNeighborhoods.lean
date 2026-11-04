module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.LocalToGlobalStep

/-!
# Domination of modifications at closed points, checked on étale neighbourhoods

Let `X` be a decent algebraic space over a scheme `S` with pairwise distinct closed points
`x₁, …, xₙ` and chosen elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` (Stacks 0BH9). Let
`g : A ⟶ X` and `l : Y ⟶ X` be algebraic spaces over `X` which are isomorphisms over
`X ∖ {x₁, …, xₙ}`. If, for every `i`, the base change of `A` to `Uᵢ` maps to the base change of
`Y` to `Uᵢ` over `Uᵢ`, then `A` maps to `Y` over `X`. This is the fullness of the functor `F` of
Stacks 0BHA, which is part of Stacks 0BHB, and it is the last step of the proof of Stacks 0BHM:
"It follows that `X_m` dominates `Y` by the equivalence of categories of Lemma 0BHB".

The local maps are produced from a scheme representing the base change of `A` (the datum
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.StageRep` of the lifting of normalized
blowups) and a scheme over `Uᵢ` dominating the base change of `Y`.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_hom_of_forall_pullback_hom`: a family
  of maps over the neighbourhoods gives a map over `X`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_pullback_hom_of_stageRep`: a map over
  `Uᵢ` out of the base change of `A` from a scheme representing it and a dominating scheme.

## References

* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
* [Stacks Project, Tag 0BHM](https://stacks.math.columbia.edu/tag/0BHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- **Maps of modifications are checked on the neighbourhoods.** Let `g : A ⟶ X` and
`l : Y ⟶ X` be isomorphisms over `X ∖ {x₁, …, xₙ}`. A family of maps over `Uᵢ` from the base
change of `A` to that of `Y` comes from a map `A ⟶ Y` over `X`, by the fullness of the functor
`F` of Stacks 0BHA (Stacks 0BHB). -/
theorem exists_hom_of_forall_pullback_hom {A Y : AlgebraicSpaces B S hS} (g : A ⟶ D.space)
    (l : Y ⟶ D.space) (hg : IsIso (pullback.snd g.hom D.openAwayFromPoints.ι))
    (hl : IsIso (pullback.snd l.hom D.openAwayFromPoints.ι))
    (m : ∀ i, pullback g.hom (D.toSpaceHom i).hom ⟶ pullback l.hom (D.toSpaceHom i).hom)
    (hm : ∀ i, m i ≫ pullback.snd l.hom (D.toSpaceHom i).hom =
      pullback.snd g.hom (D.toSpaceHom i).hom) :
    ∃ h : A ⟶ Y, h ≫ l = g := by
  let MA : D.modificationsAwayFromPoints := ⟨Over.mk g.hom, A.property, hg⟩
  let MY : D.modificationsAwayFromPoints := ⟨Over.mk l.hom, Y.property, hl⟩
  let φ : D.restrictionFunctor.obj MA ⟶ D.restrictionFunctor.obj MY := fun i =>
    ObjectProperty.homMk (Over.homMk (m i) (hm i))
  have := D.full_restrictionFunctor
  obtain ⟨ψ, -⟩ := D.restrictionFunctor.map_surjective φ
  refine ⟨ObjectProperty.homMk ψ.hom.left, ?_⟩
  ext1
  exact Over.w ψ.hom

/-- **A map over the `i`th neighbourhood out of a represented base change.** Suppose the base
change of `g : A ⟶ X` to `Uᵢ` is represented by a scheme `Z` over `Uᵢ`
(`AlgebraicGeometry.Space.ClosedPointNeighborhoods.StageRep`), and suppose `Z` maps over `Uᵢ` to
a scheme `P` of the site over `Uᵢ` which dominates the base change of `l : Y ⟶ X`. Then the base
change of `A` maps to that of `Y` over `Uᵢ`. -/
theorem exists_pullback_hom_of_stageRep (i : Fin n) {A Y : AlgebraicSpaces B S hS}
    {g : A ⟶ D.space} (l : Y ⟶ D.space) {Z : Over (D.neighborhoodScheme i)}
    (hrep : D.StageRep i g Z) {P : BigFppfOver B S hS} (qP : P ⟶ (D.neighborhood i).scheme)
    (hP : yoneda.obj P ⟶ pullback l.hom (D.toSpaceHom i).hom)
    (hhP : hP ≫ pullback.snd l.hom (D.toSpaceHom i).hom = yoneda.map qP)
    (k : Z.left ⟶ (BigFppfOver.toScheme B S hS).obj P)
    (hk : k ≫ (BigFppfOver.toScheme B S hS).map qP = Z.hom) :
    ∃ m : pullback g.hom (D.toSpaceHom i).hom ⟶ pullback l.hom (D.toSpaceHom i).hom,
      m ≫ pullback.snd l.hom (D.toSpaceHom i).hom = pullback.snd g.hom (D.toSpaceHom i).hom := by
  obtain ⟨W, q, Φ, θ, hΦ, hθ⟩ := hrep
  have hv : (θ.hom ≫ k) ≫ B.inclusion.map P.hom = B.inclusion.map W.hom := by
    have key : ∀ {V : BigFppfOver B S hS} (r : V ⟶ (D.neighborhood i).scheme),
        B.inclusion.map V.hom =
          (BigFppfOver.toScheme B S hS).map r ≫ B.inclusion.map (D.neighborhood i).scheme.hom := by
      intro V r
      rw [← Over.w r, Functor.map_comp]
      rfl
    rw [key qP, key q, ← hθ, ← hk]
    simp only [Category.assoc]
  let w : W ⟶ P := BigFppfOver.homOfCompEq B S hS (θ.hom ≫ k) hv
  have hwq : w ≫ qP = q := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq, Category.assoc, hk, hθ]
  refine ⟨Φ.hom ≫ yoneda.map w ≫ hP, ?_⟩
  rw [Category.assoc, Category.assoc, hhP, ← hΦ, ← hwq, Functor.map_comp]
  rfl

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
