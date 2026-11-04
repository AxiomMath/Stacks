module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SpaceTowerHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionOneSchematicLocus

/-!
# Algebraization of formal curves

**[Stacks, Tag 0E7R].** Let `(A, 𝔪, κ)` be a complete local Noetherian ring, `S = Spec A` and
`Sₙ = Spec (A / 𝔪ⁿ)`. Consider a commutative diagram

```
  X₁ --i₁--> X₂ --i₂--> X₃ --> ⋯
  |          |          |
  S₁ ------> S₂ ------> S₃ --> ⋯
```

of algebraic spaces with cartesian squares. If `X₁ ⟶ S₁` is proper and `dim(X₁) ≤ 1`, then there
exist a projective morphism of schemes `X ⟶ S` and isomorphisms `Xₙ ≅ X ×_S Sₙ` compatible with
the `iₙ`.

The hypothesis "`X₁ ⟶ S₁` is proper" is that of the statement in the Stacks Project source
file `spaces-more-morphisms.tex`; the website omits it, although the proof uses it
("Hence `X₁` is a proper scheme"), and without it the statement is false
(`Stacks.FormalCurve.not_formalCurveAlgebraizationWithoutProperness`).

## The proof

The source's. Every `Xₙ` is a scheme: by [Stacks, Tag 0ADD]
(`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one`)
applied at each point, its hypotheses holding on every member of the tower because `X₁` is proper
of dimension at most one (`FormalCurve/SpaceTowerHypotheses.lean`; the source takes `Xₙ` from
[Stacks, Tag 05ZR], here 0ADD is applied to `Xₙ` directly). The tower is then a tower of schemes,
and the scheme form of the lemma
(`Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`) gives an
H-projective `X ⟶ S`, which lies in the site because it is of finite type over `S`
(`AlgebraicGeometry.Space.exists_algebraization_of_isRepresentable`).

## Conventions

The algebraic spaces are algebraic spaces over `S = Spec A` on a big fppf site `B` containing
`S`; `Sₙ` is `AlgebraicGeometry.Space.adicThickeningObject`, indexed from `0` (index `n` is the
source's `n + 1`), and lies in `B` automatically
(`AlgebraicGeometry.Space.contains_adicThickening`).
The algebraization `X` is returned as a scheme in the site together with morphisms
`kₙ : Xₙ ⟶ h_X`, compatible with the `iₙ`, whose squares over `Sₙ ⟶ S` are cartesian: that is
`Xₙ ≅ X ×_S Sₙ`. "Projective" is [Stacks, Tag 01W8] (`AlgebraicGeometry.IsProjective`); the
morphism is moreover H-projective (`AlgebraicGeometry.IsProjectiveMorphism`).

## References

* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

/-- **[Stacks, Tag 0E7R], algebraization of formal curves.** Let `A` be a complete local
Noetherian ring, `S = Spec A`, `Sₙ = Spec (A / 𝔪 ^ (n + 1))`, and let `Xₙ ⟶ Sₙ` be algebraic spaces
with transition maps `iₙ : Xₙ ⟶ Xₙ₊₁` making every square over `Sₙ ⟶ Sₙ₊₁` cartesian. If
`X₀ ⟶ S₀` is proper and `dim X₀ ≤ 1`, there are a projective morphism of schemes `fY : Y ⟶ S`
and morphisms `kₙ : Xₙ ⟶ Y`, compatible with the `iₙ`, identifying each `Xₙ` with `Y ×_S Sₙ`. -/
@[stacks 0E7R]
theorem exists_isProjective_algebraization_of_dimension_le_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of A)))
    (X : ℕ → (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u)
    (hX : ∀ n, IsAlgebraicSpace B (Spec (.of A)) hS (X n))
    (p : ∀ n, X n ⟶ yoneda.obj (adicThickeningObject A (maximalIdeal A) B hS
      (contains_adicThickening A (maximalIdeal A) B hS) n))
    (i : ∀ n, X n ⟶ X (n + 1))
    (hcart : ∀ n, IsPullback (i n) (p n) (p (n + 1))
      (yoneda.map (adicThickeningSuccMap A (maximalIdeal A) B hS
        (contains_adicThickening A (maximalIdeal A) B hS) n)))
    (hproper : IsProper B (Spec (.of A)) hS (p 0))
    (hdim : dimension B (Spec (.of A)) hS (X 0) (hX 0) ≤ 1) :
    ∃ (Y : Scheme.{u}) (hY : B.Contains Y) (fY : Y ⟶ Spec (.of A)),
      IsProjective fY ∧ IsProjectiveMorphism fY ∧
      ∃ k : ∀ n, X n ⟶ yoneda.obj (siteObject B (Spec (.of A)) hS hY fY),
        (∀ n, i n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n) (p n) (yoneda.map (siteObjectToBase A B hS hY fY))
          (yoneda.map (adicThickeningMap A (maximalIdeal A) B hS
            (contains_adicThickening A (maximalIdeal A) B hS) n)) := by
  have hSn := contains_adicThickening A (maximalIdeal A) B hS
  have hrep : ∀ n, (X n).IsRepresentable := fun n =>
    isRepresentable_of_forall_mem_range A B hS (hX n) fun x =>
      exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one B _ hS (hX n)
        (isAbsolutelySeparated_adicTower A _ B hS hSn X hX p i hcart hproper n)
        (hasEtaleLocalProperty_isLocallyNoetherian_adicTower A _ B hS hSn X hX p i hcart
          hproper n)
        x (localRingDimension_le_one_adicTower A _ B hS hSn X hX p i hcart hproper hdim n x)
  obtain ⟨Y, hY, fY, hfY, k, hk, hkpb⟩ :=
    exists_algebraization_of_isRepresentable A _ B hS hSn X hX p i hcart hproper hdim hrep
  exact ⟨Y, hY, fY, IsProjectiveMorphism.isProjective hfY, hfY, k, hk, hkpb⟩

end AlgebraicGeometry.Space

end
