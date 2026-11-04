module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertDivisorAddition
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurve

/-!
# The Hilbert schemes of points of a geometrically irreducible smooth proper curve

This file assembles [Stacks, Tag 0B9I]. Let `X` be a geometrically irreducible smooth proper
curve over a field `k`.

1. The Hilbert functors `Hilb^d_{X/k}` are representable by smooth proper varieties `H^d` of
   dimension `d` over `k`.
2. For a field extension `k'/k` the `k'`-rational points of `H^d` are in bijection with the
   effective Cartier divisors of degree `d` on `X_{k'}`.
3. For `d₁, d₂ ≥ 0` the addition morphism `H^{d₁} ×_k H^{d₂} ⟶ H^{d₁ + d₂}`,
   `(D₁, D₂) ↦ D₁ + D₂`, is finite locally free of degree `(d₁ + d₂).choose d₁`.

## Main results

* `Stacks.Hilbert.exists_hilbertSchemes_of_isCurve`: the whole proposition, for a family of
  representing schemes which it produces.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_isVariety_of_isCurve`: part (1).
* `Stacks.Hilbert.isFiniteLocallyFreeOfRank_addDivisors_of_isCurve`: part (3), for every choice of
  representing schemes.

Part (2) for every representing scheme and every field extension is
`Stacks.Hilbert.rationalPointsEquivEffectiveCartierDivisors`.

## Implementation notes

Representability is `Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_isCurve`
(Tags 0B9A, 0B9B and the ampleness of a proper curve); the properties of the representing schemes
are `Stacks.Hilbert.smoothOfRelativeDimension_and_isProper_of_isCurve` (Tags 0B98, 0B9H, 0B9G,
03GN) and `Stacks.Hilbert.isVariety_and_topologicalKrullDim_of_isCurve` (Tag 038F). The degree of
the addition morphism is `Stacks.Hilbert.isFiniteLocallyFreeOfRank_addDivisors`, which holds for
any separated smooth relative curve all of whose Hilbert functors are representable. Geometric
irreducibility of `X` is used only for the irreducibility of the `H^d` in part (1).

## References

* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A representing scheme of a Hilbert functor of a geometrically irreducible smooth proper curve
is a smooth proper variety of dimension `d`. -/
private theorem isVariety_and_smooth_and_isProper_and_krullDim [IsProper f] [IsCurve k f]
    [Smooth f] [GeometricallyIrreducible f] (d : ℕ) (H : Over (Spec (.of k)))
    (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    IsVariety k H.hom ∧ SmoothOfRelativeDimension d H.hom ∧ IsProper H.hom ∧
      topologicalKrullDim H.left = d := by
  obtain ⟨hv, hdim⟩ := isVariety_and_topologicalKrullDim_of_isCurve k f d H hH
  obtain ⟨hs, hp⟩ := smoothOfRelativeDimension_and_isProper_of_isCurve k f d H hH
  exact ⟨hv, hs, hp, hdim⟩

/-- **Stacks Project, Tag 0B9I (1).** Let `X` be a geometrically irreducible smooth proper curve
over a field `k`. For every `d` the degree-`d` Hilbert functor of `X` is representable by a
smooth proper variety of dimension `d` over `k`. -/
@[stacks 0B9I "(1)"]
theorem exists_representsHilbertFunctorOfRank_isVariety_of_isCurve [IsProper f] [IsCurve k f]
    [Smooth f] [GeometricallyIrreducible f] (d : ℕ) :
    ∃ (H : Over (Spec (.of k))) (_ : RepresentsHilbertFunctorOfRank (Over.mk f) H d),
      IsVariety k H.hom ∧ SmoothOfRelativeDimension d H.hom ∧ IsProper H.hom ∧
        topologicalKrullDim H.left = d := by
  obtain ⟨⟨H, hH⟩⟩ := nonempty_representsHilbertFunctorOfRank_of_isCurve k f d
  exact ⟨H, hH, isVariety_and_smooth_and_isProper_and_krullDim k f d H hH⟩

/-- **Stacks Project, Tag 0B9I (3).** Let `X` be a smooth proper curve over a field `k`, and let
`H₁`, `H₂` and `H` be any schemes representing the Hilbert functors of `X` of degrees `d₁`, `d₂`
and `d₁ + d₂`. The addition morphism `H₁ ×_k H₂ ⟶ H`, `(D₁, D₂) ↦ D₁ + D₂`, classifies the sum of
the two families, and is finite locally free of degree `(d₁ + d₂).choose d₁`. -/
@[stacks 0B9I "(3), for every choice of representing schemes; geometric irreducibility of X is \
not needed"]
theorem isFiniteLocallyFreeOfRank_addDivisors_of_isCurve [IsProper f] [IsCurve k f] [Smooth f]
    {d₁ d₂ : ℕ} {H₁ H₂ H : Over (Spec (.of k))}
    (h₁ : RepresentsHilbertFunctorOfRank (Over.mk f) H₁ d₁)
    (h₂ : RepresentsHilbertFunctorOfRank (Over.mk f) H₂ d₂)
    (h : RepresentsHilbertFunctorOfRank (Over.mk f) H (d₁ + d₂)) :
    haveI : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
      smoothOfRelativeDimension_one_of_isCurve k f
    (∀ {T : Over (Spec (.of k))} (g : T ⟶ H₁ ⨯ H₂),
        h.family (g ≫ addDivisors h₁ h₂ h) =
          (h₁.family (g ≫ prod.fst)).add (h₂.family (g ≫ prod.snd))) ∧
      Morphisms.IsFiniteLocallyFreeOfRank (addDivisors h₁ h₂ h).left ((d₁ + d₂).choose d₁) := by
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
    smoothOfRelativeDimension_one_of_isCurve k f
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  exact ⟨family_comp_addDivisors h₁ h₂ h, isFiniteLocallyFreeOfRank_addDivisors h₁ h₂ h
    fun d ↦ (nonempty_representsHilbertFunctorOfRank_of_isCurve k f d).some.2⟩

/-- **Stacks Project, Tag 0B9I.** Let `X` be a geometrically irreducible smooth proper curve over
a field `k`. There are schemes `H d` representing the Hilbert functors `Hilb^d_{X/k}` such that

1. each `H d` is a smooth proper variety of dimension `d` over `k`;
2. for every field extension `k'/k`, the `k'`-rational points of `H d` are in bijection with the
   effective Cartier divisors of degree `d` on `X_{k'}`, i.e. the closed subschemes of `X_{k'}`
   which are effective Cartier divisors finite locally free of rank `d` over `k'`;
3. for `d₁, d₂ ≥ 0` the addition morphism `H d₁ ×_k H d₂ ⟶ H (d₁ + d₂)`,
   `(D₁, D₂) ↦ D₁ + D₂`, is finite locally free of degree `(d₁ + d₂).choose d₁`. -/
@[stacks 0B9I]
theorem exists_hilbertSchemes_of_isCurve [IsProper f] [IsCurve k f] [Smooth f]
    [GeometricallyIrreducible f] :
    haveI : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
      smoothOfRelativeDimension_one_of_isCurve k f
    ∃ (H : ℕ → Over (Spec (.of k)))
      (hH : ∀ d, RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d),
      (∀ d, IsVariety k (H d).hom ∧ SmoothOfRelativeDimension d (H d).hom ∧
          IsProper (H d).hom ∧ topologicalKrullDim (H d).left = d) ∧
      (∀ (d : ℕ) (k' : Type u) [Field k'] [Algebra k k'],
        Nonempty ((fieldExtOver k k' ⟶ H d) ≃
          {I : ((Over.pullback (fieldExtOver k k').hom).obj (Over.mk f)).left.IdealSheafData //
            Stacks.Divisors.IsEffectiveCartierDivisor I ∧
              Stacks.Morphisms.IsFiniteLocallyFreeOfRank
                (I.subschemeι ≫ ((Over.pullback (fieldExtOver k k').hom).obj (Over.mk f)).hom)
                d})) ∧
      (∀ d₁ d₂ : ℕ,
        (∀ {T : Over (Spec (.of k))} (g : T ⟶ H d₁ ⨯ H d₂),
          (hH (d₁ + d₂)).family (g ≫ addDivisors (hH d₁) (hH d₂) (hH (d₁ + d₂))) =
            ((hH d₁).family (g ≫ prod.fst)).add ((hH d₂).family (g ≫ prod.snd))) ∧
        Morphisms.IsFiniteLocallyFreeOfRank
          (addDivisors (hH d₁) (hH d₂) (hH (d₁ + d₂))).left ((d₁ + d₂).choose d₁)) := by
  let H : ℕ → Over (Spec (.of k)) := fun d ↦
    (nonempty_representsHilbertFunctorOfRank_of_isCurve k f d).some.1
  let hH : ∀ d, RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d := fun d ↦
    (nonempty_representsHilbertFunctorOfRank_of_isCurve k f d).some.2
  exact ⟨H, hH, fun d ↦ isVariety_and_smooth_and_isProper_and_krullDim k f d (H d) (hH d),
    fun d k' _ _ ↦ ⟨rationalPointsEquivEffectiveCartierDivisors k f d (H d) (hH d) k'⟩,
    fun d₁ d₂ ↦
    isFiniteLocallyFreeOfRank_addDivisors_of_isCurve k f (hH d₁) (hH d₂) (hH (d₁ + d₂))⟩

end Stacks.Hilbert

end
