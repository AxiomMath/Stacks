module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Preparation
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationProduct
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseLemmas

/-!
# Additivity of the classes `P'_p(Q)` of Stacks 0F9K

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z ⊆ X` be a closed subscheme, let `b : W ⟶ 𝐏¹_X` be proper and an
isomorphism over `𝐀¹_X`, and let `T ⊆ W_∞` be a closed subscheme containing every point of `W_∞`
lying over `X ∖ Z`. Stacks 0FAZ: if `Q, Q' ∈ D(𝒪_W)` have defined Chern classes and restrict to
zero on `T`, then the classes of Stacks 0F9K satisfy

  `P'_p(Q ⊕ Q') = P'_p(Q) + P'_p(Q')`   in `A^p(Z ⟶ X)`.

The source's proof is "immediate from the construction and Lemma 0FAM". Here it is the
additivity `Stacks.Chow.localizedModificationClass_add` of the generic construction of
`StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Modification` (which is Stacks 0FAM for the
extension along `W_∞ = T ∪ E` followed by the bilinear composition with the class of Stacks 0F9J
and the pushforward `(E ⟶ Z)_*`) at the classes `P_p(Q), P_p(Q') ∈ A^p(W)`, together with the
additivity `P_p(Q ⊕ Q') = P_p(Q) + P_p(Q')` of Stacks 0F9F (`Stacks.Chow.perfectPowerSum_biprod`).

## Main results

* `Stacks.Chow.modificationPowerSum_biprod` — **Stacks 0FAZ**.

## Implementation notes

The class `P'_p(Q ⊕ Q')` is formed with the proofs that the Chern classes of `Q ⊕ Q'` are defined
(`Stacks.Chow.hasDefinedChernClasses_biprod`) and that `Q ⊕ Q'` restricts to zero on `T`
(`Stacks.Chow.isZero_derivedPullback_biprod`), both derived from the hypotheses on `Q` and `Q'`,
as in the source. The direct sum is the biproduct `Q ⊞ Q'` of the derived category.

## References

* [Stacks Project, Tag 0FAZ](https://stacks.math.columbia.edu/tag/0FAZ)
* [Stacks Project, Tag 0FAM](https://stacks.math.columbia.edu/tag/0FAM)
* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X W Z T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {Q Q' : DerivedCategory W.Modules}

/-- **Stacks 0FAZ.** In the situation of Stacks 0F9K, let `Q, Q' ∈ D(𝒪_W)` have defined Chern
classes, and let `T ⊆ W_∞` be closed, contain every point of `W_∞` lying over `X ∖ Z`, and be such
that `Q|_T` and `Q'|_T` are zero. Then the classes `P'_p(Q)`, `P'_p(Q')`, `P'_p(Q ⊕ Q')` of
`A^p(Z ⟶ X)` constructed in Stacks 0F9K (`Stacks.Chow.modificationPowerSum`) satisfy
`P'_p(Q ⊕ Q') = P'_p(Q) + P'_p(Q')`. -/
@[stacks 0FAZ]
theorem modificationPowerSum_biprod (hQ : HasDefinedChernClasses Q)
    (hQ' : HasDefinedChernClasses Q') (p : ℕ)
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q))
    (hzero' : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q')) :
    modificationPowerSum C f b hA z t (hasDefinedChernClasses_biprod hQ hQ') p hT
        (isZero_derivedPullback_biprod _ hzero hzero') =
      modificationPowerSum C f b hA z t hQ p hT hzero +
        modificationPowerSum C f b hA z t hQ' p hT hzero' := by
  have hv : ∀ {R : DerivedCategory W.Modules} (hR : HasDefinedChernClasses R),
      IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj R) →
      BivariantClass.VanishesOver (perfectPowerSumComponent C (modificationProjection f b ≫ f) hR p)
        (t ≫ modificationInclusionAtInfinity f b) := fun hR hz ↦
    vanishesOver_perfectPowerSumClass_of_isZero C (modificationProjection f b ≫ f) _ hR p hz
  have hsum : perfectPowerSumComponent C (modificationProjection f b ≫ f)
      (hasDefinedChernClasses_biprod hQ hQ') p =
      perfectPowerSumComponent C (modificationProjection f b ≫ f) hQ p +
        perfectPowerSumComponent C (modificationProjection f b ≫ f) hQ' p :=
    congrArg (fun c : TotalChowClass C (modificationProjection f b ≫ f) ↦ c p)
      (perfectPowerSum_biprod C (modificationProjection f b ≫ f) hQ hQ'
        (hasDefinedChernClasses_biprod hQ hQ') p)
  exact (localizedModificationClass_congr (gysinAtInfinityData C f b hA) z t hT hsum
    (hv _ (isZero_derivedPullback_biprod _ hzero hzero'))
    (BivariantClass.VanishesOver.add (hv hQ hzero) (hv hQ' hzero'))).trans
    (localizedModificationClass_add (gysinAtInfinityData C f b hA) z t hT (hv hQ hzero)
      (hv hQ' hzero'))

end Stacks.Chow

end
