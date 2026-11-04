module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentIndex
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentLength
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.MultiplicityDifference

/-!
# The coefficient identity summed over the components through the point

The right-hand side of
`Stacks.Chow.exists_affineOpen_sheafMultiplicity_denominatorQuotients_sub_eq` is a sum over the
minimal primes of the local ring `𝒪_{X, ξ}`, which is the shape the length formula of
[Stacks, Tag 02QH] produces. Part (4) of [Stacks, Tag 02SW] states its right-hand side as a sum
over the irreducible components of `X` of delta-dimension `k + 1` through `ξ`. This file performs
the two changes of shape that do not need new mathematics:

* the **index** is moved along the bijection of
  `Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_bot`, which identifies the minimal primes of
  `𝒪_{X, ξ}` with the generic points of the components through `ξ`;
* the **coefficient** is rewritten into `Stacks.Chow.sheafMultiplicity F`, the multiplicity `mᵢ`
  appearing in part (4), by
  `Stacks.Chow.length_localizedModule_stalk_eq_sheafMultiplicity`.

What is deliberately *not* done is eliminating `q` from the order-of-vanishing factor. That needs
the component's order of vanishing — `Stacks.Chow.ord_subschemeStalk` together with
`Stacks.Chow.ord_eq_ringOrd_germ` on the integral component — and so belongs with that step, not
with this bookkeeping.

## Main results

* `Stacks.Chow.finsum_componentGenericPoints_eq` — a sum over the generic points of the components
  through `ξ` is the corresponding sum over the minimal primes of `𝒪_{X, ξ}`, for an arbitrary
  summand. This is the re-indexing, and it is stated for an arbitrary `AddCommMonoid` because
  nothing about it is specific to `ℤ`.
* `Stacks.Chow.exists_affineOpen_sheafMultiplicity_sub_eq_finsum_sheafMultiplicity` — the
  coefficient identity with the coefficients written as multiplicities of `F`.

## Implementation notes

The re-indexing is `Set.BijOn.image_eq` followed by Mathlib's `finsum_mem_image`, which needs
only injectivity on the index set; the surjectivity half of the bijection is what turns the image
into the set of component generic points. No finiteness of either index set is needed —
`finsum` is defined for an arbitrary summand and is zero outside the support — so the statement
carries no local finiteness hypothesis, even though in the situation of part (4) both sets are in
fact finite.

The coefficient rewrite happens *inside* the sum, by `finsum_mem_congr` at the identity on index
sets, so the index set is untouched by it and the two changes of shape compose in either order.

`Stacks.Chow.length_localizedModule_stalk_eq_sheafMultiplicity` asks for quasi-coherence of `F`,
which here comes from coherence through
`Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent`; coherence is
one of Tag 02SW's own hypotheses, so nothing new is assumed.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

universe u

namespace Stacks.Chow

/-- **A sum over the generic points of the irreducible components through `ξ` is the sum over the
minimal primes of the local ring at `ξ`.** The bijection is `X.fromSpecStalk ξ`, by
`Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_bot`; no hypothesis on `X` and no finiteness of
either index set. -/
theorem finsum_componentGenericPoints_eq {X : Scheme.{u}} {M : Type*} [AddCommMonoid M]
    (ξ : X) (g : X → M) :
    ∑ᶠ η ∈ {η : X | η ⤳ ξ ∧ ∀ η' : X, η' ⤳ η → η' = η}, g η =
      ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk ξ) |
          q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)}, g (X.fromSpecStalk ξ q) := by
  have hb := bijOn_fromSpecStalk_minimalPrimes_bot ξ
  rw [← hb.image_eq]
  exact finsum_mem_image hb.2.1

/-- **The coefficient identity of part (4) with the coefficients written as multiplicities of
`F`.** This is `Stacks.Chow.exists_affineOpen_sheafMultiplicity_denominatorQuotients_sub_eq` with
the length of the localization of `F_ξ` at each minimal prime replaced, by
`Stacks.Chow.length_localizedModule_stalk_eq_sheafMultiplicity`, by the multiplicity of `F` at
the corresponding point of `X` — which is the `mᵢ` of part (4). The index set is unchanged;
`Stacks.Chow.finsum_componentGenericPoints_eq` moves it to the component generic points. -/
theorem exists_affineOpen_sheafMultiplicity_sub_eq_finsum_sheafMultiplicity
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : X.Modules) (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    [F.IsCoherent] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (_hX : HasNoEmbeddedPoints X)
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    {ξ : X} (hξ : ξ ∈ denominatorBadLocus X L s)
    (hδ : relativeDimension C.dimensionFunction f ξ = k) :
    ∃ (V : X.Opens) (hξV : ξ ∈ V), IsAffineOpen V ∧ ∃ a b : Γ(X, V),
      sheafMultiplicity
            (@DenominatorStalk.denominatorSectionQuotientDecl X L F s
              (LocallyOfFiniteType.isLocallyNoetherian f) hL hs inferInstance hF hSupp) ξ -
          sheafMultiplicity (denominatorQuotientDecl L F s) ξ =
        ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk ξ) |
            q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)},
          sheafMultiplicity F (X.fromSpecStalk ξ q) *
            (((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
                (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV a))).toNat : ℤ) -
              ((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
                (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV b))).toNat : ℤ)) := by
  have : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  obtain ⟨V, hξV, hVaff, a, b, hid⟩ :=
    exists_affineOpen_sheafMultiplicity_denominatorQuotients_sub_eq C f L F s hdim _hX hF hSupp
      hL hs hξ hδ
  refine ⟨V, hξV, hVaff, a, b, hid.trans ?_⟩
  refine finsum_mem_congr rfl fun q _ => ?_
  exact congrArg
    (fun z : ℤ => z *
      (((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
          (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV a))).toNat : ℤ) -
        ((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
          (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV b))).toNat : ℤ)))
    (length_localizedModule_stalk_eq_sheafMultiplicity F q)

end Stacks.Chow

end
