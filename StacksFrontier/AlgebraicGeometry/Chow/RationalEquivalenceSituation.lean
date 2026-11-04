module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs

/-!
# Rational equivalence depends only on the relative dimension function

Fix a scheme `X` and two base situations `C` and `D` of chapter 42 of the Stacks Project, together
with morphisms `p : X ⟶ C.S` and `q : X ⟶ D.S` locally of finite type. The group of `k`-cycles and
the subgroup of cycles rationally equivalent to zero are both defined through the relative
dimension function `Stacks.Chow.relativeDimension` attached to the base, and through nothing else
about the base. So if the two relative dimension functions on `X` agree, and continue to agree
after restricting along an arbitrary closed immersion `j : W ⟶ X`, then the two notions of
"rationally equivalent to zero" agree as well.

The hypothesis is stated for every closed immersion into `X` because the definition of rational
equivalence quantifies over integral closed subschemes `W ⊆ X`: the dimension condition on the
family is a condition on `Stacks.Chow.schemeDeltaDimension` of `W`, and the coefficients of the
pushed-forward principal divisors are weighted by the relative dimension functions both of `X` and
of `W`. Taking `j = 𝟙 X` recovers agreement on `X` itself.

## Main results

* `Stacks.Chow.isRationallyEquivalentToZero_congr` — a cycle is rationally equivalent to zero for
  `C` and `p` exactly when the cycle with the same coefficients is rationally equivalent to zero
  for `D` and `q`, provided the two relative dimension functions agree after restriction along
  every closed immersion into `X`.

## Implementation notes

The proof is a transport of the data witnessing `Stacks.Chow.IsRationallyEquivalentToZero`: the
family of integral closed subschemes, its local finiteness and the rational functions on its
members involve neither base situation, so the same data serves both sides. Only two ingredients
have to be matched, and each gets its own auxiliary lemma: the delta-dimension of a member of the
family, and the pushforward of a principal divisor from a member of the family to `X`. The
`IsLocallyNoetherian` instance used by `Stacks.Chow.principalDivisorPushforward` is derived from
the structure morphism and hence differs between the two sides, but it is a proof of a
proposition, so the two terms are definitionally equal.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- The delta-dimension of a closed subscheme `j : W ⟶ X` is unchanged when the base situation is
replaced by one whose relative dimension function on `W` agrees with the original. -/
private theorem schemeDeltaDimension_congr (C D : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (q : X ⟶ D.S) [LocallyOfFiniteType q]
    {W : Scheme.{u}} (j : W ⟶ X) [IsClosedImmersion j]
    (h : relativeDimension C.dimensionFunction (j ≫ p) =
      relativeDimension D.dimensionFunction (j ≫ q)) :
    schemeDeltaDimension C (j ≫ p) = schemeDeltaDimension D (j ≫ q) := by
  simp only [schemeDeltaDimension, deltaDimension, h]

/-- The pushforward of the principal divisor of a rational function on an integral closed
subscheme `V ⊆ X` is unchanged when the base situation is replaced by one whose relative dimension
functions on `X` and on `V` agree with the original ones. -/
private theorem principalDivisorPushforward_congr (C D : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (q : X ⟶ D.S) [LocallyOfFiniteType q]
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (g : (rationalFunctions V.subscheme)ˣ)
    (hbase : relativeDimension C.dimensionFunction p = relativeDimension D.dimensionFunction q)
    (hsub : relativeDimension C.dimensionFunction (V.subschemeι ≫ p) =
      relativeDimension D.dimensionFunction (V.subschemeι ≫ q)) :
    principalDivisorPushforward C p V hV g = principalDivisorPushforward D q V hV g := by
  unfold principalDivisorPushforward
  rw [hbase, hsub]

/-- One direction of `Stacks.Chow.isRationallyEquivalentToZero_congr`: the witnessing family of
integral closed subschemes and rational functions is transported unchanged, only its
delta-dimension condition and the coefficients of its pushed-forward principal divisors being
rewritten. -/
private theorem isRationallyEquivalentToZero_imp (C D : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (q : X ⟶ D.S) [LocallyOfFiniteType q]
    (h : ∀ (W : Scheme.{u}) (j : W ⟶ X) [IsClosedImmersion j],
      relativeDimension C.dimensionFunction (j ≫ p) =
        relativeDimension D.dimensionFunction (j ≫ q))
    (k : ℤ) (a : CycleGroup C p k) (b : CycleGroup D q k) (hab : a.1 = b.1)
    (ha : IsRationallyEquivalentToZero C p k a) :
    IsRationallyEquivalentToZero D q k b := by
  have hbase : relativeDimension C.dimensionFunction p =
      relativeDimension D.dimensionFunction q := by
    simpa only [Category.id_comp] using h X (𝟙 X)
  obtain ⟨J, W, hW, hdim, hlf, g, hg⟩ := ha
  refine ⟨J, W, hW, fun j ↦ ?_, hlf, g, fun x ↦ ?_⟩
  · rw [← schemeDeltaDimension_congr C D p q (W j).subschemeι (h _ (W j).subschemeι)]
    exact hdim j
  · rw [← hab, hg x]
    unfold principalDivisorFamilyCoefficient
    refine finsum_congr fun j ↦ ?_
    rw [principalDivisorPushforward_congr C D p q (W j) (hW j) (g j) hbase
      (h _ (W j).subschemeι)]

/-- **Stacks 02RW.** Being rationally equivalent to zero depends only on the relative dimension
function: if two base situations `C` and `D` of chapter 42, with structure morphisms
`p : X ⟶ C.S` and `q : X ⟶ D.S` locally of finite type, induce the same relative dimension
function on `W` for every closed immersion `j : W ⟶ X`, then a `k`-cycle for `C` is rationally
equivalent to zero exactly when the `k`-cycle for `D` with the same coefficients is. -/
theorem isRationallyEquivalentToZero_congr (C D : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (q : X ⟶ D.S) [LocallyOfFiniteType q]
    (h : ∀ (W : Scheme.{u}) (j : W ⟶ X) [IsClosedImmersion j],
      relativeDimension C.dimensionFunction (j ≫ p) =
        relativeDimension D.dimensionFunction (j ≫ q))
    (k : ℤ) (a : CycleGroup C p k) (b : CycleGroup D q k) (hab : a.1 = b.1) :
    IsRationallyEquivalentToZero C p k a ↔ IsRationallyEquivalentToZero D q k b :=
  ⟨isRationallyEquivalentToZero_imp C D p q h k a b hab,
    isRationallyEquivalentToZero_imp D C q p (fun W j _ ↦ (h W j).symm) k b a hab.symm⟩

end Stacks.Chow

end
