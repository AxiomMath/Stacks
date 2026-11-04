module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.ComparisonClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FibreStalk.RationalPointClosedFibre

/-!
# The closed-fibre ring of `X ×_S Y ⟶ S` at a point of `Y_s ×_k Y_s`

[Stacks, Tag 0G0R] applies [Stacks, Tag 0G0N] to the projection `p : X ×_S Y ⟶ S` at a closed
point `z` of its fibre over `s`, and the Koszul data it must hand over —
a regular sequence in the closed fibre of the stalk map of `p` — is read off the diagonal of the
smooth fibre `Y_s`, hence lives in the stalk of `Y_s ×_k Y_s`. This file identifies the two
rings, so that the data read off the diagonal is data of the deformation situation.

## Main results

* `AlgebraicGeometry.fibreSquareToProductComparisonIsoFibre` — the comparison morphism
  `i : Y_s ×_k Y_s ⟶ X ×_S Y` of [Stacks, Tag 0G0R] exhibits `Y_s ×_k Y_s` as the fibre
  `(X ×_S Y) ×_S Spec k`, as an isomorphism of schemes; it is the pullback square
  `AlgebraicGeometry.isPullback_fibreSquareToProductComparison` read as an isomorphism, and
  `AlgebraicGeometry.fibreSquareToProductComparisonIsoFibre_hom_fibreι` says it is compatible
  with `i`.
* `AlgebraicGeometry.exists_ringEquiv_quotient_stalk_fibreSquare` — **the identification of
  rings**: for `w : Y_s ×_k Y_s`, the closed-fibre ring
  `𝒪_{X ×_S Y, i(w)} / 𝔪_{S,s} 𝒪_{X ×_S Y, i(w)}` of the stalk map of `p` at `i(w)` is the stalk
  `𝒪_{Y_s ×_k Y_s, w}`, by an isomorphism carrying the class of a germ to its image under the
  stalk map of `i`.

## Implementation notes

Nothing is reproved here: the pullback square is
`AlgebraicGeometry.isPullback_fibreSquareToProductComparison` and the closed-fibre ring of a
stalk map at a point of a pullback along a `k`-rational point is
`AlgebraicGeometry.exists_ringEquiv_quotient_stalk_pullback_fst_of_isSection`. This file composes
them: the transport from the point of the pullback to the point `w` of `Y_s ×_k Y_s` is
`AlgebraicGeometry.exists_ringEquiv_quotient_stalk_of_iso` along the isomorphism of schemes over
`X ×_S Y` that `AlgebraicGeometry.fibreSquareToProductComparisonIsoFibre_hom_fibreι` exhibits, so
the compatibility with the stalk map of `i` comes along with it.

*No hypothesis beyond the source's.* `g` is arbitrary — neither smoothness nor properness is used
here, so neither is assumed — and the only hypothesis is the section condition `s ≫ q = 𝟙`.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {S Y : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (s : Spec (.of k) ⟶ S)

/-- `Y_s ×_k Y_s`, the self-product over `k` of the fibre at the `k`-rational point `s`: the
scheme along which [Stacks, Tag 0G0R] restricts its kernel. -/
abbrev fibreAtRationalPointSelfProduct : Scheme.{u} :=
  Limits.pullback (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s)

/-- **`Y_s ×_k Y_s` is the fibre of `X ×_S Y ⟶ S` over `s`**, as an isomorphism of schemes: the
pullback square `AlgebraicGeometry.isPullback_fibreSquareToProductComparison`, which is the
identification `Y_s × Y_s = (X ×_S Y)_s` with which [Stacks, Tag 0G0R] begins, read through the
`HasPullback` API. -/
def fibreSquareToProductComparisonIsoFibre (hs : s ≫ q = 𝟙 _) :
    fibreAtRationalPointSelfProduct g s ≅
      fibreAtRationalPoint (constantFamilyProductToBase q g s) s :=
  (isPullback_fibreSquareToProductComparison q g s hs).isoPullback

/-- The isomorphism `fibreSquareToProductComparisonIsoFibre` followed by the inclusion of the
fibre `(X ×_S Y) ×_S Spec k ⟶ X ×_S Y` is the comparison morphism
`fibreSquareToProductComparison`. -/
@[reassoc (attr := simp)]
theorem fibreSquareToProductComparisonIsoFibre_hom_fibreι (hs : s ≫ q = 𝟙 _) :
    (fibreSquareToProductComparisonIsoFibre q g s hs).hom ≫
        fibreAtRationalPointι (constantFamilyProductToBase q g s) s =
      fibreSquareToProductComparison q g s hs :=
  (isPullback_fibreSquareToProductComparison q g s hs).isoPullback_hom_fst

/-- **The closed-fibre ring of `X ×_S Y ⟶ S` at `i(w)` is the stalk of `Y_s ×_k Y_s` at `w`,
compatibly with the stalk map of `i`.** For `w : Y_s ×_k Y_s`, the quotient of the stalk of
`X ×_S Y` at `i(w)` by the image of the maximal ideal of `𝒪_{S,s}` is isomorphic to the stalk of
`Y_s ×_k Y_s` at `w`, by an isomorphism sending the class of a germ `b` to `i^♯_w b`. -/
theorem exists_ringEquiv_quotient_stalk_fibreSquare (hs : s ≫ q = 𝟙 _)
    (w : fibreAtRationalPointSelfProduct g s) :
    ∃ E : (((Limits.pullback (constantFamilyπ q g s) g).presheaf.stalk
            (fibreSquareToProductComparison q g s hs w)) ⧸
          Ideal.map ((constantFamilyProductToBase q g s).stalkMap
              (fibreSquareToProductComparison q g s hs w)).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk
              (constantFamilyProductToBase q g s
                (fibreSquareToProductComparison q g s hs w))))) ≃+*
        (fibreAtRationalPointSelfProduct g s).presheaf.stalk w,
      ∀ b, E (Ideal.Quotient.mk _ b) =
        ((fibreSquareToProductComparison q g s hs).stalkMap w).hom b :=
  exists_ringEquiv_quotient_stalk_of_iso (constantFamilyProductToBase q g s)
    (fibreSquareToProductComparisonIsoFibre q g s hs)
    (fibreAtRationalPointι (constantFamilyProductToBase q g s) s)
    (fibreSquareToProductComparison q g s hs)
    (fibreSquareToProductComparisonIsoFibre_hom_fibreι q g s hs)
    w ((fibreSquareToProductComparisonIsoFibre q g s hs).hom w) rfl
    (exists_ringEquiv_quotient_stalk_pullback_fst_of_isSection
      (constantFamilyProductToBase q g s) hs _)

end AlgebraicGeometry

end
