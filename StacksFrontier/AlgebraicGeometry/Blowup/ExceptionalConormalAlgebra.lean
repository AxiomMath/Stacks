module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.ReesPullback

/-!
# The Rees algebra of a centre, pulled back to the centre, is a conormal algebra

Let `i : Z ⟶ X` be a closed immersion of schemes and let `ℐ = ker(i)` be its ideal sheaf.  The
blowup of `X` in `ℐ` is the relative `Proj` of the Rees algebra `⨁ₙ ℐⁿ`, and its exceptional
divisor is the inverse image of `Z`; so the graded algebra governing the exceptional divisor is
the pullback along `i` of that Rees algebra.

This file identifies that pullback as a *conormal algebra* in the sense of [Stacks, Tag 0630]:
it equips `Stacks.Conormal.gradedPullback i (⨁ₙ ℐⁿ)` with the canonical local
associated-graded presentations, i.e. with a `Stacks.Conormal.ConormalAlgebraData i` structure.

Together with `Stacks.Conormal.ConormalAlgebraData.iso`, which says those presentations
determine the algebra, this is the bridge between the graded algebra of the blowup and the
conormal algebra of Tag 0630.

## Main definitions

* `Stacks.Conormal.reesPullbackConormalAlgebra`: **the pullback of the Rees algebra of `ℐ` along
  `i`, with its local associated-graded presentations**, for any quasi-coherent ideal sheaf `ℐ`
  identified with `ker(i)`.

## Main results

* `Stacks.Conormal.chartIdeal_eq_ker_ideal`: on an affine open the chart ideal of a closed
  immersion is `ℐ(U)`.
* `Stacks.Conormal.reesPullbackConormalAlgebra_algebra` and
  `Stacks.Conormal.reesPullbackConormalAlgebra_localMap`: the underlying graded algebra is the
  graded pullback, and its presentation on a chart is `Stacks.Conormal.reesPullbackMap`.

## Implementation notes

Nothing is proved here that is not already proved: the six properties the structure asks of a
presentation — surjectivity, the kernel, linearity, compatibility with restriction,
multiplicativity and the unit — are exactly the six lemmas of
`StacksFrontier/AlgebraicGeometry/ConormalAlgebra/ReesPullback.lean` about
`Stacks.Conormal.reesPullbackMap`, which are stated there for an arbitrary morphism to `X`.  What
this file supplies is their assembly, and the one translation they need: those lemmas are indexed
by the powers of `ℐ(U)` while `Stacks.Conormal.ConormalAlgebraData` is indexed by the powers of
the *chart ideal* `ker (i^♯_U)` of the immersion, and the two ideals are equal, by
`AlgebraicGeometry.Scheme.Hom.ker_apply` and the hypothesis `ker(i) = ℐ`.

**The ideal sheaf is a parameter, with its identification with `ker(i)` a hypothesis, rather than
being `ker(i)` itself.**  `ker(ℐ.subschemeι) = ℐ` is a theorem and not a definitional equality, so
with `ℐ` spelled as `ker(i)` the graded algebra below would not be the one the blowup of `ℐ` is
the relative `Proj` of, and the two would have to be compared by transport through a propositional
equality of ideal sheaves — which is what making `ℐ` a parameter avoids.  The translation is
`Stacks.Conormal.chartPowEquiv`, the identity on the underlying sections, so every one of the six
fields reduces to its `ReesPullback` counterpart after rewriting that equality.

The hypotheses `Stacks.Conormal.ConormalAlgebraData` attaches to a chart — that the immersion
restricts to a closed immersion over it — are not used: `i` is a closed immersion outright, so
the affineness of the preimage of an affine open and the surjectivity of the map on its sections
hold on every affine open, by `AlgebraicGeometry.IsAffineOpen.preimage` and
`AlgebraicGeometry.Scheme.Hom.app_surjective`.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0631](https://stacks.math.columbia.edu/tag/0631)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (ℐ : X.IdealSheafData)
  (hℐ : i.ker = ℐ)

/-- The preimage of an affine open under a closed immersion is affine. -/
theorem isAffineOpen_preimage_closedImmersion (U : X.affineOpens) :
    IsAffineOpen (i ⁻¹ᵁ U.1) :=
  U.2.preimage i

include hℐ

/-- On an affine open the chart ideal of a closed immersion is the ideal sheaf of the immersion
on that open. -/
theorem chartIdeal_eq_ker_ideal (U : X.affineOpens) :
    chartIdeal i U = ℐ.ideal U :=
  (Scheme.Hom.ker_apply i U).symm.trans
    (congrArg (fun J : X.IdealSheafData => J.ideal U) hℐ)

/-- The `n`-th power of the chart ideal of `i` over an affine open, identified with the `n`-th
power of `ker(i)(U)`.  It is the identity on the underlying sections. -/
def chartPowEquiv (U : X.affineOpens) (n : ℕ) :
    ↥(chartIdeal i U ^ n) ≃+ ↥(ℐ.ideal U ^ n) :=
  (LinearEquiv.ofEq _ _ (congrArg (· ^ n) (chartIdeal_eq_ker_ideal i ℐ hℐ U))).toAddEquiv

/-- The equivalence `chartPowEquiv` is the identity on underlying sections. -/
@[simp]
theorem coe_chartPowEquiv (U : X.affineOpens) (n : ℕ)
    (a : ↥(chartIdeal i U ^ n)) :
    ((chartPowEquiv i ℐ hℐ U n a : ↥(ℐ.ideal U ^ n)) : Γ(X, U)) = (a : Γ(X, U)) :=
  rfl

/-- **The pullback along `i` of the Rees algebra `⨁ₙ ker(i)ⁿ`, as a conormal algebra.**  Its
degree-`n` sections over the preimage of an affine open `U` are `ℐ(U)ⁿ/ℐ(U)ⁿ⁺¹`, presented by
`Stacks.Conormal.reesPullbackMap`. -/
def reesPullbackConormalAlgebra : ConormalAlgebraData i where
  algebra := gradedPullback i (Stacks.Blowup.reesGradedAlgebra ℐ)
  isQuasicoherent n :=
    gradedPullback_isQuasicoherent i (Stacks.Blowup.reesGradedAlgebra ℐ)
      (Stacks.Blowup.reesPiece_isQuasicoherent ℐ) n
  negative_isZero n hn :=
    gradedPullback_negative_isZero i (Stacks.Blowup.reesGradedAlgebra ℐ)
      (Stacks.Blowup.reesPiece_negative_isZero ℐ) n hn
  localMap U _ n := (reesPullbackMap ℐ i n U).comp (chartPowEquiv i ℐ hℐ U n).toAddMonoidHom
  localMap_eq_zero_iff U _ n a := by
    refine (reesPullbackMap_eq_zero_iff ℐ i n U
      (isAffineOpen_preimage_closedImmersion i U) ?_
      (Scheme.Hom.app_surjective i U.1 U.2) _).trans ?_
    · exact chartIdeal_eq_ker_ideal i ℐ hℐ U
    · change ((chartPowEquiv i ℐ hℐ U n a : ↥(ℐ.ideal U ^ n)) : Γ(X, U)) ∈ _ ↔ _
      rw [coe_chartPowEquiv]
      exact iff_of_eq (congrArg (fun J : Ideal Γ(X, U) => (a : Γ(X, U)) ∈ J ^ (n + 1))
        (chartIdeal_eq_ker_ideal i ℐ hℐ U).symm)
  localMap_surjective U _ n :=
    (reesPullbackMap_surjective ℐ i n U (isAffineOpen_preimage_closedImmersion i U)
      (Scheme.Hom.app_surjective i U.1 U.2)).comp (chartPowEquiv i ℐ hℐ U n).surjective
  localMap_smul U _ n r a b hb := by
    have hrw : chartPowEquiv i ℐ hℐ U n b = r • chartPowEquiv i ℐ hℐ U n a := Subtype.ext (by
      simp only [coe_chartPowEquiv, SetLike.val_smul, smul_eq_mul]
      exact hb)
    change reesPullbackMap ℐ i n U (chartPowEquiv i ℐ hℐ U n b) = _
    rw [hrw]
    exact reesPullbackMap_smul ℐ i n U r (chartPowEquiv i ℐ hℐ U n a)
  localMap_naturality U V hVU hZU _ _ n a b hb := by
    change ((gradedPullback i (Stacks.Blowup.reesGradedAlgebra ℐ)).piece
          (n : ℤ)).val.map (homOfLE hZU).op
        (reesPullbackMap ℐ i n U (chartPowEquiv i ℐ hℐ U n a)) =
      reesPullbackMap ℐ i n V (chartPowEquiv i ℐ hℐ V n b)
    exact reesPullbackMap_naturality ℐ i n V U hVU hZU _ _ (by
      rw [coe_chartPowEquiv, coe_chartPowEquiv, hb])
  localMap_mul U _ n m a b c hc := by
    change reesPullbackMap ℐ i (n + m) U (chartPowEquiv i ℐ hℐ U (n + m) c) = _
    exact reesPullbackMap_mul ℐ i n m U (chartPowEquiv i ℐ hℐ U n a)
      (chartPowEquiv i ℐ hℐ U m b) (chartPowEquiv i ℐ hℐ U (n + m) c) (by
        rw [coe_chartPowEquiv, coe_chartPowEquiv, coe_chartPowEquiv, hc])
  localMap_one U _ a ha := by
    change reesPullbackMap ℐ i 0 U (chartPowEquiv i ℐ hℐ U 0 a) = _
    exact reesPullbackMap_one ℐ i U (chartPowEquiv i ℐ hℐ U 0 a) (by
      rw [coe_chartPowEquiv, ha])

/-- The graded algebra of `reesPullbackConormalAlgebra` is the pullback along `i` of the Rees
algebra of `ℐ`. -/
@[simp]
theorem reesPullbackConormalAlgebra_algebra :
    (reesPullbackConormalAlgebra i ℐ hℐ).algebra =
      gradedPullback i (Stacks.Blowup.reesGradedAlgebra ℐ) := rfl

/-- The local map of `reesPullbackConormalAlgebra` in degree `n` over an affine open `U` is
`reesPullbackMap` composed with `chartPowEquiv`. -/
theorem reesPullbackConormalAlgebra_localMap (U : X.affineOpens)
    (hU : IsClosedImmersion
      (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) (n : ℕ)
    (a : ↥(chartIdeal i U ^ n)) :
    (reesPullbackConormalAlgebra i ℐ hℐ).localMap U hU n a =
      reesPullbackMap ℐ i n U (chartPowEquiv i ℐ hℐ U n a) := rfl

end Stacks.Conormal

end
