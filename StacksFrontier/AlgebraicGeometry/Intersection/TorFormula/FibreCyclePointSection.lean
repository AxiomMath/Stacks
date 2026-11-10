module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleNonsingularVariety
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0B07 part (1)(a) at an arbitrary closed point of the projective line

The statements of Tag 0B07 in
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleRationalEquivalence` and
`...FibreCycleNonsingularVariety` read the clauses of the tag at the two *distinguished* points
`a = 0` and `b = ∞` of the projective line, because the image of a section of `X ×_S ℙ¹_S ⟶ X`
was known to be an effective Cartier divisor only for those two. This file reads part (1)(a) at
an arbitrary point instead: for a global function `t` on the base — for `S = Spec k` an element
of `k`, that is a `k`-rational point of `𝔸¹_k ⊆ ℙ¹_k`, and for `k` algebraically closed every
closed point of `ℙ¹_k` other than `∞` — the image of
`Stacks.Chow.pointSection` is an effective Cartier divisor
(`Stacks.Chow.isEffectiveCartierDivisor_ker_pointSection`), and everything part (1)(a) needs
follows from that exactly as it does at the zero section.

Together with the infinity-section statements already in the repository, part (1)(a) therefore
holds at an arbitrary pair of distinct closed points `a ≠ b` of `ℙ¹_k`: each of `a`, `b` is
either `∞` or a point of the affine chart, and the clause is proved at each of them separately.

## Main results

* `Stacks.Chow.localConditions_ker_pointSection`: **the local hypotheses of part (1)(a) at an
  arbitrary point, discharged.**
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_sup_pointSection_eq_intersectionProductCycle`:
  **Tag 0B07 part (1)(a) at an arbitrary point**, over an arbitrary Chow situation.
* the `_of_isRegular` variant of the same name: part (1)(a) at an arbitrary point for a
  nonsingular variety over an algebraically closed field, with nothing assumed about the
  ambient family.

## Implementation notes

Nothing is reproved. The two statements are the existing
`Stacks.Chow.cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle`, which is already
stated for an arbitrary closed subscheme `D`, read with `D` the image of the section at `t`; the
only thing that was missing was the effective Cartier property of that image, which is
`Stacks.Chow.isEffectiveCartierDivisor_ker_pointSection`.

Part (1)(b) at an arbitrary point is carried in
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCyclePointSectionPushforward`, which
reads the same cycle on `X` through the fibre at that point.

Part (2) at an arbitrary pair is carried in the sibling module
`TorFormula.FibreCyclePointSectionRationalEquivalence`,
not by moving the pair to `(0, ∞)` — Tag 0B2U is still not invoked anywhere — but by exhibiting
the difference of the two fibre cycles as the pushforward of the principal divisor of
`(z - t) / (z - t')`, which Tag 02RW admits for an arbitrary rational function. Part (3), the
converse, is carried at an arbitrary pair of points of the affine chart in the sibling module
`TorFormula.FibreCyclePointSectionRationalEquivalenceCycle`; what is *not* done is a pair with one
point at infinity.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.TorFormula CategoryTheory CategoryTheory.Limits
  TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (t : Γ(C.S, ⊤)) (W : (projectiveLineProduct p).IdealSheafData)

/-- **The local hypotheses of Stacks 0B07 part (1)(a) at an arbitrary point, discharged.** The
image of the section of `X ×_S ℙ¹_S` at a point `t` of the affine chart of `ℙ¹_S` is an
effective Cartier divisor (`Stacks.Chow.isEffectiveCartierDivisor_ker_pointSection`), so for a
closed subvariety `W` of delta-dimension `k + 1` meeting it properly the local conditions of
part (1)(a) hold along the intersection. This is
`Stacks.Chow.localConditions_ker_zeroSection` with the distinguished point `0` replaced by an
arbitrary one. -/
theorem localConditions_ker_pointSection [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    ∀ z : projectiveLineProduct p,
      relativeDimension C.dimensionFunction
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) z = k →
      z ∈ (W ⊔ (pointSection p t).ker).support →
        IsDomain ((projectiveLineProduct p).presheaf.stalk z ⧸ IdealSheafData.stalk W z) ∧
        (∃ g : Fin 1 → (projectiveLineProduct p).presheaf.stalk z,
          RingTheory.Sequence.IsRegular ((projectiveLineProduct p).presheaf.stalk z)
            (List.ofFn g) ∧
            IdealSheafData.stalk (pointSection p t).ker z = Ideal.span (Set.range g)) ∧
        ringKrullDim ((projectiveLineProduct p).presheaf.stalk z ⧸
          IdealSheafData.stalk ((pointSection p t).ker ⊔ W) z) = 0 ∧
        ringKrullDim ((projectiveLineProduct p).presheaf.stalk z ⧸
          IdealSheafData.stalk W z) = 1 :=
  localConditions_of_isEffectiveCartierDivisor C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) W (pointSection p t).ker
    inferInstance (isEffectiveCartierDivisor_ker_pointSection p t) hDim hWD

/-- **Stacks 0B07, part (1)(a), at an arbitrary point of the projective line.** Let `W` be a
closed subvariety of `X ×_S ℙ¹_S` of delta-dimension `k + 1` and let `a` be the point of `ℙ¹_S`
attached to a global function `t` on the base. If `W` meets `X × a` properly, then the cycle
`[W_a]_k` of the scheme-theoretic intersection is the Section 43.14 intersection product
`W · (X × a)`.

Nothing pointwise is assumed: the local conditions of the clause are derived from the source's
own hypotheses by `Stacks.Chow.localConditions_ker_pointSection`. -/
theorem cycleAssociatedToClosedSubscheme_sup_pointSection_eq_intersectionProductCycle
    [IsIntegral W.subscheme] (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (d : ℕ)
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    (cycleAssociatedToClosedSubscheme C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (W ⊔ (pointSection p t).ker).subschemeι k).1 =
      intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
        (subschemeStructureSheaf W) (subschemeStructureSheaf (pointSection p t).ker)
        (isCoherent_subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf (pointSection p t).ker) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
          (pointSection p t).ker k hWD) :=
  cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (pointSection p t).ker k d hd
    hWD (localConditions_ker_pointSection C p t W hDim hWD)

/-- **Stacks 0B07, part (1)(a), at an arbitrary point, for a nonsingular variety.** The cycle
`[W_a]_k` of the scheme-theoretic intersection `W ∩ (X × a)` is the Section 43.14 intersection
product `W · (X × a)`, for `a` an arbitrary point of the affine chart of `ℙ¹_S`. Nothing is
assumed about the ambient family: its regularity comes from nonsingularity of `X`, and the
finiteness of the alternating `Tor` sum from
`Stacks.Chow.exists_topologicalKrullDim_projectiveLineProduct_le`. -/
theorem cycleAssociatedToClosedSubscheme_sup_pointSection_eq_intersectionProductCycle_of_isRegular
    (Kf : Type u) [Field Kf] [IsAlgClosed Kf]
    (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
    [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)] (hX : IsRegular X) (k : ℤ)
    [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    (cycleAssociatedToClosedSubscheme C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (W ⊔ (pointSection p t).ker).subschemeι k).1 =
      intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (isRegular_projectiveLineProduct_of_eq p hC hX)
        (subschemeStructureSheaf W) (subschemeStructureSheaf (pointSection p t).ker)
        (isCoherent_subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf (pointSection p t).ker) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
          (isRegular_projectiveLineProduct_of_eq p hC hX) W (pointSection p t).ker k hWD) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  exact cycleAssociatedToClosedSubscheme_sup_pointSection_eq_intersectionProductCycle C p t W
    (isRegular_projectiveLineProduct_of_eq p hC hX) k d hd hDim hWD

end Stacks.Chow

end
