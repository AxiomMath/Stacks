module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Localized
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.PreparationNewton
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedCap

/-!
# Newton's identities for the localized classes of Stacks 0FB2

Let `(S, δ)`, `X`, `E` and `i : Z ⟶ X` be as in Situation 0GUJ, and assume `E|_{X ∖ Z}` is zero.
Then the zero sheaf has rank `< p` for every `p ≥ 1`, so the localized Chern classes
`c_p(Z ⟶ X, E)` are defined for every `p ≥ 1`, besides the classes `P_p(Z ⟶ X, E)`. **Stacks
0FBA** (Lemma 42.50.11) says that, in the algebra `A^{(1)}(Z ⟶ X)` of Remark 42.50.1 (Stacks 0FA0),

  `P_1 = c_1`,  `P_2 = c_1² - 2c_2`,  `P_3 = c_1³ - 3c_1c_2 + 3c_3`,

and so on. The source deduces it from Stacks 0FAX, since the localized classes are constructed by
the procedure of Stacks 0F9K; this file does exactly that.

## Main definitions

* `Stacks.Chow.LocalizedSituation.withDegree` — for `E|_{X ∖ Z}` zero, the situation with
  the degree replaced by any `q`, in which `c_q(Z ⟶ X, E)` is formed.
* `Stacks.Chow.LocalizedSituation.localizedChernClassOfIsZero` — `c_q(Z ⟶ X, E)` for
  `E|_{X ∖ Z}` zero and `q ≥ 1`.

## Main results

* `Stacks.Chow.LocalizedSituation.isFiniteLocallyFreeOfRankLTOnComplement_withDegree` — in
  degree `q ≥ 1` the second alternative of condition (2) holds, the zero module having rank `< q`.
* `Stacks.Chow.LocalizedSituation.localizedPowerSum_succ` — **Stacks 0FBA**: Newton's recursion
  `P_{q+1} = ∑_{j<q} (-1)^j c_{j+1} P_{q-j} + (-1)^q (q+1) c_{q+1}` in Situation 0GUJ, for the
  classes `P_p(Z ⟶ X, E)` and `c_p(Z ⟶ X, E)` of Stacks 0FB2.

## Implementation notes

As in Stacks 0FAX (`Stacks.Chow.modificationPowerSum_succ`), the "and so on" of the source is
Newton's recursion, which determines `P_p` as the universal power-sum polynomial in the `c_i`; the
products are the multiplication `(c, c') ↦ res(c) ∘ c'` of Stacks 0FA0
(`Stacks.Chow.supportedMul`), bracketed to the right and read in the degree of the left side.

The class `c_q(Z ⟶ X, E)` of the source is that of Stacks 0FB2 for the situation in degree `q`; it
is built with the locus `T' ⊆ T` where `Q` is finite locally free of rank `< q`, whereas `P_p` is
built with the locus where `Q` is zero. Both loci contain every point of `W_∞` over `X ∖ Z`, so
by the independence of the closed subscheme (`Stacks.Chow.localizedModificationClass_eq`, the first
assertion of Stacks 0FAU) the two constructions may be compared on the zero locus, where
Stacks 0FAX applies. The situation in degree `q` is an `abbrev`, so that the instances attached to
the fields of `S` apply to it.

## References

* [Stacks Project, Tag 0FBA](https://stacks.math.columbia.edu/tag/0FBA)
* [Stacks Project, Tag 0FAX](https://stacks.math.columbia.edu/tag/0FAX)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

namespace LocalizedSituation

variable (S : LocalizedSituation.{u}) (h : S.IsZeroOnComplement)

/-- For `E|_{X ∖ Z}` zero, the situation of Stacks 0GUJ in degree `q`: everything is that of `S`
except the degree, condition (2) holding through its first alternative. -/
abbrev withDegree (q : ℕ) : LocalizedSituation.{u} where
  base := S.base
  X := S.X
  a := S.a
  locallyOfFiniteType := S.locallyOfFiniteType
  Z := S.Z
  i := S.i
  isClosedImmersion := S.isClosedImmersion
  E := S.E
  p := q
  perfect := S.perfect
  restriction := Or.inl h
  finiteness := S.finiteness

/-- For `E|_{X ∖ Z}` zero, the situation in degree `q ≥ 1` satisfies the second alternative of
condition (2): the zero module is finite locally free of rank `< q`. -/
theorem isFiniteLocallyFreeOfRankLTOnComplement_withDegree {q : ℕ} (hq : 0 < q) :
    (S.withDegree h q).IsFiniteLocallyFreeOfRankLTOnComplement :=
  exists_isFiniteLocallyFreeOfRankLT_of_isZero (Scheme.Opens.ι _) h hq

variable {S}

/-- **The localized Chern class `c_q(Z ⟶ X, E)`, for `E|_{X ∖ Z}` zero and `q ≥ 1`**: the class of
Stacks 0FB2 for the situation in degree `q`. -/
abbrev localizedChernClassOfIsZero {q : ℕ} (hq : 0 < q) :
    BivariantClass S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl q :=
  (S.withDegree h q).localizedChern (S.isFiniteLocallyFreeOfRankLTOnComplement_withDegree h hq)

variable (S) in
/-- In Situation 0GUJ assume `E|_{X ∖ Z}` is zero. Then the
localized classes `P_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)` of Stacks 0FB2 are Newton's polynomials in the
localized Chern classes `c_i(Z ⟶ X, E)` (defined for every `i ≥ 1`, the zero module having
rank `< i`), with the multiplication of the algebra `A^{(1)}(Z ⟶ X)` of Stacks 0FA0
(`(c, c') ↦ res(c) ∘ c'`, `Stacks.Chow.supportedMul`):

  `P_{q+1} = ∑_{j < q} (-1)^j c_{j+1} P_{q-j} + (-1)^q (q + 1) c_{q+1}`

for every `q ≥ 0`. This is the recursion defining the universal power-sum polynomials, so
`P_1 = c_1`, `P_2 = c_1² - 2c_2`, `P_3 = c_1³ - 3c_1c_2 + 3c_3`, and so on. The summand
`c_{j+1} P_{q-j}` lies in `A^{(j+1)+(q-j)}(Z ⟶ X)`, read in degree `q + 1`.

Here `P_p(Z ⟶ X, E)` is `Stacks.Chow.LocalizedSituation.localizedPowerSum` and `c_i(Z ⟶ X, E)` is
`Stacks.Chow.LocalizedSituation.localizedChernClassOfIsZero`, the class
`Stacks.Chow.LocalizedSituation.localizedChern` for the situation in degree `i`; both are formed
in Situation 0GUJ, condition (3) making the Chern classes of the object `Q` of the graph
construction defined (`Stacks.Chow.LocalizedSituation.hasDefinedChernClasses_graphObject`,
Stacks 0GUE). -/
@[stacks 0FBA "In Situation 0GUJ with E|_{X ∖ Z} zero: Newton's recursion P_{q+1} = \
∑_{j<q} (-1)^j c_{j+1} P_{q-j} + (-1)^q (q+1) c_{q+1} for every q ≥ 0, products in the algebra \
A^{(1)}(Z → X) of 0FA0; it gives P_1 = c_1, P_2 = c_1² - 2c_2, P_3 = c_1³ - 3c_1c_2 + 3c_3 and \
so on, the whole lemma"]
theorem localizedPowerSum_succ (q : ℕ) :
    S.localizedPowerSum h (q + 1) =
      ∑ j ∈ (Finset.range q).attach, ((-1 : ℤ) ^ (j : ℕ)) •
          bivariantClassDegreeCongr S.base _ (S.i ≫ S.a) S.a S.i rfl
            (newton_degree_eq (Finset.mem_range.mp j.2))
            (supportedMul S.base (S.i ≫ S.a) S.a S.i rfl
              (localizedChernClassOfIsZero h (Nat.succ_pos (j : ℕ)))
              (S.localizedPowerSum h (q - j))) +
        ((-1 : ℤ) ^ q * ((q : ℤ) + 1)) • localizedChernClassOfIsZero h (Nat.succ_pos q) := by
  let := isProper_graphBlowupToBase S.a S.E S.perfect
  let := isClosedImmersion_graphZeroLocus_ι S.a S.E S.perfect S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology
  let hT₀ : IsClosedImmersion ((graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology).ι ≫ S.graphSubschemeι) :=
    IsClosedImmersion.comp _ _
  have hc : ∀ (i : ℕ) (hi : 0 < i), localizedChernClassOfIsZero h hi =
      modificationChernClassOfIsZero S.base S.a (graphBlowupToBase S.a S.E S.perfect)
        (isIso_pullback_snd_graphBlowupToBase S.a S.E S.perfect) S.i
        ((graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
          S.isFiniteLocallyFree_graphObjectRestrictHomology).ι ≫ S.graphSubschemeι)
        S.hasDefinedChernClasses_graphObject
        (mem_range_graphZeroLocus S.base S.a S.E S.perfect S.i S.graphSubschemeι
          S.isFiniteLocallyFree_graphObjectRestrictHomology S.mem_range_graphSubschemeι
          (S.finiteLocallyFreeRank_graphSubscheme_eq_zero h))
        (isZero_derivedPullback_graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
          S.isFiniteLocallyFree_graphObjectRestrictHomology) i hi := fun i hi => by
    let := isClosedImmersion_graphSmallRankLocus_ι S.a S.E S.perfect S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology i
    let : IsClosedImmersion ((graphSmallRankLocus S.a S.E S.perfect S.graphSubschemeι
        S.isFiniteLocallyFree_graphObjectRestrictHomology i).ι ≫ S.graphSubschemeι) :=
      IsClosedImmersion.comp _ _
    exact localizedModificationClass_eq _ _ _ _ _ _
      (vanishesOver_perfectChernClass_of_rankLT _ _ _ S.hasDefinedChernClasses_graphObject i
        (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_graphSmallRankLocus S.a S.E S.perfect
          S.graphSubschemeι S.isFiniteLocallyFree_graphObjectRestrictHomology i))
      (vanishesOver_perfectChernClass_of_rankLT _ _ _ S.hasDefinedChernClasses_graphObject i
        (exists_isFiniteLocallyFreeOfRankLT_of_isZero _
          (isZero_derivedPullback_graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
            S.isFiniteLocallyFree_graphObjectRestrictHomology) hi))
  simp only [hc]
  exact modificationPowerSum_succ _ _ _ _ _ _ _ _ _ q

end LocalizedSituation

end Stacks.Chow

end
