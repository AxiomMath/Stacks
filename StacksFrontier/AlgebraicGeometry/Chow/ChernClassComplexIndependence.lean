module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexLocallyBounded
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyRestrictionInjective
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# The independence of the representative, reduced to the modifications of the source's proof

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let `X`
be a scheme locally of finite type over `S`. **Stacks 0ESZ** says that for an object
`E ∈ D(𝒪_X)` represented by a locally bounded complex `ℰ^•` of finite locally free
`𝒪_X`-modules, the three classes

  `c(ℰ^•) ∈ ∏_{p ≥ 0} A^p(X)`,  `ch(ℰ^•) ∈ ∏_{p ≥ 0} A^p(X) ⊗ 𝐐`,  `P_p(ℰ^•) ∈ A^p(X)`

are independent of the choice of `ℰ^•`.

`Stacks.Chow.powerSumClassComplex_eq_of_cohomologyComparison` and its companions state that
independence in a form where the degreewise comparison datum of the source's last two
paragraphs — the finite local freeness of the kernels and images, and the module Schanuel's lemma
produces from the two presentations of each cohomology module — is assumed **on `X` itself**, as
`Stacks.Chow.BoundedComplexSplitting` and `Stacks.Chow.ComplexCohomologyComparison`. That is a
strong hypothesis, and the strength is not incidental: for a complex of finite locally free
modules on an arbitrary `X` the kernels of the differentials are *not* finite locally free, so
`Stacks.Chow.BoundedComplexSplitting X P a k` need not be inhabited for the very complexes the
source's statement is about. The source does not assume it there either. It produces it only
after two reductions:

* **Stacks 02UC**, which replaces the equality of two classes in `A^p(X)` by the vanishing of
  their difference capped against the fundamental class of every integral scheme `T` locally of
  finite type over `X`, and further allows `T` to be replaced by any integral scheme proper and
  birational over it; and
* **Stacks 0ESR**, which on such a modification makes every `H^i(Lg^*E)` perfect of tor dimension
  at most one, whereupon Stacks 0F8J gives the finite local freeness and Stacks 00O3 the Schanuel
  module.

This file carries out the **first** of those two reductions. Stacks 02UC is
`Stacks.Chow.BivariantClass.eq_zero_tfae`, and `A^p(X)` is a group of bivariant classes by
`Stacks.Chow.chowCohomologyComponent`, so the criterion applies to the difference of the two power
sum classes directly. What results is the independence statement with the comparison datum
demanded only where the source's proof produces it: on a proper birational modification of each
integral test scheme.

The file also proves the independence at the **locally bounded** generality of the source, for
the classes `Stacks.Chow.totalChernClassComplexLocallyBounded` and
`Stacks.Chow.powerSumClassComplexLocallyBounded`, on a quasi-compact scheme. That is a separate
matter from the reduction above and is independent of it; see "The locally bounded reading"
below.

## Main definitions

* `Stacks.Chow.HasPowerSumComparisonOnModifications` — the hypothesis of the reduction. For every
  integral `T` locally of finite type over `X` there is a proper birational `h : T' ⟶ T`, a power
  sum datum on `T'` compatible with the one on `X` under base change, and a comparison of the two
  pulled back complexes on `T'`. This is clause (3) of Stacks 02UC, specialized to the datum the
  source extracts on the modification.
* `Stacks.Chow.HasCohomologyComparisonAtCommonWindow` — the hypothesis of the locally bounded
  reading: a comparison of the two complexes at some one window outside which both vanish.

## Main results

* `Stacks.Chow.powerSumClassComplex_eq_of_hasPowerSumComparisonOnModifications` —
  **Stacks 0ESZ**, the independence of the representative for `P_p`, from the comparison datum on
  the modifications alone.
* `Stacks.Chow.chernCharacterComplexComponent_eq_of_hasPowerSumComparisonOnModifications` — the
  same for `ch_p(ℰ^•) = P_p(ℰ^•)/p!`.
* `Stacks.Chow.exists_common_window_of_isLocallyBoundedFiniteLocallyFree` — two locally bounded
  complexes on a quasi-compact scheme vanish outside one common window.
* `Stacks.Chow.totalChernClassComplexLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow`,
  `Stacks.Chow.powerSumClassComplexLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow`,
  `Stacks.Chow.chernCharacterLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow` —
  **Stacks 0ESZ**, the independence of the representative for the locally bounded classes, with no
  window in the statement, for all three of the source's classes.

## Implementation notes

None of the statements here carries `@[stacks 0ESZ]`. The tag, at its own hypotheses (an
isomorphism in the derived category, nothing carried), is registered on
`Stacks.Chow.complexChern_eq_of_iso`, `Stacks.Chow.complexPowerSumComponent_eq_of_iso` and
`Stacks.Chow.complexChernCharacter_eq_of_iso`; what is proved here are the comparison
statements that hold under the carried data described below.

### What this adds to `Stacks.Chow.powerSumClassComplex_eq_of_cohomologyComparison`

`Stacks.Chow.powerSumClassComplex_eq_of_cohomologyComparison` and the statements proved here are
about the same conclusion and are not comparable as hypotheses — neither implies the other — but
the hypothesis here is the source's. The datum on `X` is what the source would have to assume to
run its last two paragraphs on `X` directly, which it does not do; the datum on the modifications
is what it actually assumes, after Stacks 02UC. Both statements are kept: the one on `X` is the
cheaper to apply when a splitting happens to be available globally, and it is the one the
uniqueness theorems of Stacks 0GUD are stated against.

### The comparison datum on the modifications

On the modification, the source obtains the comparison datum from three results: Stacks 0ESR,
making every cohomology module perfect of tor dimension at most one (in the admissible blowup
form of Stacks 0ESQ, `AlgebraicGeometry.exists_admissibleBlowup_forall_isHomologyPerfectTorLEOne`);
Stacks 0F8J, the finite local freeness of the kernels and images
(`StacksDraft.Perfect.isFiniteLocallyFree_range_and_ker_of_torDimensionLE_one`); and Stacks 00O3,
Schanuel's lemma (`schanuel`, for modules over a ring). The Schanuel module is the fibre product
of the two surjections onto the cohomology module; its two projections are epimorphisms and the
kernel of each is the kernel of the opposite surjection, which holds in any abelian category, but
its finite local freeness comes from the tor dimension of the cohomology module. The statements
here take the resulting datum, `Stacks.Chow.HasPowerSumComparisonOnModifications`, as their
hypothesis.

### The base change compatibility

`Stacks.Chow.PowerSumClassRule` is data attached to a single scheme, and nothing in it relates the
datum on `X` to the datum on a scheme over `X`; `cls` is constrained only by vanishing off the
finite locally free modules and by additivity on their short exact sequences, so the zero family
and a nonzero additive family both qualify, and for two independently chosen data the equation
`res_g(P_p(ℰ)) = P_p(g^*ℰ)` is false. The reduction of Stacks 02UC is a statement about the
restriction of a class to a test scheme, so it cannot be run at all without that equation. It is
therefore asked for, as `Stacks.Chow.PowerSumClassRule.IsBaseChangeCompatible`, which is a
predicate on a pair of data and adds no field to either structure. In the source there is nothing
to ask: `P_p` is a construction and its compatibility with restriction is a theorem.

### The locally bounded reading

Stacks 0ESZ is about a *locally bounded* complex. The classes at that generality are defined on a
quasi-compact scheme, as `Stacks.Chow.totalChernClassComplexLocallyBounded` and
`Stacks.Chow.powerSumClassComplexLocallyBounded`. The statements
`Stacks.Chow.totalChernClassComplex_eq_of_cohomologyComparison` and
`Stacks.Chow.powerSumClassComplex_eq_of_cohomologyComparison` compare the classes of a complex
*presented with* a window, which are the window's classes and not the complex's; the second
section here compares the classes of the complex itself.

The locally bounded class does not depend on the window, by
`Stacks.Chow.totalChernClassComplexLocallyBounded_eq` and its power sum counterpart. So it
suffices to read both classes at one window outside which both complexes vanish — such a window
exists by `Stacks.Chow.exists_common_window_of_isLocallyBoundedFiniteLocallyFree`, which is why
the window is not a hypothesis of the statements — and apply the bounded-window statement there.
The hypothesis `Stacks.Chow.HasCohomologyComparisonAtCommonWindow` asks for the comparison datum
at one such window, not at every one, which is the weaker of the two demands. No class is
restricted along a morphism, so this reading covers the total Chern class
(`Stacks.Chow.totalChernClassComplexLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow`)
as well as the power sums and the Chern character.

For `X` not quasi-compact the source assembles the classes over a decomposition of `X` into open
and closed subschemes by Stacks 0FDZ; the classes of
`Stacks.Chow.totalChernClassComplexLocallyBounded` and
`Stacks.Chow.powerSumClassComplexLocallyBounded` take a `CompactSpace` instance, and both readings
here are stated on a quasi-compact `X` accordingly.

### The reduction of Stacks 02UC: power sums only, at a fixed window

The reduction runs through the restriction clause
`Stacks.Chow.powerSumClassComplex_chowCohomologyRestriction`. `P_p` of a complex is the
alternating **sum** of the `P_p` of its terms, so the restriction map passes through it because it
is a homomorphism of groups. The total Chern class of a complex is the alternating **product** in
the ring `A^*(X)^∧` of Stacks 0FE0, which enters as the datum
`Stacks.Chow.ChowCohomologySeriesRing`, and restricting it would need the restriction map to
respect that product; the reduction is therefore stated for `P_p` and `ch_p` only.

The reduction is stated at a fixed window `a, …, a + k`, as `Stacks.Chow.powerSumClassComplex` is,
because the restriction clause is about a complex presented with a window. The same window serves
on `X` and on every modification, the degreewise pullback of a complex vanishing outside a window
vanishing outside that window, which is why one window can be fixed once in the statement.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0ESR](https://stacks.math.columbia.edu/tag/0ESR)
* [Stacks Project, Tag 0F8J](https://stacks.math.columbia.edu/tag/0F8J)
* [Stacks Project, Tag 00O3](https://stacks.math.columbia.edu/tag/00O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Independence

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **The comparison datum of Stacks 0ESZ on the modifications of its proof.** For every integral
scheme `T` locally of finite type over `X` there is a proper birational `h : T' ⟶ T` carrying

* a power sum datum `W'` on `T'`, compatible with `W` under base change along `h ≫ t`, so that
  `res(P_p(ℰ))` is `P_p` of the pullback of `ℰ`; and
* splittings of the two pulled back complexes on `T'` in the sense of
  `Stacks.Chow.BoundedComplexSplitting`, together with a
  `Stacks.Chow.ComplexCohomologyComparison` between them.

This is clause (3) of Stacks 02UC — "every integral test scheme admits a proper birational
modification on which the difference vanishes" — with the reason for the vanishing on the
modification spelled out as the datum the source's proof produces there. It replaces the
hypothesis that the two complexes have a comparison **on `X`**, which for the complexes Stacks
0ESZ is about is generally not satisfiable; see the implementation notes of this file. -/
def HasPowerSumComparisonOnModifications (W : PowerSumClassRule C G sX)
    (P Q : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] [IsIntegral T],
    ∃ (T' : Scheme.{u}) (h : T' ⟶ T) (hproper : IsProper h),
      letI := hproper
      AlgebraicGeometry.IsBirational h ∧
        ∃ W' : PowerSumClassRule C G ((h ≫ t) ≫ sX),
          PowerSumClassRule.IsBaseChangeCompatible C G sX (h ≫ t) hgys W W' ∧
            ∃ (S : BoundedComplexSplitting T'
                  (((Scheme.Modules.pullback (h ≫ t)).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj P) a k)
                (S' : BoundedComplexSplitting T'
                  (((Scheme.Modules.pullback (h ≫ t)).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj Q) a k),
              Nonempty (ComplexCohomologyComparison S S')

/-- **Stacks 0ESZ, the independence of the representative for `P_p`, with the reduction of
Stacks 02UC discharged.** Let `ℰ^• = P` and `ℱ^• = Q` be two complexes of finite locally free
`𝒪_X`-modules bounded in the degrees `a, …, a + k`. If on a proper birational modification of
every integral test scheme the two pulled back complexes admit a comparison, then

  `P_p(ℰ^•) = P_p(ℱ^•)` in `A^p(X)`.

This is the source's proof, with its own first reduction carried out rather than assumed. The
difference of the two classes is a bivariant class for the identity of `X`, by
`Stacks.Chow.chowCohomologyComponent`; Stacks 02UC in the form
`Stacks.Chow.BivariantClass.capsIntegralFundamentalClassesToZero_of_hasBirationalModification`
reduces its vanishing to the vanishing of its cap products on the modifications; on each
modification the restriction of the difference is the difference of the classes of the pulled back
complexes, by `Stacks.Chow.powerSumClassComplex_chowCohomologyRestriction`, which the comparison
makes zero by `Stacks.Chow.powerSumClassComplex_eq_of_cohomologyComparison`; and a class whose
restriction along a morphism vanishes caps to zero on test schemes factoring through it, by
`Stacks.Chow.cap_eq_zero_of_chowCohomologyRestriction_eq_zero` at the identity test scheme.

The comparison datum on the modifications and the base change compatibility of the power sum
data are hypotheses; see the implementation notes of this file for why, and for why the
statement is not made for the total Chern class. -/
theorem powerSumClassComplex_eq_of_hasPowerSumComparisonOnModifications
    (W : PowerSumClassRule C G sX) (P Q : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflfP : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (P.X (a + (i : ℤ))))
    (hflfQ : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (Q.X (a + (i : ℤ))))
    (hcmp : HasPowerSumComparisonOnModifications C G sX hgys W P Q a k) (p : ℕ) :
    powerSumClassComplex C G sX W P a k p = powerSumClassComplex C G sX W Q a k p := by
  rw [← sub_eq_zero]
  refine BivariantClass.eq_zero_of_capsIntegralFundamentalClassesToZero C G sX sX (𝟙 X)
    (Category.id_comp sX) (p : ℤ)
    (BivariantClass.capsIntegralFundamentalClassesToZero_of_hasBirationalModification C G sX sX
      (𝟙 X) (Category.id_comp sX) (p : ℤ) ?_)
  intro T t _ _
  obtain ⟨T', h, hproper, hbir, W', hW', S, S', ⟨cmp⟩⟩ := hcmp t
  let := hproper
  refine ⟨T', h, hproper, hbir, fun j => ?_⟩
  refine cap_eq_zero_of_chowCohomologyRestriction_eq_zero C G sX (h ≫ t) (p : ℤ) hgys _ ?_
    (𝟙 T') (h ≫ t) (Category.id_comp (h ≫ t)).symm j _
  rw [map_sub,
    powerSumClassComplex_chowCohomologyRestriction C G sX (h ≫ t) hgys hW' P a k hflfP p,
    powerSumClassComplex_chowCohomologyRestriction C G sX (h ≫ t) hgys hW' Q a k hflfQ p,
    powerSumClassComplex_eq_of_cohomologyComparison C G ((h ≫ t) ≫ sX) W' S S' cmp p, sub_self]

/-- **Stacks 0ESZ, the independence of the representative for the Chern character, with the
reduction of Stacks 02UC discharged.** The component `ch_p(ℰ^•) = P_p(ℰ^•)/p!` of the Chern
character of a complex is a scalar multiple of the power sum class in
`A^p(X) ⊗ 𝐐`, so the statement follows from
`Stacks.Chow.powerSumClassComplex_eq_of_hasPowerSumComparisonOnModifications` with no further
hypothesis: the factorial is untouched. -/
theorem chernCharacterComplexComponent_eq_of_hasPowerSumComparisonOnModifications
    (W : PowerSumClassRule C G sX) (P Q : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflfP : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (P.X (a + (i : ℤ))))
    (hflfQ : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (Q.X (a + (i : ℤ))))
    (hcmp : HasPowerSumComparisonOnModifications C G sX hgys W P Q a k) (p : ℕ) :
    chernCharacterComplexComponent C G sX W P a k p =
      chernCharacterComplexComponent C G sX W Q a k p := by
  rw [chernCharacterComplexComponent, chernCharacterComplexComponent,
    powerSumClassComplex_eq_of_hasPowerSumComparisonOnModifications C G sX hgys W P Q a k
      hflfP hflfQ hcmp p]

end Independence

/-! ### The independence of the representative for a locally bounded complex -/

section LocallyBounded

variable {X : Scheme.{u}}

/-- **Two locally bounded complexes on a quasi-compact scheme vanish outside one common window.**
Each vanishes outside a window of its own by
`Stacks.Chow.exists_window_of_isLocallyBoundedFiniteLocallyFree`, and the window spanned by the
union of the two contains both.

This is what makes the window half of `Stacks.Chow.HasCohomologyComparisonAtCommonWindow` free:
the content of that hypothesis is the comparison datum, never the existence of a window to state
it at. -/
theorem exists_common_window_of_isLocallyBoundedFiniteLocallyFree [CompactSpace X]
    {P Q : CochainComplex X.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hQ : IsLocallyBoundedFiniteLocallyFree Q) :
    ∃ w : ℤ × ℕ, (∀ n : ℤ, (n < w.1 ∨ w.1 + (w.2 : ℤ) < n) → IsZero (P.X n)) ∧
      ∀ n : ℤ, (n < w.1 ∨ w.1 + (w.2 : ℤ) < n) → IsZero (Q.X n) := by
  obtain ⟨wP, hwP⟩ := exists_window_of_isLocallyBoundedFiniteLocallyFree hP
  obtain ⟨wQ, hwQ⟩ := exists_window_of_isLocallyBoundedFiniteLocallyFree hQ
  exact ⟨⟨min wP.1 wQ.1,
      (max (wP.1 + (wP.2 : ℤ)) (wQ.1 + (wQ.2 : ℤ)) - min wP.1 wQ.1).toNat⟩,
    fun n hn => hwP n (by omega), fun n hn => hwQ n (by omega)⟩

/-- **The comparison datum of Stacks 0ESZ at a window containing two locally bounded complexes.**
There is a window `a, …, a + k` outside which both complexes vanish, carrying a
`Stacks.Chow.BoundedComplexSplitting` of each and a `Stacks.Chow.ComplexCohomologyComparison`
between them.

Only the comparison datum is content. A common window always exists, by
`Stacks.Chow.exists_common_window_of_isLocallyBoundedFiniteLocallyFree`, so this asks for nothing
about the degrees of the complexes; and it asks for the datum at *one* window rather than at
every one, which is the weaker demand. -/
def HasCohomologyComparisonAtCommonWindow (P Q : CochainComplex X.Modules ℤ) : Prop :=
  ∃ (a : ℤ) (k : ℕ) (_ : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n))
      (_ : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (Q.X n))
      (S : BoundedComplexSplitting X P a k) (T : BoundedComplexSplitting X Q a k),
    Nonempty (ComplexCohomologyComparison S T)

section TotalChernClass

open ChowCohomologySeriesRing

variable (C : ChowSituation.{u}) (Gy : GysinSystem C) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [CompactSpace X] {R : ChowCohomologySeriesRing C Gy sX}

/-- **Stacks 0ESZ, the independence of the representative for the total Chern class of a locally
bounded complex.** Two locally bounded complexes of finite locally free modules on a quasi-compact
scheme that admit a comparison at a common window carry the same total Chern class:

  `c(ℰ^•) = c(ℱ^•)` in `∏_{p ≥ 0} A^p(X)`.

This is the statement of the source at the generality of the source's complex — locally bounded,
with no window in the statement — for the classes
`Stacks.Chow.totalChernClassComplexLocallyBounded`. The bounded-window surrogate
`Stacks.Chow.totalChernClassComplex_eq_of_cohomologyComparison` is about a complex *presented
with* a window, and the two classes it compares are the window's, not the complex's.

The proof is the window-independence of the locally bounded class,
`Stacks.Chow.totalChernClassComplexLocallyBounded_eq`: both classes are read at the common window
the hypothesis supplies, where the bounded-window statement applies. No restriction map is
involved, which is why this reading closes for the total Chern class as well as for the power
sums; see the implementation notes of this file. -/
theorem totalChernClassComplexLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow
    (D : TotalChernClassSeries C Gy sX R) {P Q : CochainComplex X.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (hcmp : HasCohomologyComparisonAtCommonWindow P Q) :
    totalChernClassComplexLocallyBounded C Gy sX D P hP =
      totalChernClassComplexLocallyBounded C Gy sX D Q hQ := by
  obtain ⟨a, k, hvP, hvQ, S, T, ⟨cmp⟩⟩ := hcmp
  rw [totalChernClassComplexLocallyBounded_eq C Gy sX D P hP hvP,
    totalChernClassComplexLocallyBounded_eq C Gy sX D Q hQ hvQ,
    totalChernClassComplex_eq_of_cohomologyComparison C Gy sX D S T cmp]

end TotalChernClass

section PowerSum

variable (C : ChowSituation.{u}) (Gy : GysinSystem C) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [CompactSpace X]

/-- **Stacks 0ESZ, the independence of the representative for `P_p` of a locally bounded
complex.** Two locally bounded complexes of finite locally free modules on a quasi-compact scheme
that admit a comparison at a common window carry the same class `P_p`, for every `p`.

As for the total Chern class, this is the statement at the generality of the source's complex, for
`Stacks.Chow.powerSumClassComplexLocallyBounded`, with no window in the statement. -/
theorem powerSumClassComplexLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow
    (W : PowerSumClassRule C Gy sX) {P Q : CochainComplex X.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (hcmp : HasCohomologyComparisonAtCommonWindow P Q) (p : ℕ) :
    powerSumClassComplexLocallyBounded C Gy sX W P hP p =
      powerSumClassComplexLocallyBounded C Gy sX W Q hQ p := by
  obtain ⟨a, k, hvP, hvQ, S, T, ⟨cmp⟩⟩ := hcmp
  rw [powerSumClassComplexLocallyBounded_eq C Gy sX W P hP hvP p,
    powerSumClassComplexLocallyBounded_eq C Gy sX W Q hQ hvQ p,
    powerSumClassComplex_eq_of_cohomologyComparison C Gy sX W S T cmp p]

/-- **Stacks 0ESZ, the independence of the representative for the Chern character of a locally
bounded complex.** The component `ch_p(ℰ^•) = P_p(ℰ^•)/p!` of two locally bounded complexes
admitting a comparison at a common window agree in `A^p(X) ⊗ 𝐐`.

The Chern character of a locally bounded complex is not a separate definition; it is assembled
from `Stacks.Chow.powerSumClassComplexLocallyBounded` as the pure tensor
`(p!)⁻¹ ⊗ P_p(ℰ^•)`, which is the shape
`Stacks.Chow.eq_of_restriction_eq_chernCharacterComplexLocallyBounded` — the Stacks 0GUD
uniqueness theorem for the Chern character — states its hypothesis in. The statement is therefore
made at that shape, and follows from the power sum reading because the factorial is a scalar. -/
theorem chernCharacterLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow
    (W : PowerSumClassRule C Gy sX) {P Q : CochainComplex X.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (hcmp : HasCohomologyComparisonAtCommonWindow P Q) (p : ℕ) :
    ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] powerSumClassComplexLocallyBounded C Gy sX W P hP p =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] powerSumClassComplexLocallyBounded C Gy sX W Q hQ p := by
  rw [powerSumClassComplexLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow C Gy sX W
    hP hQ hcmp p]

end PowerSum

end LocallyBounded

end Stacks.Chow

end
