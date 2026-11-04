module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentChowCohomologyCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.LocallyBoundedComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# The power sums and the Chern character of a perfect derived object: existence

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be a
scheme locally of finite type over `S` and let `E` be an object of `D(𝒪_X)` whose Chern classes
are defined in the sense of Stacks 0F9E (1): there is an envelope `g : Y ⟶ X`, Stacks 0GU5, and a
locally bounded complex `P` of finite locally free `𝒪_Y`-modules representing `Lg^*E`.
**Stacks 0GUD** asserts that there are unique classes

  `c_p(E) ∈ A^p(X)`,  `P_p(E) ∈ A^p(X)`,  `ch_p(E) ∈ A^p(X) ⊗ 𝐐`

whose restrictions along every such envelope are the corresponding classes of the presenting
complex. The uniqueness half is
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness`. This file is the
**existence half for the power sums `P_p` and for the Chern character `ch_p = P_p/p!`**.

The total Chern class `c(E)` is *not* here, and is reachable only at the price of a hypothesis
these statements do not need:
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeExistenceTotalChern` has it,
carrying a series ring of Stacks 0FEL on the source of the envelope and on the double fibre
product. See the implementation notes.

## Main results

* `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_powerSumClassComplexLocallyBounded` —
  **Stacks 0GUD, existence for the power sums**: along an envelope `g : Y ⟶ X` with `Y`
  quasi-compact there is a unique class of `A^p(X)` whose restriction of Stacks 0B7F is `P_p` of
  a given locally bounded complex of finite locally free modules on `Y`. At `g = H.f` and the
  presenting complex of an envelope presentation `H` of an object `E` of `D(𝒪_X)` this is the
  existence of `P_p(E)`.
* `Stacks.Chow.existsUnique_rationalChowCohomologyRestriction_eq_chernCharacterLocallyBounded` —
  **Stacks 0GUD, existence for the Chern character**: the same for `ch_p = P_p/p!` in
  `A^p(X) ⊗ 𝐐`.
* `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_powerSumClassComplex` — the same at a
  complex bounded in a given range of degrees, with no quasi-compactness hypothesis, which the
  two above specialize.
* `Stacks.Chow.chowCohomologyRestriction_powerSumClassComplex_eq` — the hypothesis of Stacks
  0GUC for `P_p` of a complex: the two restrictions of `P_p(P)` to `Y ×_X Y` agree.

## Main definitions

* `Stacks.Chow.powerSumClassRuleCongr` — a power sum datum read against an equal presentation of
  the structure morphism of its scheme over the base.

## Implementation notes

### What is carried

Three things, each of which the repository already carries wherever the classes of Stacks 0ESZ
meet a morphism of schemes; the second of them comes with two compatibilities, one for each
projection.

* A power sum datum `W` on `Y`, `Stacks.Chow.PowerSumClassRule`: the evaluated power sums
  `P_p(c_1, …, c_p)` of Stacks 0F9B need the multiplication of `A^*(X)`, Stacks 0FE0, which is
  not formalized here, so no datum is constructed and every statement about `P_p` in this
  repository carries one.
* A power sum datum `WZ` on `Y ×_X Y`, for the same reason, and the two base change
  compatibilities `Stacks.Chow.PowerSumClassRule.IsBaseChangeCompatible` of `W` with `WZ` along
  the two projections. That predicate is the content of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange`, which explains at length why it
  cannot be a field of the datum and must be asked for separately: two independently chosen data
  satisfy no relation at all. The two projections are different morphisms, so the two
  compatibilities are two assumptions; the second is asked of `WZ` read against the other
  presentation of the structure morphism of `Y ×_X Y`, by `Stacks.Chow.powerSumClassRuleCongr`,
  so that only one datum on `Y ×_X Y` is carried.
* The equality of `P_p` of the two pullbacks of the presenting complex to `Y ×_X Y`. This is the
  independence of the representative of Stacks 0ESZ: the two pullbacks are isomorphic in
  `D(𝒪_{Y ×_X Y})`, both representing the derived pullback of `E`, but they are different
  complexes. `Stacks.Chow.powerSumClassComplex_eq_of_cohomologyComparison` delivers it from a
  `Stacks.Chow.ComplexCohomologyComparison`, the degreewise Schanuel datum the source's proof
  extracts from a derived isomorphism after the reductions of Stacks 02UC and Stacks 0ESR; that
  datum is itself carried by this repository.

Beyond those, only what Stacks 0GUC already asks for: three cases of Stacks 02TA for the Gysin
system, all discharged for the canonical system of the genuine first Chern class rule.

### Quasi-compactness is needed on `Y` and not on `Y ×_X Y`

The classes of a *locally bounded* complex are available in this repository only on a
quasi-compact scheme, as `Stacks.Chow.powerSumClassComplexLocallyBounded`. That is not an
obstruction for the descent: the classes on `Y ×_X Y` are named only through the bounded-window
`Stacks.Chow.powerSumClassComplex`, which needs no quasi-compactness, at a window taken once on
`Y`. Accordingly the statements take that window as data — a base degree `a`, a length `k` and
the vanishing of the complex outside that range — rather than a compactness hypothesis on the
double fibre product, and `[CompactSpace Y]` appears only where the class of the locally bounded
case is named.

### Why the total Chern class is absent from *this* file

`c(E)` is the alternating **product** `∏_n c(ℰ^n)^{(-1)^n}` of Stacks 0ESZ, so the descent
argument needs the restriction map of Stacks 0B7F to be multiplicative for the Cauchy product of
the series ring in which that product is formed. The multiplicativity is available
(`Stacks.Chow.chernClassKGroup_chowCohomologyRestriction`), but the ring itself exists exactly
when the Chow cohomology of the scheme is commutative in every pair of non-negative degrees, by
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm` of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologySeriesRingConstruction` — a hypothesis the
source does not make, Stacks 0FE0 being the completed ring `A^*(X)^∧` under composition and not
a commutativity assertion. `P_p` and `ch_p` are alternating **sums**, for which the restriction
map being a homomorphism of groups is all that is needed, so they close with no series ring and
no commutativity anywhere; that is the split, and it is a split in the hypotheses carried, not in
reachability. The total Chern class with those rings carried is
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeExistenceTotalChern`, and the same
split is recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange`.

### Why the defining property is taken at a single presentation

As in the uniqueness file: the source states the defining property at *every* envelope
presentation of `E`, and the statements below produce the class from *one*, which is the weaker
hypothesis and hence the stronger theorem. The class is then unique among the classes restricting
to that one presentation's complex, which is exactly the pairing with
`Stacks.Chow.eq_of_restriction_eq_powerSumClassComplexLocallyBounded`.

No object of the derived category is named below at all: the statements are made at a bare
envelope `g : Y ⟶ X` and a locally bounded complex on `Y`, which is more general still, and an
envelope presentation `H` of an object `E` enters by instantiating `g := H.f` and the complex as
`H.P`. Nothing about the condition being descended uses that the complex represents `Lg^*E`; what
that representation is for is producing the hypothesis on `Y ×_X Y`, namely the isomorphism in
`D(𝒪_{Y ×_X Y})` of the two pullbacks, which is carried here.

## References

* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### A power sum datum against an equal presentation of the structure morphism -/

section RuleCongr

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z : Scheme.{u}} {s s' : Z ⟶ C.S}
  [LocallyOfFiniteType s] [LocallyOfFiniteType s']

/-- **A power sum datum read against an equal presentation of the structure morphism.** A datum
for `s : Z ⟶ S` is a datum for any `s'` equal to it: the two are the same type, presented
differently, and the transport is the substitution of the equality. -/
def powerSumClassRuleCongr (h : s = s') (W : PowerSumClassRule C G s) :
    PowerSumClassRule C G s' := by
  subst h
  exact W

/-- The class `P_p` of a complex computed with a transported power sum datum is the class
computed with the original one, read through the transport of the Chow cohomology groups. -/
theorem bivariantClassCongrBase_powerSumClassComplex (h : s = s')
    (W : PowerSumClassRule C G s) (P : CochainComplex Z.Modules ℤ) (a : ℤ) (k : ℕ) (p : ℕ) :
    bivariantClassCongrBase C G (𝟙 Z) h.symm h.symm (hv := Category.id_comp s')
        (hv' := Category.id_comp s) (p : ℤ)
        (powerSumClassComplex C G s' (powerSumClassRuleCongr C G h W) P a k p) =
      powerSumClassComplex C G s W P a k p := by
  subst h
  rfl

end RuleCongr

/-! ### The descent hypothesis for the power sums of a complex -/

section Descent

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : Y ⟶ X) [LocallyOfFiniteType g]
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **The two restrictions of `P_p(ℰ^•)` to `Y ×_X Y` agree.** Let `ℰ^•` be a complex of finite
locally free modules on `Y` bounded in the degrees `a, …, a + k`, let `W` be a power sum datum on
`Y` and `WZ` one on `Y ×_X Y`, compatible with `W` along both projections, and suppose that the
classes `P_p` of the two pullbacks of `ℰ^•` to `Y ×_X Y` agree. Then the two restrictions of
`P_p(ℰ^•)` to `Y ×_X Y` agree, in the shape
`Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_of_restriction_eq` consumes.

Each restriction is `P_p` of the pulled back complex by
`Stacks.Chow.powerSumClassComplex_chowCohomologyRestriction`, and the transport between the two
presentations of the structure morphism of `Y ×_X Y` is absorbed into the datum by
`Stacks.Chow.bivariantClassCongrBase_powerSumClassComplex`, which is why one datum on `Y ×_X Y`
suffices. -/
theorem chowCohomologyRestriction_powerSumClassComplex_eq
    (W : PowerSumClassRule C G (g ≫ sX))
    (WZ : PowerSumClassRule C G (pullback.fst g g ≫ (g ≫ sX)))
    (hWfst : PowerSumClassRule.IsBaseChangeCompatible C G (g ≫ sX) (pullback.fst g g) hgys W WZ)
    (hWsnd : PowerSumClassRule.IsBaseChangeCompatible C G (g ≫ sX) (pullback.snd g g) hgys W
      (powerSumClassRuleCongr C G (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm WZ))
    (P : CochainComplex Y.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
        (P.X (a + (i : ℤ))))
    (p : ℕ)
    (hPP : powerSumClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) WZ
          (((Scheme.Modules.pullback (pullback.fst g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k p =
        powerSumClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) WZ
          (((Scheme.Modules.pullback (pullback.snd g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k p) :
    chowCohomologyRestriction C G (g ≫ sX) (pullback.fst g g) (p : ℤ) hgys
        (powerSumClassComplex C G (g ≫ sX) W P a k p) =
      bivariantClassCongrBase C G (𝟙 (pullback g g))
        (selfPullbackSnd_comp_structureMorphism_eq C sX g)
        (selfPullbackSnd_comp_structureMorphism_eq C sX g) (hv := Category.id_comp _)
        (hv' := Category.id_comp _) (p : ℤ)
        (chowCohomologyRestriction C G (g ≫ sX) (pullback.snd g g) (p : ℤ) hgys
          (powerSumClassComplex C G (g ≫ sX) W P a k p)) := by
  rw [powerSumClassComplex_chowCohomologyRestriction C G (g ≫ sX) (pullback.fst g g) hgys hWfst
      P a k hflf p,
    powerSumClassComplex_chowCohomologyRestriction C G (g ≫ sX) (pullback.snd g g) hgys hWsnd
      P a k hflf p,
    bivariantClassCongrBase_powerSumClassComplex C G
      (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm WZ]
  exact hPP

/-! ### Existence at a bare envelope -/

variable (hgysP : G.IsNaturalUnderProperPushforward)
  (hgysC : G.IsNaturalUnderPullbackCompPushforward) (hgE : IsEnvelope g)

include hgysP hgysC hgE in
/-- **Existence of the class `P_p` descending along an envelope, for a complex bounded in a range
of degrees.** Let `g : Y ⟶ X` be an envelope and let `ℰ^•` be a complex of finite locally free
modules on `Y` bounded in the degrees `a, …, a + k` whose classes `P_p` are compatible with
restriction to `Y ×_X Y` in the sense of
`Stacks.Chow.chowCohomologyRestriction_powerSumClassComplex_eq`. Then there is a unique class in
`A^p(X)` whose restriction of Stacks 0B7F along `g` is `P_p(ℰ^•)`.

This is the engine of the existence half of Stacks 0GUD for the power sums: Stacks 0GUC on Chow
cohomology, `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_of_restriction_eq`, whose
descent condition is the equality of the two restrictions. No object of the
derived category is mentioned, which makes it more general than the tag's statement. -/
theorem existsUnique_chowCohomologyRestriction_eq_powerSumClassComplex
    (W : PowerSumClassRule C G (g ≫ sX))
    (WZ : PowerSumClassRule C G (pullback.fst g g ≫ (g ≫ sX)))
    (hWfst : PowerSumClassRule.IsBaseChangeCompatible C G (g ≫ sX) (pullback.fst g g) hgys W WZ)
    (hWsnd : PowerSumClassRule.IsBaseChangeCompatible C G (g ≫ sX) (pullback.snd g g) hgys W
      (powerSumClassRuleCongr C G (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm WZ))
    (P : CochainComplex Y.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
        (P.X (a + (i : ℤ))))
    (p : ℕ)
    (hPP : powerSumClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) WZ
          (((Scheme.Modules.pullback (pullback.fst g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k p =
        powerSumClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) WZ
          (((Scheme.Modules.pullback (pullback.snd g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k p) :
    ∃! c : chowCohomologyComponent C G sX (p : ℤ),
      chowCohomologyRestriction C G sX g (p : ℤ) hgys c =
        powerSumClassComplex C G (g ≫ sX) W P a k p :=
  existsUnique_chowCohomologyRestriction_eq_of_restriction_eq C G sX g (p : ℤ)
    hgys hgysP hgysC hgE _
    (chowCohomologyRestriction_powerSumClassComplex_eq C G sX g hgys W WZ hWfst hWsnd P a k
      hflf p hPP)

include hgysP hgysC hgE in
/-- **Stacks 0GUD, existence for the power sums.** Let `g : Y ⟶ X` be an envelope with `Y`
quasi-compact and let `ℰ^•` be a locally bounded complex of finite locally free modules on `Y`
whose classes `P_p` are compatible with restriction to `Y ×_X Y`. There is a **unique** class in
`A^p(X)` whose restriction of Stacks 0B7F along `g` is `P_p(ℰ^•)`:

  `res : A^p(X) ⟶ A^p(Y)`,  `res(P_p(E)) = P_p(ℰ^•)`.

Applied to an envelope presentation `H` of an object `E` of `D(𝒪_X)`, Stacks 0F9E (1), at
`g = H.f` and `ℰ^• = H.P`, this is the existence of the class `P_p(E)` of the tag, whose
uniqueness is `Stacks.Chow.eq_of_restriction_eq_powerSumClassComplexLocallyBounded`.

It is `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_powerSumClassComplex` read at the
class of the locally bounded case, `Stacks.Chow.powerSumClassComplexLocallyBounded`: a window of
degrees outside which the complex vanishes identifies that class with the bounded-window class,
by `Stacks.Chow.powerSumClassComplexLocallyBounded_eq`. The window is taken as data; on a
quasi-compact scheme `Stacks.Chow.exists_window_of_isLocallyBoundedFiniteLocallyFree` produces
one. -/
theorem existsUnique_chowCohomologyRestriction_eq_powerSumClassComplexLocallyBounded
    [CompactSpace Y] (W : PowerSumClassRule C G (g ≫ sX))
    (WZ : PowerSumClassRule C G (pullback.fst g g ≫ (g ≫ sX)))
    (hWfst : PowerSumClassRule.IsBaseChangeCompatible C G (g ≫ sX) (pullback.fst g g) hgys W WZ)
    (hWsnd : PowerSumClassRule.IsBaseChangeCompatible C G (g ≫ sX) (pullback.snd g g) hgys W
      (powerSumClassRuleCongr C G (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm WZ))
    (P : CochainComplex Y.Modules ℤ) (hP : IsLocallyBoundedFiniteLocallyFree P) {a : ℤ} {k : ℕ}
    (hvanish : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n)) (p : ℕ)
    (hPP : powerSumClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) WZ
          (((Scheme.Modules.pullback (pullback.fst g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k p =
        powerSumClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) WZ
          (((Scheme.Modules.pullback (pullback.snd g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k p) :
    ∃! c : chowCohomologyComponent C G sX (p : ℤ),
      chowCohomologyRestriction C G sX g (p : ℤ) hgys c =
        powerSumClassComplexLocallyBounded C G (g ≫ sX) W P hP p := by
  rw [powerSumClassComplexLocallyBounded_eq C G (g ≫ sX) W P hP hvanish p]
  exact existsUnique_chowCohomologyRestriction_eq_powerSumClassComplex C G sX g hgys hgysP hgysC
    hgE W WZ hWfst hWsnd P a k (fun i _ => isFiniteLocallyFree_X_of_isLocallyBounded hP _) p hPP

/-! ### Existence for the Chern character -/

include hgysP hgysC hgE in
/-- **Stacks 0GUD, existence for the Chern character.** Let `g : Y ⟶ X` be an envelope with `Y`
quasi-compact and let `ℰ^•` be a locally bounded complex of finite locally free modules on `Y`
whose classes `P_p` are compatible with restriction to `Y ×_X Y`. There is a **unique** class in
`A^p(X) ⊗ 𝐐` whose rational restriction along `g` is the component
`ch_p(ℰ^•) = P_p(ℰ^•)/p!` of the Chern character of `ℰ^•`.

Existence is the class `P_p/p!` built from
`Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_powerSumClassComplexLocallyBounded`, the
rational restriction map being the integral one tensored with `𝐐`; uniqueness is the injectivity
of the rational restriction map along an envelope,
`Stacks.Chow.rationalChowCohomologyRestriction_injective_of_isEnvelope`, so it holds among all
rational classes and not only the pure tensors. Applied to an envelope presentation `H` of an
object `E` of `D(𝒪_X)` at `g = H.f` and `ℰ^• = H.P`, this is the existence half of the tag for
`ch_p(E)`, and `Stacks.Chow.eq_of_restriction_eq_chernCharacterComplexLocallyBounded` is its
uniqueness half. -/
theorem existsUnique_rationalChowCohomologyRestriction_eq_chernCharacterLocallyBounded
    [CompactSpace Y] (W : PowerSumClassRule C G (g ≫ sX))
    (WZ : PowerSumClassRule C G (pullback.fst g g ≫ (g ≫ sX)))
    (hWfst : PowerSumClassRule.IsBaseChangeCompatible C G (g ≫ sX) (pullback.fst g g) hgys W WZ)
    (hWsnd : PowerSumClassRule.IsBaseChangeCompatible C G (g ≫ sX) (pullback.snd g g) hgys W
      (powerSumClassRuleCongr C G (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm WZ))
    (P : CochainComplex Y.Modules ℤ) (hP : IsLocallyBoundedFiniteLocallyFree P) {a : ℤ} {k : ℕ}
    (hvanish : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n)) (p : ℕ)
    (hPP : powerSumClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) WZ
          (((Scheme.Modules.pullback (pullback.fst g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k p =
        powerSumClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) WZ
          (((Scheme.Modules.pullback (pullback.snd g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k p) :
    ∃! x : rationalChowCohomologyComponent C G sX (p : ℤ),
      rationalChowCohomologyRestriction C G sX g (p : ℤ) hgys x =
        ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ]
          powerSumClassComplexLocallyBounded C G (g ≫ sX) W P hP p := by
  obtain ⟨c, hc, -⟩ :=
    existsUnique_chowCohomologyRestriction_eq_powerSumClassComplexLocallyBounded C G sX g hgys
      hgysP hgysC hgE W WZ hWfst hWsnd P hP hvanish p hPP
  refine ⟨((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] c, ?_, fun y hy => ?_⟩
  · simp only [rationalChowCohomologyRestriction_tmul, hc]
  · refine rationalChowCohomologyRestriction_injective_of_isEnvelope C G sX g (p : ℤ) hgys hgE ?_
    simp only [hy, rationalChowCohomologyRestriction_tmul, hc]

end Descent

end Stacks.Chow

end
