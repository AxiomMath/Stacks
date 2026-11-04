module

public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankStratum
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiSemicontinuity

/-!
# The open subscheme on which the bottom derived-fibre Betti number is at most `r`

Let `X` be a scheme, `E` a pseudo-coherent object of `D(𝒪_X)`, `a` an integer and `r` a natural
number.  The locus where the `a`-th derived-fibre Betti function satisfies `β_a ≤ r` is open,
because `β_a` is upper semi-continuous (part (2) of [stacks 0BDI]), and every morphism which is
universally of bottom rank `r` factors through it.

That is the first reduction of the proof of [stacks 0BDL]: the source begins "let `U ⊂ X` be the
locally constructible open subscheme where the function `β_a` of Lemma 0BDI has values `≤ r` …
hence `f` as in (2) factors through `U`. Thus we may replace `X` by `U`."  It is not a part of
the statement of [stacks 0BDL], and nothing here carries that tag; the file
`StacksFrontier/AlgebraicGeometry/Perfect/BottomRankStratum.lean` says the same of
`AlgebraicGeometry.BottomRankStratum.derivedFiberBetti_eq_of_isUniversallyFreeBottom`, which is
the other half of this reduction and which this file consumes.

## Main definitions

* `AlgebraicGeometry.BottomRankStratum.bettiLeOpen`: the open subscheme `{x | β_a(x) ≤ r}`.

## Main results

* `AlgebraicGeometry.BottomRankStratum.mem_bettiLeOpen_iff`: its points are exactly the points
  where `β_a ≤ r`.
* `AlgebraicGeometry.BottomRankStratum.factorsThrough_bettiLeOpen`: a morphism universally of
  bottom rank `r` factors through it.

## Implementation notes

Openness is `UpperSemicontinuous.isOpen_preimage` at the value `r + 1`: for a function with values
in `ℕ` the condition `β_a ≤ r` is `β_a < r + 1`.  The upper semi-continuity used is
`AlgebraicGeometry.DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti`, which is
unconditional on a pseudo-coherent `E`, so no hypothesis is carried here beyond the one `β_a`
itself needs.

The factorisation is `AlgebraicGeometry.IsOpenImmersion.lift` applied to the open immersion
`(bettiLeOpen …).ι`, which needs only the containment of set-theoretic images; that containment
is `derivedFiberBetti_eq_of_isUniversallyFreeBottom`, which gives `β_a = r` at every point of the
image, hence `β_a ≤ r` there.  The source's reduction is stated for an `f` as in its description
(2), which is exactly `IsUniversallyFreeBottom`.

## References

* [The Stacks Project, Lemma 36.31.4 (0BDL)](https://stacks.math.columbia.edu/tag/0BDL)
* [The Stacks Project, Lemma 36.31.1 (0BDI)](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.BottomRankStratum

variable {X : Scheme.{u}} (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E) (a : ℤ) (r : ℕ)

/-- **The open subscheme of `X` on which `β_a ≤ r`.**  Its underlying set is the locus where the
`a`-th derived-fibre Betti function of `E` is at most `r`; it is open because that function is
upper semi-continuous, which is part (2) of [stacks 0BDI]. -/
public def bettiLeOpen : X.Opens :=
  ⟨DerivedFibreBetti.derivedFiberBetti X E hE a ⁻¹' Set.Iio (r + 1),
    (DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti X E hE a).isOpen_preimage (r + 1)⟩

/-- A point lies in `bettiLeOpen` exactly when the `a`-th derived-fibre Betti number there is at
most `r`. -/
public theorem mem_bettiLeOpen_iff (x : X) :
    x ∈ bettiLeOpen E hE a r ↔ DerivedFibreBetti.derivedFiberBetti X E hE a x ≤ r :=
  Nat.lt_succ_iff

/-- **A morphism universally of bottom rank `r` factors through `bettiLeOpen`.**  This is the
first reduction of the proof of [stacks 0BDL]: at every point of the image the `a`-th
derived-fibre Betti number is `r`, so the image is contained in the open subscheme where it is at
most `r`, and a morphism whose image lies in an open subscheme factors through it. -/
public theorem factorsThrough_bettiLeOpen {Y : Scheme.{u}} {f : Y ⟶ X}
    (h : IsUniversallyFreeBottom E a r f) :
    ∃ g : Y ⟶ (bettiLeOpen E hE a r).toScheme, g ≫ (bettiLeOpen E hE a r).ι = f := by
  have hrange : Set.range f.base ⊆ Set.range (bettiLeOpen E hE a r).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨y, rfl⟩
    exact (mem_bettiLeOpen_iff E hE a r (f.base y)).2
      (le_of_eq (derivedFiberBetti_eq_of_isUniversallyFreeBottom E hE a r h y))
  exact ⟨AlgebraicGeometry.IsOpenImmersion.lift _ f hrange,
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry.BottomRankStratum

end
