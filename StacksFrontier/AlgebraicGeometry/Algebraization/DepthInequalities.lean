module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalk
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization

/-!
# The `(a, b)`-inequalities for a coherent formal module

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with
`X = Spec(A)`, `Y = V(I)`, `Z = V(𝔞)` and `U = X \ Z`. Let `(ℱ_n)` be an object of
`Coh(U, I𝒪_U)`, let `a` and `b` be integers, and let `δ^Y_Z` be the distance function of `Y`
from `Z`. At a point `y ∈ U ∩ Y` one has the `I`-adic completion `𝒪_{X,y}^∧` of the local ring,
its ideal `I𝒪_{X,y}^∧`, its maximal ideal `𝔪_y^∧`, and the formal stalk
`ℱ_y^∧ = lim ℱ_{n,y}`, a finite `𝒪_{X,y}^∧`-module.

The system `(ℱ_n)` *satisfies the `(a, b)`-inequalities* if for every such `y` and every prime
`𝔭 ⊆ 𝒪_{X,y}^∧` with `𝔭 ∉ V(I𝒪_{X,y}^∧)`:

* if `V(𝔭) ∩ V(I𝒪_{X,y}^∧) ≠ {𝔪_y^∧}`, then
  `depth((ℱ_y^∧)_𝔭) + δ^Y_Z(y) ≥ a` or
  `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > b`;
* if `V(𝔭) ∩ V(I𝒪_{X,y}^∧) = {𝔪_y^∧}`, then `depth((ℱ_y^∧)_𝔭) + δ^Y_Z(y) > a`.

It satisfies the *strict* `(a, b)`-inequalities if for every such `y` and `𝔭`, with no case
distinction, `depth((ℱ_y^∧)_𝔭) + δ^Y_Z(y) > a` or
`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > b`.

## Main definitions

* `Stacks.Algebraization.AlgebraizationSituation.closedSubsetZ` — `Z` as a closed subset
  of `Y`.
* `Stacks.Algebraization.AlgebraizationSituation.distanceToZ` — the distance function `δ^Y_Z`.
* `Stacks.Algebraization.completedStalkDepth` — `depth((ℱ_y^∧)_𝔭)`.
* `Stacks.Algebraization.completedMaximalIdeal` — the maximal ideal `𝔪_y^∧`.
* `Stacks.Algebraization.adicClosedFibreThrough` — the set `V(𝔭) ∩ V(I𝒪_{X,y}^∧)` of primes.
* `Stacks.Algebraization.depthAddDistance` and
  `Stacks.Algebraization.depthAddDimAddDistance` — the two quantities the bounds `a` and `b`
  are compared against.
* `Stacks.Algebraization.SatisfiesDepthInequalities` and
  `Stacks.Algebraization.SatisfiesStrictDepthInequalities` — the two conditions.

## Implementation notes

A point of `U ∩ Y` is given by a point `y` of `U` together with a point `z` of `Y` having the
same image in `X`; the distance `δ^Y_Z` is evaluated at `z`, the depth of the formal stalk at
`y`. Both `U ⟶ X` and `Y ⟶ X` are monomorphisms, so neither of the two points is extra data.

`Z` is a closed subset of `Y` because `I ⊆ 𝔞`; as such it is `V(𝔞/I)`, the zero locus of the
image of `𝔞` in `A/I`, which is the form `closedSubsetZ` takes.

The condition `𝔭 ∉ V(I𝒪_{X,y}^∧)` is `¬ I𝒪_{X,y}^∧ ≤ 𝔭`, and `V(𝔭) ∩ V(I𝒪_{X,y}^∧)` is the
set of primes of `𝒪_{X,y}^∧` containing both; it is compared with the singleton `{𝔪_y^∧}` as a
set of ideals. The two numbered cases of the source are rendered as a conjunction of two
implications, one on each side of that equality, rather than as a case split on a decidable
proposition.

Depth takes values in `ℕ∞` and Krull dimension in `WithBot ℕ∞`, while `δ^Y_Z` takes values in
`ℕ∞`; all three are placed in `EInt` by `Stacks.Algebraization.enatToEInt` and
`Stacks.Algebraization.krullDimToEInt` before being compared with the integer bounds. This
retains the infinite values, which genuinely occur and which the source intends: the depth of
the zero module is `∞` and `δ^Y_Z(y) = ∞` at a point of a connected component of `Y` missing
`Z`, and in both cases the source's inequalities hold rather than being truncated to a finite
comparison. The dimension term never contributes the opposite endpoint: `𝔭` is prime, so
`𝒪_{X,y}^∧/𝔭` is nonzero and `dim(𝒪_{X,y}^∧/𝔭)` is not `⊥`.

The formal stalk is `Stacks.Algebraization.completedStalk`, the completion of the inverse limit
of the stalks, which is the form in which it is a module over `𝒪_{X,y}^∧`.

Both conditions are `abbrev`s, so a proof of one can be applied to a point and a prime
directly, and a proof of one can be built by `intro`.

## References

* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EIX](https://stacks.math.columbia.edu/tag/0EIX), the distance function.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- The closed subscheme `Z = V(𝔞)` of an algebraization situation, viewed as a closed subset of
`Y = V(I)`: since `I ⊆ 𝔞` it is the zero locus of the image of `𝔞` in `A/I`. -/
public def AlgebraizationSituation.closedSubsetZ (S : AlgebraizationSituation.{u}) :
    TopologicalSpace.Closeds S.Y :=
  ⟨PrimeSpectrum.zeroLocus
      ((S.a.map (Ideal.Quotient.mk S.I) : Ideal (S.A ⧸ S.I)) : Set (S.A ⧸ S.I)),
    PrimeSpectrum.isClosed_zeroLocus _⟩

/-- The distance function `δ^Y_Z` of an algebraization situation: the distance, inside
`Y = V(I)`, of a point from the closed subset `Z = V(𝔞)`. -/
public def AlgebraizationSituation.distanceToZ (S : AlgebraizationSituation.{u})
    (z : S.Y) : ℕ∞ :=
  distanceFunction S.Y S.closedSubsetZ z

variable {X : Scheme.{u}}

/-- The depth `depth((ℱ_x^∧)_𝔭)` of the localization at a prime `𝔭` of the completed local ring
of the formal stalk of a coherent adic system, taken over the local ring `(𝒪_{X,x}^∧)_𝔭`. -/
public def completedStalkDepth (I : X.IdealSheafData)
    (F : Stacks.Coherent.CoherentAdicSystems I) (x : X)
    (p : PrimeSpectrum (completedLocalRing I x)) : ℕ∞ :=
  Module.depth (Localization.AtPrime p.asIdeal)
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
    (LocalizedModule p.asIdeal.primeCompl (completedStalk I F x))

/-- The maximal ideal `𝔪_x^∧` of the completed local ring `𝒪_{X,x}^∧`, the ideal generated by
the maximal ideal of `𝒪_{X,x}`. -/
public abbrev completedMaximalIdeal (I : X.IdealSheafData) (x : X) :
    Ideal (completedLocalRing I x) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
    (algebraMap (X.presheaf.stalk x) (completedLocalRing I x))

/-- The set `V(𝔭) ∩ V(I𝒪_{X,x}^∧)` of primes of the completed local ring containing both the
prime `𝔭` and the ideal `I𝒪_{X,x}^∧`. -/
public def adicClosedFibreThrough (I : X.IdealSheafData) (x : X)
    (p : PrimeSpectrum (completedLocalRing I x)) : Set (Ideal (completedLocalRing I x)) :=
  {q | q.IsPrime ∧ p.asIdeal ≤ q ∧ completedLocalIdeal I x ≤ q}

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- The quantity `depth((ℱ_y^∧)_𝔭) + δ^Y_Z(y)`, in the extended integers. -/
public def depthAddDistance (y : S.U.toScheme) (z : S.Y)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y)) : EInt :=
  enatToEInt (completedStalkDepth (idealOnOpen S) F y p) + enatToEInt (S.distanceToZ z)

/-- The quantity `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y)`, in the extended
integers. -/
public def depthAddDimAddDistance (y : S.U.toScheme) (z : S.Y)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y)) : EInt :=
  enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
      krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) +
    enatToEInt (S.distanceToZ z)

/-- **Stacks Project, Tag 0EJ3.** A coherent `I`-adic system on `U` satisfies the
`(a, b)`-inequalities when, at every point of `U ∩ Y` and every prime `𝔭` of the completed local
ring not containing `I𝒪_{X,y}^∧`, the depth of the formal stalk at `𝔭` obeys the bound `a`
strictly if `V(𝔭) ∩ V(I𝒪_{X,y}^∧) = {𝔪_y^∧}`, and in the remaining case obeys `a` weakly or
else the bound `b` strictly after adding `dim(𝒪_{X,y}^∧/𝔭)`. -/
@[stacks 0EJ3 "the (a, b)-inequalities"]
public abbrev SatisfiesDepthInequalities (a b : ℤ) : Prop :=
  ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
    ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
      ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
      (adicClosedFibreThrough (idealOnOpen S) y p ≠
            {completedMaximalIdeal (idealOnOpen S) y} →
          depthAddDistance S F y z p ≥ (a : EInt) ∨
            depthAddDimAddDistance S F y z p > (b : EInt)) ∧
        (adicClosedFibreThrough (idealOnOpen S) y p =
            {completedMaximalIdeal (idealOnOpen S) y} →
          depthAddDistance S F y z p > (a : EInt))

/-- **Stacks Project, Tag 0EJ3.** A coherent `I`-adic system on `U` satisfies the strict
`(a, b)`-inequalities when, at every point of `U ∩ Y` and every prime `𝔭` of the completed local
ring not containing `I𝒪_{X,y}^∧`, the depth of the formal stalk at `𝔭` exceeds the bound `a`,
or else exceeds the bound `b` after adding `dim(𝒪_{X,y}^∧/𝔭)`. -/
@[stacks 0EJ3 "the strict (a, b)-inequalities"]
public abbrev SatisfiesStrictDepthInequalities (a b : ℤ) : Prop :=
  ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
    ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
      ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
      depthAddDistance S F y z p > (a : EInt) ∨
        depthAddDimAddDistance S F y z p > (b : EInt)

end Stacks.Algebraization

end
