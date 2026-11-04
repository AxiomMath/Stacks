module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.EulerCharacteristicOnPoints

/-!
# The numerical subclass `Coh^P_{X/B}` of the coherent objects

In Situation 0DNC — the standing data
`AlgebraicGeometry.Space.NumericalSituation` of a separated morphism `f : X ⟶ B` of finite
presentation, an index set `I`, a perfect object `E i` of `D(𝒪_X)` for each `i ∈ I`, and
prescribed invariants `P : I → ℤ` — the source forms the substack `Coh^P_{X/B} ⊆ Coh_{X/B}` of
those objects `(T, 𝓕)` whose numerical invariants `χ_i : |T| → ℤ`,
`t ↦ χ(X_t, E_{i,t} ⊗^𝐋 𝓕_t)`, are constantly `P i`.  **Stacks 0DNE** asserts that it is an
open and closed substack, and **Stacks 0DND** that it is algebraic with
`Coh^P_{X/B} ⟶ Coh_{X/B}` a flat closed immersion.

This file constructs `Coh^P_{X/B}` as a subclass of `AlgebraicGeometry.Space.CoherentObject`
and proves that the locus in `|T|` cut out by `χ_i = P i` is open and closed, the statement to
which the openness and closedness of `Coh^P_{X/B}` reduce.

## Main definitions

* `AlgebraicGeometry.Space.NumericalSituation.ChiData`: the numerical invariants of
  Situation 0DNC as data — for every object of `Coh_{X/B}` and every index, a function on the
  points of the test scheme, characterised étale locally as the derived-fibre Euler
  characteristic of a perfect object.
* `AlgebraicGeometry.Space.NumericalSituation.cohP`: **the subclass `Coh^P_{X/B}`** of the
  objects of `Coh_{X/B}`, cut out by `χ_i = P i` for every index `i`.

## Main results

* `AlgebraicGeometry.Space.NumericalSituation.isClopen_setOf_chi_eq`: **the open-and-closed
  clause of Stacks 0DNE**, at the level of the locus in `|T|`: the subset of `|T|` on which
  `χ_i = P i` is open and closed.
* `AlgebraicGeometry.Space.NumericalSituation.cohP_iff_forall_eq_univ`: membership of
  `Coh^P_{X/B}` is exactly the condition that each of those open and closed loci is all of
  `|T|`.
* `AlgebraicGeometry.Space.NumericalSituation.cohP_restrict`: `Coh^P` only grows when the index
  set is cut down.

## Implementation notes

The numerical invariants `χ_i` are taken as data, together with the property that characterises
them étale locally (`AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreChi` of Stacks 0D1Z), as
for `AlgebraicGeometry.Space.IsPrescribedTwistedEuler` of Stacks 0DNF: reading the cohomology of
a derived fibre as a vector space over a field representing the point uses clause (2) of
Stacks 03OJ. The characterisation is stated on the test space rather than through
`K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝓕)`.

`Coh_{X/B}` carries no category structure here (`AlgebraicGeometry.Space.CoherentCategoryData`
is a specification of one), so it is not an object of `AlgebraicGeometry.Stack.AlgebraicStacks`
and the vocabulary `AlgebraicGeometry.Stack.OpenSubstack`,
`AlgebraicGeometry.Stack.IsClosedSubstack` of Stacks 04YM does not apply to it. The clause of
Stacks 0DNE proved here is that the condition cutting out `Coh^P` is, on each object, an open and
closed condition on the points of the test scheme; it needs no finiteness of `I` or local
Noetherianness of `B`, local constancy of each `χ_i` giving it index by index.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v m

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : CoherentSituation B S hS)
    [HasSheafify (smallEtaleRingedSite B S hS D.X.1 D.X.2).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS D.X.1 D.X.2).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [∀ U : (smallEtaleRingedSite B S hS D.X.1 D.X.2).C,
      HasSheafify ((smallEtaleRingedSite B S hS D.X.1 D.X.2).J.over U) AddCommGrpCat.{m}]
    [∀ U : (smallEtaleRingedSite B S hS D.X.1 D.X.2).C,
      ((smallEtaleRingedSite B S hS D.X.1 D.X.2).J.over U).WEqualsLocallyBijective
        AddCommGrpCat.{m}]
    [hSheafCompose : ∀ U : (smallEtaleRingedSite B S hS D.X.1 D.X.2).C,
      ((smallEtaleRingedSite B S hS D.X.1 D.X.2).J.over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})]

namespace NumericalSituation

/-- The points of the test scheme of an object of `Coh_{X/B}`: the points of the algebraic space
that scheme represents, which is where the source's `χ_i` is defined. -/
abbrev testPoints (A : CoherentObject D) : Type (u + 1) :=
  points B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1

/-- **The numerical invariants of Situation 0DNC, as data.**  For every object `(T, 𝓕)` of
`Coh_{X/B}` and every index `i`, a function `χ_i : |T| → ℤ`, together with the property that
characterises it étale locally: on every étale chart of `|T|` it is the derived-fibre Euler
characteristic of a perfect object of the derived category of modules on that chart. In the
source `χ_i` is `t ↦ χ(X_t, E_{i,t} ⊗^𝐋 𝓕_t)`. -/
structure ChiData (N : NumericalSituation.{u, v, m} B S hS D) where
  /-- The numerical invariant `χ_i : |T| → ℤ` of each object and each index. -/
  chi : ∀ A : CoherentObject D, N.I → testPoints B S hS D A → ℤ
  /-- Each `χ_i` is étale locally a derived-fibre Euler characteristic. -/
  isEtaleLocally : ∀ (A : CoherentObject D) (i : N.I),
    IsEtaleLocallyDerivedFibreChi B S hS
      ((schemeSpaceFunctor B S hS).obj A.T.left).1 (chi A i)

variable {B S hS D} (N : NumericalSituation.{u, v, m} B S hS D)

/-- **The subclass `Coh^P_{X/B} ⊆ Coh_{X/B}` of Situation 0DNC.**  An object `(T, 𝓕)` of
`Coh_{X/B}` belongs to it when, for every index `i`, the numerical invariant `χ_i` is
constantly the prescribed value `P i` on the points of the test scheme. -/
def cohP (c : ChiData B S hS D N) (A : CoherentObject D) : Prop :=
  ∀ (i : N.I) (t : testPoints B S hS D A), c.chi A i t = N.P i

omit hSheafCompose in
/-- **Stacks 0DNE, the open-and-closed clause, at the level of the locus in `|T|`.**  For an
object `(T, 𝓕)` of `Coh_{X/B}` and an index `i`, the subset of `|T|` on which the numerical
invariant `χ_i` takes the prescribed value `P i` is open and closed: `χ_i` is locally constant by
Stacks 0D1Z (`AlgebraicGeometry.Space.isLocallyConstant_of_isEtaleLocallyDerivedFibreChi`), and
the fibres of a locally constant function are open and closed. -/
@[stacks 0DNE "the open-and-closed clause only, at the level of the locus in |T| cut out by the
condition chi_i = P i; Coh_{X/B} is no category here, so no substack claim is made"]
theorem isClopen_setOf_chi_eq (c : ChiData B S hS D N) (A : CoherentObject D) (i : N.I) :
    IsClopen {t : testPoints B S hS D A | c.chi A i t = N.P i} :=
  (isLocallyConstant_of_isEtaleLocallyDerivedFibreChi B S hS
    ((schemeSpaceFunctor B S hS).obj A.T.left).1 (c.chi A i)
    ((schemeSpaceFunctor B S hS).obj A.T.left).2 (c.isEtaleLocally A i)).isClopen_fiber _

omit hSheafCompose in
/-- Membership of `Coh^P_{X/B}` is exactly the condition that every one of the open and closed
loci of `AlgebraicGeometry.Space.NumericalSituation.isClopen_setOf_chi_eq` is all of `|T|`. -/
theorem cohP_iff_forall_eq_univ (c : ChiData B S hS D N) (A : CoherentObject D) :
    cohP N c A ↔ ∀ i : N.I, {t : testPoints B S hS D A | c.chi A i t = N.P i} = Set.univ :=
  ⟨fun h i => Set.eq_univ_of_forall fun t => h i t, fun h i t => Set.eq_univ_iff_forall.1 (h i) t⟩

/-- The numerical invariants re-indexed by a subset of the index set, matching
`AlgebraicGeometry.Space.NumericalSituation.restrict`. -/
def ChiData.restrict (c : ChiData B S hS D N) (J : Set N.I) :
    ChiData B S hS D (N.restrict J) where
  chi A i := c.chi A i.1
  isEtaleLocally A i := c.isEtaleLocally A i.1

omit hSheafCompose in
/-- **`Coh^P` only grows when the index set is cut down.**  An object satisfying the prescribed
invariants at every index satisfies them at the indices of any subset. -/
theorem cohP_restrict (c : ChiData B S hS D N) (J : Set N.I) {A : CoherentObject D}
    (h : cohP N c A) :
    cohP (N.restrict J) (ChiData.restrict N c J) A :=
  fun i t => h i.1 t

end NumericalSituation

end AlgebraicGeometry.Space

end
