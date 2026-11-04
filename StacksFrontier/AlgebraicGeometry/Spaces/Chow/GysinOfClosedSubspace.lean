module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The refined Gysin map on the cycle of a closed subspace

In the situation of Stacks 0EDT let `X/B` be good and let `(ℒ, s, i : E → X)` be a triple as in
Definition 0ER1: `ℒ` an invertible sheaf on `X`, `s` a global section of `ℒ`, and `E = Z(s)` its
vanishing locus with its closed immersion into `X`.  Stacks 0ER7 says that for a closed subspace
`Z ⊆ X` with `dim_δ(Z) ≤ k + 1` whose intersection `E ∩ Z` is an effective Cartier divisor
on `Z`,

  `i^*([Z]_{k + 1}) = [E ∩ Z]_k`.

The letter `D` is the dimension situation of Stacks 0EDT, so the closed subspace which the source
calls `D` is called `E` here, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection`.

## Main definitions

* `AlgebraicGeometry.Space.interOnClosedSubspace`: the scheme-theoretic intersection `E ∩ Z`,
  read as a closed subspace of `Z`.  This is the object the source asks to be an effective
  Cartier divisor *on `Z`*.
* `AlgebraicGeometry.Space.interOnVanishingLocus`: the same intersection read as a closed
  subspace of `E`.  This is the object whose `k`-cycle `[E ∩ Z]_k` is the right-hand side, the
  Gysin map taking values in cycles on `E`.

## Main results

* `AlgebraicGeometry.Space.gysinCycleMap_integralCycle_of_not_le`: **Stacks 0ER7 for an integral
  `Z` of δ-dimension `k + 1`**, unconditionally.  There `[Z]_{k + 1}` is the cycle of a single
  integral closed subspace and the right-hand side is the component cycle `[E ∩ Z]_k` of Stacks
  0ER1(1)(a), so the lemma is an identification of the Gysin map with its own defining clause.
* **Stacks 0ER7** for a general closed subspace is not stated here: it is
  `AlgebraicGeometry.Space.gysinCycleMap_closedSubspaceCycle_coe_eq` and
  `AlgebraicGeometry.Space.gysinCycleMap_canonical_eq_of_cycleCoeffOfClosedSubspace`
  (`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinClosedSubspaceIntersectionAdditivity`), where
  the two inputs of the source's proof described in the implementation notes are discharged.

## Implementation notes

### How `E ∩ Z` is read

The source's `D ∩ Z` is the scheme-theoretic intersection, the fibre product `D ×_X Z`.  It
occurs in two roles with two different ambient spaces: as a closed subspace of `Z`, where it is
required to be an effective Cartier divisor, and as a closed subspace of `D`, where its `k`-cycle
is the right-hand side of the identity (the Gysin map of Stacks 0ER1 lands in cycles on `D`).
Both readings are inverse images in the sense of Stacks 083Q — `Subfunctor.preimage` — which is
the fibre product by `CategoryTheory.Subfunctor.isPullback_preimage`: `E ∩ Z` on `Z` is the
inverse image of `E` along `Z → X` and `E ∩ Z` on `E` is the inverse image of `Z` along
`i : E → X`.  Both are closed subspaces by
`AlgebraicGeometry.Space.isClosedSubspace_preimage`, and pushing either forward into `X` gives
the subfunctor intersection `E ∩ Z` there.

### The two cycles

The cycle `[Y]_k` of a closed subspace is Stacks 0EE9, which this library has coefficientwise as
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace`, a function on the integral closed subspaces
of the ambient space; that a coefficient family is a *cycle* — local finiteness of its support —
is the part of Stacks 0EE9 which is not available.  The two cycles of the statement are therefore
taken as elements `α` of `Z_{k+1}(X)` and `β` of `Z_k(E)` whose coefficient families are pinned to
that of Stacks 0EE9 by the hypotheses `hα` and `hβ`.  Nothing is weakened: `α` is `[Z]_{k+1}` and
`β` is `[E ∩ Z]_k`, coefficient by coefficient, and supplying them is exactly supplying the
missing local finiteness.

### What is proved and what is assumed

The source's proof has two steps.  The hypothesis that `E ∩ Z` is an effective Cartier divisor on
`Z` says that `s|_Z` is a regular section of `ℒ|_Z`, whence `E ∩ Z = Z(s|_Z)`; Lemma 0EQL then
gives `[E ∩ Z]_k = ∑ n_i [Z(s_i)]_k`, the sum over the irreducible components `Z_i ⊆ Z` of
δ-dimension `k + 1` weighted by their multiplicities `n_i` in `[Z]_{k + 1}`, with `s_i = s|_{Z_i}`.
Since `Z_i ⊄ E` and `E ∩ Z_i = Z(s_i)`, matching against the defining clause 0ER1(1)(a) of the
Gysin map finishes the proof.

The second step is what is proved here, and it is the only step that this library can take: the
cycle `[E ∩ W]_k` of clause (1)(a) is the explicit parameter
`AlgebraicGeometry.Space.GysinComponentRule.intersectionCycle` that Stacks 0ER1 takes it to be
here, and the computation is that the Gysin coefficient family of `α` is the `α`-weighted sum of
those cycles.  The first step is carried as hypotheses, each standing for a result of the source
that this library does not have:

* `hnotle`: no integral closed subspace occurring in `[Z]_{k + 1}` is contained in `E`.  In the
  source this comes from the effective Cartier hypothesis, through the regularity of `s|_Z`: a
  regular section does not vanish on an irreducible component.  The route available here would be
  Stacks 083S, the scheme-theoretic density of the open complement of an effective Cartier
  divisor, together with Stacks 0EE6 making a subspace of maximal δ-dimension a component;
  but scheme-theoretic density is not related to density of `|Z|` anywhere in this library, so
  the implication is not available.  The exact statement needed is the one written out in the
  hypothesis: `∀ W, α.1 W ≠ 0 → ¬ W.subspace ≤ (vanishingLocus D p hp L s).1`.
* `ic` together with `hic` and `hsum`: **Stacks 0EQL** for the triple restricted to `Z`.  The
  family `ic` is `[E ∩ W]_k` as a `k`-cycle on `E`, agreeing by `hic` with clause (1)(a) wherever
  that clause applies, and `hsum` is the identity `[E ∩ Z]_k = ∑ n_W [E ∩ W]_k` of Stacks 0EQL.
  The conditional form of Stacks 0EQL proved in
  `StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap` is stated for the zero scheme of
  a section on the ambient space, and transporting it to `Z` needs the identification
  `E ∩ W = Z(s|_W)` of the zero scheme of a restricted section with a base change, which the
  implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeFactorization` record as unavailable for want
  of quasi-coherent ideals on an algebraic space (Stacks 03MB).

The dimension bound `dim_δ(Z) ≤ k + 1` and the effective Cartier hypothesis are carried
unused: they are the hypotheses under which the source states the identity, and they are what
makes `hnotle` and `hsum` true rather than extra assumptions.

## References

* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083S](https://stacks.math.columbia.edu/tag/083S)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### A coefficient of the cycle of a closed subspace off the chosen δ-dimension -/

/-- An integral closed subspace whose δ-dimension is not `k` has coefficient zero in the
`k`-cycle `[Y]_k` of a closed subspace: only subspaces of δ-dimension `k` contribute. -/
theorem cycleCoeffOfClosedSubspace_eq_zero_of_deltaDimension_ne (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D sX W ≠ k) :
    cycleCoeffOfClosedSubspace D sX hX Y hY k γ W = 0 := by
  rw [cycleCoeffOfClosedSubspace, ite_eq_right hW]

/-! ### The scheme-theoretic intersection with the vanishing locus -/

section Intersection

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)

/-- The scheme-theoretic intersection `E ∩ Z` of the vanishing locus `E = Z(s)` with a closed
subspace `Z ⊆ X`, read as a closed subspace of `Z`: the inverse image of `E` along `Z → X`.
This is the object which Stacks 0ER7 asks to be an effective Cartier divisor on `Z`. -/
abbrev interOnClosedSubspace : ClosedSubspaces D.site D.base D.base_mem Z.1.toFunctor :=
  ⟨(vanishingLocus D p hp L s).1.preimage Z.1.ι,
    isClosedSubspace_preimage D.site D.base D.base_mem Z.1.ι (vanishingLocus D p hp L s).1
      hp.1 Z.2.1 (vanishingLocus D p hp L s).2⟩

/-- The scheme-theoretic intersection `E ∩ Z` of the vanishing locus `E = Z(s)` with a closed
subspace `Z ⊆ X`, read as a closed subspace of `E`: the inverse image of `Z` along the closed
immersion `i : E → X`.  This is the object whose `k`-cycle `[E ∩ Z]_k` is the right-hand side of
Stacks 0ER7. -/
abbrev interOnVanishingLocus :
    ClosedSubspaces D.site D.base D.base_mem (vanishingLocus D p hp L s).1.toFunctor :=
  ⟨Z.1.preimage (vanishingLocus D p hp L s).1.ι,
    isClosedSubspace_preimage D.site D.base D.base_mem (vanishingLocus D p hp L s).1.ι Z.1
      hp.1 (vanishingLocus D p hp L s).2.1 Z.2⟩

end Intersection

/-! ### Stacks 0ER7 -/

section Gysin

variable (p : X ⟶ D.space) (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ) (rule : GysinComponentRule D p E k)

/-- **Stacks 0ER7 for an integral closed subspace of δ-dimension `k + 1`.**  On the cycle of an
integral closed subspace `W ⊆ X` of δ-dimension `k + 1` which is not contained in `E`, the Gysin
map of Stacks 0ER1 is the cycle `[E ∩ W]_k`.

For such a `W` the cycle `[W]_{k+1}` of Stacks 0EE9 is the coefficient family taking the value
`1` at `W`, which is `AlgebraicGeometry.Space.integralCycle`, and `[E ∩ W]_k` is the parameter
`AlgebraicGeometry.Space.GysinComponentRule.intersectionCycle` standing for Stacks 0EE9 in clause
0ER1(1)(a).  The containment hypothesis is what the effective Cartier hypothesis of Stacks 0ER7
supplies in the source. -/
theorem gysinCycleMap_integralCycle_of_not_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    gysinCycleMap D p E hE k rule (integralCycle D p (k + 1) W hW) =
      rule.intersectionCycle W hW hWE := by
  rw [gysinCycleMap_integralCycle D p E hE k rule hW,
    gysinComponentCycle_of_not_le D p E hE k rule hW hWE]

end Gysin

section Main

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)
    (hE : D.IsGood ((vanishingLocus D p hp L s).1.ι ≫ p))
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)

end Main

end AlgebraicGeometry.Space

end
