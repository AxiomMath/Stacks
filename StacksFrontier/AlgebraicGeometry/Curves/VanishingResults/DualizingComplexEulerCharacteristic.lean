module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.HypercohomologyExtUnit
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinearSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinear
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# `χ(X, 𝒪_X) = χ(X, ω_X^•)` for a proper curve

Let `k` be a field and `f : X ⟶ Spec k` a proper morphism with `X` of topological Krull dimension
at most one, and let `ω_X^• = f^×(𝒪_{Spec k})` be the dualizing complex of [Stacks, Tag 0BS2].
This file proves the first formula of [Stacks, Tag 0BS5],

**`χ(X, 𝒪_X) = χ(X, ω_X^•)`,**

at exactly those hypotheses; neither the Cohen--Macaulay nor the equidimensionality hypothesis
of the tag's second formula enters. The second formula is
`AlgebraicGeometry.eulerCharacteristic_unit_eq_neg_eulerCharacteristic_dualizingSheafOverField`
of `Curves/VanishingResults/CohenMacaulayEulerCharacteristic.lean`, which deduces it from the
first and from `ω_X^• = ω_X[1]` ([Stacks, Tag 0BS3]) through the lemma
`AlgebraicGeometry.finsum_alternating_finrank_unit_eq_neg_dualizingSheafOverField_of_iso` here.

The Euler characteristic of the complex is the alternating sum
`χ(X, ω_X^•) = ∑_{i ∈ ℤ} (-1)^i dim_k H^i(X, ω_X^•)` that the source *defines* it to be; it is
`AlgebraicGeometry.eulerCharacteristicDerived` below.

## Main definitions

* `AlgebraicGeometry.eulerCharacteristicDerived`: the alternating sum of the dimensions of the
  hypercohomology of an object of `D(𝒪_X)`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `finrank_derivedCohomologyOverField_dualizingComplexOverField`:
  `dim_k H^i(X, ω_X^•) = dim_k H^{-i}(X, 𝒪_X)` for every `i ∈ ℤ`.
* `eulerCharacteristic_unit_eq_eulerCharacteristicDerived_dualizingComplexOverField`:
  **`χ(X, 𝒪_X) = χ(X, ω_X^•)`**, the first formula of [Stacks, Tag 0BS5].
* `finiteDimensional_derivedCohomologyOverField_dualizingComplexOverField`: every
  `H^i(X, ω_X^•)` is finite dimensional, so `χ(X, ω_X^•)` is a sum of honest dimensions.
* `finsum_alternating_finrank_unit_eq_neg_dualizingSheafOverField_of_iso`: for any isomorphism
  `ω_X^• ≅ ω_X[1]`, the alternating sums of `𝒪_X` and of `ω_X` are opposite; this is the step from
  the first formula of the tag to the second.

## The proof of the first formula

The source's proof is the computation
`H^i(X, ω_X^•) = Ext^i(𝒪_X, ω_X^•) = Hom_k(H^{-i}(X, 𝒪_X), k)`, and that is what is run here:

* the first identification is corepresentability of derived global sections by the structure
  sheaf, `Stacks.Duality.finrank_derivedCohomologyOverField_eq_finrank_extUnit`;
* the second is clause (4) of [Stacks, Tag 0BS2] in its `k`-linear form,
  `Stacks.Duality.extDualityLinearEquiv`, at `K = 𝒪_X[0]`;
* a `k`-vector space and its `k`-linear dual have the same `Module.finrank`
  (`Subspace.dual_finrank_eq`), with no finite-dimensionality hypothesis: in infinite dimensions
  both sides are zero.

That equality of dimensions holds for every `i`, and with it both sides of the formula collapse to
`h⁰ - h¹`. On the right, `dim_k H^i(X, ω_X^•) = dim_k H^{-i}(X, 𝒪_X)` vanishes unless
`0 ≤ -i ≤ 1`: for `-i ≥ 2` by [Stacks, Tag 02UZ]
(`AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le`), and for `-i < 0`
because `𝒪_X[0]` sits in degrees `≤ 0` while `𝒪_X[0][-i]` sits in degrees `≥ -i > 0`, so there is
no nonzero morphism between them at all
(`CategoryTheory.Triangulated.TStructure.zero`). Since the sign `(-1)^i` is even in `i`, the two
surviving terms are `dim_k H⁰(X, 𝒪_X)` with sign `+` and `dim_k H¹(X, 𝒪_X)` with sign `-`, which
is `χ(X, 𝒪_X)`.

Properness is used only through [Stacks, Tag 02UZ]; the dimension bound only there and in the
collapse of `χ(X, 𝒪_X)` itself.

## The second formula

The second formula, `χ(X, 𝒪_X) = -χ(X, ω_X)` for `X` Cohen--Macaulay and equidimensional of
dimension one, is the first together with `ω_X^• = ω_X[1]`. The step from an isomorphism
`ω_X^• ≅ ω_X[1]` to the equality of alternating sums is
`AlgebraicGeometry.finsum_alternating_finrank_unit_eq_neg_dualizingSheafOverField_of_iso` here;
the formula itself, with the isomorphism supplied by [Stacks, Tag 0BS3], is in
`Curves/VanishingResults/CohenMacaulayEulerCharacteristic.lean`.

## Implementation notes

*The sign.* The parity in the integer-indexed sum is written `(-1)^|i|`, which is `(-1)^i` for
every integer `i` and is what lets the reindexing `i ↦ -i` of the duality be read off the sum
without a sign.

*Why the isomorphism lemma is written with alternating sums.*
`AlgebraicGeometry.eulerCharacteristic` demands `SheafOfModules.IsCoherent` of its argument. The
lemma `finsum_alternating_finrank_unit_eq_neg_dualizingSheafOverField_of_iso` holds for any
isomorphism `ω_X^• ≅ ω_X[1]` without that instance, so it is stated with the sums that define the
Euler characteristics; the second formula itself, in
`Curves/VanishingResults/CohenMacaulayEulerCharacteristic.lean`, supplies the coherence of `ω_X`
(clause (2) of [Stacks, Tag 0BS2]) and is stated with `AlgebraicGeometry.eulerCharacteristic`.

## References

* [Stacks Project, Tag 0BS5](https://stacks.math.columbia.edu/tag/0BS5)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **The Euler characteristic of an object of `D(𝒪_X)`**: the alternating sum
`∑_{i ∈ ℤ} (-1)^i dim_k H^i(X, K)` of the dimensions of its hypercohomology over the base field.
This is the definition [Stacks, Tag 0BS5] gives for `χ(X, ω_X^•)`. -/
public def eulerCharacteristicDerived (K : DerivedCategory X.Modules) : ℤ :=
  ∑ᶠ i : ℤ, (-1 : ℤ) ^ i.natAbs *
    (Module.finrank k (Stacks.Duality.derivedCohomologyOverField f K i) : ℤ)

section Linearity

variable [IsProper f] [Linear k X.Modules] [Functor.Linear k (globalSectionsOver f)]

/-- `H^i(X, ω_X^•)` is `k`-linearly the dual of `H^{-i}(X, 𝒪_X)`: `Ext^i(𝒪_X, ω_X^•)` and
clause (4) of [Stacks, Tag 0BS2]. -/
private theorem nonempty_derivedCohomologyOverField_dualizingComplexOverField_linearEquiv_dual
    (i : ℤ) : Nonempty (Stacks.Duality.derivedCohomologyOverField f
        (Stacks.Duality.dualizingComplexOverField f).obj i ≃ₗ[k]
      Module.Dual k (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)) (-i))) :=
  ⟨(Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit f _ i).some.trans
    ((Stacks.Duality.extDualityLinearEquiv f
      (Stacks.Duality.DerivedPushforward.derivedStructureSheaf X) i).trans
        ModuleCat.homLinearEquiv)⟩

/-- **`dim_k H^i(X, ω_X^•) = dim_k H^{-i}(X, 𝒪_X)`** for every integer `i`, with
`ω_X^• = f^×(𝒪_{Spec k})` the dualizing complex of [Stacks, Tag 0BS2]. This is the computation the
proof of [Stacks, Tag 0BS5] runs: hypercohomology of `ω_X^•` is `Ext` out of the structure sheaf,
clause (4) of [Stacks, Tag 0BS2] identifies that with the `k`-linear dual of `H^{-i}(X, 𝒪_X)`, and
a space and its dual have the same dimension. -/
public theorem finrank_derivedCohomologyOverField_dualizingComplexOverField (i : ℤ) :
    Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
        (Stacks.Duality.dualizingComplexOverField f).obj i) =
      Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)) (-i)) := by
  exact (nonempty_derivedCohomologyOverField_dualizingComplexOverField_linearEquiv_dual f i).some
    |>.finrank_eq.trans Subspace.dual_finrank_eq

omit [IsProper f] in
/-- **`H^m(X, 𝒪_X) = 0` in the negative degrees.** Hypercohomology of the structure sheaf placed
in degree zero is `Ext^m` out of it, and for `m < 0` there is no nonzero morphism from an object
in degrees `≤ 0` to one in degrees `≥ -m > 0`. -/
public theorem subsingleton_derivedCohomologyOverField_unit_single_of_neg (m : ℤ) (hm : m < 0) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)) m) := by
  have := DerivedCategory.TStructure.t.isGE_shift
    ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)) 0 m (-m)
    (by omega)
  have : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X))
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)) m) :=
    ⟨fun a b => by
      rw [DerivedCategory.TStructure.t.zero a 0 (-m) (by omega),
        DerivedCategory.TStructure.t.zero b 0 (-m) (by omega)]⟩
  exact (Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit f _ m).some
    |>.toEquiv.subsingleton

omit [IsProper f] in
/-- **`dim_k H^m(X, 𝒪_X) = 0` in the negative degrees**, by
`AlgebraicGeometry.subsingleton_derivedCohomologyOverField_unit_single_of_neg`. -/
public theorem finrank_derivedCohomologyOverField_unit_single_eq_zero_of_neg (m : ℤ) (hm : m < 0) :
    Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)) m) = 0 :=
  have := subsingleton_derivedCohomologyOverField_unit_single_of_neg f m hm
  Module.finrank_zero_of_subsingleton

omit [IsProper f] [Linear k X.Modules] [Functor.Linear k (globalSectionsOver f)] in
/-- **`H^n(X, 𝒪_X) = Hⁿ(X, 𝒪_X)` in the nonnegative degrees**: hypercohomology of the structure
sheaf placed in degree zero is its sheaf cohomology, by
`Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField`. -/
public theorem finrank_derivedCohomologyOverField_unit_single_natCast (n : ℕ) :
    Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)) (n : ℤ)) =
      Module.finrank k (cohomologyOverField k f (Stacks.Ample.unitModule X) n) :=
  ((Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f
    (Stacks.Ample.unitModule X) n).symm).finrank_eq

/-- `dim_k H^{-n}(X, ω_X^•) = dim_k Hⁿ(X, 𝒪_X)` for a natural number `n`, from the duality
`AlgebraicGeometry.finrank_derivedCohomologyOverField_dualizingComplexOverField` and
`AlgebraicGeometry.finrank_derivedCohomologyOverField_unit_single_natCast`. -/
private theorem finrank_derivedCohomologyOverField_dualizingComplexOverField_neg_natCast (n : ℕ) :
    Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
        (Stacks.Duality.dualizingComplexOverField f).obj (-(n : ℤ))) =
      Module.finrank k (cohomologyOverField k f (Stacks.Ample.unitModule X) n) :=
  (finrank_derivedCohomologyOverField_dualizingComplexOverField f _).trans
    ((neg_neg (n : ℤ)).symm ▸ finrank_derivedCohomologyOverField_unit_single_natCast f n)

/-- **`H^m(X, 𝒪_X)` is finite dimensional** for every integer `m`, on `X` proper over a field:
zero for `m < 0`, and the sheaf cohomology `H^m(X, 𝒪_X)` of a coherent module on a proper scheme
for `m ≥ 0` ([Stacks, Tag 02O6]). -/
@[sga "4½ Fonctions_L 3.7" "special case"]
public theorem finiteDimensional_derivedCohomologyOverField_unit_single (m : ℤ) :
    FiniteDimensional k (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)) m) := by
  rcases lt_or_ge m 0 with hm | hm
  · have := subsingleton_derivedCohomologyOverField_unit_single_of_neg f m hm
    infer_instance
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, by omega⟩
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let : (Stacks.Ample.unitModule X).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
    have := finiteDimensional_cohomologyOverField_of_isProper k f (Stacks.Ample.unitModule X) n
    exact Module.Finite.equiv
      (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f
        (Stacks.Ample.unitModule X) n)

/-- **`H^i(X, ω_X^•)` is finite dimensional** for every integer `i`, so that the alternating sum
`AlgebraicGeometry.eulerCharacteristicDerived` defining `χ(X, ω_X^•)` is the one the source
writes, a sum of honest dimensions. As in the proof of [Stacks, Tag 0BS5],
`H^i(X, ω_X^•) = Ext^i(𝒪_X, ω_X^•) = Hom_k(H^{-i}(X, 𝒪_X), k)`, and the dual of a
finite-dimensional space is finite dimensional. -/
public theorem finiteDimensional_derivedCohomologyOverField_dualizingComplexOverField (i : ℤ) :
    FiniteDimensional k (Stacks.Duality.derivedCohomologyOverField f
      (Stacks.Duality.dualizingComplexOverField f).obj i) := by
  have : FiniteDimensional k (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)) (-i)) :=
    finiteDimensional_derivedCohomologyOverField_unit_single f (-i)
  exact Module.Finite.equiv
    (nonempty_derivedCohomologyOverField_dualizingComplexOverField_linearEquiv_dual f i).some.symm

/-- **`χ(X, ω_X^•) = dim_k H⁰(X, 𝒪_X) - dim_k H¹(X, 𝒪_X)`** on a proper scheme of dimension at
most one over a field. The duality
`AlgebraicGeometry.finrank_derivedCohomologyOverField_dualizingComplexOverField` turns the sum
over `i` into a sum of the dimensions of `H^{-i}(X, 𝒪_X)`, which vanish outside `-i ∈ {0, 1}`, so
only the degrees `i = 0` and `i = -1` contribute. -/
public theorem eulerCharacteristicDerived_dualizingComplexOverField_eq_sub
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    eulerCharacteristicDerived f (Stacks.Duality.dualizingComplexOverField f).obj =
      (Module.finrank k (cohomologyOverField k f (Stacks.Ample.unitModule X) 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f (Stacks.Ample.unitModule X) 1) : ℤ) := by
  classical
  have hvan : ∀ i : ℤ, i ≠ 0 → i ≠ -1 →
      Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
        (Stacks.Duality.dualizingComplexOverField f).obj i) = 0 := by
    intro i hi hi'
    rcases lt_or_ge i 0 with h | h
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [finrank_derivedCohomologyOverField_dualizingComplexOverField_neg_natCast]
      have := ModuleCat.subsingleton_of_isZero
        (isZero_cohomologyOverField_of_topologicalKrullDim_le k f
          (Stacks.Ample.unitModule X) (d := 1) hdim (i := n) (by omega))
      exact Module.finrank_zero_of_subsingleton
    · rw [finrank_derivedCohomologyOverField_dualizingComplexOverField f i]
      exact finrank_derivedCohomologyOverField_unit_single_eq_zero_of_neg f (-i) (by omega)
  let t : ℤ → ℤ := fun i => (-1 : ℤ) ^ i.natAbs *
    (Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
      (Stacks.Duality.dualizingComplexOverField f).obj i) : ℤ)
  have hsupp : Function.support t ⊆ ({0, -1} : Finset ℤ) := by
    intro i hi
    by_contra h
    have hi' : i ≠ 0 ∧ i ≠ -1 := by simpa using h
    exact hi (by simp [t, hvan i hi'.1 hi'.2])
  have h0 := finrank_derivedCohomologyOverField_dualizingComplexOverField_neg_natCast f 0
  have h1 := finrank_derivedCohomologyOverField_dualizingComplexOverField_neg_natCast f 1
  rw [Nat.cast_zero, neg_zero] at h0
  rw [Nat.cast_one] at h1
  change (∑ᶠ i : ℤ, t i) = _
  rw [finsum_eq_sum_of_support_subset t hsupp]
  simp only [t]
  norm_num [h0, h1]
  ring

/-- **`dim_k H¹(X, ω_X) = dim_k H⁰(X, 𝒪_X)`** on a proper scheme of dimension at most one over a
field, given an isomorphism `ω_X^• ≅ ω_X[1]` (which [Stacks, Tag 0BS3] supplies when `X` is
Cohen--Macaulay and equidimensional of dimension one).

`H¹(X, ω_X)` is `Ext¹(𝒪_X, ω_X) = Hom_{D(𝒪_X)}(𝒪_X[0], ω_X[1])`, which the hypothesis turns into
`Hom_{D(𝒪_X)}(𝒪_X[0], ω_X^•)`; clause (4) of [Stacks, Tag 0BS2] in degree zero identifies that
with the `k`-linear dual of `H⁰(X, 𝒪_X)`. -/
public theorem finrank_cohomologyOverField_one_dualizingSheafOverField_eq_zero_unit_of_iso
    (e : (Stacks.Duality.dualizingComplexOverField f).obj ≅
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (Stacks.Duality.dualizingSheafOverField f))⟦(1 : ℤ)⟧) :
    Module.finrank k
        (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 1) =
      Module.finrank k (cohomologyOverField k f (Stacks.Ample.unitModule X) 0) := by
  refine Eq.trans (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f
    (Stacks.Duality.dualizingSheafOverField f) 1).finrank_eq ?_
  refine Eq.trans
    (Stacks.Duality.finrank_derivedCohomologyOverField_eq_finrank_extUnit f _ 1) ?_
  refine Eq.trans (CategoryTheory.Linear.homCongr k
    (Iso.refl ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)))
    (e.symm ≪≫ ((CategoryTheory.shiftFunctorZero (DerivedCategory X.Modules) ℤ).app
      (Stacks.Duality.dualizingComplexOverField f).obj).symm)).finrank_eq ?_
  refine Eq.trans
    (Stacks.Duality.finrank_derivedCohomologyOverField_eq_finrank_extUnit f
      (Stacks.Duality.dualizingComplexOverField f).obj 0).symm ?_
  exact finrank_derivedCohomologyOverField_dualizingComplexOverField_neg_natCast f 0

end Linearity

variable [IsProper f]

/-- **The first formula of [Stacks, Tag 0BS5]: `χ(X, 𝒪_X) = χ(X, ω_X^•)`** for a proper scheme `X`
of dimension at most one over a field `k`, with `ω_X^• = f^×(𝒪_{Spec k})` the dualizing complex of
[Stacks, Tag 0BS2] and `χ(X, ω_X^•)` the alternating sum
`∑_{i ∈ ℤ} (-1)^i dim_k H^i(X, ω_X^•)` that the source defines it to be.

Both sides collapse to `dim_k H⁰(X, 𝒪_X) - dim_k H¹(X, 𝒪_X)`: on the right by the duality
`dim_k H^i(X, ω_X^•) = dim_k H^{-i}(X, 𝒪_X)`
(`AlgebraicGeometry.eulerCharacteristicDerived_dualizingComplexOverField_eq_sub`), on the left
because `X` is at most one-dimensional ([Stacks, Tag 02UZ]). -/
@[stacks 0BS5 "first formula, chi(X, O_X) = chi(X, omega^bullet), for X proper of dimension at \
most one over a field, omega^bullet = f^x(O_Spec k) of Tag 0BS2, and chi(X, omega^bullet) the \
alternating sum of the dimensions of its hypercohomology, as the source defines it"]
public theorem eulerCharacteristic_unit_eq_eulerCharacteristicDerived_dualizingComplexOverField
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : (Stacks.Ample.unitModule X).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
    eulerCharacteristic k f (Stacks.Ample.unitModule X) =
      eulerCharacteristicDerived f (Stacks.Duality.dualizingComplexOverField f).obj := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : (Stacks.Ample.unitModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  let := Scheme.Modules.linearOverBase f
  let : Functor.Linear k (globalSectionsOver f) :=
    AlgebraicGeometry.globalSectionsOver_linear_linearOverBase f
  rw [eulerCharacteristic_eq_finsum,
    finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f
      (Stacks.Ample.unitModule X) (fun m hm =>
        isZero_cohomologyOverField_of_topologicalKrullDim_le k f (Stacks.Ample.unitModule X)
          (d := 1) hdim (i := m) (by omega)),
    eulerCharacteristicDerived_dualizingComplexOverField_eq_sub f hdim]

/-- **From `ω_X^• ≅ ω_X[1]` to `χ(X, 𝒪_X) = -χ(X, ω_X)`**, on a proper scheme of dimension at
most one over a field: for any isomorphism `ω_X^• ≅ ω_X[1]`, the alternating sums of the
dimensions of the cohomology of `𝒪_X` and of `ω_X` are opposite. This is how the source deduces
the second formula of [Stacks, Tag 0BS5] from the first; the formula itself, at the tag's
hypotheses, is
`AlgebraicGeometry.eulerCharacteristic_unit_eq_neg_eulerCharacteristic_dualizingSheafOverField`.

The two dualities used are `dim_k H⁰(X, ω_X) = dim_k H¹(X, 𝒪_X)`,
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualizingSheafOverField_eq_finrank_one_unit`,
and `dim_k H¹(X, ω_X) = dim_k H⁰(X, 𝒪_X)`,
`AlgebraicGeometry.finrank_cohomologyOverField_one_dualizingSheafOverField_eq_zero_unit_of_iso`. -/
public theorem finsum_alternating_finrank_unit_eq_neg_dualizingSheafOverField_of_iso
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (e : (Stacks.Duality.dualizingComplexOverField f).obj ≅
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (Stacks.Duality.dualizingSheafOverField f))⟦(1 : ℤ)⟧) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        (Module.finrank k (cohomologyOverField k f (Stacks.Ample.unitModule X) n) : ℤ)) =
      -(∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        (Module.finrank k (cohomologyOverField k f
          (Stacks.Duality.dualizingSheafOverField f) n) : ℤ)) := by
  let := Scheme.Modules.linearOverBase f
  let : Functor.Linear k (globalSectionsOver f) :=
    AlgebraicGeometry.globalSectionsOver_linear_linearOverBase f
  have hvan : ∀ (M : X.Modules) (m : ℕ), 2 ≤ m → IsZero (cohomologyOverField k f M m) :=
    fun M m hm => isZero_cohomologyOverField_of_topologicalKrullDim_le k f M
      (d := 1) hdim (i := m) (by omega)
  rw [finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f
      (Stacks.Ample.unitModule X) (hvan _),
    finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f
      (Stacks.Duality.dualizingSheafOverField f) (hvan _),
    finrank_cohomologyOverField_zero_dualizingSheafOverField_eq_finrank_one_unit f hdim,
    finrank_cohomologyOverField_one_dualizingSheafOverField_eq_zero_unit_of_iso f e]
  ring

end AlgebraicGeometry

end
