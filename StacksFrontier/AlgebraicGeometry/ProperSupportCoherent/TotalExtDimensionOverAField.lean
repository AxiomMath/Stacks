module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.PerfectHomVanishingWindow
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessOverTheBase

/-!
# The total dimension of the Ext groups on a scheme proper over a field

Let `X` be a scheme proper over a field `k`, let `K` be an object of `D^b_Coh(𝒪_X)` and let `E`
be a perfect object of `D(𝒪_X)`. [Stacks, Tag 0FYC] asserts that

`∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞`.

The sum is the cardinal sum `Cardinal.sum` of the `k`-ranks of the Ext modules over the whole of
`ℤ`, and `< ∞` is `< ℵ₀`; so the assertion is the finiteness of the *total* dimension, which
splits into two independent halves: every `Ext^i_X(E, K)` is a finite-dimensional `k`-vector
space, and only finitely many of them are nonzero.

The second half is proved here from [Stacks, Tag 09M4] and [Stacks, Tag 0FXU]. The first half is
[Stacks, Tag 0D0D], of which this library carries only the degrees in which the Ext modules
vanish, so it is carried as the named hypothesis `hExtFinite`; see the main theorem's docstring.

The `k`-module structure is the canonical one of `AlgebraicGeometry.modulesLinear`, induced by the
structure morphism `X ⟶ Spec k`; this is the structure the tag's `dim_k` refers to, and it is
installed as a local instance below because it depends on that morphism.

## Main results

* `Stacks.AlgebraicGeometry.ProperSupportCoherent.lt_aleph0_cardinalSum`: a sum of cardinals is
  finite when every summand is finite and only finitely many summands are nonzero.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.isNoetherian_of_isProper_over_field`: a scheme
  proper over a field is Noetherian.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.finite_setOf_not_subsingleton_ext_of_isPerfect`:
  `Ext^i_X(E, K) = 0` for all but finitely many `i`, for `E` perfect and `K` bounded with
  coherent cohomology. This is the half of [Stacks, Tag 0FYC] that is proved outright.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.cardinalSum_rank_ext_lt_aleph0`:
  **[Stacks, Tag 0FYC]**, the finiteness of `∑_{i ∈ ℤ} dim_k Ext^i_X(E, K)`, granted
  finite-dimensionality of the individual Ext modules.

## Implementation notes

**The proof.** The source proves the tag by combining [Stacks, Tag 0D0D] (each
`Ext^i_X(E, K)` is a finite `k`-module, `E` lying in `D^-_Coh(𝒪_X)` because it is perfect) with
[Stacks, Tag 09M4] (the Ext modules vanish in all but finitely many degrees). That is exactly the
split used here. For the second factor, [Stacks, Tag 0FXU] puts the perfect object `E` in
`D^b_Coh(𝒪_X)`, which supplies the upper cohomological bound that [Stacks, Tag 09M4] needs, and
boundedness of `K` together with quasi-coherence of its cohomology sheaves — coherent modules
being quasi-coherent, [Stacks, Tag 01BW] — supplies the rest. Properness over a field makes `X`
Noetherian, which is the hypothesis of [Stacks, Tag 0FXU]: `X ⟶ Spec k` is locally of finite type
and quasi-compact, and `Spec k` is Noetherian and compact.

**What is carried as a hypothesis, and why.** Two inputs are not available in this library in a
form that applies here, and are named hypotheses rather than proved.

`hExtFinite` is finite-dimensionality of each `Ext^i_X(E, K)` over `k`, which is
[Stacks, Tag 0D0D]. That tag is now a theorem of this library,
`Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_ext_of_proper` of
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessUnconditional.lean`, so the
hypothesis is dischargeable: a field is Noetherian, `K` is bounded with coherent cohomology and a
perfect `E` lies in `D^b_Coh(𝒪_X)` by [Stacks, Tag 0FXU]. It is still carried here because
discharging it is a change to the shape of this tag's statement rather than to its content, and
because the second hypothesis below keeps the result conditional in any case.

`D` is the dual perfect complex of [Stacks, Tag 08DQ], in the form
`Stacks.DerivedQCoh.DualPerfectComplexData` in which [Stacks, Tag 09M4] is stated in this
library; there is no absolute derived internal hom on `D(𝒪_X)` here, so `E^∨` cannot be written
down and the properties of it that the proof of [Stacks, Tag 09M4] consumes travel as data.

**Spellings.** `RΓ(X, -)` enters as a pair of a functor and its structure morphism carrying the
right-derived-functor instance, exactly as in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/PerfectHomVanishingWindow.lean`, so the statements
hold for every model of it; this is a device for model-independence and not a hypothesis on the
geometry. `Ext^i_X(E, K)` is `DerivedCategory.Ext`, that is `Hom_{D(𝒪_X)}(E, K⟦i⟧)`, and
`D^b_Coh(𝒪_X)` is `DerivedCategoryB.derivedCategoryBBounded` at the coherence predicate, as in
the rest of this directory. Perfectness is
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, the predicate [Stacks, Tag 09M4] is stated at.
The derived category is the standard model `CategoryTheory.HasDerivedCategory.standard`, at the
priority used in `StacksFrontier/AlgebraicGeometry/DerivedQCoh/PerfectHomVanishingWindow.lean`,
since that is the model [Stacks, Tag 09M4] is baked at here.

## References

* [Stacks Project, Tag 0FYC](https://stacks.math.columbia.edu/tag/0FYC)
* [Stacks Project, Tag 0D0D](https://stacks.math.columbia.edu/tag/0D0D)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Cohomology (sectionsFunctor)

universe v u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Cardinal sums with finite support -/

/-- **A cardinal sum with finitely many nonzero, individually finite summands is finite.** The
sum is the cardinality of the disjoint union of the summands; only the summands indexed by the
support contribute, and that is a finite union of finite types. -/
theorem lt_aleph0_cardinalSum {ι : Type*} {f : ι → Cardinal.{v}}
    (hsupp : {i | f i ≠ 0}.Finite) (hf : ∀ i, f i < Cardinal.aleph0) :
    Cardinal.sum f < Cardinal.aleph0 := by
  have hmk : Cardinal.sum f = Cardinal.mk (Σ i, (f i).out) := rfl
  have hne : ∀ i, (f i).out → f i ≠ 0 := fun i x h0 =>
    (Cardinal.mk_eq_zero_iff.1 (by rw [Cardinal.mk_out]; exact h0)).elim x
  have : Finite {i // f i ≠ 0} := Set.Finite.to_subtype hsupp
  have : ∀ i, Finite (f i).out := fun i =>
    Cardinal.lt_aleph0_iff_finite.1 (by rw [Cardinal.mk_out]; exact hf i)
  rw [hmk, Cardinal.lt_aleph0_iff_finite]
  exact Finite.of_equiv _
    (Equiv.sigmaSubtypeEquivOfSubset (fun i => (f i).out) (fun i => f i ≠ 0) hne)

/-! ### The canonical linear structure over the base field -/

/-- The canonical `k`-linear structure on `𝒪_X`-modules for a scheme `X` over `Spec k`, induced
by the structure morphism. It is `AlgebraicGeometry.modulesLinear`, and is the structure in which
the dimensions below are taken. -/
local instance linearModulesOfOverField {k : Type u} [Field k] (X : Over (Spec (.of k))) :
    Linear k X.left.Modules :=
  AlgebraicGeometry.modulesLinear k X

/-! ### Properness over a field -/

/-- **A scheme proper over a field is Noetherian.** The structure morphism is locally of finite
type, so `X` is locally Noetherian, and it is quasi-compact over the compact space `Spec k`, so
`X` is compact. -/
theorem isNoetherian_of_isProper_over_field {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [IsProper X.hom] : IsNoetherian X.left := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact AlgebraicGeometry.IsNoetherian.mk

/-! ### Stacks 0FYC -/

section Main

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
  (RΓ : DerivedCategory X.left.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X.left, ⊤)))
  (α : (sectionsFunctor X.left ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.left.Modules (ComplexShape.up ℤ))]
  (E K : DerivedCategory X.left.Modules)

include α in
/-- **Only finitely many of the Ext modules are nonzero.** Let `X` be a scheme proper over a
field `k`, let `E` be a perfect object of `D(𝒪_X)` and let `K` be an object of `D^b_Coh(𝒪_X)`.
Then `Ext^n_X(E, K) = 0` for all but finitely many `n`.

This is the half of [Stacks, Tag 0FYC] that does not need [Stacks, Tag 0D0D]. Properness makes
`X` Noetherian, so [Stacks, Tag 0FXU] puts the perfect object `E` in `D^b_Coh(𝒪_X)` and in
particular bounds it above, which is the input [Stacks, Tag 09M4] needs of `E`; `K` is bounded
and its cohomology sheaves are coherent, hence quasi-coherent by [Stacks, Tag 01BW], which is
the input it needs of `K`. The dual perfect complex of [Stacks, Tag 08DQ] is carried as the
hypothesis `D`, as in the statement of [Stacks, Tag 09M4] in this library. -/
theorem finite_setOf_not_subsingleton_ext_of_isPerfect
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E)
    (D : Stacks.DerivedQCoh.DualPerfectComplexData X.left RΓ E)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K) :
    {n : ℤ | ¬ Subsingleton (DerivedCategory.Ext E K n)}.Finite := by
  have : IsNoetherian X.left := isNoetherian_of_isProper_over_field X
  -- `E` is perfect, hence bounded above: [Stacks, Tag 0FXU]
  obtain ⟨bE, hbE⟩ :=
    (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect
      X.left E hE).1.2
  have hELE : E.IsLE bE := (DerivedCategory.isLE_iff E bE).mpr hbE
  -- `K` is bounded, and its cohomology sheaves are quasi-coherent
  obtain ⟨c, hc⟩ := hK.1.1
  obtain ⟨d, hd⟩ := hK.1.2
  have hKqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.left.Modules i).obj K).IsQuasicoherent := fun i =>
    have := hK.2 i
    isQuasicoherent_of_isCoherent _
  exact Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect
    X.left RΓ α E hE D bE hELE K hKqc c d ((DerivedCategory.isGE_iff K c).mpr hc)
    ((DerivedCategory.isLE_iff K d).mpr hd)

include α in
/-- **Stacks Project, Tag 0FYC.** Let `X` be a scheme proper over a field `k`, let `K` be an
object of `D^b_Coh(𝒪_X)` and let `E` be a perfect object of `D(𝒪_X)`. Then

`∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞`,

the dimensions being taken for the canonical `k`-structure induced by the structure morphism
`X ⟶ Spec k`, the sum being the cardinal sum over all of `ℤ` and `< ∞` being `< ℵ₀`.

The total sum is finite exactly when every summand is finite and only finitely many summands are
nonzero. The second condition is `finite_setOf_not_subsingleton_ext_of_isPerfect`, proved from
[Stacks, Tags 09M4 and 0FXU]. The first condition is the hypothesis `hExtFinite`: it is
[Stacks, Tag 0D0D], now a theorem of this library as
`Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_ext_of_proper` of
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessUnconditional.lean`, so this
hypothesis is dischargeable; see the module documentation. The hypothesis `D` is the dual perfect
complex of [Stacks, Tag 08DQ], carried as data because there is no absolute derived internal hom
on `D(𝒪_X)` in this library.

So what is proved is the tag's conclusion in full, the finiteness of the total sum, from the
finiteness of the individual summands. Both named hypotheses stand for cited results and neither
asserts the conclusion: `hExtFinite` is finiteness of each `Ext^i_X(E, K)` separately, which
leaves the number of nonzero degrees unbounded and so does not imply finiteness of the sum. -/
@[stacks 0FYC "granted hExtFinite (substantive degrees of 0D0D) and the cited dual complex 08DQ"]
theorem cardinalSum_rank_ext_lt_aleph0
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E)
    (D : Stacks.DerivedQCoh.DualPerfectComplexData X.left RΓ E)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K)
    (hExtFinite : ∀ n : ℤ, Module.Finite k (DerivedCategory.Ext E K n)) :
    Cardinal.sum (fun n : ℤ => Module.rank k (DerivedCategory.Ext E K n)) <
      Cardinal.aleph0 := by
  refine lt_aleph0_cardinalSum ?_ fun n => Module.rank_lt_aleph0_iff.2 (hExtFinite n)
  refine (finite_setOf_not_subsingleton_ext_of_isPerfect X RΓ α E K hE D hK).subset ?_
  intro n hn hsub
  exact hn (rank_zero_iff.2 hsub)

end Main

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
