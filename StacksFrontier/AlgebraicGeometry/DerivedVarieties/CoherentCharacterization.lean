module

public import StacksFrontier.AlgebraicGeometry.Perfect.BeilinsonCoherentCharacterization
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TotalExtDimensionOverAField
import StacksCore.Tactic.StacksAttribute

/-!
# Characterizing coherent modules on a scheme proper over a field

Let `X` be a scheme proper over a field `k` and let `K` be an object of `D_QCoh(𝒪_X)`.
[Stacks, Tag 0FYD] asserts that the following are *equivalent*:

1. `K` is in `D^b_Coh(𝒪_X)`, and
2. `∑_{i ∈ ℤ} dim_k Ext^i_X(E, K)` is finite for every perfect object `E` of `D(𝒪_X)`.

**What this file delivers is ONE DIRECTION of that equivalence, (1) ⇒ (2), and it is therefore
WEAKER THAN THE TAG.** The converse (2) ⇒ (1) is *not* proved here, and it is not proved anywhere
in this library; see "Why (2) ⇒ (1) is unreachable" below for exactly which four results are
missing. A reader must not mistake what is proved here for the equivalence: nothing below lets
one conclude that an object with finite total `Ext` from every perfect object is bounded with
coherent cohomology.

The sum in (2) is the cardinal sum `Cardinal.sum` of the `k`-ranks of the `Ext` modules over the
whole of `ℤ`, and "finite" is `< ℵ₀`; so (2) is the finiteness of the *total* dimension, not the
weaker statement that each `Ext^i_X(E, K)` is finite-dimensional.

## Main results

All four live in the namespace
`Stacks.AlgebraicGeometry.DerivedVarieties.CoherentCharacterization`.

* `lt_aleph0_cardinalSum_iff`: a cardinal sum is finite exactly when every summand is finite and
  only finitely many summands are nonzero.
* `cardinalSum_rank_ext_lt_aleph0_iff_hasFiniteTotalExt`: finiteness of
  `∑_{i ∈ ℤ} dim_k Ext^i_X(E, K)` is the library's `HasFiniteTotalExt`, that is, condition (3) of
  [Stacks, Tag 0FYB] read at a single `E`.
* `cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded`: **[Stacks, Tag 0FYD], (1) ⇒ (2)**
  — one direction only, for `X` proper over `k`.
* `hasFiniteTotalExt_of_derivedCategoryBBounded`: the same implication in the
  `HasFiniteTotalExt` spelling.

## Implementation notes

**The two hypotheses that (1) ⇒ (2) carries are inherited, not introduced here.** They come from
the attribute of this library's [Stacks, Tag 0FYC], namely
`Stacks.AlgebraicGeometry.ProperSupportCoherent.cardinalSum_rank_ext_lt_aleph0`, which is tagged
`granted hExtFinite (substantive degrees of 0D0D) and the cited dual complex 08DQ`:

* `hExtFinite`: each `Ext^i_X(E, K)` is a finite `k`-module. This is [Stacks, Tag 0D0D], which
  the library now carries in full, as
  `Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_ext_of_proper` of
  `StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessUnconditional.lean`; the
  hypothesis is inherited from this library's [Stacks, Tag 0FYC] and is dischargeable there.
* `D`: the dual perfect complex `E^∨` of [Stacks, Tag 08DQ], carried as the data
  `Stacks.DerivedQCoh.DualPerfectComplexData` because there is no absolute derived internal hom
  on `D(𝒪_X)` in this library.

Both are hypotheses *on a perfect object `E`*, so they are quantified over `E` here, 0FYD's
condition (2) being a statement about every perfect `E` whereas [Stacks, Tag 0FYC] is a statement
about one. Neither hypothesis asserts (2): `hExtFinite` is finiteness of the individual summands,
which leaves the number of nonzero degrees unbounded, and `D` is a complex together with three of
its properties.

**Why (2) ⇒ (1) is unreachable.** The source gives two routes and this library carries, for each
of them, only the half that 0FYD does not use.

* The proper-case route is through More on Morphisms [Stacks, Tag 0GET], whose conclusion is that
  `K` is `Spec k`-perfect; Derived Categories of Schemes [Stacks, Tag 0DI1] would then identify
  that with `D^b_Coh(𝒪_X)`, and the library does carry both of 0DI1's equivalences,
  `AlgebraicGeometry.isPerfectRelativeTo_iff_isBounded_and_isPseudoCoherent` and
  `AlgebraicGeometry.isBounded_and_isPseudoCoherent_iff_boundedCoherent`. But the library's 0GET,
  `AlgebraicGeometry.eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect`, proves only
  the *vanishing* that the tag's hypothesis produces — that `Ext^i_X(G, K)` and
  `Hom(G⟦-i⟧, K)` vanish for `i ≪ 0` — and explicitly not relative perfectness, which needs
  three results that are absent: [Stacks, Tag 0GES], the implication (2) ⇒ (1) of
  [Stacks, Tag 0GEH] (the library carries only (1) ⇒ (2)), and condition (1) of
  [Stacks, Tag 0GEQ] (the library carries only the block of equivalences between conditions
  (2), (3), (5) and (6)).
* The projective-case route assumes `X` projective over `k`, pushes forward along a closed
  immersion `i : X → ℙⁿ_k` and concludes by [Stacks, Tag 0FYB]. The step it concludes by is
  0FYB's (4) ⇒ (1), and the library's 0FYB —
  `hasFiniteTotalTwistCohomology_of_hasFiniteTotalTensorCohomology` of
  `StacksFrontier/AlgebraicGeometry/Perfect/BeilinsonCoherentCharacterization.lean` —
  carries only (2) ⇒ (4). Its (4) ⇒ (1) is blocked on the library's Beilinson equivalence being
  stated over the endomorphism differential graded algebra rather than over the upper triangular
  algebra of [Stacks, Tag 0CS9], which puts [Stacks, Tag 0FYA] out of reach of `K`, and on
  `AlgebraicGeometry.IsRegular (ℙⁿ_k)`, which nothing in this library proves.

So assuming `X` projective buys nothing: both routes are blocked, and the implication is stated
here in the proper generality rather than hedged with a projectivity hypothesis that would not
help.

**Spellings.** All of them are the library's and none is introduced here. `D^b_Coh(𝒪_X)` is
`DerivedCategoryB.derivedCategoryBBounded` at the coherence predicate; `Ext^i_X(E, K)` is
`DerivedCategory.Ext`, that is `Hom_{D(𝒪_X)}(E, K⟦i⟧)`; perfectness is
`Stacks.Cohomology.PerfectComplexes.IsPerfect`; "proper over a field" is `IsProper` on the
structure morphism of an object of `Over (Spec k)`; the `k`-module structure in which `dim_k` is
taken is `AlgebraicGeometry.modulesLinear`, induced by that structure morphism; and the
conjunction form of the finiteness condition is
`Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.HasFiniteTotalExt`. `RΓ(X, -)` enters
as a functor together with the structure morphism carrying the right-derived-functor instance,
exactly as in [Stacks, Tag 0FYC]; that is a device for model independence and not a hypothesis on
the geometry. The derived category is the standard model, at the priority used by
[Stacks, Tag 0FYC], since that is the model its input [Stacks, Tag 09M4] is baked at.

## References

* [Stacks Project, Tag 0FYD](https://stacks.math.columbia.edu/tag/0FYD)
* [Stacks Project, Tag 0FYC](https://stacks.math.columbia.edu/tag/0FYC)
* [Stacks Project, Tag 0FYB](https://stacks.math.columbia.edu/tag/0FYB)
* [Stacks Project, Tag 0GET](https://stacks.math.columbia.edu/tag/0GET)
* [Stacks Project, Tag 0DI1](https://stacks.math.columbia.edu/tag/0DI1)
* [Stacks Project, Tag 0D0D](https://stacks.math.columbia.edu/tag/0D0D)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Cohomology (sectionsFunctor)

universe v u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.CoherentCharacterization

attribute [local instance 100000] HasDerivedCategory.standard

/-- The canonical `k`-linear structure on `𝒪_X`-modules for a scheme `X` over `Spec k`, induced
by the structure morphism. It is `AlgebraicGeometry.modulesLinear`, the structure in which the
dimensions below are taken, and it is installed locally because it depends on that morphism. -/
local instance linearModulesOverTheField {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) : Linear k X.left.Modules :=
  AlgebraicGeometry.modulesLinear k X

/-! ### Finiteness of a cardinal sum -/

/-- **A cardinal sum is finite exactly when every summand is finite and only finitely many
summands are nonzero.**

The implication from right to left is
`Stacks.AlgebraicGeometry.ProperSupportCoherent.lt_aleph0_cardinalSum`. For the other, each
summand is bounded by the sum, and picking an element of each nonzero summand embeds the support
into the disjoint union, which is finite. -/
theorem lt_aleph0_cardinalSum_iff {ι : Type u} {f : ι → Cardinal.{max u v}} :
    Cardinal.sum f < Cardinal.aleph0 ↔
      ((∀ i, f i < Cardinal.aleph0) ∧ {i | f i ≠ 0}.Finite) := by
  refine ⟨fun h => ⟨fun i => lt_of_le_of_lt (Cardinal.le_sum f i) h, ?_⟩,
    fun h => ProperSupportCoherent.lt_aleph0_cardinalSum h.2 h.1⟩
  have hmk : Cardinal.sum f = Cardinal.mk (Σ i, (f i).out) := rfl
  rw [hmk, Cardinal.lt_aleph0_iff_finite] at h
  have hne : ∀ i, f i ≠ 0 → Nonempty (f i).out := by
    intro i hi
    rw [← not_isEmpty_iff, ← Cardinal.mk_eq_zero_iff, Cardinal.mk_out]
    exact hi
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective
    (fun i : ↑{i : ι | f i ≠ 0} => (⟨i.1, (hne i.1 i.2).some⟩ : Σ i, (f i).out)) ?_
  intro a b hab
  exact Subtype.ext (congrArg Sigma.fst hab)

/-! ### The two spellings of condition (2) -/

section Conditions

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

/-- **Finiteness of `∑_{i ∈ ℤ} dim_k Ext^i_X(E, K)` is the library's `HasFiniteTotalExt`.** The
sum of cardinals is `< ℵ₀` exactly when every `Ext^i_X(E, K)` is a finite `k`-module and only
finitely many of them are nonzero, which is
`Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.HasFiniteTotalExt`, that is,
condition (3) of [Stacks, Tag 0FYB] read at a single perfect object.

A finite `k`-module is one of finite rank, and a module has rank zero exactly when it is
subsingleton, so the two conjuncts match the two conjuncts of `lt_aleph0_cardinalSum_iff`. -/
theorem cardinalSum_rank_ext_lt_aleph0_iff_hasFiniteTotalExt
    (E K : DerivedCategory X.left.Modules) :
    Cardinal.sum (fun n : ℤ => Module.rank k (DerivedCategory.Ext E K n)) < Cardinal.aleph0 ↔
      BeilinsonCoherentCharacterization.HasFiniteTotalExt k X E K := by
  rw [lt_aleph0_cardinalSum_iff]
  simp only [Module.rank_lt_aleph0_iff, ne_eq, rank_zero_iff]
  rfl

end Conditions

/-! ### Stacks 0FYD, the implication (1) ⇒ (2) -/

section Main

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
  (RΓ : DerivedCategory X.left.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X.left, ⊤)))
  (α : (sectionsFunctor X.left ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.left.Modules (ComplexShape.up ℤ))]
  (K : DerivedCategory X.left.Modules)

include α in
/-- **Stacks Project, Tag 0FYD, the implication (1) ⇒ (2).** Let `X` be a scheme proper over a
field `k` and let `K` be an object of `D^b_Coh(𝒪_X)`. Then

`∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞`

for every perfect object `E` of `D(𝒪_X)`, the dimensions being taken for the canonical
`k`-structure induced by the structure morphism `X ⟶ Spec k`, the sum being the cardinal sum over
all of `ℤ` and `< ∞` being `< ℵ₀`.

**This is ONE DIRECTION of the equivalence of [Stacks, Tag 0FYD] and is therefore WEAKER THAN THE
TAG.** The converse, (2) ⇒ (1), is not proved here and is not available in this library; the
module docstring says which four results are missing, and no statement in this file permits the
inference from finite total `Ext` to bounded coherent cohomology.

The source proves this direction by [Stacks, Tag 0FYC], which is exactly what is applied, once
for each perfect `E`. Its two hypotheses are inherited from it and are quantified over `E` here,
0FYD's condition (2) being a statement about every perfect object:

* `hExtFinite`, finite-dimensionality over `k` of each `Ext^i_X(E, K)`, is [Stacks, Tag 0D0D], of
  which this library carries only the degrees in which the `Ext` modules vanish; the substantive
  degrees need the clause of [Stacks, Tag 0D0C] that is absent. It does not assert the
  conclusion: finiteness of each summand leaves the number of nonzero degrees unbounded.
* `D`, the dual perfect complex of [Stacks, Tag 08DQ], travels as data because there is no
  absolute derived internal hom on `D(𝒪_X)` here. -/
@[stacks 0FYD "(1) ⇒ (2) ONLY, for X proper over a field; the converse (2) ⇒ (1) is NOT proved. \
Granted 0FYC's own hExtFinite (0D0D) and DualPerfectComplexData (08DQ), quantified over E."]
theorem cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K)
    (D : ∀ E : DerivedCategory X.left.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E →
        Stacks.DerivedQCoh.DualPerfectComplexData X.left RΓ E)
    (hExtFinite : ∀ E : DerivedCategory X.left.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E →
        ∀ n : ℤ, Module.Finite k (DerivedCategory.Ext E K n))
    (E : DerivedCategory X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E) :
    Cardinal.sum (fun n : ℤ => Module.rank k (DerivedCategory.Ext E K n)) < Cardinal.aleph0 :=
  ProperSupportCoherent.cardinalSum_rank_ext_lt_aleph0 X RΓ α E K hE (D E hE) hK
    (hExtFinite E hE)

include α in
/-- **Stacks Project, Tag 0FYD, the implication (1) ⇒ (2), in the `HasFiniteTotalExt`
spelling.** Let `X` be a scheme proper over a field `k` and let `K` be an object of
`D^b_Coh(𝒪_X)`. Then `∑_{i ∈ ℤ} dim_k Ext^i_X(E, K)` is finite for every perfect object `E` of
`D(𝒪_X)`, in the conjunction form
`Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.HasFiniteTotalExt` — condition (3) of
[Stacks, Tag 0FYB] — which `cardinalSum_rank_ext_lt_aleph0_iff_hasFiniteTotalExt` shows is the
same condition as the finiteness of the cardinal sum.

**Like `cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded`, this is ONE DIRECTION of the
equivalence of [Stacks, Tag 0FYD] and is therefore WEAKER THAN THE TAG**; the hypotheses
`hExtFinite` and `D` are inherited from [Stacks, Tag 0FYC], as described there. -/
@[stacks 0FYD "(1) ⇒ (2) ONLY, as HasFiniteTotalExt; the converse (2) ⇒ (1) is NOT proved. \
Granted 0FYC's own hExtFinite (0D0D) and DualPerfectComplexData (08DQ), quantified over E."]
theorem hasFiniteTotalExt_of_derivedCategoryBBounded
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K)
    (D : ∀ E : DerivedCategory X.left.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E →
        Stacks.DerivedQCoh.DualPerfectComplexData X.left RΓ E)
    (hExtFinite : ∀ E : DerivedCategory X.left.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E →
        ∀ n : ℤ, Module.Finite k (DerivedCategory.Ext E K n))
    (E : DerivedCategory X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E) :
    BeilinsonCoherentCharacterization.HasFiniteTotalExt k X E K :=
  (cardinalSum_rank_ext_lt_aleph0_iff_hasFiniteTotalExt X E K).1
    (cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded X RΓ α K hK D hExtFinite E hE)

end Main

end Stacks.AlgebraicGeometry.DerivedVarieties.CoherentCharacterization

end
