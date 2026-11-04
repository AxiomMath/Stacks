module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.IsLimit
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeOpenModel

/-!
# The canonical factorization through a subalgebra, and open models above a prescribed one

Let `W ⟶ Spec R` be an open immersion with `W` of finite type over the integers.  Tag 01Z7 says
that the open immersion already descends to a finite-type `ℤ`-subalgebra `A ⊆ R`: the composite
`W ⟶ Spec R ⟶ Spec A` is again an open immersion, and the subalgebras with this property are
directed with canonical colimit `R`.  That is proved in
`StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeOpenModel`, whose
`Stacks.FiniteTypeOpenModel.IsOpenModel` is the predicate used throughout this file.

This file adds the two things the index of absolute Noetherian approximation needs on top of that
statement: the composite *under a name*, so that the open immersion an open model carries can be
referred to rather than only existentially asserted, and the strengthening of directedness in
which the model produced dominates a **prescribed** finitely generated subalgebra.

## Main definitions

* `AlgebraicGeometry.toSpecSubalgebra` is the canonical factorization `W ⟶ Spec R ⟶ Spec A` of a
  morphism into an affine scheme through a subalgebra of its ring.

## Main results

* `AlgebraicGeometry.isFiniteTypeOpenModel_iff` says that being an open model is a property of
  the subalgebra alone, the morphism the predicate asks for being
  `AlgebraicGeometry.toSpecSubalgebra` itself.
  `Stacks.FiniteTypeOpenModel.IsOpenModel.isOpenImmersion` and
  `Stacks.FiniteTypeOpenModel.IsOpenModel.finiteType` then read the open immersion `W ⟶ Spec A`
  and the finite type over the integers off an open model.
* `AlgebraicGeometry.exists_isFiniteTypeOpenModel_ge` strengthens the directedness of Tag 01Z7
  to: every finitely generated subalgebra is contained in an open model, so finitely many
  elements of `R` lie in a common one
  (`AlgebraicGeometry.exists_isFiniteTypeOpenModel_forall_mem`).

## Implementation notes

The factorization has its codomain written out, which is what makes the composite elaborate:
`CommRingCat.ofHom A.subtype` does not determine it.  Finite type over the integers is expressed,
following Mathlib's convention and the imported file, by `LocallyOfFiniteType` together with
`QuasiCompact` for the structural morphism to the terminal scheme.

Dominating a prescribed finitely generated subalgebra is not available from the conclusion of
Tag 01Z7 alone: one must enlarge the model the construction produces, and for that the chart data
it goes through has to be kept.  That is why the proof here reaches for
`Stacks.FiniteTypeOpenModel.exists_openModel_with_charts` and
`Stacks.FiniteTypeOpenModel.openModel_of_chart_data` rather than for
`Stacks.FiniteTypeOpenModel.exists_openModel`.

## References

* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/- The family of finite-type open models itself -- the predicate, the subtype of subalgebras
carrying it, the inclusion diagram and its cocone over `R`, and the existence, directedness and
colimit statements of Tag 01Z7 -- lives in
`StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeOpenModel`, which this file imports.  Four of its
declarations are used here under their bare names. -/
open Stacks.FiniteTypeOpenModel (IsOpenModel openModel_of_chart_data
  exists_openModel_with_charts chartNumerators_mono)

/-- The canonical factorization `W ⟶ Spec R ⟶ Spec A` of a morphism into an affine scheme
through a subalgebra of its ring.  The codomain is written out, which is what makes the
composite elaborate: `CommRingCat.ofHom A.subtype` does not determine it. -/
noncomputable def toSpecSubalgebra {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) (A : Subalgebra ℤ R) : W ⟶ Spec (.of A) :=
  f ≫ Spec.map (CommRingCat.ofHom A.subtype)

/-- Being an open model is a property of the subalgebra alone: the morphism `g` the definition
asks for is *determined* by the factorization equation, being
`AlgebraicGeometry.toSpecSubalgebra` itself. -/
theorem isFiniteTypeOpenModel_iff {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) (A : Subalgebra ℤ R) :
    IsOpenModel f A ↔ A.FG ∧ IsOpenImmersion (toSpecSubalgebra f A) := by
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, _, h.2, rfl⟩⟩
  obtain ⟨g, hg, hfac⟩ := h.2
  unfold toSpecSubalgebra
  rw [hfac]
  exact hg

/-- **The open immersion `W ⟶ Spec A` carried by an open model, under a name.** It is the
composite `W ⟶ Spec R ⟶ Spec A`, so it needs no choice: the existential in
`Stacks.FiniteTypeOpenModel.IsOpenModel` is pinned by its own factorization equation.

This is the morphism the Stacks proof of [Stacks, Tag 07RN] glues `V_i` to `Spec(A_{i, p})`
along. -/
theorem _root_.Stacks.FiniteTypeOpenModel.IsOpenModel.isOpenImmersion {R : Type u} [CommRing R]
    {W : Scheme.{u}} {f : W ⟶ Spec (.of R)} {A : Subalgebra ℤ R} (h : IsOpenModel f A) :
    IsOpenImmersion (toSpecSubalgebra f A) :=
  ((isFiniteTypeOpenModel_iff f A).mp h).2

/-- An open model is of finite type over the integers. -/
theorem _root_.Stacks.FiniteTypeOpenModel.IsOpenModel.finiteType {R : Type u} [CommRing R]
    {W : Scheme.{u}} {f : W ⟶ Spec (.of R)} {A : Subalgebra ℤ R} (h : IsOpenModel f A) :
    Algebra.FiniteType ℤ A :=
  A.fg_iff_finiteType.mp h.1

/-- **Every finitely generated subalgebra is contained in an open model.** This is the form of
directedness that the index set of Noetherian approximation needs and that neither
`Stacks.FiniteTypeOpenModel.openModel_directed` (which dominates two *models*) nor
`Stacks.FiniteTypeOpenModel.openModelCocone_isColimit` (which places one *element*) provides:
finitely many elements of `R` must lie in a common open model, and the subalgebra they generate
is an arbitrary finitely generated subalgebra. -/
theorem exists_isFiniteTypeOpenModel_ge {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R))
    [LocallyOfFiniteType (terminal.from W)]
    [QuasiCompact (terminal.from W)] [IsOpenImmersion f]
    (B : Subalgebra ℤ R) (hB : B.FG) :
    ∃ C : Subalgebra ℤ R, IsOpenModel f C ∧ B ≤ C := by
  obtain ⟨A₀, hA₀, n, r, hrU, hcover, hrA₀, hnums⟩ := exists_openModel_with_charts f
  have hA₀C : A₀ ≤ A₀ ⊔ B := le_sup_left
  exact ⟨A₀ ⊔ B, openModel_of_chart_data f (A₀ ⊔ B) (hA₀.1.sup hB) n r hrU hcover
    (fun i => hA₀C (hrA₀ i)) (chartNumerators_mono hA₀C hnums), le_sup_right⟩

/-- Finitely many elements of `R` lie in a common open model. -/
theorem exists_isFiniteTypeOpenModel_forall_mem {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R))
    [LocallyOfFiniteType (terminal.from W)]
    [QuasiCompact (terminal.from W)] [IsOpenImmersion f] (s : Finset R) :
    ∃ C : Subalgebra ℤ R, IsOpenModel f C ∧ ∀ x ∈ s, x ∈ C := by
  obtain ⟨C, hC, hle⟩ := exists_isFiniteTypeOpenModel_ge f (Algebra.adjoin ℤ (s : Set R))
    (Subalgebra.fg_adjoin_finset s)
  exact ⟨C, hC, fun x hx => hle (Algebra.subset_adjoin hx)⟩

end AlgebraicGeometry
