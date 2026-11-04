module

public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic

/-!
# Germs of a module on a scheme come from sections over a common affine open

Let `S` be a scheme, `G` an `𝒪_S`-module and `y` a point of `S`.  An element of the stalk `G_y`
is by construction a germ of a section over *some* open neighbourhood of `y`, and finitely many
elements are germs of sections over *one* such neighbourhood.  This file records the refinement
in which that common neighbourhood is **affine**.

The refinement is what the first half of the proof of [Stacks, Tag 0D2N] needs.  There one lifts
a section on the fibre `X_y` to a section over `f ⁻¹ᵁ U` for a small open `U ∋ y`, and the
intermediate object is a germ in the stalk `(f_* ℱ)_y` of a module on the base.  The passage from
that germ back to an actual section is only usable over an open on which the available
identifications hold, and all of them — flat base change to `Spec 𝒪_{S, y}` in the shape
`Stacks.AlgebraicGeometry.FlatBaseChange.exists_linearEquiv_pushforwardStalk_stalkBaseChange`
(`../FlatBaseChange/Stalk.lean`), and the affine-local description of quasi-coherent sections —
are stated at an **affine** open neighbourhood of `y`.  Moreover the source's argument chooses
`r + 1` sections at once, so one affine open has to serve a whole finite family of germs; that is
the second statement below, and it is the one actually consumed.

## Main results

* `Stacks.AmpleFibreNeighbourhood.exists_isAffineOpen_germ_eq`: a single element of
  `G.presheaf.stalk y` is the germ of a section over an affine open neighbourhood of `y`.
* `Stacks.AmpleFibreNeighbourhood.exists_isAffineOpen_germ_eq_family`: a family of elements of
  `G.presheaf.stalk y` indexed by an arbitrary `Finite` type consists of the germs of sections
  over **one** affine open neighbourhood of `y`.

The spelling of the germ is the one `../FlatBaseChange/Stalk.lean` uses, namely
`G.presheaf.germ U y hy a` for `a : Γ(G, U)`, so that the two compose without a transport.

## The route, and what was already in the repository

Neither statement is new mathematics, and neither half of the argument is re-proved here.

* The **common open** for a finite family already exists, in full generality: it is
  `AlgebraicGeometry.Scheme.Modules.finite_germ_lifts` in `../FiberRank/Basic.lean`, stated for
  an arbitrary presheaf with values in a concrete category whose forgetful functor preserves
  filtered colimits, an arbitrary topological space, an arbitrary `Finite` index type, and with
  the neighbourhood produced inside a prescribed open.  It is applied below at `V = ⊤`; its own
  proof intersects the finitely many neighbourhoods one germ at a time and restricts, so there is
  nothing to repeat.  (Several further copies of that statement exist in the repository —
  `SheafOfModules.exists_germ_eq_family` in `../ProjEulerSequence/ExteriorPowerMono.lean`,
  `exists_common_germ` in `../../Algebra/Category/ModuleCat/Sheaf/SymmetricPowerPresentation.lean`
  — and none of them is extended here either.)
* **Affineness** is the fact that the affine opens of a scheme form a topological basis,
  `AlgebraicGeometry.Scheme.isBasis_affineOpens`, read through
  `TopologicalSpace.Opens.isBasis_iff_nbhd`: inside any open neighbourhood of `y` there is an
  affine one.  Shrinking the common open to such an affine open does not change any germ, because
  a germ is unchanged by restriction of its section (`TopCat.Presheaf.germ_res_apply`).
* The single-germ statement is then the family statement at the one-point index type `Unit`,
  rather than a second invocation of the same two ingredients.  Mathlib's
  `TopCat.Presheaf.exists_mem_germ_eq_of_isBasis` would prove it directly in one line — that is
  how `../PushforwardRegularity/Basic.lean` and `../AnnihilatorQcoh/Stalk.lean` obtain it for the
  presheaves they are about — but deriving it from the family version keeps the two statements
  here provably the same assertion.

## No attribute

**No `@[stacks]` attribute is attached, and none is owed.** Both statements are general
sheaf-theoretic facts about germs on a scheme — the filtered-colimit description of a stalk,
together with the affine opens being a basis — and the Stacks Project states neither as a
numbered result; they are used without comment inside the proof of [Stacks, Tag 0D2N].  Attaching
a tag here would also misreport that tag's progress, since what this file contributes to it is
one step of bookkeeping rather than any part of its content.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AmpleFibreNeighbourhood

variable {S : Scheme.{u}} (G : S.Modules) (y : S)

/-! ### A finite family of germs over one affine open -/

/-- **Finitely many germs of a module on a scheme come from sections over one common affine
open.**  For `G` an `𝒪_S`-module, `y` a point of `S` and a family `γ : ι → G_y` of elements of
the stalk indexed by an arbitrary finite type, there is an affine open `U ∋ y` and a family of
sections `a : ι → Γ(G, U)` with `a i` having germ `γ i` at `y` for every `i`.

This is the form the proof of [Stacks, Tag 0D2N] consumes: that argument chooses `r + 1` sections
of a module on the base at once, and every identification it then applies to them — flat base
change to `Spec 𝒪_{S, y}`, and the affine-local description of quasi-coherent sections — is
stated at an affine open neighbourhood of `y`.

The index type is carried as `Type*`: no universe is pinned, because
`AlgebraicGeometry.Scheme.Modules.finite_germ_lifts` does not pin one either.

Two results of the library are composed, and neither is re-proved.
`AlgebraicGeometry.Scheme.Modules.finite_germ_lifts` (in `../FiberRank/Basic.lean`), applied
inside `V = ⊤`, produces a single open neighbourhood `W ∋ y` over which all the `γ i` are germs;
`AlgebraicGeometry.Scheme.isBasis_affineOpens` read through
`TopologicalSpace.Opens.isBasis_iff_nbhd` produces an affine open `U` with `y ∈ U ≤ W`.
Restricting each section from `W` to `U` leaves its germ at `y` alone, by
`TopCat.Presheaf.germ_res_apply`, which is the only computation in the proof. -/
theorem exists_isAffineOpen_germ_eq_family {ι : Type*} [Finite ι] (γ : ι → G.presheaf.stalk y) :
    ∃ (U : S.Opens) (_ : IsAffineOpen U) (hy : y ∈ U) (a : ι → Γ(G, U)),
      ∀ i, G.presheaf.germ U y hy (a i) = γ i := by
  obtain ⟨W, -, hyW, b, hb⟩ :=
    AlgebraicGeometry.Scheme.Modules.finite_germ_lifts G.presheaf y γ (V := ⊤) trivial
  obtain ⟨U, hU, hyU, hUW⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hyW
  refine ⟨U, hU, hyU, fun i => G.presheaf.map (homOfLE hUW).op (b i), fun i => ?_⟩
  exact (TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE hUW) y hyU (b i)).trans (hb i)

/-! ### One germ over an affine open -/

/-- **A germ of a module on a scheme comes from a section over an affine open.**  For `G` an
`𝒪_S`-module, `y` a point of `S` and `γ` an element of the stalk `G_y`, there is an affine open
`U ∋ y` and a section `a : Γ(G, U)` whose germ at `y` is `γ`.

This is `Stacks.AmpleFibreNeighbourhood.exists_isAffineOpen_germ_eq_family` at the one-point
index type `Unit`, stated separately because that is the shape in which a single germ — the one
produced by the lifting step of [Stacks, Tag 0D2N] before the finite family is assembled — is
used.  Mathlib's `TopCat.Presheaf.exists_mem_germ_eq_of_isBasis` against
`AlgebraicGeometry.Scheme.isBasis_affineOpens` proves it directly as well, as in
`../PushforwardRegularity/Basic.lean`; specialising the family version instead makes it visible
that the two statements here assert the same thing. -/
theorem exists_isAffineOpen_germ_eq (γ : G.presheaf.stalk y) :
    ∃ (U : S.Opens) (_ : IsAffineOpen U) (hy : y ∈ U) (a : Γ(G, U)),
      G.presheaf.germ U y hy a = γ := by
  obtain ⟨U, hU, hyU, a, ha⟩ :=
    exists_isAffineOpen_germ_eq_family G y (ι := Unit) fun _ => γ
  exact ⟨U, hU, hyU, a (), ha ()⟩

end Stacks.AmpleFibreNeighbourhood

end
