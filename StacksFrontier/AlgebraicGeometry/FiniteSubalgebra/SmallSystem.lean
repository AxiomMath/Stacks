module

public import StacksFrontier.AlgebraicGeometry.FiniteSubalgebra.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCompactColimit.AffineCover

/-!
# An integral algebra sheaf as a colimit of finite subalgebras indexed in `Type u`

Let `S` be a scheme and `A` an integral quasi-coherent sheaf of commutative `𝒪_S`-algebras.
Part (1) of [Stacks, Tag 0817] presents `A` as a directed colimit of finite quasi-coherent
subalgebras, and for `S` quasi-compact and quasi-separated that is
`Stacks.AlgebraicGeometry.FiniteSubalgebras.nonempty_isColimit_finiteSubalgebraCocone`, over the
category `FiniteSubalgebra A` of *all* of them.  That category is a full subcategory of
`CategoryTheory.Subobject A` and so lives in `Type (u + 1)`: a subobject of `A` is an isomorphism
class of monomorphisms into `A`, hence one universe above `A` itself.  The tag asks for an
indexing preorder in the *same* universe as the scheme, and this file produces one.

It does so without shrinking `FiniteSubalgebra A` -- which would need `Small.{u}` for a type of
subobjects -- by building a small directed system out of the sections of `A`:

* the generators are the pairs `(U, x)` with `U` an affine open of `S` and `x` a section of `A`
  over `U`.  They form a type in `Type u`, and each of them lies in a finite quasi-coherent
  subalgebra of `A` by
  `Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule.exists_finiteTypeSubalgebra_section`
  together with [Stacks, Tag 02JJ] in the form `isQuasicoherentAndFiniteType_le`;
* the index is the type `JoinExpr` of formal expressions in the generators, a base symbol and a
  binary join symbol, preordered by the order induced by evaluating the join symbol as a binary
  upper bound of finite quasi-coherent subalgebras.  Such upper bounds exist because those
  subalgebras are filtered (`isFiltered_finiteSubalgebra`), which is the other half of part (1)
  of the tag;
* that system still has colimit `A`, because a filtered cocone of subalgebras of `A` is
  colimiting as soon as every section of `A` over every affine open comes from a member of the
  diagram (`Stacks.QuasiCompactColimit.nonempty_isColimit_of_sections_of_mono`), and the
  one-generator expressions supply exactly that.

## Main results

* `exists_small_directed_of_upperBound`: a family of elements of a preorder, indexed by a type in
  `Type u` and equipped with a binary upper bound operation, is the monotone image of a nonempty
  directed preorder in `Type u`.
* `exists_small_isColimit_finite`: **part (1) of [Stacks, Tag 0817] with the index in `Type u`.**
* `exists_small_isColimit_finite_mono`: the same, recording in addition that every structure
  morphism of the cocone is a monomorphism, the members of the diagram being subobjects of `A`.

## Implementation notes

The index has to be a type of formal expressions, rather than the finite sets of generators,
because filteredness of `FiniteSubalgebra A` supplies an *arbitrary* upper bound of two finite
quasi-coherent subalgebras and not a least one.  `CategoryTheory.Subobject A` does carry a join
(`Stacks.RelativeSpec.exists_isLUB_subobject`), but whether the join of two finite quasi-coherent
subalgebras is again finite is not known, so `Finset.sup` of the chosen subalgebras is not
available; and an upper bound chosen separately for each finite set of generators need not be
monotone in that set, which is what a diagram indexed by `Finset` would require.  Evaluating a
formal join as an upper bound makes monotonicity hold by construction, and directedness is then
witnessed by the join expression itself.

`exists_small_directed_of_upperBound` is stated for an arbitrary preorder, so that the construction
is separated from the subalgebras it is applied to; it is applied with the preorder of finite
quasi-coherent subobjects of `A`, taken as a subtype of `CategoryTheory.Subobject A` rather than
as `FiniteSubalgebra A`, because the latter already carries a category structure and must not be
given a second one through `Preorder`.  The preorder on `JoinExpr` is a local instance inside the
proof: the conclusion quantifies over the preorder existentially, so no caller needs an instance.

No `@[stacks 0817]` attribute is attached.  The two assertions of part (1) of the tag are covered
by `isFiltered_finiteSubalgebra` and `nonempty_isColimit_finiteSubalgebraCocone`; the statements
below are a reindexing of the second, and both of them are inputs to it.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 02JJ](https://stacks.math.columbia.edu/tag/02JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec

universe u v

namespace Stacks.AlgebraicGeometry.FiniteSubalgebras

/-- Formal join expressions in a type `Ω` of generators: a base symbol, one symbol for each
generator, and a binary join symbol.  Interpreting the join symbol as a binary upper bound turns
this type into a nonempty directed preorder lying in the universe of `Ω`, whatever universe the
elements being bounded live in. -/
inductive JoinExpr (Ω : Type u) : Type u
  /-- The base symbol, which makes the type of expressions nonempty. -/
  | base : JoinExpr Ω
  /-- The symbol for a generator. -/
  | gen (ω : Ω) : JoinExpr Ω
  /-- The formal join of two expressions. -/
  | join (a b : JoinExpr Ω) : JoinExpr Ω

/-- Evaluation of a formal join expression in a type equipped with a base point `b`, an
interpretation `f` of the generators and a binary operation `op`. -/
def JoinExpr.eval {Ω : Type u} {α : Type v} (b : α) (f : Ω → α) (op : α → α → α) :
    JoinExpr Ω → α
  | .base => b
  | .gen ω => f ω
  | .join s t => op (s.eval b f op) (t.eval b f op)

/-- **A family in a preorder closed under a binary upper bound is the monotone image of a nonempty
directed preorder in the universe of the indexing type.**  Given `f : Ω → α` with `Ω : Type u` and
an operation `op` on `α` with `x ≤ op x y` and `y ≤ op x y`, there is a nonempty directed preorder
`I : Type u` and a monotone `e : I → α` whose image contains every `f ω`.

The index is `JoinExpr Ω` ordered by the order its evaluation induces, so that monotonicity holds
by construction and the formal join of two expressions witnesses directedness. -/
theorem exists_small_directed_of_upperBound {Ω : Type u} {α : Type v} [Preorder α] (b : α)
    (f : Ω → α) (op : α → α → α) (hl : ∀ x y : α, x ≤ op x y) (hr : ∀ x y : α, y ≤ op x y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·)) (e : I → α),
      Monotone e ∧ ∀ ω, ∃ i, e i = f ω :=
  let _ : Preorder (JoinExpr Ω) := Preorder.lift (JoinExpr.eval b f op)
  ⟨JoinExpr Ω, inferInstance, ⟨.base⟩, ⟨fun a c => ⟨a.join c, hl _ _, hr _ _⟩⟩,
    JoinExpr.eval b f op, fun _ _ h => h, fun ω => ⟨.gen ω, rfl⟩⟩

variable {S : Scheme.{u}}

/-- **Part (1) of [Stacks, Tag 0817] with the index in `Type u`, with the monomorphisms.**  An
integral quasi-coherent sheaf of commutative `𝒪_S`-algebras on a quasi-compact and
quasi-separated scheme is the colimit of a directed system, indexed by a nonempty directed
preorder in `Type u`, of finite quasi-coherent subalgebras, each included in `A` by a
monomorphism.

The members of the diagram are the subalgebras attached to the formal join expressions in the
sections of `A` over the affine opens of `S`; see the module documentation. -/
theorem exists_small_isColimit_finite_mono [CompactSpace S] [QuasiSeparatedSpace S]
    (A : AlgebraSheaf S) (hAqc : AlgebraSheaf.IsQuasicoherent A) (hAint : A.IsIntegral) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf S) (t : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A t)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧ Mono (t.app i) := by
  classical
  have hfilt := isFiltered_finiteSubalgebra A hAqc hAint
  obtain ⟨B₀⟩ := IsFiltered.nonempty (C := FiniteSubalgebra A)
  choose gen sec hsec using fun ω : Σ U : S.affineOpens, A.right.obj.obj (op U.1) =>
    (exists_finiteSubalgebra_section_iff hAint ω.2).mpr
      (SubalgebraGeneratedByModule.exists_finiteTypeSubalgebra_section A hAqc ω.1.1 ω.1.2 ω.2)
  let toFin (x : {B : Subobject A // isQuasicoherentAndFinite A B}) : FiniteSubalgebra A :=
    ⟨x.1, x.2⟩
  let up (x y : {B : Subobject A // isQuasicoherentAndFinite A B}) : FiniteSubalgebra A :=
    IsFiltered.max (toFin x) (toFin y)
  obtain ⟨I, _, _, _, e, hmono, hgen⟩ :=
    exists_small_directed_of_upperBound (Ω := Σ U : S.affineOpens, A.right.obj.obj (op U.1))
      (α := {B : Subobject A // isQuasicoherentAndFinite A B})
      ⟨B₀.obj, B₀.property⟩ (fun ω => ⟨(gen ω).obj, (gen ω).property⟩)
      (fun x y => ⟨(up x y).obj, (up x y).property⟩)
      (fun x y => Subtype.coe_le_coe.mp (leOfHom (IsFiltered.leftToMax (toFin x) (toFin y)).hom))
      (fun x y => Subtype.coe_le_coe.mp (leOfHom (IsFiltered.rightToMax (toFin x) (toFin y)).hom))
  have hsub : Monotone fun i => (e i).1 := fun _ _ h => Subtype.coe_le_coe.mpr (hmono h)
  have harrow (i : I) : Mono ((e i).1.arrow) := inferInstance
  obtain ⟨hcolim⟩ := Stacks.QuasiCompactColimit.nonempty_isColimit_of_sections_of_mono
    ((finiteSubalgebraCocone A).whisker
      ((isQuasicoherentAndFinite A).lift hsub.functor fun i => (e i).2))
    harrow
    (fun U hU x => by
      obtain ⟨i, hi⟩ := hgen ⟨⟨U, hU⟩, x⟩
      have h1 : (e i).1 = (gen ⟨⟨U, hU⟩, x⟩).obj := congrArg Subtype.val hi
      refine ⟨i, ?_⟩
      show ∃ y : ((e i).1 : AlgebraSheaf S).right.obj.obj (op U),
        (e i).1.arrow.right.hom.app (op U) y = x
      rw [h1]
      exact ⟨sec ⟨⟨U, hU⟩, x⟩, hsec ⟨⟨U, hU⟩, x⟩⟩)
  exact ⟨I, inferInstance, inferInstance, inferInstance, _, _, hcolim,
    fun i => ⟨(e i).2.1, (e i).2.2, harrow i⟩⟩

/-- **[Stacks, Tag 0817] part (1) with the index in `Type u`.** An integral quasi-coherent sheaf of
commutative algebras on a quasi-compact quasi-separated scheme is the colimit of a directed system,
indexed by a nonempty directed preorder in `Type u`, of finite quasi-coherent subalgebras.

This is `exists_small_isColimit_finite_mono` with the monomorphism of each structure morphism
forgotten. -/
theorem exists_small_isColimit_finite [CompactSpace S] [QuasiSeparatedSpace S]
    (A : AlgebraSheaf S) (hAqc : AlgebraSheaf.IsQuasicoherent A) (hAint : A.IsIntegral) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf S) (t : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A t)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite := by
  obtain ⟨I, _, _, _, F, t, hcolim, h⟩ := exists_small_isColimit_finite_mono A hAqc hAint
  exact ⟨I, inferInstance, inferInstance, inferInstance, F, t, hcolim,
    fun i => ⟨(h i).1, (h i).2.1⟩⟩

end Stacks.AlgebraicGeometry.FiniteSubalgebras

end
