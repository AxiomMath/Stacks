module

public import StacksFrontier.AlgebraicGeometry.AffineReduction.Eventual
public import StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.AffineAtLateStage.Basic

/-!
# The residue of Tag 09ZN at a free index universe, as a single proposition

[Stacks, Tag 09ZN] is proved in this repository with the index type and the schemes in **one**
universe (`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral`), and at two
independent universes under a cofinality hypothesis the source does not state
(`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall`, which
`CategoryTheory.InitiallySmall.{u} Iᵒᵖ` is; `Small.{u} I` discharges it).  What stands between
those two is [Stacks, Tag 09ZM]: `StacksDraft/AlgebraicGeometry/F3/Tag09ZNAffineReduction/`
`StacksFrontier/AlgebraicGeometry/AffineReduction/Eventual.lean` proves Tag 09ZN at two independent universes with no smallness of any kind, given
Tag 09ZM's conclusion for the system at hand.

This file turns that reduction into a statement about *statements*.  Each of the two source
statements is written out as a closed proposition with its universes named and independent —
`Statement09ZN.{w, u}` and `Statement09ZM.{w, u}`, where `w` is the index universe and `u` the
scheme universe — and the reduction becomes one implication between them.  The point of doing so
is that the residue of Tag 09ZN then has a *name*: it is `Statement09ZM.{w, u}` for `w ≠ u`, and
nothing else.

## Main results

* `Statement09ZN`: the statement of Tag 09ZN verbatim — the same binders in the same order, the two
  universes independent, no smallness hypothesis — as a proposition in two universe parameters.
* `Statement09ZM`: the statement of Tag 09ZM verbatim, likewise.
* `statement09ZN_of_statement09ZM`: **`Statement09ZM.{w, u} → Statement09ZN.{w, u}`.**  Tag 09ZM
  implies Tag 09ZN at any pair of universes whatsoever.
* `statement09ZN_of_statement09ZM_succ`: the same implication instantiated at `w := u + 1`, so
  that the independence of the two universes is machine-checked rather than asserted.
* `statement09ZN_self`, `statement09ZM_self`: both propositions hold when the index universe *is*
  the scheme universe.  Together with the implication these locate the open problem exactly: the
  residue of Tag 09ZN is `Statement09ZM.{w, u}`, which is known for `w = u` and open otherwise.

## Why no Stacks attribute is attached here

Nothing in this file carries `@[stacks 09ZN]`.  `Statement09ZN.{w, u}` is not proved here for
independent `w` and `u` — it is proved *from* `Statement09ZM.{w, u}`, which is the conclusion of
a different tag and is open at a free index universe, and a smallness hypothesis spelled
`CategoryTheory.InitiallySmall.{u} Iᵒᵖ` is no less a hypothesis for being spelled that way.

Tag 09ZN itself is carried elsewhere, on the form whose index type lies in the universe of the
schemes: `AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral`
in `StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic`.  The two free universes of
`Statement09ZN` come from the formal statement spelling its binders `Type*` and `Scheme`, which Lean
auto-bound independently; the source quantifies no universes at all, so coupling them is a
formalisation convention rather than a weakening.  It is the convention Mathlib uses for this
same family: `Mathlib.AlgebraicGeometry.AffineTransitionLimit` carries Tags 01Z2, 01Z3, 01Z4,
01Z5, 01Z6 and 01ZC on `{I : Type u} [Category.{u} I]` with `D : I ⥤ Scheme.{u}`, and Tag 01Z6
is what the proof of 09ZN invokes.  The free-index-universe statement remains the genuinely open
question this file isolates.

## Implementation notes

`Statement09ZN` and `Statement09ZM` reproduce the binder lists of the formal statements of the two tags exactly,
instance-implicit binders included, so that each is the tag's statement and not a paraphrase of it.  Consequently
they are applied through `@`: the instance arguments of a proposition are not in the local
instance cache of whoever consumes it.

The index category of Tag 09ZN is `Iᵒᵖ` for `I` a nonempty directed preorder, and Tag 09ZM's is
an arbitrary cofiltered category whose hom types lie in the universe of its objects.  The former
is an instance of the latter: `CategoryTheory.Preorder.smallCategory` puts the homs of `I : Type w`
in `Type w`, and `CategoryTheory.isCofiltered_op_of_isFiltered` together with
`CategoryTheory.isFiltered_of_directed_le_nonempty` makes `Iᵒᵖ` cofiltered.  So the implication
needs no reindexing and no smallness; it is Tag 09ZM read at Tag 09ZN's index category.

## References

* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
* [The Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
* [The Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
-/

@[expose] public section

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.Card09ZNResidue

/-- **The statement of Tag 09ZN, verbatim, as a proposition in two independent universes.**

`w` is the universe of the index type and `u` that of the schemes; neither constrains the other.
The binder list is the tag's formal statement's, in its order, with its `{I : Type*}` and bare
`Scheme` replaced by `{I : Type w}` and `Scheme.{u}` — which is only to give the two universes
names, since those are precisely the two parameters that statement elaborates with. -/
def Statement09ZN : Prop :=
  ∀ {I : Type w} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (F : Iᵒᵖ ⥤ Scheme.{u}) (p : F ⟶ (Functor.const Iᵒᵖ).obj S)
    (c : Cone F) (_hc : IsLimit c) (f : c.pt ⟶ S)
    (_hf : ∀ i, f = c.π.app (op i) ≫ p.app (op i))
    [IsIntegralHom f]
    [∀ i, CompactSpace (F.obj (op i))]
    [∀ i, QuasiSeparatedSpace (F.obj (op i))]
    (_haffine : ∀ {i j : I} (h : i ≤ j), IsAffineHom (F.map (homOfLE h).op))
    (_hfinite : ∀ {i j : I} (h : i ≤ j), IsFinite (F.map (homOfLE h).op))
    [∀ i, LocallyOfFiniteType (p.app (op i))],
    ∀ᶠ i in Filter.atTop, IsFinite (p.app (op i))

/-- **The statement of Tag 09ZM, verbatim, as a proposition in two independent universes.**

`w` is the universe of the index category — objects and homs alike, as the statement has it — and `u`
that of the schemes. -/
def Statement09ZM : Prop :=
  ∀ {I : Type w} [Category.{w} I] [IsCofiltered I]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ S)
    (_hf : c.π ≫ t = (Functor.const I).map f)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)] [IsAffineHom f],
    ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsAffineHom (t.app j)

/-- **[Stacks, Tag 09ZM] implies [Stacks, Tag 09ZN], at an arbitrary pair of universes.**

The statement of Tag 09ZM at index universe `w` and scheme universe `u` implies that of Tag 09ZN
at the same two universes.  No smallness, cofinality or reindexing hypothesis appears on either
side, and the two universes are unrelated throughout.

The index category of Tag 09ZN, the opposite of a nonempty directed preorder in `Type w`, is a
cofiltered category with objects and homs in `Type w`, so Tag 09ZM applies to it directly; the
transition morphisms are affine because they are finite, `f` is affine because it is integral, and
Tag 09ZM's conclusion at that index category is exactly the hypothesis of
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_card09ZM`. -/
theorem statement09ZN_of_statement09ZM (h : Statement09ZM.{w, u}) : Statement09ZN.{w, u} := by
  intro I _ _ _ S _ _ F q c hc f hf _ _ _ haffine hfinite _
  refine eventually_isFinite_of_isLimit_of_isIntegral_of_card09ZM F q c hc f hf
    (fun hle ↦ haffine hle) (fun hle ↦ hfinite hle) fun hfaff ↦ ?_
  have hcpt : ∀ k : Iᵒᵖ, CompactSpace (F.obj k) := fun k ↦
    inferInstanceAs (CompactSpace ↥(F.obj (op k.unop)))
  have hqs : ∀ k : Iᵒᵖ, QuasiSeparatedSpace (F.obj k) := fun k ↦
    inferInstanceAs (QuasiSeparatedSpace ↥(F.obj (op k.unop)))
  have haff : ∀ {k l : Iᵒᵖ} (g : k ⟶ l), IsAffineHom (F.map g) := by
    intro k l g
    rw [show g = (homOfLE (leOfHom g.unop)).op from rfl]
    exact haffine _
  have hnat : c.π ≫ q = (Functor.const Iᵒᵖ).map f := by
    refine NatTrans.ext (funext fun k ↦ ?_)
    obtain ⟨i⟩ := k
    simpa using (hf i).symm
  exact @h Iᵒᵖ _ _ S _ _ F q c hc f hnat hcpt hqs haff hfaff

/-- The two universes of `statement09ZN_of_statement09ZM` are genuinely independent: here is the
implication with the index universe one level above the scheme universe. -/
theorem statement09ZN_of_statement09ZM_succ (h : Statement09ZM.{u + 1, u}) :
    Statement09ZN.{u + 1, u} :=
  statement09ZN_of_statement09ZM h

/-- **Tag 09ZN holds when the index universe is the scheme universe.**  This is
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral` read as a statement about
statements, and it is the only pair of universes at which `Statement09ZN` is known. -/
theorem statement09ZN_self : Statement09ZN.{u, u} := by
  intro I _ _ _ S _ _ F q c hc f hf _ _ _ haffine hfinite _
  exact eventually_isFinite_of_isLimit_of_isIntegral F q c hc f hf
    (fun hle ↦ haffine hle) fun hle ↦ hfinite hle

/-- **Tag 09ZM holds when the index universe is the scheme universe.**  This is
`Stacks.AlgebraicGeometry.AffineAtLateStage.eventually_isAffineHom_of_isLimit` read as a statement
about statements.  With `statement09ZN_of_statement09ZM` it shows that the implication is the
whole of the gap: `Statement09ZN.{w, u}` is open for `w ≠ u` exactly because
`Statement09ZM.{w, u}` is. -/
theorem statement09ZM_self : Statement09ZM.{u, u} := by
  intro I _ _ S _ _ D t c hc f hf _ _ _ _
  exact Stacks.AlgebraicGeometry.AffineAtLateStage.eventually_isAffineHom_of_isLimit D c t hc f hf

end Stacks.Card09ZNResidue

end
