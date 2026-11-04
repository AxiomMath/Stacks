module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafCoproduct

/-!
# A coproduct decomposition of an algebraic space, read in the lattice of subfunctors

A decomposition of an algebraic space `P` into two open-and-closed pieces is, concretely, an
isomorphism `P ≅ W ⨿ V` of sheaves on the big fppf site over `S`. Statements about such a
decomposition are usually phrased instead in the complete lattice of subfunctors of `P`: the
pieces are the ranges of the two legs, they *locally* cover `P`, and they are *locally*
disjoint. Both qualifications are unavoidable — the ranges are subpresheaves, not subsheaves,
so a section over a disconnected test object may fail to lie in either range before
refinement, and an object of the site with no points carries a section of every subfunctor,
so the intersection of the ranges is the sheafification of `⊥` rather than `⊥`.

This file supplies those two identities for a coproduct cocone of sheaves on the big fppf
site over `S`. They are the form in which Stacks 082H and Stacks 0ADU state the conclusion
`U ×_Y X = W ⨿ V`, and the form in which Stacks 02WO and Stacks 0F15 state disjointness of a
coproduct of algebraic spaces.

## Main results

* `AlgebraicGeometry.Sheaf.range_inf_range_eq_sheafify_bot`: two legs of a coproduct cocone of
  sheaves on the big fppf site over `S` with distinct indices have intersection of ranges the
  sheafification of the bottom subfunctor.
* `AlgebraicGeometry.Sheaf.sheafify_eq_top_of_range_le_of_isColimit_cofan`: a subfunctor of the
  vertex containing the range of every leg sheafifies to the whole vertex.
* `AlgebraicGeometry.Sheaf.sheafify_sup_range_eq_top_of_isColimit_cofan`: the two-index case, in
  which the ranges of the two legs have join sheafifying to the whole vertex.

## Implementation notes

The join identity is a restatement of
`CategoryTheory.Sheaf.sheafify_iSup_range_eq_top`, which is pure topos theory. The meet
identity is where the site enters, in both directions:

* a section lying in two ranges with distinct indices forces the test object to have no points
  (`AlgebraicGeometry.Sheaf.isEmpty_toScheme_of_eq_of_ne`, the disjointness half of Stacks
  02WO), and an object of the big fppf site with no points is covered by the empty sieve
  (`AlgebraicGeometry.BigFppfOver.bot_mem_topology`), which is exactly membership in the
  sheafification of `⊥`;
* conversely, over an object covered by the empty sieve every sheaf has exactly one section
  (`CategoryTheory.Presieve.IsSheaf.nonempty_obj_of_bot_mem` and
  `CategoryTheory.Presieve.IsSheaf.subsingleton_obj_of_bot_mem`), so the unique section of the
  vertex is in the range of every leg.

Nothing here carries a Stacks tag: Stacks 082H, 0ADU and 02WO each assert the existence of
such a decomposition, which is not proved, and these are the lattice identities its
conclusion is phrased with.

## References

* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A section of a presheaf lies in the sheafification of the bottom subfunctor exactly when
the empty sieve covers the object it lives on: the sieve of the section cut out by the bottom
subfunctor is the empty sieve, whatever the section. -/
theorem mem_sheafify_bot_iff {C : Type*} [Category C] (J : GrothendieckTopology C)
    {F : Cᵒᵖ ⥤ Type w} {U : Cᵒᵖ} (s : F.obj U) :
    s ∈ ((⊥ : Subfunctor F).sheafify J).obj U ↔ (⊥ : Sieve (unop U)) ∈ J (unop U) := by
  have hsieve : (⊥ : Subfunctor F).sieveOfSection s = ⊥ :=
    le_antisymm (fun _ _ h => h) bot_le
  show (⊥ : Subfunctor F).sieveOfSection s ∈ J (unop U) ↔ _
  rw [hsieve]

/-- **Distinct legs of a coproduct of algebraic spaces are locally disjoint.** The ranges of two
legs with distinct indices of a coproduct cocone of sheaves on the big fppf site over `S` meet
in the sheafification of the bottom subfunctor.

This is the sheafification of `⊥` and not `⊥` itself because an object of the site whose
underlying scheme has no points is covered by the empty sieve, and therefore carries a (unique)
section of every sheaf in the family; the content of the statement is that such objects are the
only ones carrying a section of two pieces at once. -/
theorem Sheaf.range_inf_range_eq_sheafify_bot {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) {i j : I} (hij : i ≠ j) :
    Subfunctor.range (ι i).hom ⊓ Subfunctor.range (ι j).hom
      = (⊥ : Subfunctor P.obj).sheafify (BigFppfOver.topology B S hS) := by
  have hsheaf (G : Sheaf (BigFppfOver.topology B S hS) (Type u)) : Presieve.IsSheaf _ G.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  refine le_antisymm ?_ ?_
  · rintro ⟨W⟩ x ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩
    rw [mem_sheafify_bot_iff]
    exact BigFppfOver.bot_mem_topology W
      (Sheaf.isEmpty_toScheme_of_eq_of_ne ι hP hij z z' (hz.trans hz'.symm))
  · rintro ⟨W⟩ x hx
    rw [mem_sheafify_bot_iff] at hx
    have hone (k : I) : x ∈ (Subfunctor.range (ι k).hom).obj (op W) := by
      obtain ⟨z⟩ := (hsheaf (F k)).nonempty_obj_of_bot_mem _ hx
      exact ⟨z, ((hsheaf P).subsingleton_obj_of_bot_mem _ hx).elim _ _⟩
    exact ⟨hone i, hone j⟩

/-- Sheafification of subfunctors is monotone: it enlarges the sieve cut out by a section. -/
theorem _root_.CategoryTheory.Subfunctor.sheafify_le_sheafify {C : Type*} [Category C]
    (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type w} {G G' : Subfunctor F} (h : G ≤ G') :
    G.sheafify J ≤ G'.sheafify J := fun _ _ hx =>
  J.superset_covering (fun _ _ hf => h _ hf) hx

/-- **The pieces of a coproduct of algebraic spaces locally cover it.** A subfunctor of the
vertex of a coproduct cocone of sheaves on the big fppf site over `S` which contains the range
of every leg sheafifies to the whole vertex.

The sheafification is not removable: the ranges are subpresheaves, so a section over a test
object which the decomposition splits into several pieces lies in no single range until it is
restricted. -/
theorem Sheaf.sheafify_eq_top_of_range_le_of_isColimit_cofan {I : Type w}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (T : Subfunctor P.obj)
    (hT : ∀ i, Subfunctor.range (ι i).hom ≤ T) :
    T.sheafify (BigFppfOver.topology B S hS) = ⊤ :=
  top_le_iff.1 (le_of_eq_of_le
    (CategoryTheory.Sheaf.sheafify_iSup_range_eq_top (BigFppfOver.topology B S hS) ι hP).symm
    (Subfunctor.sheafify_le_sheafify _ (iSup_le hT)))

/-- **The two pieces of a binary coproduct of algebraic spaces locally cover it.** The ranges of
the two legs of a coproduct cocone of sheaves on the big fppf site over `S` indexed by `Bool`
have join sheafifying to the whole vertex.

This is the shape in which Stacks 082H and Stacks 0ADU state that the two open-and-closed
pieces exhaust the base change. -/
theorem Sheaf.sheafify_sup_range_eq_top_of_isColimit_cofan
    {F : Bool → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) :
    (Subfunctor.range (ι false).hom ⊔ Subfunctor.range (ι true).hom).sheafify
      (BigFppfOver.topology B S hS) = ⊤ :=
  Sheaf.sheafify_eq_top_of_range_le_of_isColimit_cofan ι hP _
    (Bool.forall_bool.2 ⟨le_sup_left, le_sup_right⟩)

end AlgebraicGeometry

end
