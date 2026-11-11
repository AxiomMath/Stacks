module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.CategoryTheory.Limits.SizeCutoff
public import StacksFrontier.SetTheory.Cardinal.ClosurePoint

/-!
# A cutoff category of schemes with countable limits and colimits

Stacks 000J: for a set `S₀` of schemes there is a cutoff `Sch_α ⊆ Sch` which contains `S₀`, contains
a copy of every scheme of size at most `Bound(size S)` for `S ∈ Sch_α`, and in which a countable
diagram has a limit (a colimit) if and only if it has one in `Sch`, the comparison morphism being an
isomorphism.

Here `Sch_α` is the full subcategory `AlgebraicGeometry.SchemeBelow κ` of schemes of size below a
cardinal `κ`. The cardinal is chosen as in the proof of 000J: it is closed under the operations
bounding the sizes of the countable limits and colimits that exist in `Sch` of diagrams in a
smaller cutoff (`CategoryTheory.Limits.exists_sizeCutoff_bound`, which uses that the countable
categories and the diagrams in a cutoff form a set up to isomorphism), and it is closed in addition
under the sizes of witnesses that a cone or cocone in a smaller cutoff is not a limit or colimit in
`Sch`. The second closure gives the direction "a limit in `Sch_α` is a limit in `Sch`", which
Stacks comment #608 notes the proof in the Stacks project does not address.

## Main results

* `AlgebraicGeometry.exists_schemeBelow_countable_limits_colimits`: Stacks 000J.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Order

universe w v u

namespace AlgebraicGeometry

/-- The schemes of size below `μ` form an essentially small property, for every cardinal `μ`. -/
theorem essentiallySmall_sizeLT_size (μ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u} (sizeLT Scheme.size μ) :=
  have _ : ObjectProperty.EssentiallySmall.{u}
      (schemeSizeBelow (Order.succ (max μ Cardinal.aleph0.{u}))) :=
    essentiallySmall_schemeSizeBelow _ ((le_max_right _ _).trans (Order.le_succ _))
  ObjectProperty.EssentiallySmall.of_le
    (Q := schemeSizeBelow (Order.succ (max μ Cardinal.aleph0.{u}))) fun _ hX =>
      lt_of_lt_of_le hX ((le_max_left _ _).trans (Order.le_succ _))

/-- **Stacks 000J.** Let `S₀` be a set of schemes. There is an uncountable strong limit cardinal
`κ` of uncountable cofinality such that the full subcategory `Sch_κ = SchemeBelow κ` of schemes of
size below `κ` has the following properties.
1. `S₀ ⊆ Ob(Sch_κ)`.
2. For any `S ∈ Ob(Sch_κ)` and any scheme `T` with `size(T) ≤ Bound(size(S))` there is
   `S' ∈ Ob(Sch_κ)` with `T ≅ S'`.
3. For any countable category `J` (countably many objects and morphisms) and any functor
   `F : J ⥤ Sch_κ`, the limit of `F` exists in `Sch_κ` if and only if the limit of `F` exists in
   `Sch`, and in this case the natural morphism between them is an isomorphism.
4. The same holds for colimits. -/
@[stacks 000J]
theorem exists_schemeBelow_countable_limits_colimits (S₀ : Set Scheme.{u}) [Small.{u} S₀] :
    ∃ κ : Cardinal.{u}, ℵ₀ < κ ∧ IsStrongPrelimit κ ∧ ℵ₀ < κ.ord.cof ∧
      (∀ S ∈ S₀, schemeSizeBelow κ S) ∧
      (∀ (S : SchemeBelow κ) (T : Scheme.{u}), T.size ≤ stacksBound S.obj.size →
        ∃ S' : SchemeBelow κ, Nonempty (T ≅ S'.obj)) ∧
      (∀ (J : Type v) [Category.{w} J] [CountableCategory J] (F : J ⥤ SchemeBelow κ),
        (HasLimit F ↔ HasLimit (F ⋙ schemeBelowInclusion κ)) ∧
        ∀ [HasLimit F] [HasLimit (F ⋙ schemeBelowInclusion κ)],
          IsIso (limit.post F (schemeBelowInclusion κ))) ∧
      (∀ (J : Type v) [Category.{w} J] [CountableCategory J] (F : J ⥤ SchemeBelow κ),
        (HasColimit F ↔ HasColimit (F ⋙ schemeBelowInclusion κ)) ∧
        ∀ [HasColimit F] [HasColimit (F ⋙ schemeBelowInclusion κ)],
          IsIso (colimit.post F (schemeBelowInclusion κ))) := by
  have := essentiallySmall_sizeLT_size.{u}
  obtain ⟨ν, hν⟩ := exists_sizeCutoff_bound.{w, v} (s := Scheme.size) fun e => Scheme.size_congr e
  obtain ⟨κ, hμκ, hsl, hcof, hclosed⟩ :=
    exists_isStrongPrelimit_gt_forall_lt ν (max ℵ₀ (⨆ S : S₀, (S : Scheme.{u}).size))
  have hκ : ℵ₀ < κ := (le_max_left _ _).trans_lt hμκ
  have hsucc : ∀ μ < κ, succ μ < κ := fun μ hμ => (succ_le_of_lt (cantor μ)).trans_lt (hsl hμ)
  have H := hν κ hsucc hcof hclosed
  refine ⟨κ, hκ, hsl, hcof, fun S hS => ?_, fun S T hT =>
    ⟨⟨T, Scheme.size_lt_of_le_stacksBound hκ hsl S.2 hT⟩, ⟨Iso.refl _⟩⟩, fun J _ _ F => ?_,
    fun J _ _ F => ?_⟩
  · exact ((le_ciSup (f := fun S : S₀ => (S : Scheme.{u}).size) Cardinal.bddAbove_of_small
      ⟨S, hS⟩).trans (le_max_right _ _)).trans_lt hμκ
  · obtain ⟨h1, h2, -, -⟩ := H J (F ⋙ schemeBelowInclusion κ) fun j => (F.obj j).2
    exact (schemeSizeBelow κ).hasLimit_iff_and_isIso_limit_post F h1 h2
  · obtain ⟨-, -, h3, h4⟩ := H J (F ⋙ schemeBelowInclusion κ) fun j => (F.obj j).2
    exact (schemeSizeBelow κ).hasColimit_iff_and_isIso_colimit_post F h3 h4

end AlgebraicGeometry
