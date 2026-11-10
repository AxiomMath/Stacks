module

public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.Cotangent.DirectedColimit
public import StacksFrontier.Cotangent.FilteredColimitVanishing

/-!
# A directed cofinal system of neighbourhoods of a point of a site

Let `Φ` be a point of a site. The fibre `Φ.presheafFiber P` of a presheaf `P` is the colimit of
`P` over the opposite of the category of neighbourhoods `Φ.fiber.Elements`, which is filtered but
in general not a preorder: an object `(U, x)` may have several maps to another. By Mathlib's
`CategoryTheory.FinallySmall.exists_of_isFiltered` and Deligne's lemma
`CategoryTheory.IsFiltered.exists_directed` ([Stacks, Tag 0032]), there is a directed partially
ordered set `α` with a final functor `α ⥤ (Φ.fiber.Elements)ᵒᵖ`, so the fibre is a directed
colimit, indexed by a preorder, of sections over neighbourhoods.

This puts the fibres of a point of a site in the scope of the elementwise colimit criterion
`IsDirectedColimitOfTypes` of `StacksFrontier.Cotangent.DirectedColimit`, whose main application is
[Stacks, Tag 08S9]: the cotangent complex commutes with directed colimits of ring maps. Applied to
the germ maps of two sheaves of rings `A → B` at `Φ`, it computes the stalk of the presheaf
`U ↦ L_{B(U)/A(U)}` as `L_{B_Φ/A_Φ}`, the ring-level form of [Stacks, Tag 08T0] used in the proof
of [Stacks, Tag 09DM].

## Main results

* `IsDirectedColimitOfTypes.of_isColimit`: a colimit cocone of types over a directed nonempty
  preorder satisfies the elementwise criterion.
* `CategoryTheory.GrothendieckTopology.Point.exists_directed_final`: a directed nonempty
  partially ordered set with a final functor to the opposite of the neighbourhoods of `Φ`.
* `CategoryTheory.GrothendieckTopology.Point.isDirectedColimitOfTypes_toPresheafFiber`: along
  such a functor, the germ maps of a presheaf of types exhibit its fibre as a directed colimit.
* `CategoryTheory.GrothendieckTopology.Point.isDirectedColimitOfTypes_toPresheafFiber_commRingCat`:
  the same for a presheaf of commutative rings and its stalk ring.

## References

* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
* [Stacks Project, Tag 08S9](https://stacks.math.columbia.edu/tag/08S9)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u

/-- **A colimit of types over a directed preorder is a directed colimit.** For a colimit cocone
`c` of a functor `F : α ⥤ Type w'` out of a directed nonempty preorder, the transition maps of
`F` and the legs of `c` satisfy the elementwise criterion `IsDirectedColimitOfTypes`. -/
theorem IsDirectedColimitOfTypes.of_isColimit {α : Type w} [Preorder α]
    [IsDirected α (· ≤ ·)] [Nonempty α] {F : α ⥤ Type w'} {c : Cocone F} (hc : IsColimit c) :
    IsDirectedColimitOfTypes (fun _ _ h a => F.map (homOfLE h) a) (fun i a => c.ι.app i a) where
  map_id i a := by
    rw [show homOfLE (le_refl i) = 𝟙 i from Subsingleton.elim _ _, F.map_id]
    rfl
  map_comp i j k hij hjk a := by
    rw [← Functor.map_comp_apply]
    rfl
  comp i j hij a := Cocone.w_apply c (homOfLE hij) a
  jointly_surjective b := Types.jointly_surjective_of_isColimit hc b
  exists_eq i a b h := by
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc a b).1 h
    exact ⟨j, leOfHom f, by rwa [show homOfLE (leOfHom f) = f from Subsingleton.elim _ _]⟩

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w})

/-- **A directed cofinal system of neighbourhoods.** For a point `Φ` of a site, there is a
directed nonempty partially ordered set `α` in the universe of the fibres, with a final functor
to the opposite of the category of neighbourhoods of `Φ`. -/
theorem exists_directed_final :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (F : α ⥤ (Φ.fiber.Elements)ᵒᵖ), F.Final := by
  obtain ⟨D, _, _, G, _⟩ := FinallySmall.exists_of_isFiltered.{w} (Φ.fiber.Elements)ᵒᵖ
  obtain ⟨α, _, _, _, F, _⟩ := IsFiltered.exists_directed D
  exact ⟨α, _, inferInstance, inferInstance, F ⋙ G, inferInstance⟩

omit [LocallySmall.{w, v, u} C] in
/-- **The fibre of a presheaf of types is a directed colimit of sections over neighbourhoods.**
Along a final functor `F` from a directed nonempty preorder to the opposite of the neighbourhoods
of `Φ`, the germ maps `P(U_i) → P_Φ` at the neighbourhoods `(U_i, x_i) = F i` exhibit the fibre
`Φ.presheafFiber P` as the directed colimit of the restriction maps `P(U_i) → P(U_j)`. -/
theorem isDirectedColimitOfTypes_toPresheafFiber {α : Type w} [Preorder α]
    [IsDirected α (· ≤ ·)] [Nonempty α] (F : α ⥤ (Φ.fiber.Elements)ᵒᵖ) [F.Final]
    (P : Cᵒᵖ ⥤ Type w) :
    IsDirectedColimitOfTypes
      (fun _ _ h a => P.map (F.map (homOfLE h)).unop.1.op a)
      (fun i a => Φ.toPresheafFiber (F.obj i).unop.1 (F.obj i).unop.2 P a) :=
  IsDirectedColimitOfTypes.of_isColimit
    ((Functor.Final.isColimitWhiskerEquiv F _).symm (Φ.isColimitPresheafFiberCocone P))

/-- **The stalk ring is a directed colimit of rings of sections over neighbourhoods.** The
form of `CategoryTheory.GrothendieckTopology.Point.isDirectedColimitOfTypes_toPresheafFiber` for
a presheaf of commutative rings and its stalk computed in `CommRingCat`, which is the hypothesis
of [Stacks, Tag 08S9] (`CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb`) for the germ
maps of a map of sheaves of rings. -/
theorem isDirectedColimitOfTypes_toPresheafFiber_commRingCat {α : Type w} [Preorder α]
    [IsDirected α (· ≤ ·)] [Nonempty α] (F : α ⥤ (Φ.fiber.Elements)ᵒᵖ) [F.Final]
    (R : Cᵒᵖ ⥤ CommRingCat.{w}) :
    IsDirectedColimitOfTypes
      (fun _ _ h a => (R.map (F.map (homOfLE h)).unop.1.op).hom a)
      (fun i a => (Φ.toPresheafFiber (F.obj i).unop.1 (F.obj i).unop.2 R).hom a) :=
  CommRingCat.isDirectedColimitOfTypes_of_isColimit (F ⋙ (Functor.Elements.π Φ.fiber).op ⋙ R) _
    ((Functor.Final.isColimitWhiskerEquiv F _).symm (Φ.isColimitPresheafFiberCocone R))

end CategoryTheory.GrothendieckTopology.Point

end
