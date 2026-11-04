module
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Consequences
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Pullback

/-!
# Stacks 007P — factoring through an injective morphism

Let `(C, F)` be a type of algebraic structure (tag 007M, the imported
`AlgebraicStructureType`): a category `C` with a faithful functor `F : C ⥤ Type v`
that preserves all small limits, preserves filtered colimits, and reflects
isomorphisms. Let `A`, `B`, `C` be objects of `C`, and let `f : A ⟶ B`, `g : C ⟶ B`.
If `F.map g` is injective and the range of `F.map f` is contained in the range of
`F.map g`, then `f` factors as `f = t ≫ g` for some `t : A ⟶ C`.

The proof: form the pullback `P = A ×_B C` in `C` with projections `p : P ⟶ A`,
`q : P ⟶ C`. Since `F` preserves finite limits, the image square is a pullback in
`Type v`, and under the hypotheses its projection `F p` is bijective, hence an
isomorphism there. Because `F` reflects isomorphisms, `p` itself is an isomorphism, and
we may take `t := inv p ≫ q`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

/-- **Stacks Project, Tag 007P (Lemma 6.15.4).**
Let `(C, F)` be a type of algebraic structure. Let `A`, `B`, `C` be objects of `C` and
let `f : A ⟶ B`, `g : C ⟶ B`. If `F.map g` is injective and the range of `F.map f` is
contained in the range of `F.map g`, then `f` factors through `g`: there is a morphism
`t : A ⟶ C` with `f = t ≫ g`. -/
@[stacks_fixed 007P]
theorem factor_through_injective_image_subset
    (S : AlgebraicStructureType.{v, u})
    (A B C : S.C) (f : A ⟶ B) (g : C ⟶ B)
    (hg : Function.Injective (S.F.map g))
    (hsub : Set.range (S.F.map f) ⊆ Set.range (S.F.map g)) :
    ∃ t : A ⟶ C, f = t ≫ g := by
  have : PreservesFiniteLimits S.F := PreservesLimitsOfSize.preservesFiniteLimits S.F
  have := isIso_pullbackFst_of_injective_of_range_subset S.F f g hg hsub
  refine ⟨inv (pullback.fst f g) ≫ pullback.snd f g, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

