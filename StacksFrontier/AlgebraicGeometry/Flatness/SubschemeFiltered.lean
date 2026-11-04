module

public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation

/-!
# The finite-presentation closed subschemes above a closed subscheme form a directed system

Fix a scheme `X` and quasi-coherent ideal sheaf data `K` on it, cutting out a closed subscheme
`Z`. The closed subschemes of `X` which are of finite presentation over `X` and contain `Z`
are indexed by `Stacks.Flatness.FinitePresentationSubscheme K`, the ideal sheaves `J ≤ K`
whose closed immersion `J.subschemeι` is of finite presentation. Ordered by `≤` this is a
filtered category, and the closed subschemes it indexes form an inverse system over `X`
receiving a canonical cone from `Z`.

Directedness needs no hypothesis on `X`, `K` or the index set: the zero ideal sheaf is a
member, and the sum of two members is a member because `J₁ ⊔ J₂ ≤ K` and because the sum of
two finitely generated ideal sheaves is finitely generated.

## Main definitions

* `Stacks.Flatness.FinitePresentationSubscheme` indexes the finite-presentation closed
  subschemes of `X` containing the closed subscheme cut out by `K`.
* `Stacks.Flatness.subschemeDiagram` is their inverse system over `X`.
* `Stacks.Flatness.subschemeCone` is the canonical cone on it with vertex the closed subscheme
  cut out by `K`.

## Main results

* `Stacks.Flatness.finitePresentationSubscheme_isFiltered` gives the directedness.

## Implementation notes

This is the directedness half of Tag 0EV9, in the generality in which it is true. Tag 0EV9
states it for `K` the ideal of sections supported on the inverse image of the center of an
almost blowup square over a quasi-compact and quasi-separated scheme; none of that enters the
argument, and the statement here specializes to the tag's at that `K`.

An ideal sheaf `J` satisfies `J ≤ K` exactly when the closed subscheme it cuts out contains
the one cut out by `K`, which by Tag 0EV8 is the condition appearing in Tag 0EV9. The index
category is the subtype of `AlgebraicGeometry.Scheme.IdealSheafData` with its order,
read as a category through `CategoryTheory.Preorder.smallCategory`; a filtered preorder is a
nonempty directed one, so `CategoryTheory.isFiltered_of_directed_le_nonempty` applies.

The diagram is taken with values in `CategoryTheory.Over X` rather than in `Scheme`, so that
it retains the closed immersions into `X` and the transition maps are automatically maps over
`X`.

## References

* [Stacks Project, Tag 0EV9](https://stacks.math.columbia.edu/tag/0EV9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Flatness

/-- The ideal sheaves cutting out the closed subschemes that are of finite presentation over
`X` and contain the closed subscheme cut out by `K`. -/
abbrev FinitePresentationSubscheme {X : Scheme.{u}} (K : X.IdealSheafData) :=
  {J : X.IdealSheafData // FinitePresentation J.subschemeι ∧ J ≤ K}

/-- The inverse system over `X` of all finite-presentation closed subschemes containing the
closed subscheme cut out by `K`. -/
def subschemeDiagram {X : Scheme.{u}} (K : X.IdealSheafData) :
    (FinitePresentationSubscheme K)ᵒᵖ ⥤ Over X where
  obj J := Over.mk J.unop.val.subschemeι
  map {J H} f := Over.homMk (Scheme.IdealSheafData.inclusion f.unop.le) (by simp)
  map_id J := by ext; simp
  map_comp f g := by ext; simp

/-- The canonical cone with vertex the closed subscheme cut out by `K` on the inverse system
of its finite-presentation closed enlargements. -/
def subschemeCone {X : Scheme.{u}} (K : X.IdealSheafData) : Cone (subschemeDiagram K) where
  pt := Over.mk K.subschemeι
  π :=
    { app J := Over.homMk (Scheme.IdealSheafData.inclusion J.unop.property.2)
        (by simp [subschemeDiagram])
      naturality J H f := by
        ext
        change Scheme.IdealSheafData.inclusion H.unop.property.2 =
          Scheme.IdealSheafData.inclusion J.unop.property.2 ≫
            Scheme.IdealSheafData.inclusion f.unop.le
        exact (Scheme.IdealSheafData.inclusion_comp f.unop.le J.unop.property.2).symm }

/-- The finite-presentation closed enlargements of a closed subscheme form a directed
system. Tag 0EV9 uses this at the ideal of sections supported on the exceptional subscheme of an
almost blowup square, see `AlgebraicGeometry.isFiltered_and_exists_isLimit_blowUpCone`. -/
theorem finitePresentationSubscheme_isFiltered {X : Scheme.{u}} (K : X.IdealSheafData) :
    IsFiltered (FinitePresentationSubscheme K) := by
  have : Nonempty (FinitePresentationSubscheme K) :=
    ⟨⟨⊥, finitePresentation_subschemeι_bot, bot_le⟩⟩
  have : IsDirectedOrder (FinitePresentationSubscheme K) :=
    ⟨fun J H ↦ ⟨⟨J.1 ⊔ H.1, finitePresentation_subschemeι_sup J.2.1 H.2.1,
      sup_le J.2.2 H.2.2⟩, Subtype.coe_le_coe.mp le_sup_left,
      Subtype.coe_le_coe.mp le_sup_right⟩⟩
  infer_instance

end Stacks.Flatness

end
