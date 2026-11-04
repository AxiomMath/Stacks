module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import StacksFrontier.AlgebraicGeometry.LimitDescent.BaseChangeLimit
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit

/-!
# Faithfulness of base change to a directed limit of schemes

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms, and let
`Xᵢ`, `Yᵢ` be quasi-compact, quasi-separated schemes locally of finite presentation over a stage
`Sᵢ`.  This file proves that two morphisms `Xᵢ ⟶ Yᵢ` over `Sᵢ` whose base changes to `S` agree
already have equal base changes to some later stage `Sⱼ`.

This is the faithfulness half of Stacks Tag 0EY1.

## Main results

* `AlgebraicGeometry.LimitDescent.eventually_eq_of_baseChange_eq_of_small`.

## Implementation notes

The statement reduces, via `AlgebraicGeometry.LimitDescent.bcDiagram` and
`AlgebraicGeometry.LimitDescent.isLimitBcCone`, to the injectivity half of Stacks Tag 01ZC —
injectivity of `colim Hom_{Sᵢ}(Xⱼ, Yᵢ) ⟶ Hom_{Sᵢ}(X, Yᵢ)` for the cofiltered diagram
`j ↦ Xⱼ = Xᵢ ×_{Sᵢ} Sⱼ` over `Sᵢ`, whose limit is `X`.  Mathlib proves that as
`AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`, and the index
universe is freed by
`AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_initiallySmall`.

That bridge needs `CategoryTheory.InitiallySmall.{u}` on the index category, which for the
index `Over (Opposite.op i)` of the diagram of base changes follows from `Small.{u} I` (the hom
types are automatically `u`-small, `Iᵒᵖ` being thin).  Hence the extra hypothesis `Small.{u} I`,
which the Stacks statement has for free, `I` there being a set.  It is a genuine restriction and
not an artefact: a cofiltered index category need not have a `u`-small cofinal subcategory —
for instance `(Ordinal.{u})ᵒᵖ` does not — and then no reindexing by a `u`-small diagram exists.

Only `CompactSpace Xᵢ.left` and `LocallyOfFinitePresentation Yᵢ.hom` are used; the remaining
finiteness hypotheses are carried for uniformity with the other parts of the tag.

## References

* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.LimitDescent

/-- **Faithfulness in Stacks Tag 0EY1**, under the extra hypothesis `Small.{u} I`.

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms, let
`Xᵢ`, `Yᵢ` be quasi-compact, quasi-separated schemes locally of finite presentation over a stage
`Sᵢ`, and let `f`, `g : Xᵢ ⟶ Yᵢ` be morphisms over `Sᵢ` whose base changes to `S` agree.  Then
the base changes of `f` and `g` to some later stage `Sⱼ` already agree.

The index type is assumed `u`-small, where `u` is the universe of the schemes; see the
implementation notes. -/
theorem eventually_eq_of_baseChange_eq_of_small
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [Small.{u} I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (Xᵢ Yᵢ : Over (D.obj (.op i)))
    (hXqc : CompactSpace Xᵢ.left) (hXqs : QuasiSeparatedSpace Xᵢ.left)
    (hYqc : CompactSpace Yᵢ.left) (hYqs : QuasiSeparatedSpace Yᵢ.left)
    (hX : LocallyOfFinitePresentation Xᵢ.hom)
    (hY : LocallyOfFinitePresentation Yᵢ.hom)
    (f g : Xᵢ ⟶ Yᵢ)
    (hfg : (Over.pullback (c.π.app (.op i))).map f =
      (Over.pullback (c.π.app (.op i))).map g) :
    ∃ (j : I) (hij : i ≤ j),
      (Over.pullback (D.map (homOfLE hij).op)).map f =
        (Over.pullback (D.map (homOfLE hij).op)).map g := by
  -- Only `hXqc` and `hY` are used; the others are recorded for uniformity with the tag.
  have := hXqc
  have := hXqs
  have := hYqc
  have := hYqs
  have := hX
  have := hY
  have : InitiallySmall.{u} Iᵒᵖ := CategoryTheory.initiallySmall_of_small_of_locallySmall _
  -- The two base changes to `S`, read off through the projection to `Yᵢ`.
  have hfgfst : pullback.fst Xᵢ.hom (c.π.app (.op i)) ≫ f.left =
      pullback.fst Xᵢ.hom (c.π.app (.op i)) ≫ g.left := by
    have h := congrArg Over.Hom.left hfg
    simp only [Over.pullback_map_left] at h
    simpa only [pullback.lift_fst] using
      congrArg (· ≫ pullback.fst Yᵢ.hom (c.π.app (Opposite.op i))) h
  -- Injectivity for the diagram of base changes of `Xᵢ`, whose limit is `X`.
  obtain ⟨k, hik, hjk, hk⟩ :=
    Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_initiallySmall
      (bcDiagram D (.op i) Xᵢ) (bcCone D c (.op i) Xᵢ) (bcToBase D (.op i) Xᵢ) Yᵢ.hom
      (isLimitBcCone D c (.op i) Xᵢ hc)
      (i := Over.mk (𝟙 (Opposite.op i)))
      (pullback.fst Xᵢ.hom
        (D.map (Over.mk (𝟙 (Opposite.op i)) : Over (Opposite.op i)).hom) ≫ f.left)
      (by simp only [bcToBase_app, Category.assoc, Over.w])
      (j := Over.mk (𝟙 (Opposite.op i)))
      (pullback.fst Xᵢ.hom
        (D.map (Over.mk (𝟙 (Opposite.op i)) : Over (Opposite.op i)).hom) ≫ g.left)
      (by simp only [bcToBase_app, Category.assoc, Over.w])
      (by rw [bcπ_fst_assoc, bcπ_fst_assoc]; exact hfgfst)
  -- Read the resulting stage off as an index of `I` above `i`.
  refine ⟨k.left.unop, leOfHom k.hom.unop, ?_⟩
  have hkh : (homOfLE (leOfHom k.hom.unop)).op = k.hom := Subsingleton.elim _ _
  rw [bcMap_fst_assoc, bcMap_fst_assoc] at hk
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    rw [hkh]
    exact hk
  · simp only [Over.pullback_map_left, pullback.lift_snd]

end AlgebraicGeometry.LimitDescent
