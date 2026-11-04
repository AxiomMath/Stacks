module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import StacksFrontier.AlgebraicGeometry.LimitDescent.BaseChangeLimit
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit

/-!
# Fullness of base change to a directed limit of schemes

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms, and let
`Xᵢ`, `Yᵢ` be quasi-compact, quasi-separated schemes locally of finite presentation over a stage
`Sᵢ`.  This file proves that a morphism `Xᵢ ×_{Sᵢ} S ⟶ Yᵢ ×_{Sᵢ} S` over `S` is the base change
of a morphism `Xᵢ ×_{Sᵢ} Sⱼ ⟶ Yᵢ ×_{Sᵢ} Sⱼ` over some later stage `Sⱼ`.

This is the fullness half of Stacks Tag 0EY1.

## Main definitions

* `AlgebraicGeometry.LimitDescent.bcCompIso`: the canonical identification
  `(X ×_{Sᵢ} Sⱼ) ×_{Sⱼ} S ≅ X ×_{Sᵢ} S` of the iterated base change with the base change to the
  limit, as an isomorphism in `Over S`.
* `AlgebraicGeometry.LimitDescent.bcCompLeft` and
  `AlgebraicGeometry.LimitDescent.bcCompInvLeft`: the two underlying morphisms of schemes, out of
  which it is assembled.

## Main results

* `AlgebraicGeometry.LimitDescent.exists_morphism_after_baseChange_of_small`.

## Implementation notes

A morphism `X ⟶ Yᵢ ×_{Sᵢ} S` over `S` is the same thing as a morphism `X ⟶ Yᵢ` over `Sᵢ`, so the
statement reduces, via `AlgebraicGeometry.LimitDescent.bcDiagram` and
`AlgebraicGeometry.LimitDescent.isLimitBcCone`, to the factorization property of a scheme locally
of finite presentation over the cofiltered diagram `j ↦ Xⱼ = Xᵢ ×_{Sᵢ} Sⱼ`, whose limit is `X`.
Mathlib proves that as
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`, and the index
universe is freed by
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall`.

That bridge needs `CategoryTheory.InitiallySmall.{u}` on the index category, which for the index
`Over (Opposite.op i)` of the diagram of base changes follows from `Small.{u} I` (the hom types
are automatically `u`-small, `Iᵒᵖ` being thin).  Hence the extra hypothesis `Small.{u} I`, which
the Stacks statement has for free, `I` there being a set.  This is exactly the restriction already
present in `AlgebraicGeometry.LimitDescent.eventually_eq_of_baseChange_eq_of_small`, and it comes
from the same place: every result of `Mathlib.AlgebraicGeometry.AffineTransitionLimit` is stated
for an index category at the universe of the schemes.

The two isomorphisms demanded by the Stacks statement are both instances of `bcCompIso`.  It is
built from `CategoryTheory.Limits.pullback.lift` rather than from
`CategoryTheory.Over.pullbackComp`: the latter is assembled by `conjugateIsoEquiv` from an
adjunction, so its components are not in a form in which the two conditions on `pullback.fst`
demanded by the Stacks statement can be read off.

Only `CompactSpace Xᵢ.left`, `QuasiSeparatedSpace Xᵢ.left` and `LocallyOfFinitePresentation
Yᵢ.hom` are used; the remaining finiteness hypotheses are carried for uniformity with the other
parts of the tag.

## References

* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
-/

@[expose] public section

universe v uI u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.LimitDescent

/-! ### The composition isomorphism -/

section Comp

variable {I : Type uI} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
  (X : Over (D.obj i)) (j : Over i)

/-- The commutativity which exhibits `(X ×_{D i} D j) ×_{D j} c.pt` as a cone over the square
defining `X ×_{D i} c.pt`. -/
lemma bcComp_condition :
    (pullback.fst (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) ≫
        pullback.fst X.hom (D.map j.hom)) ≫ X.hom =
      pullback.snd (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) ≫ c.π.app i := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
    Category.assoc, c.w]

/-- The underlying morphism `(X ×_{D i} D j) ×_{D j} c.pt ⟶ X ×_{D i} c.pt` of
`AlgebraicGeometry.LimitDescent.bcCompIso`. -/
noncomputable def bcCompLeft :
    pullback (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) ⟶ pullback X.hom (c.π.app i) :=
  pullback.lift
    (pullback.fst (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) ≫
      pullback.fst X.hom (D.map j.hom))
    (pullback.snd (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left))
    (bcComp_condition D c i X j)

/-- The component of `bcCompLeft D c i X j` towards `X` is the composite of the two first
projections. -/
@[reassoc (attr := simp)]
lemma bcCompLeft_fst :
    bcCompLeft D c i X j ≫ pullback.fst X.hom (c.π.app i) =
      pullback.fst (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) ≫
        pullback.fst X.hom (D.map j.hom) :=
  pullback.lift_fst _ _ _

/-- The component of `bcCompLeft D c i X j` towards `c.pt` is the second projection. -/
@[reassoc (attr := simp)]
lemma bcCompLeft_snd :
    bcCompLeft D c i X j ≫ pullback.snd X.hom (c.π.app i) =
      pullback.snd (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) :=
  pullback.lift_snd _ _ _

/-- The underlying morphism `X ×_{D i} c.pt ⟶ (X ×_{D i} D j) ×_{D j} c.pt` of the inverse of
`AlgebraicGeometry.LimitDescent.bcCompIso`. -/
noncomputable def bcCompInvLeft :
    pullback X.hom (c.π.app i) ⟶ pullback (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) :=
  pullback.lift (bcπ D c i X j) (pullback.snd X.hom (c.π.app i)) (bcπ_snd D c i X j)

/-- The component of `bcCompInvLeft D c i X j` towards `X ×_{D i} D j` is `bcπ D c i X j`. -/
@[reassoc (attr := simp)]
lemma bcCompInvLeft_fst :
    bcCompInvLeft D c i X j ≫
        pullback.fst (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) =
      bcπ D c i X j :=
  pullback.lift_fst _ _ _

/-- The component of `bcCompInvLeft D c i X j` towards `c.pt` is the second projection. -/
@[reassoc (attr := simp)]
lemma bcCompInvLeft_snd :
    bcCompInvLeft D c i X j ≫
        pullback.snd (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) =
      pullback.snd X.hom (c.π.app i) :=
  pullback.lift_snd _ _ _

/-- Composing `bcCompLeft D c i X j` with `bcπ D c i X j` gives the first projection of
`(X ×_{D i} D j) ×_{D j} c.pt`. -/
@[reassoc]
lemma bcCompLeft_bcπ :
    bcCompLeft D c i X j ≫ bcπ D c i X j =
      pullback.fst (pullback.snd X.hom (D.map j.hom)) (c.π.app j.left) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, bcπ_fst, bcCompLeft_fst]
  · rw [Category.assoc, bcπ_snd, bcCompLeft_snd_assoc, pullback.condition]

/-- `bcCompLeft D c i X j` followed by `bcCompInvLeft D c i X j` is the identity. -/
@[simp]
lemma bcCompLeft_bcCompInvLeft :
    bcCompLeft D c i X j ≫ bcCompInvLeft D c i X j = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, bcCompInvLeft_fst, bcCompLeft_bcπ, Category.id_comp]
  · rw [Category.assoc, bcCompInvLeft_snd, bcCompLeft_snd, Category.id_comp]

/-- `bcCompInvLeft D c i X j` followed by `bcCompLeft D c i X j` is the identity. -/
@[simp]
lemma bcCompInvLeft_bcCompLeft :
    bcCompInvLeft D c i X j ≫ bcCompLeft D c i X j = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, bcCompLeft_fst, bcCompInvLeft_fst_assoc, bcπ_fst, Category.id_comp]
  · rw [Category.assoc, bcCompLeft_snd, bcCompInvLeft_snd, Category.id_comp]

/-- The canonical identification `(X ×_{D i} D j) ×_{D j} c.pt ≅ X ×_{D i} c.pt` of the iterated
base change of `X : Over (D i)` with its base change to the limit, as an isomorphism over the
vertex of the cone `c`.

Its inverse component towards `X ×_{D i} D j` is `AlgebraicGeometry.LimitDescent.bcπ`. -/
noncomputable def bcCompIso :
    (Over.pullback (c.π.app j.left)).obj ((Over.pullback (D.map j.hom)).obj X) ≅
      (Over.pullback (c.π.app i)).obj X where
  hom := Over.homMk (bcCompLeft D c i X j) (bcCompLeft_snd D c i X j)
  inv := Over.homMk (bcCompInvLeft D c i X j) (bcCompInvLeft_snd D c i X j)
  hom_inv_id := Over.OverMorphism.ext (bcCompLeft_bcCompInvLeft D c i X j)
  inv_hom_id := Over.OverMorphism.ext (bcCompInvLeft_bcCompLeft D c i X j)

/-- The underlying morphism of schemes of `(bcCompIso D c i X j).hom` is `bcCompLeft D c i X j`. -/
@[simp]
lemma bcCompIso_hom_left : (bcCompIso D c i X j).hom.left = bcCompLeft D c i X j := rfl

/-- The underlying morphism of schemes of `(bcCompIso D c i X j).inv` is
`bcCompInvLeft D c i X j`. -/
@[simp]
lemma bcCompIso_inv_left : (bcCompIso D c i X j).inv.left = bcCompInvLeft D c i X j := rfl

/-- The first of the two conditions the Stacks statement imposes on the composition isomorphism:
it is the canonical one over `X`. -/
@[reassoc]
lemma bcCompIso_hom_left_fst :
    (bcCompIso D c i X j).hom.left ≫ pullback.fst X.hom (c.π.app i) =
      pullback.fst ((Over.pullback (D.map j.hom)).obj X).hom (c.π.app j.left) ≫
        pullback.fst X.hom (D.map j.hom) :=
  bcCompLeft_fst D c i X j

/-- The composition isomorphism is compatible with the projection to the stage `j`. -/
@[reassoc]
lemma bcCompIso_hom_left_bcπ :
    (bcCompIso D c i X j).hom.left ≫ bcπ D c i X j =
      pullback.fst ((Over.pullback (D.map j.hom)).obj X).hom (c.π.app j.left) :=
  bcCompLeft_bcπ D c i X j

/-- A morphism `u : X ×_{D i} D j ⟶ Y` over `D i` gives a morphism of objects over `D j`, and
under the composition isomorphisms its base change to `c.pt` is the morphism over `c.pt` whose
component towards `Y` is `u`.  This is the compatibility demanded by the fullness assertion of
Stacks Tag 0EY1. -/
lemma bcCompIso_hom_comp (Y : Over (D.obj i))
    (u : pullback X.hom (D.map j.hom) ⟶ Y.left)
    (hu : u ≫ Y.hom = pullback.snd X.hom (D.map j.hom) ≫ D.map j.hom)
    (φ : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y)
    (hφ : bcπ D c i X j ≫ u = φ.left ≫ pullback.fst Y.hom (c.π.app i)) :
    (bcCompIso D c i X j).hom ≫ φ =
      (Over.pullback (c.π.app j.left)).map
          (Over.homMk (pullback.lift u (pullback.snd X.hom (D.map j.hom)) hu)
            (pullback.lift_snd _ _ _)) ≫
        (bcCompIso D c i Y j).hom := by
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · simp only [Over.comp_left, bcCompIso_hom_left, Over.pullback_map_left, Over.homMk_left,
      Over.pullback_obj_hom, Category.assoc, bcCompLeft_fst, pullback.lift_fst_assoc,
      pullback.lift_fst]
    rw [← hφ, bcCompLeft_bcπ_assoc]
  · exact (Over.w _).trans (Over.w _).symm

end Comp

/-! ### Fullness -/

/-- **Fullness in Stacks Tag 0EY1**, under the extra hypothesis `Small.{u} I`.

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms, let
`Xᵢ`, `Yᵢ` be quasi-compact, quasi-separated schemes locally of finite presentation over a stage
`Sᵢ`, and let `f : Xᵢ ×_{Sᵢ} S ⟶ Yᵢ ×_{Sᵢ} S` be a morphism over `S`.  Then `f` is the base
change of a morphism `Xᵢ ×_{Sᵢ} Sⱼ ⟶ Yᵢ ×_{Sᵢ} Sⱼ` over some later stage `Sⱼ`, the identification
of the iterated base change with the base change to the limit being the canonical one over both
factors.

The index type is assumed `u`-small, where `u` is the universe of the schemes; see the
implementation notes. -/
theorem exists_morphism_after_baseChange_of_small
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [Small.{u} I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (Xᵢ Yᵢ : Over (D.obj (.op i)))
    (hXqc : CompactSpace Xᵢ.left) (hXqs : QuasiSeparatedSpace Xᵢ.left)
    (hYqc : CompactSpace Yᵢ.left) (hYqs : QuasiSeparatedSpace Yᵢ.left)
    (hX : LocallyOfFinitePresentation Xᵢ.hom)
    (hY : LocallyOfFinitePresentation Yᵢ.hom)
    (f : (Over.pullback (c.π.app (.op i))).obj Xᵢ ⟶
      (Over.pullback (c.π.app (.op i))).obj Yᵢ) :
    ∃ (j : I) (hij : i ≤ j)
      (g : (Over.pullback (D.map (homOfLE hij).op)).obj Xᵢ ⟶
        (Over.pullback (D.map (homOfLE hij).op)).obj Yᵢ)
      (α : (Over.pullback (c.π.app (.op j))).obj
          ((Over.pullback (D.map (homOfLE hij).op)).obj Xᵢ) ≅
        (Over.pullback (c.π.app (.op i))).obj Xᵢ)
      (β : (Over.pullback (c.π.app (.op j))).obj
          ((Over.pullback (D.map (homOfLE hij).op)).obj Yᵢ) ≅
        (Over.pullback (c.π.app (.op i))).obj Yᵢ),
      (α.hom.left ≫ pullback.fst Xᵢ.hom (c.π.app (.op i)) =
        pullback.fst ((Over.pullback (D.map (homOfLE hij).op)).obj Xᵢ).hom
            (c.π.app (.op j)) ≫ pullback.fst Xᵢ.hom (D.map (homOfLE hij).op)) ∧
      (β.hom.left ≫ pullback.fst Yᵢ.hom (c.π.app (.op i)) =
        pullback.fst ((Over.pullback (D.map (homOfLE hij).op)).obj Yᵢ).hom
            (c.π.app (.op j)) ≫ pullback.fst Yᵢ.hom (D.map (homOfLE hij).op)) ∧
      α.hom ≫ f = (Over.pullback (c.π.app (.op j))).map g ≫ β.hom := by
  -- Only `hXqc`, `hXqs` and `hY` are used; the others are recorded for uniformity with the tag.
  have := hYqc
  have := hYqs
  have := hX
  have : InitiallySmall.{u} Iᵒᵖ := CategoryTheory.initiallySmall_of_small_of_locallySmall _
  -- That `f` is a morphism over `c.pt`, in terms of the two projections.
  have hwf : f.left ≫ pullback.snd Yᵢ.hom (c.π.app (.op i)) =
      pullback.snd Xᵢ.hom (c.π.app (.op i)) := Over.w f
  -- Factor `f`, read as a morphism to `Yᵢ` over the stage `D i`, through a stage.
  obtain ⟨k, g, hg₁, hg₂⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall
      (bcDiagram D (.op i) Xᵢ) (bcCone D c (.op i) Xᵢ) (bcToBase D (.op i) Xᵢ) Yᵢ.hom
      (isLimitBcCone D c (.op i) Xᵢ hc)
      (f.left ≫ pullback.fst Yᵢ.hom (c.π.app (.op i))) <| by
        refine NatTrans.ext (funext fun l ↦ ?_)
        simp only [NatTrans.comp_app, bcToBase_app, Functor.const_map_app]
        rw [← Category.assoc, bcπ_fst, pullback.condition, Category.assoc,
          pullback.condition, ← Category.assoc, hwf]
  have hcond : g ≫ Yᵢ.hom = pullback.snd Xᵢ.hom (D.map k.hom) ≫ D.map k.hom := by
    rw [hg₂, bcToBase_app]; exact pullback.condition
  have hf : bcπ D c (.op i) Xᵢ k ≫ g =
    f.left ≫ pullback.fst Yᵢ.hom (c.π.app (.op i)) := hg₁
  -- Read the stage off as an index of `I` above `i`, and assemble the three data.
  exact ⟨k.left.unop, leOfHom k.hom.unop,
    Over.homMk (pullback.lift g (pullback.snd Xᵢ.hom (D.map k.hom)) hcond)
      (pullback.lift_snd _ _ _),
    bcCompIso D c (.op i) Xᵢ k, bcCompIso D c (.op i) Yᵢ k,
    bcCompIso_hom_left_fst D c (.op i) Xᵢ k, bcCompIso_hom_left_fst D c (.op i) Yᵢ k,
    bcCompIso_hom_comp D c (.op i) Xᵢ k Yᵢ g hcond f hf⟩

end AlgebraicGeometry.LimitDescent
