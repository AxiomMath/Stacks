module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniqueness
public import StacksFrontier.CategoryTheory.DottedArrows.Defs
public import StacksFrontier.CategoryTheory.DottedArrows.Faithful
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Setoid
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.JointlyFaithful

/-!
# Valuative criterion for the diagonal (Stacks 0E8L)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site and let
`D` be a valuative diagram for the *relative diagonal* `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳`: a valuation ring `A`
with fraction field `K`, a generic point `x : Spec K ⟶ 𝒳`, a special point
`y = (a₁, a₂, φ) : Spec A ⟶ 𝒳 ×_𝒴 𝒳` and a 2-morphism `γ : y ∘ j ⟶ Δ_f ∘ x`.

Writing `γ` as the pair `(α₁, α₂)` of its two projections, **Stacks 0E8L** says that `(a₁, α₁, id)`
and `(a₂, α₂, φ)` are two dotted arrows for the square of `f` whose bottom row is `f ∘ a₁`, that
the category of dotted arrows of the `Δ_f`-square is a setoid, and that its isomorphism classes are
exactly the morphisms `(a₁, α₁, id) ⟶ (a₂, α₂, φ)` in the category of dotted arrows of that
`f`-square.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.diagonalCellFst`, `..._Snd`: the two projections
  `α₁`, `α₂` of the 2-morphism filling a valuative diagram for the relative diagonal.
* `AlgebraicGeometry.Stack.AlgebraicStacks.diagonalComparisonCell`: the comparison `φ` carried by
  the special point of the diagram.
* `AlgebraicGeometry.Stack.AlgebraicStacks.diagonalDottedArrowFst`, `..._Snd`: the two dotted
  arrows `(a₁, α₁, id)` and `(a₂, α₂, φ)` of **Stacks 0E8L**, part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.dottedArrowOfProjections`: a dotted arrow for the
  `Δ_f`-square assembled from a compatible pair of projections.
* `AlgebraicGeometry.Stack.AlgebraicStacks.diagonalDottedArrowClassesEquiv`: **Stacks 0E8L**,
  part (2), the bijection of isomorphism classes with morphisms of dotted arrows.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSetoidCategory_dottedArrow_relativeDiagonal`:
  **Stacks 0E8L**, part (2), the category of dotted arrows of the `Δ_f`-square is a setoid.
* `AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal_whiskerLeft_twoFibreProductCell`: the
  relative diagonal identifies the two images of a point by the identity.

## Implementation notes

The source deduces the setoid property from separatedness of the diagonal of `Δ_f` and the
uniqueness criterion of Stacks 0CLC. The route taken here is shorter and has the same hypothesis:
`Δ_f` is representable by algebraic spaces (**Stacks 04XS**, part (1)), hence has faithful
underlying functor (**Stacks 04Y5**, the implication (3) ⟹ (2)), and the category of dotted arrows
along a faithful 1-morphism is a thin groupoid, hence a setoid
(`CategoryTheory.isSetoidCategory_dottedArrow_of_faithful`).

Everything else is a 2-diagrammatic computation, carried out against the canonical model
`AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare` of the 2-fibre product, for which
both projections undo the relative diagonal on the nose. The only genuinely two-dimensional inputs
are the exchange law and the fact that the diagonal's comparison 2-cell is the identity; the
bijection of part (2) is bijectivity of the explicit map `d ↦ (β ⋆ pr₁) ∘ (β ⋆ pr₂)⁻¹`, whose
surjectivity uses that the two projections of a 2-fibre product are jointly full on invertible
2-cells (`CategoryTheory.Bicategory.twoFibreProduct_jointlyFaithful`) — every 2-morphism of
categories fibred in groupoids is invertible, so that is no restriction.

`CategoryTheory.DottedArrow` is the one of `StacksFrontier/CategoryTheory/DottedArrows/Defs.lean`,
whose `γ`, `α` and `β` are 2-morphisms, as in the source; the name is written out because a
different structure of the same name in the root namespace shadows it under `open CategoryTheory`.

## References

* [Stacks Project, Tag 0E8L](https://stacks.math.columbia.edu/tag/0E8L)
* [Stacks Project, Tag 0CLG](https://stacks.math.columbia.edu/tag/0CLG)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 0H18](https://stacks.math.columbia.edu/tag/0H18)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.BasedCategory.ofFunctor

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The invertible 2-morphism `pr₁ ≫ f ⟶ pr₂ ≫ f` filling the canonical 2-fibre product square
`𝒳 ×_{f, 𝒴, f} 𝒳`, as a 2-morphism of categories fibred in groupoids. At a point `(x₁, x₂, ι)` of
the 2-fibre product its component is the identification `ι : f(x₁) ⟶ f(x₂)`. -/
def twoFibreProductCell (f : 𝒳 ⟶ 𝒴) :
    ((twoFibreProductSquare B S hS f f).fst.hom ≫ f.hom) ⟶
      ((twoFibreProductSquare B S hS f f).snd.hom ≫ f.hom) :=
  (twoFibreProductSquare B S hS f f).iso.hom.hom

/-- The first projection undoes the relative diagonal, as 1-morphisms of categories fibred in
groupoids. -/
@[simp]
theorem relativeDiagonal_hom_comp_fst_hom (f : 𝒳 ⟶ 𝒴) :
    (relativeDiagonal B S hS f).hom ≫ (twoFibreProductSquare B S hS f f).fst.hom
      = 𝟙 𝒳.val := rfl

/-- The second projection undoes the relative diagonal, as 1-morphisms of categories fibred in
groupoids. -/
@[simp]
theorem relativeDiagonal_hom_comp_snd_hom (f : 𝒳 ⟶ 𝒴) :
    (relativeDiagonal B S hS f).hom ≫ (twoFibreProductSquare B S hS f f).snd.hom
      = 𝟙 𝒳.val := rfl

/-- **The relative diagonal identifies the two images of a point by the identity.** The diagonal
sends `x` to the triple `(x, x, id)`, so whiskering the filler of the 2-fibre product square into
it gives the identity 2-morphism of `f`. -/
theorem relativeDiagonal_whiskerLeft_twoFibreProductCell (f : 𝒳 ⟶ 𝒴) :
    (relativeDiagonal B S hS f).hom ◁ twoFibreProductCell B S hS f
      = 𝟙 ((relativeDiagonal B S hS f).hom ≫
          ((twoFibreProductSquare B S hS f f).fst.hom ≫ f.hom)) := by
  refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
  funext z
  rfl

/-- **The comparison of a point of the form `Δ_f ∘ a` is the identity**, the previous statement
precomposed with a 1-morphism `a`. -/
theorem whiskerLeft_relativeDiagonal_whiskerLeft_twoFibreProductCell (f : 𝒳 ⟶ 𝒴)
    {A : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : A ⟶ 𝒳.val) :
    (a ≫ (relativeDiagonal B S hS f).hom) ◁ twoFibreProductCell B S hS f = 𝟙 _ :=
  (congrArg (fun t => a ◁ t)
    (relativeDiagonal_whiskerLeft_twoFibreProductCell B S hS f)).trans (whiskerLeft_id a _)

/-- **Whiskering a 2-morphism into the relative diagonal is undone by the first projection.** -/
theorem whiskerRight_relativeDiagonal_whiskerRight_fst {f : 𝒳 ⟶ 𝒴}
    {A : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} {a b : A ⟶ 𝒳.val}
    (η : a ⟶ b) :
    (η ▷ (relativeDiagonal B S hS f).hom) ▷ (twoFibreProductSquare B S hS f f).fst.hom = η := by
  refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
  funext z
  rfl

/-- **Whiskering a 2-morphism into the relative diagonal is undone by the second projection.** -/
theorem whiskerRight_relativeDiagonal_whiskerRight_snd {f : 𝒳 ⟶ 𝒴}
    {A : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} {a b : A ⟶ 𝒳.val}
    (η : a ⟶ b) :
    (η ▷ (relativeDiagonal B S hS f).hom) ▷ (twoFibreProductSquare B S hS f f).snd.hom = η := by
  refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
  funext z
  rfl

variable {f : 𝒳 ⟶ 𝒴}
  (D : ValuativeDiagram B S hS 𝒳 (twoFibreProduct B S hS f f) (relativeDiagonal B S hS f))

/-! ### The two dotted arrows for `f` -/

/-- The first projection `α₁ : a₁ ∘ j ⟶ x` of the 2-morphism filling a valuative diagram for the
relative diagonal, where `a₁ = y ∘ pr₁`. -/
def diagonalCellFst :
    (D.j ≫ (D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom)) ⟶ D.x :=
  D.γ ▷ (twoFibreProductSquare B S hS f f).fst.hom

/-- The second projection `α₂ : a₂ ∘ j ⟶ x` of the 2-morphism filling a valuative diagram for the
relative diagonal, where `a₂ = y ∘ pr₂`. -/
def diagonalCellSnd :
    (D.j ≫ (D.y ≫ (twoFibreProductSquare B S hS f f).snd.hom)) ⟶ D.x :=
  D.γ ▷ (twoFibreProductSquare B S hS f f).snd.hom

/-- The comparison `φ : f ∘ a₁ ⟶ f ∘ a₂` carried by the special point `y = (a₁, a₂, φ)` of a
valuative diagram for the relative diagonal: the filler of the 2-fibre product square whiskered
into `y`. -/
def diagonalComparisonCell :
    ((D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) ≫ f.hom) ⟶
      ((D.y ≫ (twoFibreProductSquare B S hS f f).snd.hom) ≫ f.hom) :=
  D.y ◁ twoFibreProductCell B S hS f

/-- The 2-morphism filling the square of `f` with top row `x`, bottom row `f ∘ a₁` and right edge
`f`: the pasting of `α₁` with `f`. -/
def diagonalWitness :
    (D.j ≫ ((D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) ≫ f.hom)) ⟶ (D.x ≫ f.hom) :=
  (α_ D.j (D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) f.hom).inv ≫
    (diagonalCellFst B S hS D ▷ f.hom)

/-- **Stacks 0E8L, part (1), first arrow.** The triple `(a₁, α₁, id)` is a dotted arrow for the
square of `f` with top row `x`, bottom row `f ∘ a₁` and right edge `f`. -/
@[stacks 0E8L "part (1): the dotted arrow coming from the first projection"]
def diagonalDottedArrowFst :
    CategoryTheory.DottedArrow D.x D.j f.hom
      ((D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) ≫ f.hom)
      (diagonalWitness B S hS D) where
  a := D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom
  α := diagonalCellFst B S hS D
  β := 𝟙 _
  compat := by rw [diagonalWitness, whiskerLeft_id, Category.id_comp]

/-- **Stacks 0E8L, part (1), second arrow.** The triple `(a₂, α₂, φ)` is a dotted arrow for the
*same* square of `f`: the compatibility triangle is the statement that `γ` is a 2-morphism into
the 2-fibre product, by the exchange law and
`AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal_whiskerLeft_twoFibreProductCell`. -/
@[stacks 0E8L "part (1): the dotted arrow coming from the second projection"]
def diagonalDottedArrowSnd :
    CategoryTheory.DottedArrow D.x D.j f.hom
      ((D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) ≫ f.hom)
      (diagonalWitness B S hS D) where
  a := D.y ≫ (twoFibreProductSquare B S hS f f).snd.hom
  α := diagonalCellSnd B S hS D
  β := diagonalComparisonCell B S hS D
  compat := by
    have hex := whisker_exchange D.γ (twoFibreProductCell B S hS f)
    rw [whiskerLeft_relativeDiagonal_whiskerLeft_twoFibreProductCell B S hS f D.x] at hex
    have key := (hex.trans (Category.comp_id _)).symm
    refine Eq.trans (Category.id_comp
      (D.γ ▷ ((twoFibreProductSquare B S hS f f).fst.hom ≫ f.hom))) (key.trans ?_)
    exact (congrArg (fun t => ((D.j ≫ D.y) ◁ twoFibreProductCell B S hS f) ≫ t)
      (Category.id_comp
        (D.γ ▷ ((twoFibreProductSquare B S hS f f).snd.hom ≫ f.hom)))).symm

/-- The underlying 1-morphism of `diagonalDottedArrowFst` is the first projection `a₁` of `y`. -/
@[simp] theorem diagonalDottedArrowFst_a :
    (diagonalDottedArrowFst B S hS D).a
      = D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom := rfl

/-- The 2-morphism `α` of `diagonalDottedArrowFst` is `diagonalCellFst`. -/
@[simp] theorem diagonalDottedArrowFst_α :
    (diagonalDottedArrowFst B S hS D).α = diagonalCellFst B S hS D := rfl

/-- The 2-morphism `β` of `diagonalDottedArrowFst` is the identity. -/
@[simp] theorem diagonalDottedArrowFst_β :
    (diagonalDottedArrowFst B S hS D).β = 𝟙 _ := rfl

/-- The underlying 1-morphism of `diagonalDottedArrowSnd` is the second projection `a₂` of `y`. -/
@[simp] theorem diagonalDottedArrowSnd_a :
    (diagonalDottedArrowSnd B S hS D).a
      = D.y ≫ (twoFibreProductSquare B S hS f f).snd.hom := rfl

/-- The 2-morphism `α` of `diagonalDottedArrowSnd` is `diagonalCellSnd`. -/
@[simp] theorem diagonalDottedArrowSnd_α :
    (diagonalDottedArrowSnd B S hS D).α = diagonalCellSnd B S hS D := rfl

/-- The 2-morphism `β` of `diagonalDottedArrowSnd` is the comparison
`diagonalComparisonCell`. -/
@[simp] theorem diagonalDottedArrowSnd_β :
    (diagonalDottedArrowSnd B S hS D).β = diagonalComparisonCell B S hS D := rfl

/-! ### The category of dotted arrows of the diagonal square -/

/-- **Stacks 0E8L, part (2), first assertion.** The category of dotted arrows of a valuative
diagram for the relative diagonal of a 1-morphism of algebraic stacks is a setoid.

The relative diagonal is representable by algebraic spaces (Stacks 04XS), hence its underlying
functor is faithful (Stacks 04Y5), and the category of dotted arrows along a faithful 1-morphism
is a thin groupoid. -/
@[stacks 0E8L "part (2): the category of diagonal fillers is a setoid"]
theorem isSetoidCategory_dottedArrow_relativeDiagonal :
    IsSetoidCategory
      (CategoryTheory.DottedArrow D.x D.j (relativeDiagonal B S hS f).hom D.y D.γ) :=
  have : (relativeDiagonal B S hS f).hom.hom.toFunctor.Faithful :=
    faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS (relativeDiagonal B S hS f)
      (Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
  CategoryTheory.isSetoidCategory_dottedArrow_of_faithful

variable (d : CategoryTheory.DottedArrow D.x D.j (relativeDiagonal B S hS f).hom D.y D.γ)

/-- The first projection `β ⋆ pr₁ : a₁ ⟶ a` of the 2-morphism of a dotted arrow `d = (a, α, β)` of
the diagonal square. -/
def diagonalFillerFst :
    (D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) ⟶ d.a :=
  d.β ▷ (twoFibreProductSquare B S hS f f).fst.hom

/-- The second projection `β ⋆ pr₂ : a₂ ⟶ a` of the 2-morphism of a dotted arrow `d = (a, α, β)` of
the diagonal square. -/
def diagonalFillerSnd :
    (D.y ≫ (twoFibreProductSquare B S hS f f).snd.hom) ⟶ d.a :=
  d.β ▷ (twoFibreProductSquare B S hS f f).snd.hom

/-- Inserting an identity in a composite does not change an equation. -/
private theorem eq_comp_id_comp_iff {C : Type*} [Category C] {X Y Z : C} (w : X ⟶ Z) (u : X ⟶ Y)
    (v : Y ⟶ Z) : w = u ≫ 𝟙 Y ≫ v ↔ w = u ≫ v := by
  rw [Category.id_comp]

/-- **The first projection of a dotted arrow of the diagonal square relates `α₁` to its own `α`.**
This is the first projection of its compatibility triangle. -/
theorem diagonalCellFst_eq :
    diagonalCellFst B S hS D = (D.j ◁ diagonalFillerFst B S hS D d) ≫ d.α := by
  refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
  funext z
  have h := congrArg (fun η => (η.hom.app z).a) d.compat
  change (D.γ.hom.app z).a
    = (d.β.hom.app (D.j.hom.obj z)).a ≫ 𝟙 _ ≫ d.α.hom.app z at h
  show (D.γ.hom.app z).a = (d.β.hom.app (D.j.hom.obj z)).a ≫ d.α.hom.app z
  exact (eq_comp_id_comp_iff _ _ _).1 h

/-- **The second projection of a dotted arrow of the diagonal square relates `α₂` to its own `α`.**
This is the second projection of its compatibility triangle. -/
theorem diagonalCellSnd_eq :
    diagonalCellSnd B S hS D = (D.j ◁ diagonalFillerSnd B S hS D d) ≫ d.α := by
  refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
  funext z
  have h := congrArg (fun η => (η.hom.app z).b) d.compat
  change (D.γ.hom.app z).b
    = (d.β.hom.app (D.j.hom.obj z)).b ≫ 𝟙 _ ≫ d.α.hom.app z at h
  show (D.γ.hom.app z).b = (d.β.hom.app (D.j.hom.obj z)).b ≫ d.α.hom.app z
  exact (eq_comp_id_comp_iff _ _ _).1 h

/-- **The comparison `φ` becomes trivial on the projections of a dotted arrow of the diagonal
square**, since the point it compares to carries the identity comparison. -/
theorem diagonalComparisonCell_comp :
    diagonalComparisonCell B S hS D ≫ (diagonalFillerSnd B S hS D d ▷ f.hom)
      = diagonalFillerFst B S hS D d ▷ f.hom := by
  have hex := whisker_exchange d.β (twoFibreProductCell B S hS f)
  rw [whiskerLeft_relativeDiagonal_whiskerLeft_twoFibreProductCell B S hS f d.a] at hex
  exact hex.trans (Category.comp_id _)

/-- The 2-morphism `a₁ ⟶ a₂` read off a dotted arrow `d` of the diagonal square: the first
projection of its 2-morphism followed by the inverse of the second. -/
noncomputable def diagonalFillerCell :
    (D.y ≫ (twoFibreProductSquare B S hS f f).fst.hom) ⟶
      (D.y ≫ (twoFibreProductSquare B S hS f f).snd.hom) :=
  diagonalFillerFst B S hS D d ≫ inv (diagonalFillerSnd B S hS D d)

/-- **A dotted arrow of the diagonal square induces a morphism of the two dotted arrows for `f`.**
Its underlying 2-morphism is `AlgebraicGeometry.Stack.AlgebraicStacks.diagonalFillerCell`. -/
noncomputable def diagonalDottedArrowHom :
    diagonalDottedArrowFst B S hS D ⟶ diagonalDottedArrowSnd B S hS D where
  θ := diagonalFillerCell B S hS D d
  cond_α := by
    change diagonalCellFst B S hS D
      = (D.j ◁ diagonalFillerCell B S hS D d) ≫ diagonalCellSnd B S hS D
    rw [diagonalCellFst_eq B S hS D d, diagonalCellSnd_eq B S hS D d, diagonalFillerCell,
      whiskerLeft_comp, Category.assoc,
      ← Category.assoc (D.j ◁ inv (diagonalFillerSnd B S hS D d)), ← whiskerLeft_comp,
      IsIso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  cond_β := by
    change diagonalComparisonCell B S hS D
      = 𝟙 _ ≫ (diagonalFillerCell B S hS D d ▷ f.hom)
    rw [Category.id_comp, diagonalFillerCell, comp_whiskerRight, ← inv_whiskerRight,
      IsIso.eq_comp_inv]
    exact diagonalComparisonCell_comp B S hS D d

/-- The underlying 2-morphism of `diagonalDottedArrowHom` is `diagonalFillerCell`. -/
@[simp] theorem diagonalDottedArrowHom_θ :
    (diagonalDottedArrowHom B S hS D d).θ = diagonalFillerCell B S hS D d := rfl

/-- **A compatible pair of projections assembles into a dotted arrow of the diagonal square.** A
2-morphism into the 2-fibre product is a pair of 2-morphisms into the two factors, so the
compatibility triangle for `γ` is the conjunction of its two projections. -/
def dottedArrowOfProjections
    (a : schemeFibredCategory B S hS D.whole ⟶ 𝒳.val) (α : (D.j ≫ a) ⟶ D.x)
    (β : D.y ⟶ (a ≫ (relativeDiagonal B S hS f).hom))
    (h₁ : diagonalCellFst B S hS D
      = (D.j ◁ (β ▷ (twoFibreProductSquare B S hS f f).fst.hom)) ≫ α)
    (h₂ : diagonalCellSnd B S hS D
      = (D.j ◁ (β ▷ (twoFibreProductSquare B S hS f f).snd.hom)) ≫ α) :
    CategoryTheory.DottedArrow D.x D.j (relativeDiagonal B S hS f).hom D.y D.γ where
  a := a
  α := α
  β := β
  compat := by
    refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
    funext z
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · have h := congrArg (fun η => η.hom.app z) h₁
      change (D.γ.hom.app z).a = (β.hom.app (D.j.hom.obj z)).a ≫ α.hom.app z at h
      change (D.γ.hom.app z).a = (β.hom.app (D.j.hom.obj z)).a ≫ 𝟙 _ ≫ α.hom.app z
      exact h.trans (congrArg (fun t => (β.hom.app (D.j.hom.obj z)).a ≫ t)
        (Category.id_comp (α.hom.app z))).symm
    · have h := congrArg (fun η => η.hom.app z) h₂
      change (D.γ.hom.app z).b = (β.hom.app (D.j.hom.obj z)).b ≫ α.hom.app z at h
      change (D.γ.hom.app z).b = (β.hom.app (D.j.hom.obj z)).b ≫ 𝟙 _ ≫ α.hom.app z
      exact h.trans (congrArg (fun t => (β.hom.app (D.j.hom.obj z)).b ≫ t)
        (Category.id_comp (α.hom.app z))).symm

/-! ### Isomorphism classes of dotted arrows of the diagonal square -/

section Compare

variable {d₁ d₂ : CategoryTheory.DottedArrow D.x D.j (relativeDiagonal B S hS f).hom D.y D.γ}

/-- Along a morphism of dotted arrows of the diagonal square, the first projections compose. -/
theorem diagonalFillerFst_comp (ψ : d₁ ⟶ d₂) :
    diagonalFillerFst B S hS D d₂ = diagonalFillerFst B S hS D d₁ ≫ ψ.θ := by
  show d₂.β ▷ (twoFibreProductSquare B S hS f f).fst.hom
    = (d₁.β ▷ (twoFibreProductSquare B S hS f f).fst.hom) ≫ ψ.θ
  rw [ψ.cond_β, comp_whiskerRight, whiskerRight_relativeDiagonal_whiskerRight_fst]
  rfl

/-- Along a morphism of dotted arrows of the diagonal square, the second projections compose. -/
theorem diagonalFillerSnd_comp (ψ : d₁ ⟶ d₂) :
    diagonalFillerSnd B S hS D d₂ = diagonalFillerSnd B S hS D d₁ ≫ ψ.θ := by
  show d₂.β ▷ (twoFibreProductSquare B S hS f f).snd.hom
    = (d₁.β ▷ (twoFibreProductSquare B S hS f f).snd.hom) ≫ ψ.θ
  rw [ψ.cond_β, comp_whiskerRight, whiskerRight_relativeDiagonal_whiskerRight_snd]
  rfl

/-- **A 2-morphism of dotted arrows of the diagonal square is recognised by its projections.**
The two projections of the 2-fibre product jointly detect 2-morphisms into its apex. -/
theorem beta_eq_of_fillers (θ : d₁.a ⟶ d₂.a)
    (h₁ : diagonalFillerFst B S hS D d₂ = diagonalFillerFst B S hS D d₁ ≫ θ)
    (h₂ : diagonalFillerSnd B S hS D d₂ = diagonalFillerSnd B S hS D d₁ ≫ θ) :
    d₂.β = d₁.β ≫ (θ ▷ (relativeDiagonal B S hS f).hom) := by
  refine CatFiberedInGroupoids.hom₂_ext_of_whiskerRight_twoFibreProductSquare.{u, u, u + 1,
    u + 1} ?_ ?_
  · show diagonalFillerFst B S hS D d₂
      = (d₁.β ≫ (θ ▷ (relativeDiagonal B S hS f).hom))
          ▷ (twoFibreProductSquare B S hS f f).fst.hom
    rwa [comp_whiskerRight, whiskerRight_relativeDiagonal_whiskerRight_fst]
  · show diagonalFillerSnd B S hS D d₂
      = (d₁.β ≫ (θ ▷ (relativeDiagonal B S hS f).hom))
          ▷ (twoFibreProductSquare B S hS f f).snd.hom
    rwa [comp_whiskerRight, whiskerRight_relativeDiagonal_whiskerRight_snd]

/-- **Isomorphic dotted arrows of the diagonal square induce the same morphism for `f`.** -/
theorem diagonalDottedArrowHom_congr (ψ : d₁ ⟶ d₂) :
    diagonalDottedArrowHom B S hS D d₁ = diagonalDottedArrowHom B S hS D d₂ := by
  refine CategoryTheory.DottedArrow.Hom.ext ?_
  show diagonalFillerCell B S hS D d₁ = diagonalFillerCell B S hS D d₂
  simp only [diagonalFillerCell, diagonalFillerFst_comp B S hS D ψ,
    diagonalFillerSnd_comp B S hS D ψ, IsIso.inv_comp]
  simp

/-- **Two dotted arrows of the diagonal square inducing the same morphism for `f` are isomorphic.**
The isomorphism is `(β₁ ⋆ pr₁)⁻¹` followed by `β₂ ⋆ pr₁`; the hypothesis says that this agrees with
the same expression formed from the second projections. -/
theorem nonempty_iso_of_diagonalDottedArrowHom_eq
    (h : diagonalDottedArrowHom B S hS D d₁ = diagonalDottedArrowHom B S hS D d₂) :
    Nonempty (d₁ ≅ d₂) := by
  have hθ : diagonalFillerFst B S hS D d₁ ≫ inv (diagonalFillerSnd B S hS D d₁)
      = diagonalFillerFst B S hS D d₂ ≫ inv (diagonalFillerSnd B S hS D d₂) :=
    congrArg CategoryTheory.DottedArrow.Hom.θ h
  have hkey : inv (diagonalFillerFst B S hS D d₁) ≫ diagonalFillerFst B S hS D d₂
      = inv (diagonalFillerSnd B S hS D d₁) ≫ diagonalFillerSnd B S hS D d₂ := by
    calc inv (diagonalFillerFst B S hS D d₁) ≫ diagonalFillerFst B S hS D d₂
        = inv (diagonalFillerFst B S hS D d₁) ≫
            (diagonalFillerFst B S hS D d₂ ≫ inv (diagonalFillerSnd B S hS D d₂)) ≫
              diagonalFillerSnd B S hS D d₂ := by simp
      _ = inv (diagonalFillerFst B S hS D d₁) ≫
            (diagonalFillerFst B S hS D d₁ ≫ inv (diagonalFillerSnd B S hS D d₁)) ≫
              diagonalFillerSnd B S hS D d₂ := by rw [hθ]
      _ = inv (diagonalFillerSnd B S hS D d₁) ≫ diagonalFillerSnd B S hS D d₂ := by simp
  have e := (diagonalCellFst_eq B S hS D d₁).symm.trans (diagonalCellFst_eq B S hS D d₂)
  let ψ : d₁ ⟶ d₂ :=
    { θ := inv (diagonalFillerFst B S hS D d₁) ≫ diagonalFillerFst B S hS D d₂
      cond_α := by
        rw [whiskerLeft_comp, Category.assoc, ← e, ← Category.assoc, ← whiskerLeft_comp,
          IsIso.inv_hom_id, whiskerLeft_id, Category.id_comp]
      cond_β := beta_eq_of_fillers B S hS D _ (by simp) (by simp [hkey]) }
  have := (isSetoidCategory_dottedArrow_relativeDiagonal B S hS D).1 ψ
  exact ⟨asIso ψ⟩

/-- **Every morphism of the two dotted arrows for `f` comes from a dotted arrow of the diagonal
square.** The 2-morphism of the dotted arrow is produced from the pair `(θ, id)` by joint fullness
of the two projections of the 2-fibre product on invertible 2-cells. -/
theorem exists_diagonalDottedArrowHom_eq
    (m : diagonalDottedArrowFst B S hS D ⟶ diagonalDottedArrowSnd B S hS D) :
    ∃ e, diagonalDottedArrowHom B S hS D e = m := by
  have hP : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom f.hom) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom f.hom
  have hmiso : IsIso m.θ := (CatFiberedInGroupoids.homGroupoid _ _).all_isIso _
  have hex := Bicategory.twoFibreProduct_jointlyFaithful hP D.y
    ((D.y ≫ (twoFibreProductSquare B S hS f f).snd.hom) ≫ (relativeDiagonal B S hS f).hom)
    (@asIso _ _ _ _ m.θ hmiso) (Iso.refl _) (by
      refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
      funext z
      have h := congrArg (fun η => η.hom.app z) m.cond_β
      change (D.y.hom.obj z).iso.hom = 𝟙 _ ≫ f.hom.hom.map (m.θ.hom.app z) at h
      show (𝟙 _ ≫ (D.y.hom.obj z).iso.hom ≫ 𝟙 _) ≫ f.hom.hom.map (𝟙 _)
        = f.hom.hom.map (m.θ.hom.app z) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
      simpa using h)
  obtain ⟨θ, hθ₁, hθ₂⟩ := hex
  have h₁ : diagonalCellFst B S hS D
      = (D.j ◁ (θ.hom ▷ (twoFibreProductSquare B S hS f f).fst.hom))
        ≫ diagonalCellSnd B S hS D := by
    rw [show θ.hom ▷ (twoFibreProductSquare B S hS f f).fst.hom = m.θ from hθ₁]
    exact m.cond_α
  have h₂ : diagonalCellSnd B S hS D
      = (D.j ◁ (θ.hom ▷ (twoFibreProductSquare B S hS f f).snd.hom))
        ≫ diagonalCellSnd B S hS D := by
    rw [show θ.hom ▷ (twoFibreProductSquare B S hS f f).snd.hom
      = 𝟙 (D.y ≫ (twoFibreProductSquare B S hS f f).snd.hom) from hθ₂]
    exact ((congrArg (fun t => t ≫ diagonalCellSnd B S hS D)
      (whiskerLeft_id D.j (D.y ≫ (twoFibreProductSquare B S hS f f).snd.hom))).trans
      (Category.id_comp (diagonalCellSnd B S hS D))).symm
  refine ⟨dottedArrowOfProjections B S hS D _ (diagonalCellSnd B S hS D) θ.hom h₁ h₂,
    CategoryTheory.DottedArrow.Hom.ext ?_⟩
  have hs : diagonalFillerSnd B S hS D (dottedArrowOfProjections B S hS D _
      (diagonalCellSnd B S hS D) θ.hom h₁ h₂)
      = 𝟙 (D.y ≫ (twoFibreProductSquare B S hS f f).snd.hom) := hθ₂
  have hf : diagonalFillerFst B S hS D (dottedArrowOfProjections B S hS D _
      (diagonalCellSnd B S hS D) θ.hom h₁ h₂) = m.θ := hθ₁
  rw [diagonalDottedArrowHom_θ, diagonalFillerCell, hf]
  simp only [hs]
  exact (congrArg (fun t => m.θ ≫ t) IsIso.inv_id).trans (Category.comp_id m.θ)

/-- **Stacks 0E8L, part (2), second assertion.** The isomorphism classes of dotted arrows of a
valuative diagram for the relative diagonal of `f` correspond bijectively to the morphisms
`(a₁, α₁, id) ⟶ (a₂, α₂, φ)` of dotted arrows for `f`, by `d ↦ (β ⋆ pr₁) ∘ (β ⋆ pr₂)⁻¹`. -/
@[stacks 0E8L "part (2): isomorphism classes are the morphisms between the two dotted arrows"]
noncomputable def diagonalDottedArrowClassesEquiv :
    Quotient (isIsomorphicSetoid
        (CategoryTheory.DottedArrow D.x D.j (relativeDiagonal B S hS f).hom D.y D.γ)) ≃
      (diagonalDottedArrowFst B S hS D ⟶ diagonalDottedArrowSnd B S hS D) := by
  refine Equiv.ofBijective (Quotient.lift (diagonalDottedArrowHom B S hS D)
    (fun _ _ h => diagonalDottedArrowHom_congr B S hS D (Nonempty.some h).hom)) ⟨?_, ?_⟩
  · intro a b h
    obtain ⟨e₁, rfl⟩ := Quotient.exists_rep a
    obtain ⟨e₂, rfl⟩ := Quotient.exists_rep b
    exact Quotient.sound (nonempty_iso_of_diagonalDottedArrowHom_eq B S hS D h)
  · intro m
    obtain ⟨e, he⟩ := exists_diagonalDottedArrowHom_eq B S hS D m
    exact ⟨Quotient.mk _ e, he⟩

/-- `diagonalDottedArrowClassesEquiv` sends the class of a dotted arrow `e` to
`diagonalDottedArrowHom e`. -/
@[simp] theorem diagonalDottedArrowClassesEquiv_mk
    (e : CategoryTheory.DottedArrow D.x D.j (relativeDiagonal B S hS f).hom D.y D.γ) :
    diagonalDottedArrowClassesEquiv B S hS D (Quotient.mk _ e)
      = diagonalDottedArrowHom B S hS D e := rfl

end Compare

end AlgebraicGeometry.Stack.AlgebraicStacks

end
