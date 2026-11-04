module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Commuting squares of commutative group objects

A commuting square of braided functors induces one on commutative group objects, and such a
square can be transported through dictionaries presenting the four categories involved as
categories of commutative group objects.

## Main definitions

* `CategoryTheory.Functor.mapCommGrpSquare` — a commuting square of braided functors induces a
  commuting square of the induced functors on commutative group objects.
* `CategoryTheory.commGrpTransportSquare` — the same square read through four dictionaries, two
  presenting the sources as commutative group objects and two the targets.

## Implementation notes

`CategoryTheory.commGrpTransportSquare` is the shape in which a commuting square of equivalences
is transported from a cartesian setting to a commutative-group setting: the horizontal
equivalences `e₁` and `e₂` contribute only through `CategoryTheory.Functor.mapCommGrp`, so a
square of them transports as soon as the two vertical functors are compared with their
commutative-group counterparts through the dictionaries. This is what Stacks Tag 0DV6 for
sheaves of abelian groups is deduced from, its sheaves-of-sets case supplying `α`.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ v₁' v₂' v₃' v₄' u₁ u₂ u₃ u₄ u₁' u₂' u₃' u₄'

section Square

variable {A₁ : Type u₁} [Category.{v₁} A₁] [CartesianMonoidalCategory A₁] [BraidedCategory A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [CartesianMonoidalCategory A₂] [BraidedCategory A₂]
  {B₁ : Type u₃} [Category.{v₃} B₁] [CartesianMonoidalCategory B₁] [BraidedCategory B₁]
  {B₂ : Type u₄} [Category.{v₄} B₂] [CartesianMonoidalCategory B₂] [BraidedCategory B₂]

/-- **A commuting square of braided functors induces a commuting square on commutative group
objects.** -/
noncomputable def Functor.mapCommGrpSquare {F : A₁ ⥤ B₁} [F.Braided] {G : B₁ ⥤ B₂} [G.Braided]
    {H : A₁ ⥤ A₂} [H.Braided] {K : A₂ ⥤ B₂} [K.Braided] (α : F ⋙ G ≅ H ⋙ K) :
    F.mapCommGrp ⋙ G.mapCommGrp ≅ H.mapCommGrp ⋙ K.mapCommGrp :=
  (Functor.mapCommGrpCompIso (F := F) (G := G)).symm ≪≫
    Functor.mapCommGrpNatIso α ≪≫ Functor.mapCommGrpCompIso (F := H) (G := K)

end Square

section Transport

variable {A₁ : Type u₁} [Category.{v₁} A₁] [CartesianMonoidalCategory A₁] [BraidedCategory A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [CartesianMonoidalCategory A₂] [BraidedCategory A₂]
  {B₁ : Type u₃} [Category.{v₃} B₁] [CartesianMonoidalCategory B₁] [BraidedCategory B₁]
  {B₂ : Type u₄} [Category.{v₄} B₂] [CartesianMonoidalCategory B₂] [BraidedCategory B₂]
  {A₁' : Type u₁'} [Category.{v₁'} A₁'] {A₂' : Type u₂'} [Category.{v₂'} A₂']
  {B₁' : Type u₃'} [Category.{v₃'} B₁'] {B₂' : Type u₄'} [Category.{v₄'} B₂']

/-- **Transport a commuting square of braided functors through the dictionaries presenting four
categories as commutative group objects.** The horizontal equivalences `e₁` and `e₂` enter only
through `CategoryTheory.Functor.mapCommGrp`, so the square of commutative group objects they
induce is the given one; the two vertical functors `Pab` and `Rab` are matched with their
cartesian counterparts by `h₁` and `h₂`. -/
noncomputable def commGrpTransportSquare
    (Φ₁ : A₁' ≌ CommGrp A₁) (Φ₂ : A₂' ≌ CommGrp A₂)
    (Ψ₁ : CommGrp B₁ ≌ B₁') (Ψ₂ : CommGrp B₂ ≌ B₂')
    {e₁ : A₁ ≌ B₁} [e₁.functor.Braided] {e₂ : A₂ ≌ B₂} [e₂.functor.Braided]
    {P : A₁ ⥤ A₂} [P.Braided] {R : B₁ ⥤ B₂} [R.Braided]
    {Pab : A₁' ⥤ A₂'} {Rab : B₁' ⥤ B₂'}
    (h₁ : Pab ⋙ Φ₂.functor ≅ Φ₁.functor ⋙ P.mapCommGrp)
    (h₂ : R.mapCommGrp ⋙ Ψ₂.functor ≅ Ψ₁.functor ⋙ Rab)
    (α : e₁.functor ⋙ R ≅ P ⋙ e₂.functor) :
    (Φ₁.functor ⋙ e₁.functor.mapCommGrp ⋙ Ψ₁.functor) ⋙ Rab ≅
      Pab ⋙ (Φ₂.functor ⋙ e₂.functor.mapCommGrp ⋙ Ψ₂.functor) :=
  Functor.isoWhiskerLeft (Φ₁.functor ⋙ e₁.functor.mapCommGrp) h₂.symm ≪≫
    Functor.isoWhiskerLeft Φ₁.functor
      (Functor.isoWhiskerRight (Functor.mapCommGrpSquare α) Ψ₂.functor) ≪≫
    Functor.isoWhiskerRight h₁.symm (e₂.functor.mapCommGrp ⋙ Ψ₂.functor)

end Transport

end CategoryTheory

end
