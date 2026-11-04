module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Isomorphisms of functors into a slice category

A functor `F : A ⥤ Over X` is the same data as a functor `F ⋙ Over.forget X : A ⥤ C` together
with a natural transformation from it to the constant functor `X`.  Accordingly an isomorphism
`F ≅ G` of functors into `Over X` is *not* the same as an isomorphism of the underlying functors:
`Over.forget X` is faithful but not full, so an isomorphism `β : F ⋙ Over.forget X ≅
G ⋙ Over.forget X` lifts to `Over X` exactly when it commutes with the two structure maps to `X`.
`natIsoOfForgetIso` records that this triangle is the only obligation — naturality in `Over X` is
free, because `Over.forget X` is faithful.

The point of the file is `comp_hom_of_terminal`: when `A` has a terminal object the triangles for
all objects of `A` follow from the single triangle at the terminal object. Indeed the structure map
of `F.obj a` factors through the structure map of `F.obj (⊤_ A)` along `F.map (terminal.from a)`
(this is `Over.w`), so naturality of `β` at `terminal.from a` propagates the triangle at `⊤_ A` to
every `a`. Consequently `natIsoOfForgetIsoTerminal` builds the isomorphism in `Over X` from an
isomorphism of the underlying functors plus one equation of morphisms.

This is what makes the "cancel `j_{U!}`" step in Stacks 7.28 an equation rather than an exactness
statement; see `StacksFrontier.CategoryTheory.Sites.SliceTopos.InverseImage`.

## Main results

* `CategoryTheory.Over.natIsoOfForgetIso`: an isomorphism of the underlying functors which commutes
  with the structure maps is an isomorphism of functors into `Over X`.
* `CategoryTheory.Over.comp_hom_of_terminal`: the triangle at a terminal object implies the
  triangle everywhere.
* `CategoryTheory.Over.natIsoOfForgetIsoTerminal`: the combination of the two.
-/

@[expose] public section

namespace CategoryTheory.Over

open Limits

universe v u v' u'

variable {A : Type u} [Category.{v} A] {C : Type u'} [Category.{v'} C] {X : C}
  {F G : A ⥤ Over X}

/-- An isomorphism `β` of the underlying functors of `F G : A ⥤ Over X` which commutes with the
structure maps to `X` is an isomorphism `F ≅ G` in `A ⥤ Over X`.

Only the triangles are an obligation: naturality of the lifted family holds because
`Over.forget X` is faithful, so it suffices to know naturality of `β`. -/
def natIsoOfForgetIso (β : F ⋙ forget X ≅ G ⋙ forget X)
    (h : ∀ a, β.hom.app a ≫ (G.obj a).hom = (F.obj a).hom) : F ≅ G :=
  NatIso.ofComponents (fun a => Over.isoMk (β.app a) (h a))
    (fun f => Over.OverMorphism.ext (β.hom.naturality f))

/-- **The triangle at a terminal object suffices.**  If `A` has a terminal object and
`β : F ⋙ Over.forget X ≅ G ⋙ Over.forget X` commutes with the structure maps at `⊤_ A`, then it
commutes with them at every object.

The structure map of `F.obj a` is `(F.map (terminal.from a)).left ≫ (F.obj (⊤_ A)).hom` by
`Over.w`, and likewise for `G`; naturality of `β` at `terminal.from a` interchanges the two. -/
lemma comp_hom_of_terminal [HasTerminal A] (β : F ⋙ forget X ≅ G ⋙ forget X)
    (h : β.hom.app (⊤_ A) ≫ (G.obj (⊤_ A)).hom = (F.obj (⊤_ A)).hom) (a : A) :
    β.hom.app a ≫ (G.obj a).hom = (F.obj a).hom := by
  have hG : (G.map (terminal.from a)).left ≫ (G.obj (⊤_ A)).hom = (G.obj a).hom :=
    Over.w (G.map (terminal.from a))
  have hF : (F.map (terminal.from a)).left ≫ (F.obj (⊤_ A)).hom = (F.obj a).hom :=
    Over.w (F.map (terminal.from a))
  have hnat : β.hom.app a ≫ (G.map (terminal.from a)).left =
      (F.map (terminal.from a)).left ≫ β.hom.app (⊤_ A) :=
    (β.hom.naturality (terminal.from a)).symm
  rw [← hG, ← hF, ← Category.assoc, hnat, Category.assoc, h]

/-- `natIsoOfForgetIso` with the triangle checked only at a terminal object. -/
def natIsoOfForgetIsoTerminal [HasTerminal A] (β : F ⋙ forget X ≅ G ⋙ forget X)
    (h : β.hom.app (⊤_ A) ≫ (G.obj (⊤_ A)).hom = (F.obj (⊤_ A)).hom) : F ≅ G :=
  natIsoOfForgetIso β (comp_hom_of_terminal β h)

/-- The structure map of a terminal object of `Over X` is an isomorphism: a terminal object is
isomorphic to `Over.mk (𝟙 X)`, and the underlying morphism of that isomorphism *is* the structure
map, by `Over.w`. -/
lemma isIso_hom_of_isTerminal {T : Over X} (hT : IsTerminal T) : IsIso T.hom := by
  have h : (hT.uniqueUpToIso Over.mkIdTerminal).hom.left = T.hom := by
    simp
  exact h ▸ inferInstanceAs (IsIso ((forget X).mapIso
    (hT.uniqueUpToIso (Over.mkIdTerminal (X := X)))).hom)

end CategoryTheory.Over
