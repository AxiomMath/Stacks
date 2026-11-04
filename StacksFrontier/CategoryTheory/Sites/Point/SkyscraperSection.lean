module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber

/-!
# The counit of the skyscraper adjunction at a point of a site is split

Let `Φ` be a point of a site `(C, J)` and `A` a category with the products and colimits the
skyscraper adjunction `Φ.sheafFiber ⊣ Φ.skyscraperSheafFunctor` needs. Every object `M` of `A` is
a retract of the stalk `(Φ_* M)_Φ` of its skyscraper sheaf, naturally in `M`: the counit
`(Φ_* M)_Φ ⟶ M` has the natural section which sends `M` diagonally into the sections
`∏_{x ∈ Φ(U)} M` of the skyscraper over one fixed neighbourhood `(U, x)` of `Φ` and then to the
stalk; equivalently, the stalk of the diagonal morphism from the constant presheaf with value
`M` to the skyscraper presheaf. On a neighbourhood the counit is the projection to the factor
indexed by `x`, so the composite is the identity.

This is the retract that reduces K-flatness of the stalk of a K-flat complex of sheaves to
K-flatness of the complex itself ([Stacks, Tag 06YB]): an acyclic complex `N` of objects of `A`
is a retract of the stalk of the skyscraper complex of `N`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.skyscraperSection`: the natural section of the
  counit.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.skyscraperSection_comp_counit`: it is a section.
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]

omit [HasProducts A] in
/-- The identification of the stalk of a constant presheaf with its value is natural in the
value. -/
lemma constantPresheafFiberIso_hom_naturality {M N : A} (f : M ⟶ N) :
    (Sites.constantPresheafFiberIso Φ M).hom ≫ f =
      Φ.presheafFiber.map ((Functor.const Cᵒᵖ).map f) ≫
        (Sites.constantPresheafFiberIso Φ N).hom := by
  apply Φ.presheafFiber_hom_ext
  intro V q
  rw [reassoc_of% Sites.constantPresheafFiberIso_ι, toPresheafFiber_naturality_assoc,
    Sites.constantPresheafFiberIso_ι]
  simp

/-- The natural map `M ⟶ (Φ_* M)_Φ` from an object to the stalk of its skyscraper sheaf: the
identification of `M` with the stalk of the constant presheaf, followed by the stalk of the
morphism from the constant presheaf to the skyscraper presheaf adjoint to that identification
(over `U` it is the diagonal `M ⟶ ∏_{x ∈ Φ(U)} M`). -/
noncomputable def skyscraperSection :
    𝟭 A ⟶ Φ.skyscraperSheafFunctor ⋙ Φ.sheafFiber where
  app M := (Sites.constantPresheafFiberIso Φ M).inv ≫
    Φ.presheafFiber.map (Φ.skyscraperPresheafHomEquiv (Sites.constantPresheafFiberIso Φ M).hom)
  naturality M N f := by
    change f ≫ (Sites.constantPresheafFiberIso Φ N).inv ≫ Φ.presheafFiber.map
          (Φ.skyscraperPresheafHomEquiv (Sites.constantPresheafFiberIso Φ N).hom) =
        ((Sites.constantPresheafFiberIso Φ M).inv ≫ Φ.presheafFiber.map
        (Φ.skyscraperPresheafHomEquiv (Sites.constantPresheafFiberIso Φ M).hom)) ≫
          Φ.presheafFiber.map (Φ.skyscraperPresheafFunctor.map f)
    symm
    rw [Category.assoc, ← Functor.map_comp, ← skyscraperPresheafHomEquiv_naturality_right,
      constantPresheafFiberIso_hom_naturality, skyscraperPresheafHomEquiv_naturality_left,
      Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [Iso.inv_comp_eq, ← Category.assoc, constantPresheafFiberIso_hom_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The counit of the skyscraper adjunction is split** by `skyscraperSection`. -/
@[reassoc (attr := simp)]
lemma skyscraperSection_comp_counit (M : A) :
    Φ.skyscraperSection.app M ≫ Φ.skyscraperSheafAdjunction.counit.app M = 𝟙 M := by
  show ((Sites.constantPresheafFiberIso Φ M).inv ≫
    Φ.presheafFiber.map (Φ.skyscraperPresheafHomEquiv (Sites.constantPresheafFiberIso Φ M).hom)) ≫
      Φ.skyscraperPresheafHomEquiv.symm (𝟙 (Φ.skyscraperPresheaf M)) = 𝟙 M
  rw [Category.assoc, ← skyscraperPresheafHomEquiv_naturality_left_symm, Category.comp_id,
    Equiv.symm_apply_apply, Iso.inv_hom_id]

end CategoryTheory.GrothendieckTopology.Point
