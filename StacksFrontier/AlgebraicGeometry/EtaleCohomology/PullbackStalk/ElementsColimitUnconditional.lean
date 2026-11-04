module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ElementsColimit
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ElementsColimit

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Colimits over categories of elements, for arbitrary coefficient universes

For functors `P Q : C ⥤ Type u` and an isomorphism `e : P ≅ Q`, the functors on presheaves
(and on sheaves) of types in an arbitrary universe given by taking the colimit over the opposite
of the category of elements are isomorphic, compatibly with the colimit inclusions.

These generalise declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ElementsColimit` to arbitrary
coefficient universes.

## Main definitions

* `CategoryTheory.CategoryOfElements.presheafColimIsoOfNatIsoGeneral`: The isomorphism between
  the colimit-over-elements functors on presheaves induced by `e : P ≅ Q`.
* `CategoryTheory.CategoryOfElements.sheafColimIsoOfNatIsoGeneral`: The corresponding
  isomorphism between the colimit-over-elements functors on sheaves.

## Main results

* `CategoryTheory.CategoryOfElements.ι_presheafColimIsoOfNatIso_hom_general`: The isomorphism
  sends the colimit inclusion at an element to the inclusion at the transported element.
* `CategoryTheory.CategoryOfElements.ι_sheafColimIsoOfNatIso_hom_general`: The same
  compatibility for sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w v' u' t

namespace CategoryTheory.CategoryOfElements

variable {C : Type v} [Category.{w} C] {P Q : C ⥤ Type u}

variable [HasColimitsOfShape P.Elementsᵒᵖ (Type t)]
  [HasColimitsOfShape Q.Elementsᵒᵖ (Type t)]

/-- The stalk functor on presheaves given by taking the colimit over a category of elements
depends on the indexing functor only through its isomorphism class. -/
public def presheafColimIsoOfNatIsoGeneral (e : P ≅ Q) :
    (Functor.whiskeringLeft P.Elementsᵒᵖ Cᵒᵖ (Type t)).obj
        (CategoryOfElements.π P).op ⋙ colim ≅
      (Functor.whiskeringLeft Q.Elementsᵒᵖ Cᵒᵖ (Type t)).obj
        (CategoryOfElements.π Q).op ⋙ colim :=
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft Q.Elementsᵒᵖ Cᵒᵖ (Type t)).obj (CategoryOfElements.π Q).op)
    (Functor.Final.colimIso (equivalenceOfNatIso e).op.functor)

/-- The comparison of stalk functors on presheaves sends the colimit inclusion at an element to
the colimit inclusion at the transported element. -/
@[reassoc]
public lemma ι_presheafColimIsoOfNatIso_hom_general (e : P ≅ Q) (F : Cᵒᵖ ⥤ Type t)
    (X : P.Elementsᵒᵖ) :
    colimit.ι ((CategoryOfElements.π P).op ⋙ F) X ≫
        (presheafColimIsoOfNatIsoGeneral e).hom.app F =
      colimit.ι ((CategoryOfElements.π Q).op ⋙ F)
        ((equivalenceOfNatIso e).op.functor.obj X) :=
  Functor.Final.ι_colimitIso_hom (equivalenceOfNatIso e).op.functor
    ((CategoryOfElements.π Q).op ⋙ F) X

/-- The stalk functor on sheaves given by taking the colimit over a category of elements
depends on the indexing functor only through its isomorphism class. -/
public def sheafColimIsoOfNatIsoGeneral (J : GrothendieckTopology C) (e : P ≅ Q) :
    (sheafToPresheaf J (Type t) ⋙
      (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π P).op ⋙ colim) ≅
    (sheafToPresheaf J (Type t) ⋙
      (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Q).op ⋙ colim) :=
  Functor.isoWhiskerLeft (sheafToPresheaf J (Type t)) (presheafColimIsoOfNatIsoGeneral e)

/-- The comparison of stalk functors on sheaves sends the germ of a section at an element to
its germ at the transported element. -/
public lemma ι_sheafColimIsoOfNatIso_hom_general (J : GrothendieckTopology C) (e : P ≅ Q)
    (F : Sheaf J (Type t)) (V : P.Elements) :
    colimit.ι ((CategoryOfElements.π P).op ⋙ F.obj) (Opposite.op V) ≫
      (sheafColimIsoOfNatIsoGeneral J e).hom.app F =
    colimit.ι ((CategoryOfElements.π Q).op ⋙ F.obj)
      (Opposite.op ((CategoryOfElements.map e.hom).obj V)) :=
  ι_presheafColimIsoOfNatIso_hom_general e F.obj (Opposite.op V)

end CategoryTheory.CategoryOfElements

namespace CategoryTheory.GrothendieckTopology.Point

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryOfElements

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{u, u} A]

end CategoryTheory.GrothendieckTopology.Point


end
