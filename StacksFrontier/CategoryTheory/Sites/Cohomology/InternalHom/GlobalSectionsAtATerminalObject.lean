module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex

/-!
# Global sections on a site with a terminal object

Let `(C, J)` be a site whose underlying category has a terminal object `T`. The global sections
of a sheaf `F` of abelian groups on `C` — the compatible families of sections of `F` over all
the objects of `C`, which is the spelling
`AlgebraicGeometry.RingedSite.abelianGlobalSectionsFunctor` the derived internal Hom cluster
uses — are then the sections of `F` over `T`, naturally in `F`.

This is the bridge between that spelling and the evaluation spelling
`(CategoryTheory.sheafSections J AddCommGrpCat).obj (op T)`. The implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructure`
record that the two underived global-sections functors of the library, "both being the limit of
the underlying presheaf", had no bridge between them; on a site with a terminal object this file
supplies one.

## Main definitions

* `AlgebraicGeometry.RingedSite.sectionOfTerminal`: the compatible family determined by a
  section over a terminal object.
* `AlgebraicGeometry.RingedSite.globalSectionsAtTerminalIso`: the natural isomorphism
  `Γ(C, -) ≅ Γ(T, -)` of functors on abelian sheaves.

## Implementation notes

A compatible family is a section of the underlying presheaf viewed as a functor on `Cᵒᵖ`, so it
is determined by its value at the initial object `op T` of `Cᵒᵖ`, and conversely restriction
along the unique morphisms out of `T` turns a section over `T` into a compatible family: the
compatibility is the functoriality of `F` together with the uniqueness of morphisms into a
terminal object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe m u v w

variable (X : RingedSite.{u, v, w}) {T : X.C} (hT : IsTerminal T)

/-- **The compatible family determined by a section over a terminal object.** Its value over an
object `U` is the restriction of the given section along the unique morphism `U ⟶ T`. -/
def sectionOfTerminal (F : Sheaf X.J AddCommGrpCat.{max u m})
    (t : F.obj.obj (op T)) (U : X.Cᵒᵖ) : F.obj.obj U :=
  (F.obj.map (hT.from U.unop).op) t

/-- The family of `AlgebraicGeometry.RingedSite.sectionOfTerminal` is compatible with
restriction: two morphisms into a terminal object agree. -/
theorem sectionOfTerminal_map (F : Sheaf X.J AddCommGrpCat.{max u m})
    (t : F.obj.obj (op T)) {U V : X.Cᵒᵖ} (f : U ⟶ V) :
    (F.obj.map f) (sectionOfTerminal X hT F t U) = sectionOfTerminal X hT F t V := by
  have h : (hT.from U.unop).op ≫ f = (hT.from V.unop).op :=
    Quiver.Hom.unop_inj (hT.hom_ext _ _)
  dsimp only [sectionOfTerminal]
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, h]

/-- **Global sections on a site with a terminal object are sections over that object.** The
compatible families of sections of an abelian sheaf `F` over all objects of `C` are the sections
of `F` over a terminal object `T`, naturally in `F`. -/
def globalSectionsAtTerminalIso :
    abelianGlobalSectionsFunctor.{max u m} X ≅
      (sheafSections X.J AddCommGrpCat.{max u m}).obj (op T) :=
  NatIso.ofComponents
    (fun F => AddEquiv.toAddCommGrpIso
      { toFun := fun s => s.val (op T)
        invFun := fun t => ⟨sectionOfTerminal X hT F t, fun f =>
          sectionOfTerminal_map X hT F t f⟩
        left_inv := fun s => Subtype.ext (funext fun U => by
          dsimp only [sectionOfTerminal]
          exact s.property (hT.from U.unop).op)
        right_inv := fun t => by
          dsimp only [sectionOfTerminal]
          rw [show (hT.from (op T).unop).op = 𝟙 (op T) from
            Quiver.Hom.unop_inj (hT.hom_ext _ _)]
          simp
        map_add' := fun s s' => rfl })
    (by intros; rfl)

end AlgebraicGeometry.RingedSite

end
