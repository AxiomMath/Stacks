module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyForgetCommShift
public import Mathlib.CategoryTheory.Shift.Localization

/-!
# Forgetting the action `D(A, d) ⥤ D(O)` commutes with the translations

Let `X` be a ringed site and `(A, d)` a sheaf of differential graded algebras on it. Forgetting the
action of `A` is the functor `SheafOfModules.DifferentialGradedModule.derivedForget :
D(A, d) ⥤ D(O)`, induced from `homotopyForget : K(Mod(A, d)) ⥤ D(O)` along the localization
`K(Mod(A, d)) ⥤ D(A, d)`. Since `homotopyForget` commutes with the translations
(`SheafOfModules.DifferentialGradedModule.homotopyForget_commShift`), so does the induced functor
(Mathlib's `Functor.commShiftOfLocalization`); at the image of a module it is the commutation of
the localization functor `Q : K(O) ⥤ D(O)` with the translation, at the underlying complex.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedForget_commShift`: the commutation of
  `derivedForget` with the translations.

## Main results

* `SheafOfModules.DifferentialGradedModule.derivedForget_commShiftIso_hom_app`: its value at the
  image of a module.
-/

@[expose] public section

open CategoryTheory

universe w u

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [HasDerivedCategory.{w} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- `derivedForget` is induced by `homotopyForget` along the localization functor
`K(Mod(A, d)) ⥤ D(A, d)`; the two composites agree on objects. -/
noncomputable instance derivedForget_lifting :
    Localization.Lifting (toDerivedCategory.{u, u, u} A) (quasiIsomorphisms.{u, u, u} A)
      (homotopyForget.{w, u, u, u} A) (derivedForget.{w, u, u, u} A) :=
  ⟨NatIso.ofComponents (fun _ => Iso.refl _) (fun {Z Z'} f => by
    have h := Functor.congr_hom (toDerivedCategory_comp_derivedForget.{w, u, u, u} A) f
    refine (Category.comp_id _).trans (h.trans ?_)
    change 𝟙 _ ≫ (homotopyForget.{w, u, u, u} A).map f ≫ 𝟙 _ =
      𝟙 _ ≫ (homotopyForget.{w, u, u, u} A).map f
    rw [Category.id_comp, Category.comp_id, Category.id_comp])⟩

/-- **Forgetting the action `D(A, d) ⥤ D(O)` commutes with the translations.** -/
@[instance_reducible]
noncomputable instance derivedForget_commShift : (derivedForget.{w, u, u, u} A).CommShift ℤ :=
  Functor.commShiftOfLocalization (toDerivedCategory.{u, u, u} A)
    (quasiIsomorphisms.{u, u, u} A) ℤ (homotopyForget.{w, u, u, u} A) (derivedForget.{w, u, u, u} A)

/-- Forgetting the action of an image under the localization functor `K(Mod(A, d)) ⥤ D(A, d)`
is forgetting it on the homotopy category. -/
theorem derivedForget_map_toDerivedCategory_map_eq {Z Z' : HomotopyCategory.{u, u, u} A}
    (f : Z ⟶ Z') :
    (derivedForget.{w, u, u, u} A).map ((toDerivedCategory.{u, u, u} A).map f) =
      (homotopyForget.{w, u, u, u} A).map f := by
  have h := Functor.congr_hom (toDerivedCategory_comp_derivedForget.{w, u, u, u} A) f
  refine h.trans ?_
  change 𝟙 _ ≫ (homotopyForget.{w, u, u, u} A).map f ≫ 𝟙 _ = (homotopyForget.{w, u, u, u} A).map f
  rw [Category.id_comp, Category.comp_id]

/-- **The commutation of forgetting the action with the translations, at the image of an object
of the homotopy category**: the commutation of `toDerivedCategory` with the translation, read
backwards, followed by that of `homotopyForget`. -/
theorem derivedForget_commShiftIso_hom_app (n : ℤ) (Z : HomotopyCategory.{u, u, u} A) :
    ((derivedForget.{w, u, u, u} A).commShiftIso n).hom.app
        ((toDerivedCategory.{u, u, u} A).obj Z) =
      ((derivedForget.{w, u, u, u} A).map
          (((toDerivedCategory.{u, u, u} A).commShiftIso n).inv.app Z) ≫
        ((homotopyForget.{w, u, u, u} A).commShiftIso n).hom.app Z :
          (derivedForget.{w, u, u, u} A).obj (((toDerivedCategory.{u, u, u} A).obj Z)⟦n⟧) ⟶
            ((derivedForget.{w, u, u, u} A).obj ((toDerivedCategory.{u, u, u} A).obj Z))⟦n⟧) := by
  rw [Functor.commShiftOfLocalization_iso_hom_app]
  exact congrArg (_ ≫ ·) ((Category.id_comp _).trans ((congrArg (_ ≫ ·)
    ((shiftFunctor _ n).map_id ((homotopyForget.{w, u, u, u} A).obj Z))).trans
      (Category.comp_id _)))

/-- **The commutation of forgetting the action with the translations, at a module**: the
commutation of `toDerivedCategory` with the translation, read backwards, the transport along the
identification of the underlying complex of the translate with the translate of the underlying
complex, and the commutation of `Q` with the translation. -/
theorem derivedForget_commShiftIso_hom_app_quotient (n : ℤ)
    (M : DifferentialGradedModule.{u, u, u} A) :
    ((derivedForget.{w, u, u, u} A).commShiftIso n).hom.app
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M)) =
      ((derivedForget.{w, u, u, u} A).map (((toDerivedCategory.{u, u, u} A).commShiftIso n).inv.app
          ((HomotopyCategory.quotient A).obj M)) ≫
        eqToHom (homotopyForget_obj_shift.{w} A n M) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app M.complex :
          (derivedForget.{w, u, u, u} A).obj
              (((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M))⟦n⟧) ⟶
            ((derivedForget.{w, u, u, u} A).obj
              ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M)))⟦n⟧) := by
  rw [derivedForget_commShiftIso_hom_app, homotopyForget_commShiftIso_hom_app]
  rfl

end SheafOfModules.DifferentialGradedModule

end
