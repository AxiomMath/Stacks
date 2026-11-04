module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FreeSplitUniverse

/-!
# The fibre of a free sheaf of modules at a point of a site

Let `(C, J)` be a site with a point `Φ` and `R` a ring. The free sheaf of `R`-modules `R[P]` on a
sheaf of sets `P` is the sheafification of the free module on the sections of `P`. Its fibre at
`Φ` is the free module on the fibre of `P`: fibres do not see sheafification, and the free module
functor, a left adjoint, commutes with the filtered colimits computing fibres.

## Main definitions

* `ModuleCat.freeSplitAdj`: the free–forgetful adjunction for `ModuleCat.freeSplit`.
* `CategoryTheory.GrothendieckTopology.Point.freeSheafFiberIso`: the fibre of `R[P]` is `R[Φ P]`,
  naturally in `P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace ModuleCat

variable (R : Type) [Ring R]

/-- **The free–forgetful adjunction** at split universes, for a ring `R : Type` and carriers in
`Type w`. -/
def freeSplitAdj : freeSplit.{w, 0} R ⊣ forget (ModuleCat.{w} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun S M => freeSplitHomEquiv.trans TypeCat.homEquiv.symm
      homEquiv_naturality_left_symm := fun {S S' M} f g => by
        apply freeSplit_hom_ext
        intro x
        simp [freeSplitHomEquiv]
      homEquiv_naturality_right := fun {S M M'} f g => rfl }

end ModuleCat

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : J.Point.{w})
  [LocallySmall.{w} C] (R : Type) [Ring R] [HasWeakSheafify J (ModuleCat.{w} R)]

/-- **The fibre of the free sheaf of modules on a sheaf of sets is the free module on its fibre**,
naturally in the sheaf of sets. -/
def freeSheafFiberIso :
    Sheaf.composeAndSheafify J (ModuleCat.freeSplit.{w, 0} R) ⋙ Φ.sheafFiber ≅
      Φ.sheafFiber (A := Type w) ⋙ ModuleCat.freeSplit.{w, 0} R :=
  haveI : PreservesFilteredColimitsOfSize.{w, w} (ModuleCat.freeSplit.{w, 0} R) :=
    have := (ModuleCat.freeSplitAdj.{w} R).leftAdjoint_preservesColimits
    inferInstance
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type w))
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft ((Functor.whiskeringRight _ _ _).obj
          (ModuleCat.freeSplit.{w, 0} R))
          (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{w} R)) ≪≫
        Φ.presheafFiberCompIso (ModuleCat.freeSplit.{w, 0} R)) ≪≫
    (Functor.associator _ _ _).symm

/-- **The fibre iso on germs of generators**: the germ of the generator `[p]` of the free sheaf
goes to the generator on the germ of `p`. -/
theorem freeSheafFiberIso_hom_app_toPresheafFiber (P : Sheaf J (Type w)) (X : C)
    (x : Φ.fiber.obj X) (p : P.obj.obj (Opposite.op X)) :
    (Φ.freeSheafFiberIso R).hom.app P
      (Φ.toPresheafFiber X x ((Sheaf.composeAndSheafify J (ModuleCat.freeSplit.{w, 0} R)).obj P).obj
        ((CategoryTheory.toSheafify J (P.obj ⋙ ModuleCat.freeSplit.{w, 0} R)).app (Opposite.op X)
          (ModuleCat.freeSplitMk p))) =
      ModuleCat.freeSplitMk (Φ.toPresheafFiber X x P.obj p) := by
  have : PreservesFilteredColimitsOfSize.{w, w} (ModuleCat.freeSplit.{w, 0} R) :=
    have := (ModuleCat.freeSplitAdj.{w} R).leftAdjoint_preservesColimits
    inferInstance
  have h1 : Φ.toPresheafFiber X x ((Sheaf.composeAndSheafify J
        (ModuleCat.freeSplit.{w, 0} R)).obj P).obj
        ((CategoryTheory.toSheafify J (P.obj ⋙ ModuleCat.freeSplit.{w, 0} R)).app (Opposite.op X)
          (ModuleCat.freeSplitMk p)) =
      Φ.presheafFiber.map (CategoryTheory.toSheafify J (P.obj ⋙ ModuleCat.freeSplit.{w, 0} R))
        (Φ.toPresheafFiber X x (P.obj ⋙ ModuleCat.freeSplit.{w, 0} R)
          (ModuleCat.freeSplitMk p)) :=
    (ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality
      (CategoryTheory.toSheafify J (P.obj ⋙ ModuleCat.freeSplit.{w, 0} R)) X x)
      (ModuleCat.freeSplitMk p)).symm
  rw [h1]
  show (Φ.presheafFiberCompIso (ModuleCat.freeSplit.{w, 0} R)).hom.app P.obj
      (inv (Φ.presheafFiber.map
        (CategoryTheory.toSheafify J (P.obj ⋙ ModuleCat.freeSplit.{w, 0} R)))
        (Φ.presheafFiber.map (CategoryTheory.toSheafify J (P.obj ⋙ ModuleCat.freeSplit.{w, 0} R))
          (Φ.toPresheafFiber X x (P.obj ⋙ ModuleCat.freeSplit.{w, 0} R)
            (ModuleCat.freeSplitMk p)))) = _
  have h2 := ConcreteCategory.congr_hom (IsIso.hom_inv_id
    (Φ.presheafFiber.map (CategoryTheory.toSheafify J (P.obj ⋙ ModuleCat.freeSplit.{w, 0} R))))
    (Φ.toPresheafFiber X x (P.obj ⋙ ModuleCat.freeSplit.{w, 0} R) (ModuleCat.freeSplitMk p))
  rw [ModuleCat.comp_apply] at h2
  rw [h2]
  have h3 := ConcreteCategory.congr_hom (Φ.toPresheafFiber_presheafFiberCompIso_hom_app
    (ModuleCat.freeSplit.{w, 0} R) X x P.obj) (ModuleCat.freeSplitMk p)
  rw [ModuleCat.comp_apply] at h3
  exact h3.trans (ModuleCat.freeSplit_map_apply _ _)

end CategoryTheory.GrothendieckTopology.Point

end
