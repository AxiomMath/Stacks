module

public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!
# Shrinking a presheaf of types with small values: sheaves, subfunctors, representability

For a presheaf `G : Cᵒᵖ ⥤ Type w'` all of whose values are `w`-small, Mathlib's
`CategoryTheory.FunctorToTypes.shrink` is a presheaf in `Type w` with values `Shrink (G.obj X)`.
This file records that shrinking preserves the sheaf condition, transports subfunctors and their
representing objects, and reflects representability.

## Main definitions

* `CategoryTheory.FunctorToTypes.shrinkSubfunctor`: a subfunctor of `G`, as a subfunctor of the
  shrunk presheaf.

## Main results

* `CategoryTheory.FunctorToTypes.isSheaf_shrink`: the shrunk presheaf of a sheaf is a sheaf.
* `CategoryTheory.FunctorToTypes.shrinkSubfunctorRepresentableBy`: a represented subfunctor stays
  represented by the same object.
* `CategoryTheory.FunctorToTypes.representableByOfShrink`: an object representing the shrunk
  presheaf represents `G`.
-/

@[expose] public noncomputable section

universe w w' v u

open CategoryTheory Opposite

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C] (G : Cᵒᵖ ⥤ Type w') [FunctorToTypes.Small.{w} G]

/-- The shrunk presheaf acts on a morphism `g` by conjugating `G.map g` with `equivShrink`. -/
theorem shrink_map_apply {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : (shrink.{w} G).obj X) :
    (shrink.{w} G).map g x = equivShrink _ (G.map g ((equivShrink _).symm x)) :=
  rfl

/-- **The shrunk presheaf of a sheaf is a sheaf.** -/
theorem isSheaf_shrink {J : GrothendieckTopology C} (hG : Presieve.IsSheaf J G) :
    Presieve.IsSheaf J (shrink.{w} G) := by
  have e : shrink.{w} G ⋙ uliftFunctor.{max w w'} ≅ G ⋙ uliftFunctor.{max w w'} :=
    NatIso.ofComponents (fun X => Equiv.toIso (Equiv.ulift.trans ((equivShrink _).symm.trans
      Equiv.ulift.symm))) (fun {X Y} g => by
        ext x
        show ULift.up ((equivShrink _).symm
            (equivShrink _ (G.map g ((equivShrink _).symm x.down)))) =
          ULift.up (G.map g ((equivShrink _).symm x.down))
        rw [Equiv.symm_apply_apply])
  exact (Presieve.isSheaf_comp_uliftFunctor_iff J).1
    (Presieve.isSheaf_iso J e.symm ((Presieve.isSheaf_comp_uliftFunctor_iff J).2 hG))

/-- A subfunctor of `G`, as a subfunctor of the shrunk presheaf. -/
def shrinkSubfunctor (F : Subfunctor G) : Subfunctor (shrink.{w} G) where
  obj X := (equivShrink _).symm ⁻¹' F.obj X
  map {X Y} g x hx := by simpa [shrink_map_apply] using F.map g hx

/-- An element of the shrunk presheaf lies in `shrinkSubfunctor G F` if and only if its preimage
under `equivShrink` lies in `F`. -/
theorem mem_shrinkSubfunctor_iff (F : Subfunctor G) {X : Cᵒᵖ} (x : (shrink.{w} G).obj X) :
    x ∈ (shrinkSubfunctor.{w} G F).obj X ↔ (equivShrink _).symm x ∈ F.obj X :=
  Iff.rfl

/-- The values of a subfunctor and of its shrunk counterpart correspond. -/
def shrinkSubfunctorObjEquiv (F : Subfunctor G) (X : Cᵒᵖ) :
    F.toFunctor.obj X ≃ (shrinkSubfunctor.{w} G F).toFunctor.obj X where
  toFun z := ⟨equivShrink _ z.1, by
    change (equivShrink _).symm (equivShrink _ z.1) ∈ F.obj X
    rw [Equiv.symm_apply_apply]
    exact z.2⟩
  invFun z := ⟨(equivShrink _).symm z.1, z.2⟩
  left_inv z := Subtype.ext ((equivShrink _).symm_apply_apply z.1)
  right_inv z := Subtype.ext ((equivShrink _).apply_symm_apply z.1)

/-- **A represented subfunctor of `G` is represented, by the same object, as a subfunctor of the
shrunk presheaf.** -/
def shrinkSubfunctorRepresentableBy (F : Subfunctor G) {Y : C}
    (e : F.toFunctor.RepresentableBy Y) :
    (shrinkSubfunctor.{w} G F).toFunctor.RepresentableBy Y where
  homEquiv {X} := e.homEquiv.trans (shrinkSubfunctorObjEquiv G F (op X))
  homEquiv_comp {X X'} g h := by
    apply Subtype.ext
    change equivShrink _ (e.homEquiv (g ≫ h)).1 =
      equivShrink _ (G.map g.op ((equivShrink _).symm (equivShrink _ (e.homEquiv h).1)))
    rw [Equiv.symm_apply_apply, e.homEquiv_comp]
    rfl

/-- **An object representing the shrunk presheaf represents `G`.** -/
def representableByOfShrink {Y : C} (e : (shrink.{w} G).RepresentableBy Y) :
    G.RepresentableBy Y where
  homEquiv {X} := e.homEquiv.trans (equivShrink _).symm
  homEquiv_comp {X X'} g h := by
    change (equivShrink _).symm (e.homEquiv (g ≫ h)) = _
    rw [e.homEquiv_comp, shrink_map_apply, Equiv.symm_apply_apply]
    rfl

end CategoryTheory.FunctorToTypes

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {G G' : Cᵒᵖ ⥤ Type w'}

/-- **The preimage of a represented subfunctor along an isomorphism is represented by the same
object.** -/
def preimageIsoRepresentableBy (F : Subfunctor G) (α : G' ≅ G) {Y : C}
    (e : F.toFunctor.RepresentableBy Y) : (F.preimage α.hom).toFunctor.RepresentableBy Y where
  homEquiv {X} := e.homEquiv.trans
    { toFun := fun z => ⟨α.inv.app _ z.1, by simpa using z.2⟩
      invFun := fun z => ⟨α.hom.app _ z.1, z.2⟩
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun z => Subtype.ext (by simp) }
  homEquiv_comp {X X'} g h := Subtype.ext <| by
    change α.inv.app _ (e.homEquiv (g ≫ h)).1 = G'.map g.op (α.inv.app _ (e.homEquiv h).1)
    rw [e.homEquiv_comp]
    exact ConcreteCategory.congr_hom (α.inv.naturality g.op) (e.homEquiv h).1

end CategoryTheory.Subfunctor
