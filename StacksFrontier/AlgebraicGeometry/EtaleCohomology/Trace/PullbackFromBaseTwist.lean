module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BaseChangeTwistTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat

/-!
# The Frobenius twist of a sheaf pulled back along a morphism over `k`

Let `k` be a finite field, `i : Z ⟶ Y` a morphism of schemes over `k` and `k̄` an extension of
`k`, with base change `i_k̄ : Z_k̄ ⟶ Y_k̄`. For a sheaf `L` of `Λ`-modules on `Y_étale`, the
canonical Frobenius twist of the inverse image `i⁻¹ L` on `Z_k̄` is carried, by the base change
map `L|_{Y_k̄} ⟶ (i_k̄)_* ((i⁻¹ L)|_{Z_k̄})`, to the canonical Frobenius twist of `L` on `Y_k̄`
(`Stacks.EtaleCohomology.etaleModuleBaseChangeMap_comp_frobeniusBaseChangeTwist`). This is the
instance of `Stacks.EtaleCohomology.etaleModuleBaseChangeMap_comp_twist` at the two geometric
Frobenius squares, the compatibility of the two Frobenius descent isomorphisms with `i_*` being
`Stacks.EtaleCohomology.geometricFrobeniusPushforwardIso_hom_app_directImage`.

For `Y = Spec k` and `Z` a curve over `k` this computes the Frobenius of a sheaf pulled back from
the base field: on `(Spec k)_k̄ = Spec k̄` the twist is the action of the geometric Frobenius on
the stalk, which is how the Galois action on the coinvariants `F''` of [Stacks, Tag 03VK]
enters the Frobenius of `H²_c`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleBaseChangeMap_comp_frobeniusBaseChangeTwist`: the base
  change map intertwines the Frobenius twists of `L` and of `i⁻¹ L`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))}
  (i : Z ⟶ Y) (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The base change map `L|_{Y_k̄} ⟶ (i_k̄)_* ((i⁻¹ L)|_{Z_k̄})` along a morphism `i : Z ⟶ Y`
over `k`. -/
abbrev fieldBaseChangeInverseImageMap :=
  etaleModuleBaseChangeMap Λ (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar) i.left
    (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Z kbar ≫ i.left) rfl
    (fieldBaseChangeMap_comp_fst i kbar).symm

/-- **The base change map intertwines the Frobenius twists of `L` and of `i⁻¹ L`.** -/
theorem etaleModuleBaseChangeMap_comp_frobeniusBaseChangeTwist (L : EtaleModules.{u, r} Λ Y.left) :
    (fieldBaseChangeInverseImageMap Λ i kbar).app L ≫
        (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar)).map
          ((frobeniusBaseChangeTwist.{u, r} Λ Z kbar p q hcard).app
            ((etaleModuleInverseImage.{u, r} Λ i.left).obj L)) ≫
        ((etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Z kbar p q hcard)
            (fieldBaseChangeMap i kbar)
            (geometricFrobeniusBaseChange Z kbar p q hcard ≫ fieldBaseChangeMap i kbar) rfl).hom.app
            ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Z kbar)).obj
              ((etaleModuleInverseImage.{u, r} Λ i.left).obj L)) ≫
          (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap i kbar)
            (geometricFrobeniusBaseChange Y kbar p q hcard)
            (geometricFrobeniusBaseChange Z kbar p q hcard ≫ fieldBaseChangeMap i kbar)
            (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)).inv.app
            ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Z kbar)).obj
              ((etaleModuleInverseImage.{u, r} Λ i.left).obj L))) =
      (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app L ≫
        (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          ((fieldBaseChangeInverseImageMap Λ i kbar).app L) := by
  refine etaleModuleBaseChangeMap_comp_twist Λ (fieldBaseChangeProj Y kbar)
    (fieldBaseChangeProj Z kbar) i.left (fieldBaseChangeMap i kbar) _ rfl
    (fieldBaseChangeMap_comp_fst i kbar).symm
    (geometricFrobeniusBaseChange Y kbar p q hcard) (geometricFrobenius Y p q hcard).left
    (geometricFrobeniusBaseChange_comp_fst Y kbar p q hcard)
    (geometricFrobeniusBaseChange Z kbar p q hcard) (geometricFrobenius Z p q hcard).left
    (geometricFrobeniusBaseChange_comp_fst Z kbar p q hcard) _ rfl
    (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar) _ rfl
    (geometricFrobenius_left_comp p q hcard i)
    (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{max (u + 1) r} Λ)).hom
    (geometricFrobeniusPushforwardIso Z p q hcard (ModuleCat.{max (u + 1) r} Λ)).hom ?_ L
  intro M
  rw [geometricFrobeniusPushforwardIso_hom_app_directImage Λ i p q hcard M]
  simp only [directImageTwistTransfer, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

end Stacks.EtaleCohomology

end
